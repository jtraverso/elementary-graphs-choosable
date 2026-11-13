/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.ECol
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.AppBuilder

/-!
# The configuration tactic `elem_contra`

`elem_contra K [v₁, …, vₙ]` refutes the goal (or proves a linear consequence about `K.c`) by a
parity argument: it reads the local context once, collecting the hypotheses `G.Adj a b`,
`¬ G.Adj a b` and `a ≠ b`, adds the equation `K.c u v + K.c v w = 1` for every induced `P3`
`u - v - w` among the listed vertices whose adjacency, non-adjacency and distinctness facts are
available (distinctness also from a vertex adjacent to one end and not to the other), adds the
symmetry equations `K.c u v = K.c v u`, and calls `omega`.
-/

public meta section

namespace ElemChoos.MR

open Lean Meta Elab Tactic

/-- The arguments `(a, b)` of a hypothesis `G.Adj a b`, `¬ G.Adj a b` or `a ≠ b`. -/
def ecPair? (e : Expr) : Option (Nat × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``SimpleGraph.Adj 4 then
    some (0, e.getArg! 2, e.getArg! 3)
  else if e.isAppOfArity ``Not 1 then
    let f := e.appArg!.consumeMData
    if f.isAppOfArity ``SimpleGraph.Adj 4 then some (1, f.getArg! 2, f.getArg! 3)
    else if f.isAppOfArity ``Eq 3 then some (2, f.getArg! 1, f.getArg! 2)
    else none
  else if e.isAppOfArity ``Ne 3 then
    some (2, e.getArg! 1, e.getArg! 2)
  else none

elab "elem_contra " K:term:max " [" ws:term,* "]" : tactic => withMainContext do
  let k ← instantiateMVars (← Term.elabTerm K none)
  let vs : Array Expr ← ws.getElems.mapM fun w =>
    (do instantiateMVars (← Term.elabTerm w none) : TermElabM Expr)
  let mut adj : Array (Expr × Expr × Expr) := #[]
  let mut nadj : Array (Expr × Expr × Expr) := #[]
  let mut nes : Array (Expr × Expr × Expr) := #[]
  let mut mems : Array (Expr × Expr × Expr) := #[]
  let mut nmems : Array (Expr × Expr × Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' := ty.consumeMData
    if ty'.isAppOfArity ``Membership.mem 5 then
      mems := mems.push (ty'.getArg! 3, ty'.getArg! 4, d.toExpr)
    if ty'.isAppOfArity ``Not 1 then
      let f := ty'.appArg!.consumeMData
      if f.isAppOfArity ``Membership.mem 5 then
        nmems := nmems.push (f.getArg! 3, f.getArg! 4, d.toExpr)
    match ecPair? ty with
    | some (0, a, b) => adj := adj.push (a, b, d.toExpr)
    | some (1, a, b) => nadj := nadj.push (a, b, d.toExpr)
    | some (_, a, b) => nes := nes.push (a, b, d.toExpr)
    | none => pure ()
  let findIn (arr : Array (Expr × Expr × Expr)) (a b : Expr) : Option Expr :=
    (arr.find? fun (x, y, _) => x == a && y == b).map fun (_, _, p) => p
  let getAdj (a b : Expr) : MetaM (Option Expr) := do
    match findIn adj a b with
    | some p => return some p
    | none =>
      match findIn adj b a with
      | some p => return some (← mkAppM ``SimpleGraph.Adj.symm #[p])
      | none => return none
  let getNadj (a b : Expr) : MetaM (Option Expr) := do
    match findIn nadj a b with
    | some p => return some p
    | none =>
      match findIn nadj b a with
      | some p => return some (← mkAppM ``ElemChoos.MR.nadj_symm #[p])
      | none => return none
  let getNe (a b : Expr) : MetaM (Option Expr) := do
    if let some p := findIn nes a b then return some p
    if let some p := findIn nes b a then return some (← mkAppM ``Ne.symm #[p])
    -- a set containing one and not the other
    for (c, e, p) in mems do
      if e == a then
        for (c', e', q) in nmems do
          if e' == b && c' == c then
            return some (← mkAppM ``ElemChoos.MR.ne_of_mem_nmem #[p, q])
      if e == b then
        for (c', e', q) in nmems do
          if e' == a && c' == c then
            return some (← mkAppM ``Ne.symm #[← mkAppM ``ElemChoos.MR.ne_of_mem_nmem #[p, q]])
    -- a witness among all vertices of the adjacency hypotheses
    for (p, q, _) in adj do
      for x in #[p, q] do
        if let some h1 ← getAdj a x then
          if let some h2 ← getNadj b x then
            return some (← mkAppM ``ElemChoos.MR.ne_of_adj_nadj #[h1, h2])
        if let some h1 ← getAdj b x then
          if let some h2 ← getNadj a x then
            return some (← mkAppM ``Ne.symm #[← mkAppM ``ElemChoos.MR.ne_of_adj_nadj #[h1, h2]])
    return none
  let n := vs.size
  -- the induced `P3`s: (node of `uv`, node of `vw`, proof), nodes = unordered pairs of indices
  let key (a b : Nat) : Nat := if a < b then a * n + b else b * n + a
  let mut p3s : Array (Nat × Nat × Expr) := #[]
  for i in [0:n] do
    for j in [i+1:n] do
      let u := vs[i]!
      let w := vs[j]!
      for l in [0:n] do
        let v := vs[l]!
        if l == i || l == j then continue
        let some h1 ← getAdj u v | continue
        let some h2 ← getAdj v w | continue
        let some h4 ← getNadj u w | continue
        let some h3 ← getNe u w | continue
        p3s := p3s.push (key i l, key l j, ← mkAppM ``ElemChoos.MR.ECol.p3 #[k, u, v, w, h1, h2, h3, h4])
  -- look for an odd cycle in the parity graph (each `P3` says: the two pairs differ)
  let mut cycle : Option (Array Nat) := none
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  let isFalse := tgt.consumeMData.isConstOf ``False
  if isFalse then
    let size := n * n
    let mut nbrs : Array (Array (Nat × Nat)) := Array.replicate size #[]
    for t in [0:p3s.size] do
      let (a, b, _) := p3s[t]!
      nbrs := nbrs.modify a (·.push (b, t))
      nbrs := nbrs.modify b (·.push (a, t))
    let mut color : Array (Option Bool) := Array.replicate size none
    let mut par : Array (Option (Nat × Nat)) := Array.replicate size none
    for r in [0:size] do
      if cycle.isSome then break
      if color[r]!.isSome || nbrs[r]!.isEmpty then continue
      color := color.set! r (some false)
      let mut queue : Array Nat := #[r]
      let mut qi := 0
      while qi < queue.size && cycle.isNone do
        let a := queue[qi]!
        qi := qi + 1
        let ca := color[a]!.getD false
        for (b, t) in nbrs[a]! do
          match color[b]! with
          | none =>
            color := color.set! b (some (!ca))
            par := par.set! b (some (a, t))
            queue := queue.push b
          | some cb =>
            if cb == ca && cycle.isNone then
              -- paths to the root
              let mut pa : Array (Nat × Nat) := #[]
              let mut x := a
              while (par[x]!).isSome do
                let (y, e) := (par[x]!).get!
                pa := pa.push (x, e)
                x := y
              let mut pb : Array (Nat × Nat) := #[]
              x := b
              while (par[x]!).isSome do
                let (y, e) := (par[x]!).get!
                pb := pb.push (x, e)
                x := y
              -- drop the common part (below the lowest common ancestor)
              while pa.size > 0 && pb.size > 0 && pa.back!.2 == pb.back!.2 do
                pa := pa.pop
                pb := pb.pop
              cycle := some ((pa.map (·.2)) ++ (pb.map (·.2)) |>.push t)
  let chosen : Array Nat := cycle.getD (Array.range p3s.size)
  let mut facts : Array Expr := chosen.map fun t => (p3s[t]!).2.2
  -- symmetry equations for the pairs involved
  let mut used : Array Nat := #[]
  for t in chosen do
    let (a, b, _) := p3s[t]!
    used := used.push a |>.push b
  for i in [0:n] do
    for j in [i+1:n] do
      if cycle.isNone || used.contains (key i j) then
        facts := facts.push (← mkAppM ``ElemChoos.MR.ECol.symm #[k, vs[i]!, vs[j]!])
  let hyps ← facts.mapM fun p => do
    return ({ userName := `ec, type := ← inferType p, value := p } : Hypothesis)
  let g ← getMainGoal
  let (_, g') ← g.assertHypotheses hyps
  replaceMainGoal [g']
  evalTactic (← `(tactic| omega))

end ElemChoos.MR
