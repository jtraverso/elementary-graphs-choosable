/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card

/-!
# Elementary colourings: basic facts and the configuration tactic

We fix an elementary colouring as a `0/1`-valued symmetric function `c` on pairs of vertices
such that the two edges of every induced `P3` get different values (`c u v + c v w = 1`).

Every forbidden configuration used by Maffray and Reed (claw, odd hole, pyramid, lighthouse,
mausoleum, garden, colossus) has an odd cycle in its Gallai graph, so it is refuted by a parity
argument: the tactic `elem_contra K [v₁, …, vₙ]` adds the equation `c u v + c v w = 1` for every
induced `P3` among the listed vertices whose adjacencies are hypotheses, together with the
symmetry equations, and closes the goal with `omega`.
-/

@[expose] public section

namespace ElemChoos.MR

variable {V : Type*}

/-- An elementary colouring of `G`, with values `0` (blue) and `1` (red). -/
structure ECol (G : SimpleGraph V) where
  /-- The colour of the pair `{u, v}`. -/
  c : V → V → ℕ
  le_one : ∀ u v, c u v ≤ 1
  symm : ∀ u v, c u v = c v u
  p3 : ∀ u v w, G.Adj u v → G.Adj v w → u ≠ w → ¬ G.Adj u w → c u v + c v w = 1

/-- Discharge an adjacency goal from a hypothesis (in either orientation). -/
macro "ec_adj" : tactic =>
  `(tactic| first | assumption | exact SimpleGraph.Adj.symm (by assumption))

/-- Discharge a distinctness goal `u ≠ w`. -/
macro "ec_ne" : tactic =>
  `(tactic| first | assumption | exact Ne.symm (by assumption) |
      (intro h; subst h; first | contradiction |
        ((try simp only [SimpleGraph.adj_comm] at *) <;> contradiction)))

/-- Discharge a non-adjacency goal `¬ G.Adj u w` (in either orientation). -/
macro "ec_nadj0" : tactic =>
  `(tactic| first | assumption |
      (intro h; exact absurd (SimpleGraph.Adj.symm h) (by assumption)))

/-- Discharge a non-adjacency goal `¬ G.Adj u w`. -/
syntax "ec_nadj " term:max ppSpace term:max : tactic
macro_rules
  | `(tactic| ec_nadj $_u $_w) => `(tactic| ec_nadj0)

/-- Try to add the `P3` equation for `u - v - w`. -/
syntax "ec_p3 " term:max ppSpace term:max ppSpace term:max ppSpace term:max : tactic
macro_rules
  | `(tactic| ec_p3 $K $u $v $w) =>
    `(tactic| try have := ($K).p3 $u $v $w (by ec_adj) (by ec_adj) (by ec_ne) (by ec_nadj $u $w))

syntax "ec_l3 " term:max ppSpace term:max ppSpace term:max " [" term,* "]" : tactic
macro_rules
  | `(tactic| ec_l3 $_K $_u $_v []) => `(tactic| skip)
  | `(tactic| ec_l3 $K $u $v [$w]) => `(tactic| ec_p3 $K $u $v $w)
  | `(tactic| ec_l3 $K $u $v [$w, $ws,*]) =>
    `(tactic| (ec_p3 $K $u $v $w); ec_l3 $K $u $v [$ws,*])

syntax "ec_l2 " term:max ppSpace term:max " [" term,* "]" " [" term,* "]" : tactic
macro_rules
  | `(tactic| ec_l2 $_K $_u [] [$_ws,*]) => `(tactic| skip)
  | `(tactic| ec_l2 $K $u [$v] [$ws,*]) => `(tactic| ec_l3 $K $u $v [$ws,*])
  | `(tactic| ec_l2 $K $u [$v, $vs,*] [$ws,*]) =>
    `(tactic| (ec_l3 $K $u $v [$ws,*]); ec_l2 $K $u [$vs,*] [$ws,*])

syntax "ec_l1 " term:max " [" term,* "]" " [" term,* "]" : tactic
macro_rules
  | `(tactic| ec_l1 $_K [] [$_ws,*]) => `(tactic| skip)
  | `(tactic| ec_l1 $_K [$_u] [$_ws,*]) => `(tactic| skip)
  | `(tactic| ec_l1 $K [$u, $us,*] [$ws,*]) =>
    `(tactic| (ec_l2 $K $u [$ws,*] [$us,*]); ec_l1 $K [$us,*] [$ws,*])

syntax "ec_s2 " term:max ppSpace term:max " [" term,* "]" : tactic
macro_rules
  | `(tactic| ec_s2 $_K $_u []) => `(tactic| skip)
  | `(tactic| ec_s2 $K $u [$v]) => `(tactic| have := ($K).symm $u $v)
  | `(tactic| ec_s2 $K $u [$v, $vs,*]) =>
    `(tactic| (have := ($K).symm $u $v); ec_s2 $K $u [$vs,*])

syntax "ec_s1 " term:max " [" term,* "]" " [" term,* "]" : tactic
macro_rules
  | `(tactic| ec_s1 $_K [] [$_ws,*]) => `(tactic| skip)
  | `(tactic| ec_s1 $K [$u] [$ws,*]) => `(tactic| ec_s2 $K $u [$ws,*])
  | `(tactic| ec_s1 $K [$u, $us,*] [$ws,*]) =>
    `(tactic| (ec_s2 $K $u [$ws,*]); ec_s1 $K [$us,*] [$ws,*])

/-- `elem_contra K [v₁, …, vₙ]`: refute (or prove a linear consequence about `K.c`) using all
induced `P3`s among the listed vertices whose adjacency facts are hypotheses. -/
syntax "elem_contra " term:max " [" term,* "]" : tactic
macro_rules
  | `(tactic| elem_contra $K [$ws,*]) =>
    `(tactic| (ec_l1 $K [$ws,*] [$ws,*]); (ec_s1 $K [$ws,*] [$ws,*]); omega)

variable {G : SimpleGraph V} (K : ECol G)

theorem ECol.same_adj {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : u ≠ w)
    (h : K.c u v = K.c v w) : G.Adj u w := by
  by_contra hn
  have := K.p3 u v w huv hvw huw hn
  have := K.le_one u v
  omega

/-- A *strong homogeneous pair* inside `W` (Maffray–Reed): two disjoint cliques with an edge
between them and at least three vertices, such that every other vertex of `W` sees none of one
of them and all or none of the other. -/
structure SHP (G : SimpleGraph V) (W C1 C2 : Finset V) : Prop where
  sub1 : C1 ⊆ W
  sub2 : C2 ⊆ W
  disj : Disjoint C1 C2
  clq1 : ∀ u ∈ C1, ∀ v ∈ C1, u ≠ v → G.Adj u v
  clq2 : ∀ u ∈ C2, ∀ v ∈ C2, u ≠ v → G.Adj u v
  edge : ∃ a ∈ C1, ∃ b ∈ C2, G.Adj a b
  three : 3 ≤ C1.card + C2.card
  homog : ∀ v ∈ W, v ∉ C1 → v ∉ C2 →
    ((∀ u ∈ C1, ¬ G.Adj v u) ∧ ((∀ u ∈ C2, G.Adj v u) ∨ ∀ u ∈ C2, ¬ G.Adj v u)) ∨
    ((∀ u ∈ C2, ¬ G.Adj v u) ∧ ((∀ u ∈ C1, G.Adj v u) ∨ ∀ u ∈ C1, ¬ G.Adj v u))

/-- `W` is connected in `G`: every nonempty proper subset has an edge leaving it. -/
def ConnOn (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ S ⊆ W, S.Nonempty → S ≠ W → ∃ u ∈ S, ∃ v ∈ W, v ∉ S ∧ G.Adj u v

/-- `W` has no (adjacent) twins. -/
def TwinFreeOn (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, u ≠ v → G.Adj u v → ∃ z ∈ W, z ≠ u ∧ z ≠ v ∧ ¬ (G.Adj z u ↔ G.Adj z v)

/-- The graph `D` of Maffray–Reed: `x o p2 p3 p4` is an induced path and `p1` sees all of
`o, p2, p3, p4` but not `x`. -/
def IsD (G : SimpleGraph V) (x o p1 p2 p3 p4 : V) : Prop :=
  G.Adj x o ∧ G.Adj o p2 ∧ G.Adj p2 p3 ∧ G.Adj p3 p4 ∧ G.Adj p1 o ∧ G.Adj p1 p2 ∧
  G.Adj p1 p3 ∧ G.Adj p1 p4 ∧ ¬ G.Adj x p1 ∧ ¬ G.Adj x p2 ∧ ¬ G.Adj x p3 ∧ ¬ G.Adj x p4 ∧
  ¬ G.Adj o p3 ∧ ¬ G.Adj o p4 ∧ ¬ G.Adj p2 p4

/-- A gem: `p1 p2 p3 p4` is an induced path and `q` sees all of it. -/
def IsGem (G : SimpleGraph V) (p1 p2 p3 p4 q : V) : Prop :=
  G.Adj p1 p2 ∧ G.Adj p2 p3 ∧ G.Adj p3 p4 ∧ ¬ G.Adj p1 p3 ∧ ¬ G.Adj p1 p4 ∧ ¬ G.Adj p2 p4 ∧
  G.Adj q p1 ∧ G.Adj q p2 ∧ G.Adj q p3 ∧ G.Adj q p4

/-- A 4-wheel: `p1 p2 p3 p4` is an induced square and `q` sees all of it. -/
def IsWheel (G : SimpleGraph V) (p1 p2 p3 p4 q : V) : Prop :=
  G.Adj p1 p2 ∧ G.Adj p2 p3 ∧ G.Adj p3 p4 ∧ G.Adj p4 p1 ∧ ¬ G.Adj p1 p3 ∧ ¬ G.Adj p2 p4 ∧
  p1 ≠ p3 ∧ p2 ≠ p4 ∧ G.Adj q p1 ∧ G.Adj q p2 ∧ G.Adj q p3 ∧ G.Adj q p4

/-- Test: a claw is not elementary. -/
example {o a b d : V} (h1 : G.Adj o a) (h2 : G.Adj o b) (h3 : G.Adj d o) (n1 : ¬ G.Adj a b)
    (n2 : ¬ G.Adj a d) (n3 : ¬ G.Adj b d) (d1 : a ≠ b) (d2 : a ≠ d) (d3 : b ≠ d) : False := by
  elem_contra K [o, a, b, d]

/-- Test: a 5-hole is not elementary. -/
example {v0 v1 v2 v3 v4 : V} (h1 : G.Adj v0 v1) (h2 : G.Adj v1 v2) (h3 : G.Adj v2 v3)
    (h4 : G.Adj v3 v4) (h5 : G.Adj v4 v0) (n1 : ¬ G.Adj v0 v2) (n2 : ¬ G.Adj v1 v3)
    (n3 : ¬ G.Adj v2 v4) (n4 : ¬ G.Adj v3 v0) (n5 : ¬ G.Adj v4 v1) : False := by
  elem_contra K [v0, v1, v2, v3, v4]

end ElemChoos.MR
