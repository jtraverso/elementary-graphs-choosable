/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Flat
public import Mathlib.Logic.Relation

/-!
# Augmenting a flat edge (undoing a compression)

Let `(C1, C2)` be a strong homogeneous pair in `W`, `a ∈ C1`, `b ∈ C2` adjacent, and let
`W' = (W \ (C1 ∪ C2)) ∪ {a, b}` be the compressed set. Given a normalized representation of
`W'` in which `ab` has the normal form of `flat_normal` (on side `true`), we build a normalized
representation of `W`: old ends are doubled; every vertex of `C1` (resp. `C2`) takes the
`false`-end of `a` (resp. `b`); and every connected component of the bipartite graph of
`C1`–`C2` edges gets a fresh `true`-end, which is a hub when both sides of the component have at
least two vertices.
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Cross edges of the pair. -/
def crossRel (G : SimpleGraph V) (C1 C2 : Finset V) (u v : V) : Prop :=
  G.Adj u v ∧ ((u ∈ C1 ∧ v ∈ C2) ∨ (u ∈ C2 ∧ v ∈ C1))

theorem crossRel_symm {C1 C2 : Finset V} {u v : V} (h : crossRel G C1 C2 u v) :
    crossRel G C1 C2 v u :=
  ⟨h.1.symm, h.2.symm.imp And.symm And.symm⟩

theorem crossRT_symm {C1 C2 : Finset V} {u v : V}
    (h : Relation.ReflTransGen (crossRel G C1 C2) u v) :
    Relation.ReflTransGen (crossRel G C1 C2) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (crossRel_symm hbc) ih

/-- If a component meets `C1` only in `u`, everything reachable from `u` is `u` or a
neighbour of `u` in `C2`. -/
theorem crossRT_single {C1 C2 : Finset V} (hd : Disjoint C1 C2) {u : V} (hu : u ∈ C1)
    (honly : ∀ w ∈ C1, Relation.ReflTransGen (crossRel G C1 C2) u w → w = u) {v : V}
    (h : Relation.ReflTransGen (crossRel G C1 C2) u v) : v = u ∨ (v ∈ C2 ∧ G.Adj u v) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c hab hbc ih =>
    rcases ih with rfl | ⟨hb2, hub⟩
    · rcases hbc.2 with ⟨-, hc⟩ | ⟨hb, -⟩
      · exact Or.inr ⟨hc, hbc.1⟩
      · exact absurd hb (disjoint_left.1 hd hu)
    · rcases hbc.2 with ⟨hb1, -⟩ | ⟨-, hc⟩
      · exact absurd hb2 (disjoint_left.1 hd hb1)
      · exact Or.inl (honly c hc (hab.tail hbc))

/-- A path inside a reachability class leaves any proper subset through a cross edge. -/
theorem crossRT_cut {C1 C2 S : Finset V} {u v : V} (hu : u ∈ S)
    (h : Relation.ReflTransGen (crossRel G C1 C2) u v) (hv : v ∉ S) :
    ∃ x ∈ S, ∃ y, y ∉ S ∧ Relation.ReflTransGen (crossRel G C1 C2) u y ∧
      crossRel G C1 C2 x y := by
  induction h with
  | refl => exact absurd hu hv
  | @tail b c hab hbc ih =>
    by_cases hb : b ∈ S
    · exact ⟨b, hb, c, hv, hab.tail hbc, hbc⟩
    · exact ih hb

end ElemChoos.MR
