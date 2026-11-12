/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Basic

/-!
# The growth procedure of Maffray–Reed: invariants and claim (1)

Starting from a `D` (`x o p2 p3 p4` an induced path, `p1` seeing `o, p2, p3, p4` but not `x`),
Maffray and Reed grow two cliques `C1 ⊇ {p1, p2}`, `C2 ⊇ {p3, p4}` by repeatedly adding a vertex
that sees all of one clique and some but not all of the other. Instead of their labels we carry
an invariant `Good` that is preserved by each addition:

* claim (1): `C1` sees `o` and misses `x`; `C2` misses `o` and `x`;
* every vertex of `Ci` has a neighbour in `C(3-i)`, and a non-neighbour there unless it is
  `p1` or `p3` (these replace the label arguments of the paper);
* claim (2) in the form "no outside vertex is *bad*": an outside vertex that misses a vertex of
  each clique sees no vertex of `C1 ∪ C2`.

This file proves claim (1) for an added vertex; the "no bad vertex" part is in `Claim2.lean`.
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} (K : ECol G)

/-- `z` misses a vertex of `C1` and a vertex of `C2`, and sees a vertex of `C1 ∪ C2`. -/
def Bad (G : SimpleGraph V) (z : V) (C1 C2 : Finset V) : Prop :=
  (∃ u ∈ C1, ¬ G.Adj z u) ∧ (∃ u ∈ C2, ¬ G.Adj z u) ∧
    ((∃ u ∈ C1, G.Adj z u) ∨ (∃ u ∈ C2, G.Adj z u))

/-- The invariant of the growth procedure. -/
structure Good (G : SimpleGraph V) (W : Finset V) (x o p1 p2 p3 p4 : V) (C1 C2 : Finset V) :
    Prop where
  sub1 : C1 ⊆ W
  sub2 : C2 ⊆ W
  disj : Disjoint C1 C2
  mem : p1 ∈ C1 ∧ p2 ∈ C1 ∧ p3 ∈ C2 ∧ p4 ∈ C2
  clq1 : ∀ u ∈ C1, ∀ v ∈ C1, u ≠ v → G.Adj u v
  clq2 : ∀ u ∈ C2, ∀ v ∈ C2, u ≠ v → G.Adj u v
  c1 : ∀ u ∈ C1, G.Adj u o ∧ ¬ G.Adj u x
  c2 : ∀ u ∈ C2, ¬ G.Adj u o ∧ ¬ G.Adj u x
  nb1 : ∀ u ∈ C1, ∃ v ∈ C2, G.Adj u v
  nb2 : ∀ u ∈ C2, ∃ v ∈ C1, G.Adj u v
  non1 : ∀ u ∈ C1, u ≠ p1 → ∃ v ∈ C2, ¬ G.Adj u v
  non2 : ∀ u ∈ C2, u ≠ p3 → ∃ v ∈ C1, ¬ G.Adj u v
  nobad : ∀ z ∈ W, z ∉ C1 → z ∉ C2 → ¬ Bad G z C1 C2

variable {W : Finset V} {x o p1 p2 p3 p4 : V}

theorem Good.ne_x1 {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {j : V} (hj : j ∈ C1) : j ≠ x := by
  rintro rfl
  obtain ⟨-, -, -, -, -, d12, -, -, nx1, nx2, -⟩ := hD
  have hx1 : j ≠ p1 := by rintro rfl; exact nx2 d12
  exact nx1 (hG.clq1 j hj p1 hG.mem.1 hx1)

theorem Good.ne_x2 {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {r : V} (hr : r ∈ C2) : r ≠ x := by
  rintro rfl
  exact (hG.c2 r hr).1 hD.1

theorem Good.ne_o1 {C1 C2 : Finset V} (hG : Good G W x o p1 p2 p3 p4 C1 C2) {j : V}
    (hj : j ∈ C1) : j ≠ o :=
  G.ne_of_adj (hG.c1 j hj).1

theorem Good.ne_o2 {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {r : V} (hr : r ∈ C2) : r ≠ o := by
  rintro rfl
  exact (hG.c2 r hr).2 hD.1.symm

theorem Good.ne12 {C1 C2 : Finset V} (hG : Good G W x o p1 p2 p3 p4 C1 C2) {j r : V}
    (hj : j ∈ C1) (hr : r ∈ C2) : j ≠ r := by
  rintro rfl
  exact disjoint_left.1 hG.disj hj hr

set_option maxHeartbeats 40000000 in
include K in
/-- Claim (1) for a vertex added to `C1`. -/
theorem Good.claim1_left {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {m : V} (hmC2 : m ∉ C2)
    (hm1 : ∀ u ∈ C1, G.Adj m u) (hm2 : ∃ u ∈ C2, G.Adj m u) (hm2' : ∃ u ∈ C2, ¬ G.Adj m u) :
    G.Adj m o ∧ ¬ G.Adj m x := by
  have hD' := hD
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD'
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hG.mem
  obtain ⟨u0, hu0, hmu0⟩ := hm2
  have hu0o := (hG.c2 u0 hu0).1
  have hom : m ≠ o := fun h => hu0o (h ▸ hmu0.symm)
  have hmo : G.Adj m o := by
    by_contra hmo
    obtain ⟨j, hj, hmj⟩ := hm2'
    obtain ⟨r, hr, hjr⟩ := hG.nb2 j hj
    have hro := (hG.c1 r hr).1
    have hjo := (hG.c2 j hj).1
    have hmr := hm1 r hr
    have hjm : j ≠ m := fun h => hmC2 (h ▸ hj)
    have hjo' := hG.ne_o2 hD hj
    elem_contra K [r, o, j, m]
  refine ⟨hmo, fun hmx => ?_⟩
  -- every neighbour of `m` in `C2` sees all of `C1`
  have hall : ∀ r ∈ C2, G.Adj m r → ∀ j ∈ C1, G.Adj r j := by
    intro r hr hmr j hj
    by_contra hrj
    have hxr := (hG.c2 r hr).2
    have hxj := (hG.c1 j hj).2
    have hmj := hm1 j hj
    have d1 := hG.ne12 hj hr
    have d2 := hG.ne_x1 hD hj
    have d3 := hG.ne_x2 hD hr
    elem_contra K [m, x, r, j]
  have h3 : ∀ r ∈ C2, G.Adj m r → r = p3 := by
    intro r hr hmr
    by_contra hr3
    obtain ⟨j, hj, hrj⟩ := hG.non2 r hr hr3
    exact hrj (hall r hr hmr j hj)
  have hm3 : G.Adj m p3 := by
    have := h3 u0 hu0 hmu0
    rw [this] at hmu0
    exact hmu0
  have hm4 : ¬ G.Adj m p4 := by
    intro h
    have := h3 p4 hp4 h
    rw [this] at d34
    exact G.loopless.irrefl _ d34
  have hm1' := hm1 p1 hp1
  have hm2'' := hm1 p2 hp2
  have hmp4 : m ≠ p4 := fun h => hmC2 (h ▸ hp4)
  elem_contra K [x, o, p1, p2, p3, p4, m]

set_option maxHeartbeats 40000000 in
include K in
/-- Claim (1) for a vertex added to `C2`. -/
theorem Good.claim1_right {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {m : V} (hmC1 : m ∉ C1)
    (hm2 : ∀ u ∈ C2, G.Adj m u) (hm1 : ∃ u ∈ C1, G.Adj m u) (hm1' : ∃ u ∈ C1, ¬ G.Adj m u) :
    ¬ G.Adj m o ∧ ¬ G.Adj m x := by
  have hD' := hD
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD'
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hG.mem
  have hmx : ¬ G.Adj m x := by
    intro hmx
    have hall : ∀ r ∈ C1, G.Adj m r → ∀ j ∈ C2, G.Adj r j := by
      intro r hr hmr j hj
      by_contra hrj
      have hxr := (hG.c1 r hr).2
      have hxj := (hG.c2 j hj).2
      have hmj := hm2 j hj
      have d1 := hG.ne12 hr hj
      have d2 := hG.ne_x1 hD hr
      have d3 := hG.ne_x2 hD hj
      elem_contra K [m, x, r, j]
    have h1 : ∀ r ∈ C1, G.Adj m r → r = p1 := by
      intro r hr hmr
      by_contra hr1
      obtain ⟨j, hj, hrj⟩ := hG.non1 r hr hr1
      exact hrj (hall r hr hmr j hj)
    obtain ⟨u0, hu0, hmu0⟩ := hm1
    have hmp1 : G.Adj m p1 := by
      have := h1 u0 hu0 hmu0
      rw [this] at hmu0
      exact hmu0
    have hmp2 : ¬ G.Adj m p2 := by
      intro h
      have := h1 p2 hp2 h
      rw [this] at d12
      exact G.loopless.irrefl _ d12
    have hm3 := hm2 p3 hp3
    have hm4 := hm2 p4 hp4
    have hmp2' : m ≠ p2 := fun h => hmC1 (h ▸ hp2)
    by_cases hmo : G.Adj m o
    · elem_contra K [x, o, p1, p2, p3, p4, m]
    · elem_contra K [x, o, p2, p3, m]
  refine ⟨fun hmo => ?_, hmx⟩
  obtain ⟨j, hj, hmj⟩ := hm1'
  have hjo := (hG.c1 j hj).1
  have hjx := (hG.c1 j hj).2
  have hjm : j ≠ m := fun h => hmC1 (h ▸ hj)
  have hjx' := hG.ne_x1 hD hj
  have hm3 := hm2 p3 hp3
  elem_contra K [o, x, m, j]

end ElemChoos.MR
