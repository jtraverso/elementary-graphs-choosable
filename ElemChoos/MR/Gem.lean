/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Basic

/-!
# Theorem 5 of Maffray–Reed, gem case

A connected elementary graph containing a gem but no `D` is cobipartite. We follow
Maffray–Reed: every vertex outside the gem `a1 a2 a3 a4 / q` sees `{a1, a2}` and misses one of
`a3, a4`, or symmetrically, or sees all of `a1, …, a4` (or sees nothing, which connectivity
excludes). The stable-set/odd-antihole step of the paper is replaced by the colouring: a vertex
seeing all of `a1, …, a4` goes to the side of `a1 a2` exactly when `c v a2 = c a1 a2`.
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} (K : ECol G)

/-- No induced `D` inside `W`. -/
def NoDIn (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ x ∈ W, ∀ o ∈ W, ∀ p1 ∈ W, ∀ p2 ∈ W, ∀ p3 ∈ W, ∀ p4 ∈ W, ¬ IsD G x o p1 p2 p3 p4

/-- A cobipartition with an edge across gives a strong homogeneous pair. -/
theorem shp_of_cobip {W C : Finset V} (hC : C ⊆ W) (h1 : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v)
    (h2 : ∀ u ∈ W \ C, ∀ v ∈ W \ C, u ≠ v → G.Adj u v) {a b : V} (ha : a ∈ C) (hb : b ∈ W)
    (hbC : b ∉ C) (hab : G.Adj a b) (h3 : 3 ≤ #W) : SHP G W C (W \ C) where
  sub1 := hC
  sub2 := sdiff_subset
  disj := disjoint_sdiff
  clq1 := h1
  clq2 := h2
  edge := ⟨a, ha, b, mem_sdiff.2 ⟨hb, hbC⟩, hab⟩
  three := by rw [add_comm, card_sdiff_add_card_eq_card hC]; exact h3
  homog := fun v hv hv1 hv2 => absurd (mem_sdiff.2 ⟨hv, hv1⟩) hv2

macro "d_facts" : tactic =>
  `(tactic| exact ⟨by ec_adj, by ec_adj, by ec_adj, by ec_adj, by ec_adj, by ec_adj, by ec_adj,
      by ec_adj, by ec_nadj0, by ec_nadj0, by ec_nadj0, by ec_nadj0, by ec_nadj0,
      by ec_nadj0, by ec_nadj0⟩)

set_option maxHeartbeats 40000000 in
include K in
theorem gem_trace {W : Finset V} (hnoD : NoDIn G W) {a1 a2 a3 a4 q v : V} (h1 : a1 ∈ W) (h2 : a2 ∈ W)
    (h3 : a3 ∈ W) (h4 : a4 ∈ W) (hq : q ∈ W) (hv : v ∈ W) (hg : IsGem G a1 a2 a3 a4 q)
    (hv1 : v ≠ a1) (hv2 : v ≠ a2) (hv3 : v ≠ a3) (hv4 : v ≠ a4) (hvq : v ≠ q)
    (hsee : G.Adj v a1 ∨ G.Adj v a2 ∨ G.Adj v a3 ∨ G.Adj v a4 ∨ G.Adj v q) :
    (G.Adj v a1 ∧ G.Adj v a2 ∧ (¬ G.Adj v a3 ∨ ¬ G.Adj v a4)) ∨
    (G.Adj v a3 ∧ G.Adj v a4 ∧ (¬ G.Adj v a1 ∨ ¬ G.Adj v a2)) ∨
    (G.Adj v a1 ∧ G.Adj v a2 ∧ G.Adj v a3 ∧ G.Adj v a4) := by
  obtain ⟨g12, g23, g34, n13, n14, n24, gq1, gq2, gq3, gq4⟩ := hg
  have d13 : a1 ≠ a3 := fun h => n14 (h ▸ g34)
  have d14 : a1 ≠ a4 := fun h => n24 (h ▸ g12.symm)
  have d24 : a2 ≠ a4 := fun h => n14 (h ▸ g12)
  by_cases e1 : G.Adj v a1 <;> by_cases e2 : G.Adj v a2 <;> by_cases e3 : G.Adj v a3 <;>
    by_cases e4 : G.Adj v a4 <;> by_cases e5 : G.Adj v q <;>
    first
    | (simp only [e1, e2, e3, e4, not_true_eq_false, not_false_eq_true, true_and, and_true,
        false_and, and_false, or_true, true_or, or_false, false_or]; done)
    | (exfalso; elem_contra K [a1, a2, a3, a4, q, v])
    | (exfalso; exact hnoD v hv a1 h1 q hq a2 h2 a3 h3 a4 h4 (by d_facts))
    | (exfalso; exact hnoD v hv a4 h4 q hq a3 h3 a2 h2 a1 h1 (by d_facts))
    | (exfalso; simp_all)

set_option maxHeartbeats 40000000 in
include K in
theorem gem_noZ {W : Finset V} (hnoD : NoDIn G W) {a1 a2 a3 a4 q v z : V} (h1 : a1 ∈ W)
    (h2 : a2 ∈ W) (h3 : a3 ∈ W) (h4 : a4 ∈ W) (hq : q ∈ W) (hv : v ∈ W) (hz : z ∈ W)
    (hg : IsGem G a1 a2 a3 a4 q)
    (htype : (G.Adj v a1 ∧ G.Adj v a2 ∧ (¬ G.Adj v a3 ∨ ¬ G.Adj v a4)) ∨
      (G.Adj v a3 ∧ G.Adj v a4 ∧ (¬ G.Adj v a1 ∨ ¬ G.Adj v a2)) ∨
      (G.Adj v a1 ∧ G.Adj v a2 ∧ G.Adj v a3 ∧ G.Adj v a4))
    (z1 : ¬ G.Adj z a1) (z2 : ¬ G.Adj z a2) (z3 : ¬ G.Adj z a3) (z4 : ¬ G.Adj z a4)
    (z5 : ¬ G.Adj z q) (hzv : G.Adj z v) : False := by
  obtain ⟨g12, g23, g34, n13, n14, n24, gq1, gq2, gq3, gq4⟩ := hg
  have d13 : a1 ≠ a3 := fun h => n14 (h ▸ g34)
  have d14 : a1 ≠ a4 := fun h => n24 (h ▸ g12.symm)
  have d24 : a2 ≠ a4 := fun h => n14 (h ▸ g12)
  by_cases e1 : G.Adj v a1 <;> by_cases e2 : G.Adj v a2 <;> by_cases e3 : G.Adj v a3 <;>
    by_cases e4 : G.Adj v a4 <;> by_cases e5 : G.Adj v q <;>
    first
    | (simp only [e1, e2, e3, e4, not_true_eq_false, not_false_eq_true, true_and, and_true,
        false_and, and_false, or_true, true_or, or_false, false_or] at htype; done)
    | elem_contra K [a1, a2, a3, a4, q, v, z]
    | exact hnoD z hz v hv q hq a2 h2 a3 h3 a4 h4 (by d_facts)
    | exact hnoD z hz v hv a2 h2 a1 h1 q hq a3 h3 (by d_facts)
    | exact hnoD z hz v hv q hq a3 h3 a2 h2 a1 h1 (by d_facts)
    | exact hnoD z hz v hv a3 h3 a4 h4 q hq a2 h2 (by d_facts)

/-- The side of `a1 a2` in the cobipartition. -/
def gemSide (G : SimpleGraph V) (K : ECol G) (a1 a2 a3 a4 q v : V) : Prop :=
  v = a1 ∨ v = a2 ∨
    ((v ≠ a1 ∧ v ≠ a2 ∧ v ≠ a3 ∧ v ≠ a4 ∧ v ≠ q) ∧
      G.Adj v a1 ∧ G.Adj v a2 ∧ (¬ G.Adj v a3 ∨ ¬ G.Adj v a4)) ∨
    ((G.Adj v a1 ∧ G.Adj v a2 ∧ G.Adj v a3 ∧ G.Adj v a4) ∧ K.c v a2 = K.c a1 a2)

set_option maxHeartbeats 40000000 in
theorem gemSide_clique {a1 a2 a3 a4 q u v : V} (hg : IsGem G a1 a2 a3 a4 q)
    (hu : gemSide G K a1 a2 a3 a4 q u) (hv : gemSide G K a1 a2 a3 a4 q v) (huv : u ≠ v) :
    G.Adj u v := by
  obtain ⟨g12, g23, g34, n13, n14, n24, gq1, gq2, gq3, gq4⟩ := hg
  have d13 : a1 ≠ a3 := fun h => n14 (h ▸ g34)
  have d14 : a1 ≠ a4 := fun h => n24 (h ▸ g12.symm)
  have d24 : a2 ≠ a4 := fun h => n14 (h ▸ g12)
  have hq3 : q ≠ a3 := G.ne_of_adj gq3
  have hq4 : q ≠ a4 := G.ne_of_adj gq4
  -- vertices seeing all of the path, including `q`
  have AA : ∀ x y, G.Adj x a1 → G.Adj x a2 → G.Adj x a3 → G.Adj x a4 → G.Adj y a1 →
      G.Adj y a2 → G.Adj y a3 → G.Adj y a4 → K.c x a2 = K.c a1 a2 → K.c y a2 = K.c a1 a2 →
      x ≠ y → G.Adj x y := by
    intro x y x1 x2 x3 x4 y1 y2 y3 y4 cx cy hxy
    by_contra hna
    elem_contra K [a1, a2, x, y]
  -- a vertex of type `X` sees every vertex of type `A` on its side
  have XA : ∀ x y, (x ≠ a1 ∧ x ≠ a2 ∧ x ≠ a3 ∧ x ≠ a4 ∧ x ≠ q) → G.Adj x a1 → G.Adj x a2 →
      (¬ G.Adj x a3 ∨ ¬ G.Adj x a4) → G.Adj y a1 → G.Adj y a2 → G.Adj y a3 → G.Adj y a4 →
      K.c y a2 = K.c a1 a2 → x ≠ y → G.Adj x y := by
    rintro x y ⟨xn1, xn2, xn3, xn4, xnq⟩ x1 x2 x34 y1 y2 y3 y4 cy hxy
    by_contra hna
    rcases x34 with x3 | x4
    · elem_contra K [a1, a2, a3, a4, x, y]
    · by_cases x3 : G.Adj x a3
      · elem_contra K [a1, a2, a3, a4, x, y]
      · elem_contra K [a1, a2, a3, a4, x, y]
  have XX : ∀ x y, (x ≠ a1 ∧ x ≠ a2 ∧ x ≠ a3 ∧ x ≠ a4 ∧ x ≠ q) → G.Adj x a1 → G.Adj x a2 →
      (¬ G.Adj x a3 ∨ ¬ G.Adj x a4) → (y ≠ a1 ∧ y ≠ a2 ∧ y ≠ a3 ∧ y ≠ a4 ∧ y ≠ q) →
      G.Adj y a1 → G.Adj y a2 → (¬ G.Adj y a3 ∨ ¬ G.Adj y a4) → x ≠ y → G.Adj x y := by
    rintro x y ⟨xn1, xn2, xn3, xn4, xnq⟩ x1 x2 x34 ⟨yn1, yn2, yn3, yn4, ynq⟩ y1 y2 y34 hxy
    by_contra hna
    by_cases x3 : G.Adj x a3 <;> by_cases x4 : G.Adj x a4 <;> by_cases y3 : G.Adj y a3 <;>
      by_cases y4 : G.Adj y a4 <;> by_cases xq : G.Adj x q <;> by_cases yq : G.Adj y q <;>
      first
      | (rcases x34 with h | h <;> contradiction)
      | (rcases y34 with h | h <;> contradiction)
      | elem_contra K [a1, a2, a3, a4, q, x, y]
  rcases hu with rfl | rfl | ⟨hun, u1, u2, u34⟩ | ⟨⟨u1, u2, u3, u4⟩, uc⟩ <;>
    rcases hv with rfl | rfl | ⟨hvn, v1, v2, v34⟩ | ⟨⟨v1, v2, v3, v4⟩, vc⟩
  all_goals first
    | exact absurd rfl huv
    | ec_adj
    | exact XA _ _ hun u1 u2 u34 v1 v2 v3 v4 vc huv
    | exact (XA _ _ hvn v1 v2 v34 u1 u2 u3 u4 uc (Ne.symm huv)).symm
    | exact XX _ _ hun u1 u2 u34 hvn v1 v2 v34 huv
    | exact AA _ _ u1 u2 u3 u4 v1 v2 v3 v4 uc vc huv

set_option maxHeartbeats 40000000 in
include K in
/-- **Theorem 5, gem case.** A connected set with a gem and no `D` is cobipartite, hence a
strong homogeneous pair. -/
theorem shp_of_gem {W : Finset V} (hconn : ConnOn G W) (hnoD : NoDIn G W) {a1 a2 a3 a4 q : V}
    (h1 : a1 ∈ W) (h2 : a2 ∈ W) (h3 : a3 ∈ W) (h4 : a4 ∈ W) (hq : q ∈ W)
    (hg : IsGem G a1 a2 a3 a4 q) : ∃ C1 C2, SHP G W C1 C2 := by
  classical
  have hg' := hg
  obtain ⟨g12, g23, g34, n13, n14, n24, gq1, gq2, gq3, gq4⟩ := hg'
  have d13 : a1 ≠ a3 := fun h => n14 (h ▸ g34)
  have d14 : a1 ≠ a4 := fun h => n24 (h ▸ g12.symm)
  have d24 : a2 ≠ a4 := fun h => n14 (h ▸ g12)
  have hrev : IsGem G a4 a3 a2 a1 q :=
    ⟨g34.symm, g23.symm, g12.symm, fun h => n24 h.symm, fun h => n14 h.symm,
      fun h => n13 h.symm, gq4, gq3, gq2, gq1⟩
  -- every vertex outside the gem sees it (connectivity)
  have see : ∀ v ∈ W, (v ≠ a1 ∧ v ≠ a2 ∧ v ≠ a3 ∧ v ≠ a4 ∧ v ≠ q) →
      (G.Adj v a1 ∨ G.Adj v a2 ∨ G.Adj v a3 ∨ G.Adj v a4 ∨ G.Adj v q) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨v0, hv0, hv0g, n1, n2, n3, n4, n5⟩ := hcon
    set Z := W.filter (fun z => (z ≠ a1 ∧ z ≠ a2 ∧ z ≠ a3 ∧ z ≠ a4 ∧ z ≠ q) ∧
      ¬ G.Adj z a1 ∧ ¬ G.Adj z a2 ∧ ¬ G.Adj z a3 ∧ ¬ G.Adj z a4 ∧ ¬ G.Adj z q) with hZ
    have hZne : Z.Nonempty := ⟨v0, mem_filter.2 ⟨hv0, hv0g, n1, n2, n3, n4, n5⟩⟩
    have hZW : Z ≠ W := by
      intro h
      have : a1 ∈ Z := h ▸ h1
      exact (mem_filter.1 this).2.1.1 rfl
    obtain ⟨z, hz, v, hv, hvZ, hzv⟩ := hconn Z (filter_subset _ _) hZne hZW
    obtain ⟨hzW, -, z1, z2, z3, z4, z5⟩ := mem_filter.1 hz
    by_cases hvg : v ≠ a1 ∧ v ≠ a2 ∧ v ≠ a3 ∧ v ≠ a4 ∧ v ≠ q
    · have hsee : G.Adj v a1 ∨ G.Adj v a2 ∨ G.Adj v a3 ∨ G.Adj v a4 ∨ G.Adj v q := by
        by_contra hn
        push_neg at hn
        exact hvZ (mem_filter.2 ⟨hv, hvg, hn⟩)
      exact gem_noZ K hnoD h1 h2 h3 h4 hq hv hzW hg
        (gem_trace K hnoD h1 h2 h3 h4 hq hv hg hvg.1 hvg.2.1 hvg.2.2.1 hvg.2.2.2.1
          hvg.2.2.2.2 hsee) z1 z2 z3 z4 z5 hzv
    · simp only [not_and_or, not_not] at hvg
      rcases hvg with rfl | rfl | rfl | rfl | rfl <;> contradiction
  -- every vertex is on one of the two sides
  have classify : ∀ v ∈ W, gemSide G K a1 a2 a3 a4 q v ∨ gemSide G K a4 a3 a2 a1 q v := by
    intro v hv
    by_cases hvg : v ≠ a1 ∧ v ≠ a2 ∧ v ≠ a3 ∧ v ≠ a4 ∧ v ≠ q
    · rcases gem_trace K hnoD h1 h2 h3 h4 hq hv hg hvg.1 hvg.2.1 hvg.2.2.1 hvg.2.2.2.1
        hvg.2.2.2.2 (see v hv hvg) with ⟨v1, v2, v34⟩ | ⟨v3, v4, v12⟩ | ⟨v1, v2, v3, v4⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hvg, v1, v2, v34⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨⟨hvg.2.2.2.1, hvg.2.2.1, hvg.2.1, hvg.1, hvg.2.2.2.2⟩, v4, v3, v12.symm⟩)))
      · by_cases hc : K.c v a2 = K.c a1 a2
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨⟨v1, v2, v3, v4⟩, hc⟩)))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨v4, v3, v2, v1⟩, ?_⟩)))
          have hv1 : v ≠ a1 := hvg.1
          have hv3 : v ≠ a3 := hvg.2.2.1
          have hv2 : v ≠ a2 := hvg.2.1
          have hv4 : v ≠ a4 := hvg.2.2.2.1
          elem_contra K [a1, a2, a3, a4, v]
    · simp only [not_and_or, not_not] at hvg
      rcases hvg with h | h | h | h | h <;> rw [h]
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · by_cases hc : K.c q a2 = K.c a1 a2
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨⟨gq1, gq2, gq3, gq4⟩, hc⟩)))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨gq4, gq3, gq2, gq1⟩, ?_⟩)))
          elem_contra K [a1, a2, a3, a4, q]
  set C := W.filter (gemSide G K a1 a2 a3 a4 q) with hC
  have hC2 : ∀ v ∈ W \ C, gemSide G K a4 a3 a2 a1 q v := by
    intro v hv
    obtain ⟨hvW, hvC⟩ := mem_sdiff.1 hv
    rcases classify v hvW with h | h
    · exact absurd (mem_filter.2 ⟨hvW, h⟩) hvC
    · exact h
  have ha3 : a3 ∉ C := by
    intro h
    rcases (mem_filter.1 h).2 with h' | h' | ⟨⟨-, -, h', -⟩, -⟩ | ⟨⟨-, -, h', -⟩, -⟩
    · exact d13 h'.symm
    · exact G.ne_of_adj g23 h'.symm
    · exact h' rfl
    · exact G.loopless.irrefl _ h'
  refine ⟨C, W \ C, shp_of_cobip (filter_subset _ _) ?_ ?_ (a := a2) (b := a3)
    (mem_filter.2 ⟨h2, Or.inr (Or.inl rfl)⟩) h3 ha3 g23 ?_⟩
  · intro u hu v hv huv
    exact gemSide_clique K hg (mem_filter.1 hu).2 (mem_filter.1 hv).2 huv
  · intro u hu v hv huv
    exact gemSide_clique K hrev (hC2 u hu) (hC2 v hv) huv
  · have : ({a1, a2, a3} : Finset V) ⊆ W := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h3' := card_le_card this
    rw [card_insert_of_notMem (by simp [G.ne_of_adj g12, d13]),
      card_pair (G.ne_of_adj g23)] at h3'
    omega

end ElemChoos.MR
