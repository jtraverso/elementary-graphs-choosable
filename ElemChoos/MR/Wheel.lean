/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Gem

/-!
# Theorem 5 of Maffray–Reed, 4-wheel case

A connected elementary graph containing a 4-wheel but no gem is cobipartite. With the square
`b1 b2 b3 b4` and centre `q`, every other vertex sees exactly three of `b1, …, b4` or all of
them; the two sides are `{b1, b2}` with the vertices seeing `b1, b2` and one of `b3, b4`, and
`{b3, b4}` with the symmetric ones; the vertices seeing all four are split by the colour of
their edge to `b1` (this replaces the stable-set/odd-antihole step of the paper).
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} (K : ECol G)

/-- No induced gem inside `W`. -/
def NoGemIn (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∀ p1 ∈ W, ∀ p2 ∈ W, ∀ p3 ∈ W, ∀ p4 ∈ W, ∀ q ∈ W, ¬ IsGem G p1 p2 p3 p4 q

macro "gem_facts" : tactic =>
  `(tactic| exact ⟨by ec_adj, by ec_adj, by ec_adj, by ec_nadj0, by ec_nadj0, by ec_nadj0,
      by ec_adj, by ec_adj, by ec_adj, by ec_adj⟩)

set_option maxHeartbeats 40000000 in
include K in
theorem wheel_trace {W : Finset V} (hng : NoGemIn G W) {b1 b2 b3 b4 q v : V} (h1 : b1 ∈ W)
    (h2 : b2 ∈ W) (h3 : b3 ∈ W) (h4 : b4 ∈ W) (hq : q ∈ W) (hv : v ∈ W)
    (hw : IsWheel G b1 b2 b3 b4 q)
    (hv1 : v ≠ b1) (hv2 : v ≠ b2) (hv3 : v ≠ b3) (hv4 : v ≠ b4) (hvq : v ≠ q)
    (hsee : G.Adj v b1 ∨ G.Adj v b2 ∨ G.Adj v b3 ∨ G.Adj v b4 ∨ G.Adj v q) :
    (G.Adj v b1 ∧ G.Adj v b2 ∧ ((G.Adj v b3 ∧ ¬ G.Adj v b4) ∨ (¬ G.Adj v b3 ∧ G.Adj v b4))) ∨
    (G.Adj v b3 ∧ G.Adj v b4 ∧ ((G.Adj v b1 ∧ ¬ G.Adj v b2) ∨ (¬ G.Adj v b1 ∧ G.Adj v b2))) ∨
    (G.Adj v b1 ∧ G.Adj v b2 ∧ G.Adj v b3 ∧ G.Adj v b4) := by
  obtain ⟨w12, w23, w34, w41, n13, n24, d13, d24, wq1, wq2, wq3, wq4⟩ := hw
  by_cases e1 : G.Adj v b1 <;> by_cases e2 : G.Adj v b2 <;> by_cases e3 : G.Adj v b3 <;>
    by_cases e4 : G.Adj v b4 <;> by_cases e5 : G.Adj v q <;>
    first
    | (simp only [e1, e2, e3, e4, not_true_eq_false, not_false_eq_true, true_and, and_true,
        false_and, and_false, or_true, true_or, or_false, false_or]; done)
    | (exfalso; elem_contra K [b1, b2, b3, b4, q, v])
    | (exfalso; exact hng b3 h3 b4 h4 b1 h1 v hv q hq (by gem_facts))
    | (exfalso; exact hng b3 h3 q hq b1 h1 v hv b2 h2 (by gem_facts))
    | (exfalso; exact hng b2 h2 b3 h3 b4 h4 v hv q hq (by gem_facts))
    | (exfalso; exact hng b2 h2 q hq b4 h4 v hv b1 h1 (by gem_facts))
    | (exfalso; exact hng b1 h1 b4 h4 b3 h3 v hv q hq (by gem_facts))
    | (exfalso; exact hng b1 h1 q hq b3 h3 v hv b2 h2 (by gem_facts))
    | (exfalso; exact hng b1 h1 b2 h2 b3 h3 v hv q hq (by gem_facts))
    | (exfalso; exact hng b1 h1 q hq b3 h3 v hv b4 h4 (by gem_facts))
    | (exfalso; simp_all)

/-- The side of `b1 b2` in the cobipartition. -/
def wheelSide (G : SimpleGraph V) (K : ECol G) (b1 b2 b3 b4 q v : V) : Prop :=
  v = b1 ∨ v = b2 ∨
    ((v ≠ b1 ∧ v ≠ b2 ∧ v ≠ b3 ∧ v ≠ b4 ∧ v ≠ q) ∧ G.Adj v b1 ∧ G.Adj v b2 ∧
      ((G.Adj v b3 ∧ ¬ G.Adj v b4) ∨ (¬ G.Adj v b3 ∧ G.Adj v b4))) ∨
    ((G.Adj v b1 ∧ G.Adj v b2 ∧ G.Adj v b3 ∧ G.Adj v b4) ∧ K.c v b1 = 1)

set_option maxHeartbeats 40000000 in
theorem wheelSide_clique {W : Finset V} (hng : NoGemIn G W) {b1 b2 b3 b4 q u v : V}
    (h1 : b1 ∈ W) (h2 : b2 ∈ W) (h3 : b3 ∈ W) (h4 : b4 ∈ W) (hu : u ∈ W) (hv : v ∈ W)
    (hw : IsWheel G b1 b2 b3 b4 q)
    (hus : wheelSide G K b1 b2 b3 b4 q u) (hvs : wheelSide G K b1 b2 b3 b4 q v) (huv : u ≠ v) :
    G.Adj u v := by
  obtain ⟨w12, w23, w34, w41, n13, n24, d13, d24, wq1, wq2, wq3, wq4⟩ := hw
  have AA : ∀ x y, G.Adj x b1 → G.Adj y b1 → K.c x b1 = 1 → K.c y b1 = 1 → x ≠ y →
      G.Adj x y := by
    intro x y x1 y1 cx cy hxy
    by_contra hna
    elem_contra K [b1, x, y]
  have XA : ∀ x ∈ W, ∀ y ∈ W, (x ≠ b1 ∧ x ≠ b2 ∧ x ≠ b3 ∧ x ≠ b4 ∧ x ≠ q) → G.Adj x b1 →
      G.Adj x b2 → ((G.Adj x b3 ∧ ¬ G.Adj x b4) ∨ (¬ G.Adj x b3 ∧ G.Adj x b4)) →
      G.Adj y b1 → G.Adj y b2 → G.Adj y b3 → G.Adj y b4 → x ≠ y → G.Adj x y := by
    intro x hx y hy _ x1 x2 x34 y1 y2 y3 y4 hxy
    by_contra hna
    rcases x34 with ⟨x3, x4⟩ | ⟨x3, x4⟩
    · exact hng b4 h4 y hy b2 h2 x hx b1 h1 (by gem_facts)
    · exact hng b3 h3 y hy b1 h1 x hx b2 h2 (by gem_facts)
  have XX : ∀ x ∈ W, ∀ y ∈ W, (x ≠ b1 ∧ x ≠ b2 ∧ x ≠ b3 ∧ x ≠ b4 ∧ x ≠ q) → G.Adj x b1 →
      G.Adj x b2 → ((G.Adj x b3 ∧ ¬ G.Adj x b4) ∨ (¬ G.Adj x b3 ∧ G.Adj x b4)) →
      (y ≠ b1 ∧ y ≠ b2 ∧ y ≠ b3 ∧ y ≠ b4 ∧ y ≠ q) → G.Adj y b1 → G.Adj y b2 →
      ((G.Adj y b3 ∧ ¬ G.Adj y b4) ∨ (¬ G.Adj y b3 ∧ G.Adj y b4)) → x ≠ y → G.Adj x y := by
    intro x hx y hy ⟨xn1, xn2, xn3, xn4, xnq⟩ x1 x2 x34 ⟨yn1, yn2, yn3, yn4, ynq⟩ y1 y2 y34 hxy
    by_contra hna
    rcases x34 with ⟨x3, x4⟩ | ⟨x3, x4⟩ <;> rcases y34 with ⟨y3, y4⟩ | ⟨y3, y4⟩
    · elem_contra K [b1, b4, x, y]
    · exact hng b3 h3 x hx b1 h1 y hy b2 h2 (by gem_facts)
    · exact hng b3 h3 y hy b1 h1 x hx b2 h2 (by gem_facts)
    · elem_contra K [b2, b3, x, y]
  rcases hus with h | h | ⟨hun, u1, u2, u34⟩ | ⟨⟨u1, u2, u3, u4⟩, uc⟩ <;>
    rcases hvs with h' | h' | ⟨hvn, v1, v2, v34⟩ | ⟨⟨v1, v2, v3, v4⟩, vc⟩
  all_goals ((try subst h); (try subst h'))
  all_goals first
    | exact absurd rfl huv
    | ec_adj
    | exact XA _ hu _ hv hun u1 u2 u34 v1 v2 v3 v4 huv
    | exact (XA _ hv _ hu hvn v1 v2 v34 u1 u2 u3 u4 (Ne.symm huv)).symm
    | exact XX _ hu _ hv hun u1 u2 u34 hvn v1 v2 v34 huv
    | exact AA _ _ u1 v1 uc vc huv

set_option maxHeartbeats 40000000 in
include K in
/-- **Theorem 5, 4-wheel case.** A connected set with a 4-wheel and no gem is cobipartite,
hence a strong homogeneous pair. -/
theorem shp_of_wheel {W : Finset V} (hconn : ConnOn G W) (hng : NoGemIn G W) {b1 b2 b3 b4 q : V}
    (h1 : b1 ∈ W) (h2 : b2 ∈ W) (h3 : b3 ∈ W) (h4 : b4 ∈ W) (hq : q ∈ W)
    (hw : IsWheel G b1 b2 b3 b4 q) : ∃ C1 C2, SHP G W C1 C2 := by
  classical
  have hw' := hw
  obtain ⟨w12, w23, w34, w41, n13, n24, d13, d24, wq1, wq2, wq3, wq4⟩ := hw'
  have hrot : IsWheel G b3 b4 b1 b2 q :=
    ⟨w34, w41, w12, w23, fun h => n13 h.symm, fun h => n24 h.symm, Ne.symm d13, Ne.symm d24,
      wq3, wq4, wq1, wq2⟩
  have see : ∀ v ∈ W, (v ≠ b1 ∧ v ≠ b2 ∧ v ≠ b3 ∧ v ≠ b4 ∧ v ≠ q) →
      (G.Adj v b1 ∨ G.Adj v b2 ∨ G.Adj v b3 ∨ G.Adj v b4 ∨ G.Adj v q) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨v0, hv0, hv0g, n1, n2, n3, n4, n5⟩ := hcon
    set Z := W.filter (fun z => (z ≠ b1 ∧ z ≠ b2 ∧ z ≠ b3 ∧ z ≠ b4 ∧ z ≠ q) ∧
      ¬ G.Adj z b1 ∧ ¬ G.Adj z b2 ∧ ¬ G.Adj z b3 ∧ ¬ G.Adj z b4 ∧ ¬ G.Adj z q) with hZ
    have hZne : Z.Nonempty := ⟨v0, mem_filter.2 ⟨hv0, hv0g, n1, n2, n3, n4, n5⟩⟩
    have hZW : Z ≠ W := by
      intro h
      have : b1 ∈ Z := h ▸ h1
      exact (mem_filter.1 this).2.1.1 rfl
    obtain ⟨z, hz, v, hv, hvZ, hzv⟩ := hconn Z (filter_subset _ _) hZne hZW
    obtain ⟨hzW, ⟨zn1, zn2, zn3, zn4, znq⟩, z1, z2, z3, z4, z5⟩ := mem_filter.1 hz
    by_cases hvg : v ≠ b1 ∧ v ≠ b2 ∧ v ≠ b3 ∧ v ≠ b4 ∧ v ≠ q
    · have hsee : G.Adj v b1 ∨ G.Adj v b2 ∨ G.Adj v b3 ∨ G.Adj v b4 ∨ G.Adj v q := by
        by_contra hn
        push_neg at hn
        exact hvZ (mem_filter.2 ⟨hv, hvg, hn⟩)
      have hzv' : z ≠ v := G.ne_of_adj hzv
      rcases wheel_trace K hng h1 h2 h3 h4 hq hv hw hvg.1 hvg.2.1 hvg.2.2.1 hvg.2.2.2.1
        hvg.2.2.2.2 hsee with ⟨v1, v2, ⟨v3, v4⟩ | ⟨v3, v4⟩⟩ | ⟨v3, v4, ⟨v1, v2⟩ | ⟨v1, v2⟩⟩ |
        ⟨v1, v2, v3, v4⟩
      all_goals elem_contra K [b1, b2, b3, b4, v, z]
    · simp only [not_and_or, not_not] at hvg
      rcases hvg with rfl | rfl | rfl | rfl | rfl <;> contradiction
  have classify : ∀ v ∈ W, wheelSide G K b1 b2 b3 b4 q v ∨ wheelSide G K b3 b4 b1 b2 q v := by
    intro v hv
    by_cases hvg : v ≠ b1 ∧ v ≠ b2 ∧ v ≠ b3 ∧ v ≠ b4 ∧ v ≠ q
    · rcases wheel_trace K hng h1 h2 h3 h4 hq hv hw hvg.1 hvg.2.1 hvg.2.2.1 hvg.2.2.2.1
        hvg.2.2.2.2 (see v hv hvg) with ⟨v1, v2, v34⟩ | ⟨v3, v4, v12⟩ | ⟨v1, v2, v3, v4⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hvg, v1, v2, v34⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨⟨hvg.2.2.1, hvg.2.2.2.1, hvg.1, hvg.2.1, hvg.2.2.2.2⟩, v3, v4, v12⟩)))
      · by_cases hc : K.c v b1 = 1
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨⟨v1, v2, v3, v4⟩, hc⟩)))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨v3, v4, v1, v2⟩, ?_⟩)))
          have hv1 : v ≠ b1 := hvg.1
          have hv3 : v ≠ b3 := hvg.2.2.1
          have := K.le_one v b1
          elem_contra K [b1, b3, v]
    · simp only [not_and_or, not_not] at hvg
      rcases hvg with h | h | h | h | h <;> rw [h]
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · by_cases hc : K.c q b1 = 1
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨⟨wq1, wq2, wq3, wq4⟩, hc⟩)))
        · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨wq3, wq4, wq1, wq2⟩, ?_⟩)))
          have := K.le_one q b1
          elem_contra K [b1, b3, q]
  set C := W.filter (wheelSide G K b1 b2 b3 b4 q) with hC
  have hC2 : ∀ v ∈ W \ C, wheelSide G K b3 b4 b1 b2 q v := by
    intro v hv
    obtain ⟨hvW, hvC⟩ := mem_sdiff.1 hv
    rcases classify v hvW with h | h
    · exact absurd (mem_filter.2 ⟨hvW, h⟩) hvC
    · exact h
  have hb3 : b3 ∉ C := by
    intro h
    rcases (mem_filter.1 h).2 with h' | h' | ⟨⟨-, -, h', -⟩, -⟩ | ⟨⟨-, -, h', -⟩, -⟩
    · exact d13 h'.symm
    · exact G.ne_of_adj w23 h'.symm
    · exact h' rfl
    · exact G.loopless.irrefl _ h'
  refine ⟨C, W \ C, shp_of_cobip (filter_subset _ _) ?_ ?_ (a := b2) (b := b3)
    (mem_filter.2 ⟨h2, Or.inr (Or.inl rfl)⟩) h3 hb3 w23 ?_⟩
  · intro u hu v hv huv
    exact wheelSide_clique K hng h1 h2 h3 h4 (filter_subset _ _ hu) (filter_subset _ _ hv) hw
      (mem_filter.1 hu).2 (mem_filter.1 hv).2 huv
  · intro u hu v hv huv
    exact wheelSide_clique K hng h3 h4 h1 h2 (sdiff_subset hu) (sdiff_subset hv) hrot
      (hC2 u hu) (hC2 v hv) huv
  · have : ({b1, b2, b3} : Finset V) ⊆ W := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h3' := card_le_card this
    rw [card_insert_of_notMem (by simp [G.ne_of_adj w12, d13]),
      card_pair (G.ne_of_adj w23)] at h3'
    omega

end ElemChoos.MR
