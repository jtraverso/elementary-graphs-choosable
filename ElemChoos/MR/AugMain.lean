/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Aug

/-!
# The augmentation step

`aug_rep`: from a normalized representation of the compressed set
`(W \ (C1 ∪ C2)) ∪ {a, b}` in which `ab` is in normal form on side `true`, build a normalized
representation of `W`.
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A vertex outside a strong homogeneous pair that sees a vertex of `C1` sees all of `C1` and
none of `C2`. -/
theorem SHP.out1 {W C1 C2 : Finset V} (hP : SHP G W C1 C2) {v u : V} (hv : v ∈ W)
    (hv1 : v ∉ C1) (hv2 : v ∉ C2) (hu : u ∈ C1) (hvu : G.Adj v u) :
    (∀ u' ∈ C1, G.Adj v u') ∧ ∀ u' ∈ C2, ¬ G.Adj v u' := by
  rcases hP.homog v hv hv1 hv2 with ⟨h1, -⟩ | ⟨h1, h2 | h2⟩
  · exact absurd hvu (h1 u hu)
  · exact ⟨h2, h1⟩
  · exact absurd hvu (h2 u hu)

theorem SHP.out2 {W C1 C2 : Finset V} (hP : SHP G W C1 C2) {v u : V} (hv : v ∈ W)
    (hv1 : v ∉ C1) (hv2 : v ∉ C2) (hu : u ∈ C2) (hvu : G.Adj v u) :
    (∀ u' ∈ C2, G.Adj v u') ∧ ∀ u' ∈ C1, ¬ G.Adj v u' := by
  rcases hP.homog v hv hv1 hv2 with ⟨h1, h2 | h2⟩ | ⟨h1, -⟩
  · exact ⟨h2, h1⟩
  · exact absurd hvu (h2 u hu)
  · exact absurd hvu (h1 u hu)

theorem aug_rep [Fintype V] {W C1 C2 : Finset V} (hP : SHP G W C1 C2) {a b : V} (ha : a ∈ C1)
    (hb : b ∈ C2) {e : Bool → V → ℕ} {h : Bool → Set ℕ}
    (hR : RepOn G (W \ (C1 ∪ C2) ∪ {a, b}) e h) (hN : NormOn G (W \ (C1 ∪ C2) ∪ {a, b}) e h)
    (hs : e true a = e true b) (hsn : e true a ∉ h true)
    (hstar : ∀ v ∈ W \ (C1 ∪ C2) ∪ {a, b}, e true v = e true a → v = a ∨ v = b)
    (hne : e false a ≠ e false b) (hta : e false a ∉ h false) (htb : e false b ∉ h false) :
    ∃ e' h', RepOn G W e' h' ∧ NormOn G W e' h' := by
  classical
  set C := C1 ∪ C2 with hCdef
  set W' := W \ C ∪ {a, b} with hW'def
  have hd := hP.disj
  have haC : a ∈ C := mem_union_left _ ha
  have hbC : b ∈ C := mem_union_right _ hb
  have hout : ∀ v ∈ W, v ∉ C → v ∈ W' := fun v hv hvC => mem_union_left _ (mem_sdiff.2 ⟨hv, hvC⟩)
  have haW' : a ∈ W' := mem_union_right _ (by simp)
  have hbW' : b ∈ W' := mem_union_right _ (by simp)
  have hW'C : ∀ v ∈ W', v ∈ C → v = a ∨ v = b := by
    intro v hv hvC
    rcases mem_union.1 hv with hv | hv
    · exact absurd hvC (mem_sdiff.1 hv).2
    · simpa using hv
  have hC1 : ∀ v ∈ C1, v ∈ W := fun v hv => hP.sub1 hv
  have hC2 : ∀ v ∈ C2, v ∈ W := fun v hv => hP.sub2 hv
  have hCW : ∀ v ∈ C, v ∈ W := fun v hv => (mem_union.1 hv).elim (hC1 v) (hC2 v)
  have n12 : ∀ v ∈ C1, v ∉ C2 := fun v hv => disjoint_left.1 hd hv
  -- vertices outside `C` adjacent to `a` (resp. `b`) share its `false`-end, and conversely
  have endA : ∀ v ∈ W, v ∉ C → G.Adj v a → e false v = e false a := by
    intro v hv hvC hva
    obtain ⟨σ, hσ⟩ := hR.2.2.1 v (hout v hv hvC) a haW' hva
    cases σ
    · exact hσ
    · rcases hstar v (hout v hv hvC) hσ with rfl | rfl
      · exact absurd haC hvC
      · exact absurd hbC hvC
  have endB : ∀ v ∈ W, v ∉ C → G.Adj v b → e false v = e false b := by
    intro v hv hvC hvb
    obtain ⟨σ, hσ⟩ := hR.2.2.1 v (hout v hv hvC) b hbW' hvb
    cases σ
    · exact hσ
    · rcases hstar v (hout v hv hvC) (hσ.trans hs.symm) with rfl | rfl
      · exact absurd haC hvC
      · exact absurd hbC hvC
  have adjA : ∀ v ∈ W, v ∉ C → e false v = e false a → G.Adj v a := by
    intro v hv hvC hva
    exact hR.adj_of_nonhub (hout v hv hvC) haW' (fun e' => hvC (e' ▸ haC)) (σ := false) hva
      (by rw [hva]; exact hta)
  have adjB : ∀ v ∈ W, v ∉ C → e false v = e false b → G.Adj v b := by
    intro v hv hvC hvb
    exact hR.adj_of_nonhub (hout v hv hvC) hbW' (fun e' => hvC (e' ▸ hbC)) (σ := false) hvb
      (by rw [hvb]; exact htb)
  have notC1 : ∀ v, v ∉ C → v ∉ C1 := fun v hv h' => hv (mem_union_left _ h')
  have notC2 : ∀ v, v ∉ C → v ∉ C2 := fun v hv h' => hv (mem_union_right _ h')
  -- components of the cross graph
  set R := Relation.ReflTransGen (crossRel G C1 C2) with hRdef
  let comp : V → Finset V := fun v => C.filter (R v)
  have comp_eq : ∀ u v, v ∈ C → (comp u = comp v ↔ R u v) := by
    intro u v hv
    constructor
    · intro h'
      have : v ∈ comp v := mem_filter.2 ⟨hv, Relation.ReflTransGen.refl⟩
      rw [← h'] at this
      exact (mem_filter.1 this).2
    · intro h'
      ext w
      simp only [comp, mem_filter]
      constructor
      · rintro ⟨hw, h''⟩
        exact ⟨hw, (crossRT_symm h').trans h''⟩
      · rintro ⟨hw, h''⟩
        exact ⟨hw, h'.trans h''⟩
  have cross_C : ∀ x y, crossRel G C1 C2 x y → x ∈ C ∧ y ∈ C := by
    rintro x y ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨mem_union_left _ h1, mem_union_right _ h2⟩
    · exact ⟨mem_union_right _ h1, mem_union_left _ h2⟩
  -- the new ends
  let eT : V → ℕ := fun v => if v ∈ C then 2 * finsetCode (comp v) + 1 else 2 * e true v
  let eF : V → ℕ := fun v =>
    if v ∈ C1 then 2 * e false a else if v ∈ C2 then 2 * e false b else 2 * e false v
  let e' : Bool → V → ℕ := fun τ v => bif τ then eT v else eF v
  let big : Finset V → Prop := fun K => 2 ≤ #(K ∩ C1) ∧ 2 ≤ #(K ∩ C2)
  let h' : Bool → Set ℕ := fun τ => bif τ then
      ({n | ∃ m ∈ h true, n = 2 * m} ∪ {n | ∃ v ∈ C, n = 2 * finsetCode (comp v) + 1 ∧
        big (comp v)})
    else {n | ∃ m ∈ h false, n = 2 * m}
  have eT_in : ∀ v ∈ C, e' true v = 2 * finsetCode (comp v) + 1 := fun v hv => by
    simp [e', eT, hv]
  have e_out : ∀ τ, ∀ v, v ∉ C → e' τ v = 2 * e τ v := fun τ v hv => by
    cases τ <;> simp [e', eT, eF, hv, notC1 v hv, notC2 v hv]
  have eF1 : ∀ v ∈ C1, e' false v = 2 * e false a := fun v hv => by simp [e', eF, hv]
  have eF2 : ∀ v ∈ C2, e' false v = 2 * e false b := fun v hv => by
    simp [e', eF, hv, disjoint_right.1 hd hv]
  have hub_even : ∀ τ m, 2 * m ∈ h' τ ↔ m ∈ h τ := by
    intro τ m
    cases τ
    · simp only [h', cond_false, Set.mem_setOf_eq]
      constructor
      · rintro ⟨m', hm', e1⟩
        rwa [show m = m' by omega]
      · exact fun hm => ⟨m, hm, rfl⟩
    · simp only [h', cond_true, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (⟨m', hm', e1⟩ | ⟨v, -, e1, -⟩)
        · rwa [show m = m' by omega]
        · omega
      · exact fun hm => Or.inl ⟨m, hm, rfl⟩
  have hubF_odd : ∀ m, 2 * m + 1 ∉ h' false := by
    rintro m ⟨m', -, e1⟩
    omega
  have hub_odd : ∀ v ∈ C, 2 * finsetCode (comp v) + 1 ∈ h' true ↔ big (comp v) := by
    intro v hv
    simp only [h', cond_true, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨m', -, e1⟩ | ⟨w, hw, e1, hbig⟩)
      · omega
      · rwa [finsetCode_inj (show finsetCode (comp v) = finsetCode (comp w) by omega)]
    · exact fun hbig => Or.inr ⟨v, hv, rfl, hbig⟩
  have eFC_nhub : ∀ v ∈ C, e' false v ∉ h' false := by
    intro v hv
    rcases mem_union.1 hv with hv | hv
    · rw [eF1 v hv, hub_even]; exact hta
    · rw [eF2 v hv, hub_even]; exact htb
  -- a component containing a non-adjacent cross pair is big
  have big_of : ∀ u ∈ C1, ∀ v ∈ C2, R u v → ¬ G.Adj u v → big (comp u) := by
    intro u hu v hv huv hna
    have huC : u ∈ C := mem_union_left _ hu
    have hvC : v ∈ C := mem_union_right _ hv
    constructor
    · by_contra hlt
      push_neg at hlt
      have honly : ∀ w ∈ C1, R u w → w = u := by
        intro w hw hRw
        have hsub : ({u, w} : Finset V) ⊆ comp u ∩ C1 := by
          intro x hx
          rcases mem_insert.1 hx with rfl | hx
          · exact mem_inter.2 ⟨mem_filter.2 ⟨huC, Relation.ReflTransGen.refl⟩, hu⟩
          · rw [mem_singleton.1 hx]
            exact mem_inter.2 ⟨mem_filter.2 ⟨mem_union_left _ hw, hRw⟩, hw⟩
        by_contra hwu
        have := card_le_card hsub
        rw [card_pair (Ne.symm hwu)] at this
        omega
      rcases crossRT_single hd hu honly huv with rfl | ⟨-, hadj⟩
      · exact n12 _ hu hv
      · exact hna hadj
    · by_contra hlt
      push_neg at hlt
      have hRvu : R v u := crossRT_symm huv
      have hcomp : comp u = comp v := (comp_eq u v hvC).2 huv
      have honly : ∀ w ∈ C2, Relation.ReflTransGen (crossRel G C2 C1) v w → w = v := by
        intro w hw hRw
        have hRw' : R v w := by
          have : crossRel G C2 C1 = crossRel G C1 C2 := by
            funext x y
            simp only [crossRel, eq_iff_iff]
            tauto
          rw [this] at hRw
          exact hRw
        have hsub : ({v, w} : Finset V) ⊆ comp u ∩ C2 := by
          rw [hcomp]
          intro x hx
          rcases mem_insert.1 hx with rfl | hx
          · exact mem_inter.2 ⟨mem_filter.2 ⟨hvC, Relation.ReflTransGen.refl⟩, hv⟩
          · rw [mem_singleton.1 hx]
            exact mem_inter.2 ⟨mem_filter.2 ⟨mem_union_right _ hw, hRw'⟩, hw⟩
        by_contra hwv
        have := card_le_card hsub
        rw [card_pair (Ne.symm hwv)] at this
        omega
      have hRvu' : Relation.ReflTransGen (crossRel G C2 C1) v u := by
        have : crossRel G C2 C1 = crossRel G C1 C2 := by
          funext x y
          simp only [crossRel, eq_iff_iff]
          tauto
        rw [this]
        exact hRvu
      rcases crossRT_single (disjoint_comm.1 hd) hv honly hRvu' with rfl | ⟨-, hadj⟩
      · exact n12 _ hu hv
      · exact hna hadj.symm
  refine ⟨e', h', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- (1) no vertex has two hub ends
    intro v hv σ
    by_cases hvC : v ∈ C
    · cases σ
      · intro h1; exact absurd h1 (eFC_nhub v hvC)
      · intro _; exact eFC_nhub v hvC
    · rw [e_out σ v hvC, e_out (!σ) v hvC, hub_even, hub_even]
      exact hR.1 v (hout v hv hvC) σ
  · -- (2) hubs have at most two partners
    intro σ u hu v hv w hw e1 e2 hhub
    cases σ
    · -- side `false`: the hub is an old hub, all three vertices are outside `C`
      have notin : ∀ x ∈ W, e' false x = e' false u → x ∉ C := by
        intro x hx hx' hxC
        have huC : u ∉ C := by
          intro huC
          exact eFC_nhub u huC hhub
        rw [e_out false u huC] at hhub hx'
        rw [hub_even] at hhub
        rcases mem_union.1 hxC with hx1 | hx2
        · rw [eF1 x hx1] at hx'
          exact hta (by rw [show e false a = e false u by omega]; exact hhub)
        · rw [eF2 x hx2] at hx'
          exact htb (by rw [show e false b = e false u by omega]; exact hhub)
      have huC := notin u hu rfl
      have hvC := notin v hv e1.symm
      have hwC := notin w hw e2.symm
      simp only [Bool.not_false]
      rw [e_out false u huC, e_out false v hvC] at e1
      rw [e_out false u huC, e_out false w hwC] at e2
      rw [e_out false u huC, hub_even] at hhub
      rw [e_out true u huC, e_out true v hvC, e_out true w hwC]
      rcases hR.2.1 false u (hout u hu huC) v (hout v hv hvC) w (hout w hw hwC) (by omega)
        (by omega) hhub with h1 | h1 | h1
      · exact Or.inl (by simp only [Bool.not_false] at h1; rw [h1])
      · exact Or.inr (Or.inl (by simp only [Bool.not_false] at h1; rw [h1]))
      · exact Or.inr (Or.inr (by simp only [Bool.not_false] at h1; rw [h1]))
    · simp only [Bool.not_true]
      by_cases huC : u ∈ C
      · have inC : ∀ x ∈ W, e' true x = e' true u → x ∈ C := by
          intro x hx hx'
          by_contra hxC
          rw [e_out true x hxC, eT_in u huC] at hx'
          omega
        have hvC := inC v hv e1.symm
        have hwC := inC w hw e2.symm
        have side : ∀ x ∈ C, e' false x = 2 * e false a ∧ x ∈ C1 ∨
            e' false x = 2 * e false b ∧ x ∈ C2 := by
          intro x hx
          rcases mem_union.1 hx with h1 | h1
          · exact Or.inl ⟨eF1 x h1, h1⟩
          · exact Or.inr ⟨eF2 x h1, h1⟩
        rcases side u huC with ⟨hu1, -⟩ | ⟨hu1, -⟩ <;> rcases side v hvC with ⟨hv1, -⟩ | ⟨hv1, -⟩ <;>
          rcases side w hwC with ⟨hw1, -⟩ | ⟨hw1, -⟩ <;> omega
      · have outC : ∀ x ∈ W, e' true x = e' true u → x ∉ C := by
          intro x hx hx' hxC
          rw [e_out true u huC, eT_in x hxC] at hx'
          omega
        have hvC := outC v hv e1.symm
        have hwC := outC w hw e2.symm
        rw [e_out true u huC, e_out true v hvC] at e1
        rw [e_out true u huC, e_out true w hwC] at e2
        rw [e_out true u huC, hub_even] at hhub
        rw [e_out false u huC, e_out false v hvC, e_out false w hwC]
        rcases hR.2.1 true u (hout u hu huC) v (hout v hv hvC) w (hout w hw hwC) (by omega)
          (by omega) hhub with h1 | h1 | h1
        · exact Or.inl (by simp only [Bool.not_true] at h1; rw [h1])
        · exact Or.inr (Or.inl (by simp only [Bool.not_true] at h1; rw [h1]))
        · exact Or.inr (Or.inr (by simp only [Bool.not_true] at h1; rw [h1]))
  · -- (3) adjacent vertices share an end
    intro u hu v hv huv
    by_cases huC : u ∈ C <;> by_cases hvC : v ∈ C
    · rcases mem_union.1 huC with hu1 | hu2 <;> rcases mem_union.1 hvC with hv1 | hv2
      · exact ⟨false, by rw [eF1 u hu1, eF1 v hv1]⟩
      · exact ⟨true, by rw [eT_in u huC, eT_in v hvC, (comp_eq u v hvC).2
          (Relation.ReflTransGen.single ⟨huv, Or.inl ⟨hu1, hv2⟩⟩)]⟩
      · exact ⟨true, by rw [eT_in u huC, eT_in v hvC, (comp_eq u v hvC).2
          (Relation.ReflTransGen.single ⟨huv, Or.inr ⟨hu2, hv1⟩⟩)]⟩
      · exact ⟨false, by rw [eF2 u hu2, eF2 v hv2]⟩
    · rcases mem_union.1 huC with hu1 | hu2
      · have := (hP.out1 hv (notC1 v hvC) (notC2 v hvC) hu1 huv.symm).1 a ha
        exact ⟨false, by rw [eF1 u hu1, e_out false v hvC, endA v hv hvC this]⟩
      · have := (hP.out2 hv (notC1 v hvC) (notC2 v hvC) hu2 huv.symm).1 b hb
        exact ⟨false, by rw [eF2 u hu2, e_out false v hvC, endB v hv hvC this]⟩
    · rcases mem_union.1 hvC with hv1 | hv2
      · have := (hP.out1 hu (notC1 u huC) (notC2 u huC) hv1 huv).1 a ha
        exact ⟨false, by rw [eF1 v hv1, e_out false u huC, endA u hu huC this]⟩
      · have := (hP.out2 hu (notC1 u huC) (notC2 u huC) hv2 huv).1 b hb
        exact ⟨false, by rw [eF2 v hv2, e_out false u huC, endB u hu huC this]⟩
    · obtain ⟨σ, hσ⟩ := hR.2.2.1 u (hout u hu huC) v (hout v hv hvC) huv
      exact ⟨σ, by rw [e_out σ u huC, e_out σ v hvC, hσ]⟩
  · -- (4) non-adjacent vertices sharing an end share a hub
    intro u hu v hv huv hsh hna
    have mixed : ∀ x ∈ W, ∀ y ∈ W, x ∈ C → y ∉ C → (∃ σ, e' σ x = e' σ y) →
        ¬ G.Adj x y → False := by
      rintro x hx y hy hxC hyC ⟨σ, hσ⟩ hxy
      cases σ
      · rcases mem_union.1 hxC with hx1 | hx2
        · rw [eF1 x hx1, e_out false y hyC] at hσ
          have hya := adjA y hy hyC (by omega)
          exact hxy ((hP.out1 hy (notC1 y hyC) (notC2 y hyC) ha hya).1 x hx1).symm
        · rw [eF2 x hx2, e_out false y hyC] at hσ
          have hyb := adjB y hy hyC (by omega)
          exact hxy ((hP.out2 hy (notC1 y hyC) (notC2 y hyC) hb hyb).1 x hx2).symm
      · rw [eT_in x hxC, e_out true y hyC] at hσ
        omega
    have cross12 : ∀ x ∈ C1, ∀ y ∈ C2, (∃ σ, e' σ x = e' σ y) → ¬ G.Adj x y →
        ∃ σ, e' σ x = e' σ y ∧ e' σ x ∈ h' σ ∧ e' (!σ) x ≠ e' (!σ) y := by
      rintro x hx y hy ⟨σ, hσ⟩ hxy
      have hxC : x ∈ C := mem_union_left _ hx
      have hyC : y ∈ C := mem_union_right _ hy
      cases σ
      · rw [eF1 x hx, eF2 y hy] at hσ
        exact absurd (by omega : e false a = e false b) hne
      · have hcomp : comp x = comp y := by
          rw [eT_in x hxC, eT_in y hyC] at hσ
          exact finsetCode_inj (by omega)
        have hRxy := (comp_eq x y hyC).1 hcomp
        refine ⟨true, hσ, ?_, ?_⟩
        · rw [eT_in x hxC, hub_odd x hxC]
          exact big_of x hx y hy hRxy hxy
        · simp only [Bool.not_true]
          rw [eF1 x hx, eF2 y hy]
          omega
    by_cases huC : u ∈ C <;> by_cases hvC : v ∈ C
    · rcases mem_union.1 huC with hu1 | hu2 <;> rcases mem_union.1 hvC with hv1 | hv2
      · exact absurd (hP.clq1 u hu1 v hv1 huv) hna
      · exact cross12 u hu1 v hv2 hsh hna
      · obtain ⟨σ, h1, h2, h3⟩ := cross12 v hv1 u hu2 (hsh.imp fun _ h => h.symm)
          (fun h => hna h.symm)
        exact ⟨σ, h1.symm, by rw [← h1]; exact h2, fun h => h3 h.symm⟩
      · exact absurd (hP.clq2 u hu2 v hv2 huv) hna
    · exact (mixed u hu v hv huC hvC hsh hna).elim
    · exact (mixed v hv u hu hvC huC (hsh.imp fun _ h => h.symm) (fun h => hna h.symm)).elim
    · obtain ⟨σ, hσ⟩ := hsh
      rw [e_out σ u huC, e_out σ v hvC] at hσ
      obtain ⟨τ, t1, t2, t3⟩ :=
        hR.2.2.2 u (hout u hu huC) v (hout v hv hvC) huv ⟨σ, by omega⟩ hna
      refine ⟨τ, by rw [e_out τ u huC, e_out τ v hvC, t1],
        by rw [e_out τ u huC, hub_even]; exact t2, ?_⟩
      rw [e_out _ u huC, e_out _ v hvC]
      omega
  · -- normalization
    intro σ s hs
    have transfer : ∀ τ m, m ∈ h τ → (∀ x ∈ W, e' τ x = 2 * m → x ∉ C) →
        (∀ x ∈ W', e τ x = m → x ∉ C) →
        (∀ v ∈ W, e' τ v = 2 * m → ∃ w ∈ W, w ≠ v ∧ e' τ w = 2 * m ∧ e' (!τ) w = e' (!τ) v) ∧
        (∃ u ∈ W, ∃ v ∈ W, e' τ u = 2 * m ∧ e' τ v = 2 * m ∧ e' (!τ) u ≠ e' (!τ) v) ∧
        (∀ S ⊆ star W e' τ (2 * m), S.Nonempty → S ≠ star W e' τ (2 * m) →
          ∃ u ∈ S, ∃ v ∈ star W e' τ (2 * m), v ∉ S ∧ G.Adj u v ∧ e' (!τ) u ≠ e' (!τ) v) := by
      intro τ m hm f1 f2
      obtain ⟨n1, n2, n3⟩ := hN τ m hm
      have inW : ∀ x ∈ W', x ∉ C → x ∈ W := by
        intro x hx hxC
        rcases mem_union.1 hx with hx | hx
        · exact (mem_sdiff.1 hx).1
        · rcases mem_insert.1 hx with rfl | hx
          · exact absurd haC hxC
          · rw [mem_singleton.1 hx] at hxC; exact absurd hbC hxC
      have hst : star W e' τ (2 * m) = star W' e τ m := by
        ext x
        simp only [mem_star]
        constructor
        · rintro ⟨hx, hxe⟩
          have hxC := f1 x hx hxe
          rw [e_out τ x hxC] at hxe
          exact ⟨hout x hx hxC, by omega⟩
        · rintro ⟨hx, hxe⟩
          have hxC := f2 x hx hxe
          exact ⟨inW x hx hxC, by rw [e_out τ x hxC, hxe]⟩
      refine ⟨fun v hv hve => ?_, ?_, fun S hS hSne hSW => ?_⟩
      · have hvC := f1 v hv hve
        rw [e_out τ v hvC] at hve
        obtain ⟨w, hw, hwv, e1, e2⟩ := n1 v (hout v hv hvC) (by omega)
        have hwC := f2 w hw e1
        exact ⟨w, inW w hw hwC, hwv, by rw [e_out τ w hwC, e1],
          by rw [e_out _ w hwC, e_out _ v hvC, e2]⟩
      · obtain ⟨u, hu, v, hv, e1, e2, e3⟩ := n2
        have huC := f2 u hu e1
        have hvC := f2 v hv e2
        refine ⟨u, inW u hu huC, v, inW v hv hvC, by rw [e_out τ u huC, e1],
          by rw [e_out τ v hvC, e2], ?_⟩
        rw [e_out _ u huC, e_out _ v hvC]
        omega
      · rw [hst] at hS hSW
        obtain ⟨u, hu, v, hv, hvS, hadj, hne'⟩ := n3 S hS hSne hSW
        have huC := f2 u (mem_star.1 (hS hu)).1 (mem_star.1 (hS hu)).2
        have hvC := f2 v (mem_star.1 hv).1 (mem_star.1 hv).2
        refine ⟨u, hu, v, hst ▸ hv, hvS, hadj, ?_⟩
        rw [e_out _ u huC, e_out _ v hvC]
        omega
    cases σ
    · obtain ⟨m, hm, rfl⟩ := hs
      refine transfer false m hm ?_ ?_
      · intro x hx hxe hxC
        rcases mem_union.1 hxC with hx1 | hx2
        · rw [eF1 x hx1] at hxe
          exact hta (by rw [show e false a = m by omega]; exact hm)
        · rw [eF2 x hx2] at hxe
          exact htb (by rw [show e false b = m by omega]; exact hm)
      · intro x hx hxe hxC
        rcases hW'C x hx hxC with rfl | rfl
        · exact hta (hxe ▸ hm)
        · exact htb (hxe ▸ hm)
    · rcases hs with ⟨m, hm, rfl⟩ | ⟨v0, hv0, rfl, hbig⟩
      · refine transfer true m hm ?_ ?_
        · intro x hx hxe hxC
          rw [eT_in x hxC] at hxe
          omega
        · intro x hx hxe hxC
          rcases hW'C x hx hxC with rfl | rfl
          · exact hsn (hxe ▸ hm)
          · exact hsn (by rw [hs, hxe]; exact hm)
      · -- a new hub: the star is the component of `v0`
        have hst : star W e' true (2 * finsetCode (comp v0) + 1) = comp v0 := by
          ext x
          simp only [mem_star]
          constructor
          · rintro ⟨hx, hxe⟩
            by_cases hxC : x ∈ C
            · rw [eT_in x hxC] at hxe
              have hc : comp x = comp v0 := finsetCode_inj (by omega)
              exact mem_filter.2 ⟨hxC, crossRT_symm ((comp_eq x v0 hv0).1 hc)⟩
            · rw [e_out true x hxC] at hxe
              omega
          · intro hx
            obtain ⟨hxC, hRx⟩ := mem_filter.1 hx
            exact ⟨hCW x hxC, by rw [eT_in x hxC, (comp_eq x v0 hv0).2 (crossRT_symm hRx)]⟩
        have inst : ∀ x ∈ W, e' true x = 2 * finsetCode (comp v0) + 1 → x ∈ comp v0 :=
          fun x hx hxe => hst ▸ mem_star.2 ⟨hx, hxe⟩
        refine ⟨fun v hv hve => ?_, ?_, fun S hS hSne hSW => ?_⟩
        · have hvK := inst v hv hve
          obtain ⟨hvC, -⟩ := mem_filter.1 hvK
          rcases mem_union.1 hvC with hv1 | hv2
          · obtain ⟨w, hw, hwv⟩ :=
              exists_mem_ne (by have := hbig.1; omega : 1 < #(comp v0 ∩ C1)) v
            obtain ⟨hwK, hw1⟩ := mem_inter.1 hw
            rw [← hst] at hwK
            exact ⟨w, hC1 w hw1, hwv, (mem_star.1 hwK).2,
              by simp only [Bool.not_true]; rw [eF1 w hw1, eF1 v hv1]⟩
          · obtain ⟨w, hw, hwv⟩ :=
              exists_mem_ne (by have := hbig.2; omega : 1 < #(comp v0 ∩ C2)) v
            obtain ⟨hwK, hw2⟩ := mem_inter.1 hw
            rw [← hst] at hwK
            exact ⟨w, hC2 w hw2, hwv, (mem_star.1 hwK).2,
              by simp only [Bool.not_true]; rw [eF2 w hw2, eF2 v hv2]⟩
        · obtain ⟨u, hu⟩ := card_pos.1 (by have := hbig.1; omega : 0 < #(comp v0 ∩ C1))
          obtain ⟨w, hw⟩ := card_pos.1 (by have := hbig.2; omega : 0 < #(comp v0 ∩ C2))
          obtain ⟨huK, hu1⟩ := mem_inter.1 hu
          obtain ⟨hwK, hw2⟩ := mem_inter.1 hw
          rw [← hst] at huK hwK
          refine ⟨u, hC1 u hu1, w, hC2 w hw2, (mem_star.1 huK).2, (mem_star.1 hwK).2, ?_⟩
          simp only [Bool.not_true]
          rw [eF1 u hu1, eF2 w hw2]
          omega
        · rw [hst] at hS hSW
          obtain ⟨x, hx⟩ := hSne
          have hyex : ∃ y ∈ comp v0, y ∉ S := by
            by_contra hno
            push_neg at hno
            exact hSW (Subset.antisymm hS hno)
          obtain ⟨y, hy, hyS⟩ := hyex
          have hRx := (mem_filter.1 (hS hx)).2
          have hRy := (mem_filter.1 hy).2
          obtain ⟨p, hp, q, hqS, hRq, hpq⟩ :=
            crossRT_cut hx ((crossRT_symm hRx).trans hRy) hyS
          have hqC := (cross_C p q hpq).2
          have hqK : q ∈ comp v0 := mem_filter.2 ⟨hqC, hRx.trans hRq⟩
          refine ⟨p, hp, q, (by rw [hst]; exact hqK), hqS, hpq.1, ?_⟩
          simp only [Bool.not_true]
          rcases hpq.2 with ⟨hp1, hq2⟩ | ⟨hp2, hq1⟩
          · rw [eF1 p hp1, eF2 q hq2]; omega
          · rw [eF2 p hp2, eF1 q hq1]; omega

end ElemChoos.MR
