/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MainStep

/-!
# Proposition 3.7: the main step

With the notation of the paper: `U`, `V` are the free vertices of `X`, `Y` (here `free G X Y`,
`free G Y X`), `X0`, `Y0` the matched ones, `S ⊆ U` a set of minimum surplus with `z ∈ S`.
-/

@[expose] public section

open Finset

namespace ElemChoos

open scoped Classical

variable {V C : Type*}

namespace Aug

variable {G : SimpleGraph V} {W : Finset V} {k : ℕ} {X Y NX NY : Finset V}

theorem notMem_matched_of_mem_free {G : SimpleGraph V} {X Y : Finset V} {v : V}
    (h : v ∈ free G X Y) : v ∉ matched G X Y := fun h' =>
  (mem_filter.1 h).2 (mem_filter.1 h').2

/-- **Proposition 3.7, main step.** With `S ⊆ U` of minimum surplus on the side chosen by
inequality (3), the counterexample is colourable: contradiction. -/
theorem main_step [Nonempty C] (A : Aug G W k X Y NX NY) {L : V → Finset C}
    (hL : ∀ v ∈ W, k ≤ #(L v))
    (IH : ∀ W' ⊂ W, ∀ L' : V → Finset C, (∀ v ∈ W', k ≤ #(L' v)) → ∃ f, Colours G W' L' f)
    (hbad : ¬ ∃ f, Colours G W L f) {x0 y0 : V} (hx0 : x0 ∈ X) (hy0 : y0 ∈ Y)
    (hxy0 : ¬ G.Adj x0 y0) {S : Finset V} (hSU : S ⊆ free G X Y) (hSn : S.Nonempty)
    (hSmin : ∀ I ⊆ free G X Y, I.Nonempty → surplus L S ≤ surplus L I)
    (hSY : ∀ S' ⊆ free G Y X, S'.Nonempty →
      surplus L S + #(free G X Y) ≤ surplus L S' + #(free G Y X)) : False := by
  have hk : #X + #(free G Y X) = k := A.k_eq hx0 hy0 hxy0
  have hkY : #Y + #(free G X Y) = k := A.swap.k_eq hy0 hx0 (fun h => hxy0 h.symm)
  have hcX := card_matched_add_card_free G X Y
  have hXnY : ∀ v ∈ X, v ∉ Y := fun v hv hv' => disjoint_left.1 A.hXY hv hv'
  obtain ⟨z, hzS⟩ := hSn
  have hzU := hSU hzS
  have hzX : z ∈ X := free_subset G X Y hzU
  have hzW := A.hXW hzX
  have hy0Y0 : y0 ∈ matched G Y X := mem_filter.2 ⟨hy0, x0, hx0, fun h => hxy0 h.symm⟩
  have hY0Y : matched G Y X ⊆ Y := matched_subset G Y X
  have hss : W \ matched G Y X ⊂ W := by
    refine sdiff_subset.ssubset_of_ne ?_
    intro h
    have hy' : y0 ∈ W \ matched G Y X := by rw [h]; exact A.hYW hy0
    exact (mem_sdiff.1 hy').2 hy0Y0
  -- colour `G - Y0` with the list of `z` copied onto `X0`
  obtain ⟨f, hfL, hfP⟩ := IH (W \ matched G Y X) hss
    (fun v => if v ∈ matched G X Y then L z else L v) (by
      intro v hv
      split_ifs
      · exact hL z hzW
      · exact hL v (mem_sdiff.1 hv).1)
  have hW'of : ∀ v ∈ W, v ∉ Y → v ∈ W \ matched G Y X :=
    fun v hv h => mem_sdiff.2 ⟨hv, fun h' => h (hY0Y h')⟩
  have hfL0 : ∀ v ∈ W, v ∉ X → v ∉ Y → f v ∈ L v := by
    intro v hv h1 h2
    have := hfL v (hW'of v hv h2)
    have hv0 : v ∉ matched G X Y := fun h => h1 (matched_subset G X Y h)
    simpa [hv0] using this
  have hfP0 : ∀ u ∈ W, ∀ v ∈ W, u ∉ X → u ∉ Y → v ∉ X → v ∉ Y → G.Adj u v → f u ≠ f v :=
    fun u hu v hv _ h2 _ h4 huv => hfP u (hW'of u hu h2) v (hW'of v hv h4) huv
  by_cases hg : ∃ g, Colours G (X ∪ Y) (resid X NX NY L f) g
  · obtain ⟨g, hg⟩ := hg
    exact hbad (A.colours_of_resid hfL0 hfP0 hg)
  obtain ⟨T, hT, hTU, hTV, hTR⟩ := deficiency G _ X Y (resid X NX NY L f) A.hXY A.hX A.hY
    A.uniqMiss A.uniqMiss' rfl (fun v hv => A.card_resid_X hL f hv)
    (fun v hv => A.card_resid_Y hL f hv) hg
  -- (B2)
  have hNXW' : ∀ w ∈ NX, w ∈ W \ matched G Y X :=
    fun w hw => hW'of w (A.hNXW hw) (A.hNXJ w hw).2
  have hNYW' : ∀ w ∈ NY, w ∈ W \ matched G Y X :=
    fun w hw => hW'of w (A.hNYW hw) (A.hNYJ w hw).2
  have hVW' : ∀ w ∈ free G Y X, w ∈ W \ matched G Y X := fun w hw =>
    mem_sdiff.2 ⟨A.hYW (free_subset G Y X hw), notMem_matched_of_mem_free hw⟩
  have hfX : ∀ x ∈ X, f x ∉ NX.image f := by
    intro x hx hmem
    obtain ⟨w, hw, hfw⟩ := mem_image.1 hmem
    have hadj := (A.hNX x hx w (A.hNXW hw) (A.hNXJ w hw).1 (A.hNXJ w hw).2).2 hw
    exact hfP x (hW'of x (A.hXW hx) (hXnY x hx)) w (hNXW' w hw) hadj hfw.symm
  have hB2a : ∀ x ∈ matched G X Y, f x ∈ resid X NX NY L f z := by
    intro x hx
    have hxX := matched_subset G X Y hx
    have h1 := hfL x (hW'of x (A.hXW hxX) (hXnY x hxX))
    simp only [if_pos hx] at h1
    simp only [resid, if_pos hzX, mem_sdiff]
    exact ⟨h1, hfX x hxX⟩
  have hB2b : ∀ w ∈ free G X Y ∪ free G Y X, f w ∈ resid X NX NY L f w := by
    intro w hw
    rcases mem_union.1 hw with hwU | hwV
    · have hwX := free_subset G X Y hwU
      have h1 := hfL w (hW'of w (A.hXW hwX) (hXnY w hwX))
      simp only [if_neg (notMem_matched_of_mem_free hwU)] at h1
      simp only [resid, if_pos hwX, mem_sdiff]
      exact ⟨h1, hfX w hwX⟩
    · have hwY := free_subset G Y X hwV
      have hwX : w ∉ X := fun h => hXnY w h hwY
      have hw0 : w ∉ matched G X Y := fun h => hwX (matched_subset G X Y h)
      have h1 := hfL w (hVW' w hwV)
      simp only [if_neg hw0] at h1
      simp only [resid, if_neg hwX, mem_sdiff]
      refine ⟨h1, ?_⟩
      intro hmem
      obtain ⟨u, hu, hfu⟩ := mem_image.1 hmem
      have hadj := (A.hNY w hwY u (A.hNYW hu) (A.hNYJ u hu).1 (A.hNYJ u hu).2).2 hu
      exact hfP w (hVW' w hwV) u (hNYW' u hu) hadj hfu.symm
  have hQinj : ∀ u ∈ X ∪ free G Y X, ∀ v ∈ X ∪ free G Y X, f u = f v → u = v := by
    intro u hu v hv huv
    by_contra hne
    have hadj : G.Adj u v := A.isClique_X_free hu hv hne
    have hu' : u ∈ W \ matched G Y X := by
      rcases mem_union.1 hu with h | h
      · exact hW'of u (A.hXW h) (hXnY u h)
      · exact hVW' u h
    have hv' : v ∈ W \ matched G Y X := by
      rcases mem_union.1 hv with h | h
      · exact hW'of v (A.hXW h) (hXnY v h)
      · exact hVW' v h
    exact hfP u hu' v hv' hadj huv
  -- (C1): `T` meets `S`
  have hTsplit : #T = #(T ∩ free G X Y) + #(T ∩ free G Y X) := by
    have hdis : Disjoint (T ∩ free G X Y) (T ∩ free G Y X) :=
      disjoint_of_subset_left (inter_subset_right.trans (free_subset G X Y))
        (disjoint_of_subset_right (inter_subset_right.trans (free_subset G Y X)) A.hXY)
    rw [← card_union_of_disjoint hdis, ← inter_union_distrib_left, inter_eq_left.2 hT]
  have hLTV : #((T ∩ free G Y X).biUnion L) ≤
      #(T.biUnion (resid X NX NY L f)) + #(NY.image f) := by
    have : (T ∩ free G Y X).biUnion L ⊆ T.biUnion (resid X NX NY L f) ∪ NY.image f := by
      intro c hc
      obtain ⟨y, hy, hcy⟩ := mem_biUnion.1 hc
      have hyT := (mem_inter.1 hy).1
      have hyY := free_subset G Y X (mem_inter.1 hy).2
      by_cases hcF : c ∈ NY.image f
      · exact mem_union_right _ hcF
      · refine mem_union_left _ (mem_biUnion.2 ⟨y, hyT, ?_⟩)
        simp only [resid, if_neg (fun h => hXnY y h hyY), mem_sdiff]
        exact ⟨hcy, hcF⟩
    exact (card_le_card this).trans (card_union_le _ _)
  have hFY : #(NY.image f) ≤ #(free G X Y) := by
    have := A.swap.card_NX_le
    have := card_image_le (s := NY) (f := f)
    omega
  have hTVsur := hSY _ inter_subset_right hTV
  have hSsur : (k : ℤ) ≤ #(S.biUnion L) := by
    have : #(L z) ≤ #(S.biUnion L) := card_le_card (subset_biUnion_of_mem L hzS)
    have := hL z hzW
    omega
  have hTS : (T ∩ S).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hTUS : T ∩ free G X Y ⊆ free G X Y \ S := by
      intro v hv
      refine mem_sdiff.2 ⟨(mem_inter.1 hv).2, fun hvS => ?_⟩
      have : v ∈ T ∩ S := mem_inter.2 ⟨(mem_inter.1 hv).1, hvS⟩
      rw [hne] at this
      exact absurd this (notMem_empty _)
    have h1 := card_le_card hTUS
    have h2 := card_sdiff_add_card_eq_card hSU
    simp only [surplus] at hTVsur
    omega
  -- (C2): `T ∪ S` is still deficient
  obtain ⟨i0, hi0⟩ := hTS
  have hRTs : #((T ∪ S).biUnion (resid X NX NY L f)) ≤
      #(T.biUnion (resid X NX NY L f)) + #(S \ T) := by
    have hsub : (T ∪ S).biUnion (resid X NX NY L f) ⊆
        T.biUnion (resid X NX NY L f) ∪ (S.biUnion L \ (T ∩ S).biUnion L) := by
      intro c hc
      obtain ⟨v, hv, hcv⟩ := mem_biUnion.1 hc
      by_cases hcT : c ∈ T.biUnion (resid X NX NY L f)
      · exact mem_union_left _ hcT
      · have hvS : v ∈ S := (mem_union.1 hv).resolve_left
          (fun hvT => hcT (mem_biUnion.2 ⟨v, hvT, hcv⟩))
        have hvX := free_subset G X Y (hSU hvS)
        simp only [resid, if_pos hvX, mem_sdiff] at hcv
        refine mem_union_right _ (mem_sdiff.2 ⟨mem_biUnion.2 ⟨v, hvS, hcv.1⟩, ?_⟩)
        intro hcI
        obtain ⟨i, hi, hci⟩ := mem_biUnion.1 hcI
        have hiX := free_subset G X Y (hSU (mem_inter.1 hi).2)
        apply hcT
        refine mem_biUnion.2 ⟨i, (mem_inter.1 hi).1, ?_⟩
        simp only [resid, if_pos hiX, mem_sdiff]
        exact ⟨hci, hcv.2⟩
    have hIS : T ∩ S ⊆ S := inter_subset_right
    have hLI : (T ∩ S).biUnion L ⊆ S.biUnion L := biUnion_subset_biUnion_of_subset_left L hIS
    have h1 := card_le_card hsub
    have h2 := card_union_le (T.biUnion (resid X NX NY L f)) (S.biUnion L \ (T ∩ S).biUnion L)
    have h3 := card_sdiff_add_card_eq_card hLI
    have h4 := hSmin (T ∩ S) (hIS.trans hSU) ⟨i0, hi0⟩
    have h5 := card_sdiff_add_card_inter S T
    rw [inter_comm S T] at h5
    simp only [surplus] at h4
    omega
  -- final count on the clique `X ∪ V`
  have hTsQ : T ∪ S ⊆ free G X Y ∪ free G Y X := union_subset hT (hSU.trans subset_union_left)
  have hcardTs : #(T ∪ S) = #T + #(S \ T) := by
    rw [← union_sdiff_self_eq_union, card_union_of_disjoint disjoint_sdiff]
  have hX0Ts : Disjoint (matched G X Y) (T ∪ S) := by
    refine disjoint_left.2 fun v hv hv' => ?_
    rcases mem_union.1 (hTsQ hv') with h | h
    · exact notMem_matched_of_mem_free h hv
    · exact hXnY v (matched_subset G X Y hv) (free_subset G Y X h)
  have hinQ : ∀ v ∈ matched G X Y ∪ (T ∪ S), v ∈ X ∪ free G Y X := by
    intro v hv
    rcases mem_union.1 hv with h | h
    · exact mem_union_left _ (matched_subset G X Y h)
    · rcases mem_union.1 (hTsQ h) with h' | h'
      · exact mem_union_left _ (free_subset G X Y h')
      · exact mem_union_right _ h'
  have hinj : #(matched G X Y ∪ (T ∪ S)) ≤ #((T ∪ S).biUnion (resid X NX NY L f)) := by
    refine card_le_card_of_injOn f ?_ ?_
    · intro v hv
      rw [mem_coe] at hv ⊢
      rcases mem_union.1 hv with h | h
      · exact mem_biUnion.2 ⟨z, mem_union_right _ hzS, hB2a v h⟩
      · exact mem_biUnion.2 ⟨v, h, hB2b v (hTsQ h)⟩
    · intro u hu v hv huv
      rw [mem_coe] at hu hv
      exact hQinj u (hinQ u hu) v (hinQ v hv) huv
  rw [card_union_of_disjoint hX0Ts] at hinj
  omega

/-- **Proposition 3.7.** Every augment of a minimal counterexample is complete. -/
theorem complete [Nonempty C] (A : Aug G W k X Y NX NY) {L : V → Finset C}
    (hL : ∀ v ∈ W, k ≤ #(L v))
    (IH : ∀ W' ⊂ W, ∀ L' : V → Finset C, (∀ v ∈ W', k ≤ #(L' v)) → ∃ f, Colours G W' L' f)
    (hbad : ¬ ∃ f, Colours G W L f) : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y := by
  intro x hx y hy
  by_contra hxy
  by_cases hfree : free G X Y = ∅ ∨ free G Y X = ∅
  · exact A.false_of_free_empty hL IH hbad hx hy hfree
  push_neg at hfree
  obtain ⟨hU, hV⟩ := hfree
  obtain ⟨SX, hSX, hSXmin⟩ := exists_min_image
    ((free G X Y).powerset.filter Finset.Nonempty) (surplus L) ⟨free G X Y, by simp [hU]⟩
  obtain ⟨SY, hSY, hSYmin⟩ := exists_min_image
    ((free G Y X).powerset.filter Finset.Nonempty) (surplus L) ⟨free G Y X, by simp [hV]⟩
  simp only [mem_filter, mem_powerset] at hSX hSY
  by_cases hcmp : surplus L SX + #(free G X Y) ≤ surplus L SY + #(free G Y X)
  · refine A.main_step hL IH hbad hx hy hxy hSX.1 hSX.2
      (fun I hI hIn => hSXmin I (by simp [hI, hIn])) (fun S' hS' hS'n => ?_)
    have := hSYmin S' (by simp [hS', hS'n])
    omega
  · refine A.swap.main_step hL IH hbad hy hx (fun h => hxy h.symm) hSY.1 hSY.2
      (fun I hI hIn => hSYmin I (by simp [hI, hIn])) (fun S' hS' hS'n => ?_)
    have := hSXmin S' (by simp [hS', hS'n])
    omega

end Aug

end ElemChoos
