/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.Hall.Basic

/-!
# Hall's theorem for list colourings and the Deficiency Lemma

Lemma 2.1, Corollary 2.2 and Lemma 2.5 of Narayanan–Vasudevan–Somasundaram,
*Elementary graphs are chromatic-choosable* (arXiv:2610.16258).

A graph `K(X, Y) - M` is described by two disjoint cliques `X`, `Y` of a graph `G` whose
non-adjacent `X`–`Y` pairs form a matching (`UniqMiss G X Y` and `UniqMiss G Y X`).
-/

@[expose] public section

open Finset

namespace ElemChoos

open scoped Classical

variable {V C : Type*}

/-- `f` is an `L`-colouring of `G` on the vertex set `S`. -/
abbrev Colours (G : SimpleGraph V) (S : Finset V) (L : V → Finset C) (f : V → C) : Prop :=
  (∀ v ∈ S, f v ∈ L v) ∧ ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → f u ≠ f v

/-- Every vertex of `X` has at most one non-neighbour in `Y`. -/
def UniqMiss (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, ¬ G.Adj x y → ¬ G.Adj x y' → y = y'

/-- The vertices of `X` with a non-neighbour in `Y` (the matched vertices). -/
noncomputable def matched (G : SimpleGraph V) (X Y : Finset V) : Finset V :=
  X.filter fun x => ∃ y ∈ Y, ¬ G.Adj x y

/-- The vertices of `X` complete to `Y` (the free vertices). -/
noncomputable def free (G : SimpleGraph V) (X Y : Finset V) : Finset V :=
  X.filter fun x => ¬ ∃ y ∈ Y, ¬ G.Adj x y

theorem card_matched_add_card_free (G : SimpleGraph V) (X Y : Finset V) :
    #(matched G X Y) + #(free G X Y) = #X :=
  card_filter_add_card_filter_not _

theorem free_subset (G : SimpleGraph V) (X Y : Finset V) : free G X Y ⊆ X := filter_subset _ _

theorem matched_subset (G : SimpleGraph V) (X Y : Finset V) : matched G X Y ⊆ X :=
  filter_subset _ _

/-- **Hall (Corollary 2.2).** If `G` has no `L`-colouring on `S`, some nonempty `W ⊆ S` is
deficient. -/
theorem exists_deficient [Nonempty C] (G : SimpleGraph V) (S : Finset V) (L : V → Finset C)
    (h : ¬ ∃ f, Colours G S L f) :
    ∃ W ⊆ S, W.Nonempty ∧ #(W.biUnion L) < #W := by
  by_contra hW
  push_neg at hW
  apply h
  have hall : ∀ s : Finset S, #s ≤ #(s.biUnion fun i => L i) := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have h1 := hW (s.map (Function.Embedding.subtype _)) (by
        intro v hv
        simp only [mem_map, Function.Embedding.coe_subtype] at hv
        obtain ⟨w, -, rfl⟩ := hv
        exact w.2) (hs.map)
      rw [card_map] at h1
      have h2 : (s.map (Function.Embedding.subtype _)).biUnion L = s.biUnion fun i => L i := by
        ext c; simp
      rwa [h2] at h1
  obtain ⟨g, hg, hgL⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective _).1 hall
  refine ⟨fun v => if hv : v ∈ S then g ⟨v, hv⟩ else Classical.arbitrary C, ?_, ?_⟩
  · intro v hv
    simp only [dif_pos hv]
    exact hgL _
  · intro u hu v hv huv heq
    simp only [dif_pos hu, dif_pos hv] at heq
    have := hg heq
    simp only [Subtype.mk.injEq] at this
    exact huv.ne this

/-- A set `D ⊆ X ∪ Y` of matched vertices containing no non-adjacent pair has at most as many
vertices as there are matched vertices in `X`. -/
theorem card_le_matched (G : SimpleGraph V) {X Y D : Finset V} (hmX : UniqMiss G X Y)
    (hD : D ⊆ X ∪ Y) (hDX : ∀ v ∈ D, v ∈ X → v ∈ matched G X Y)
    (hDY : ∀ v ∈ D, v ∈ Y → ∃ x ∈ X, ¬ G.Adj v x)
    (hnp : ∀ x ∈ D, ∀ y ∈ D, x ∈ X → y ∈ Y → G.Adj x y) : #D ≤ #(matched G X Y) := by
  let φ : V → V := fun v =>
    if v ∈ X then v else if h' : ∃ x ∈ X, ¬ G.Adj v x then h'.choose else v
  have hφY : ∀ v ∈ D, v ∉ X → φ v ∈ X ∧ ¬ G.Adj v (φ v) := by
    intro v hv hX
    have hY : v ∈ Y := by
      have := hD hv
      rw [mem_union] at this
      tauto
    have h' := hDY v hv hY
    simp only [φ, if_neg hX, dif_pos h']
    exact h'.choose_spec
  refine card_le_card_of_injOn φ ?_ ?_
  · intro v hv
    rw [mem_coe] at hv ⊢
    by_cases hX : v ∈ X
    · simp only [φ, if_pos hX]
      exact hDX v hv hX
    · obtain ⟨h1, h2⟩ := hφY v hv hX
      refine mem_filter.2 ⟨h1, v, ?_, fun h => h2 h.symm⟩
      have := hD hv
      rw [mem_union] at this
      tauto
  · intro u hu v hv huv
    rw [mem_coe] at hu hv
    have hYof : ∀ w ∈ D, w ∉ X → w ∈ Y := by
      intro w hw hX
      have := hD hw
      rw [mem_union] at this
      tauto
    by_cases hu' : u ∈ X <;> by_cases hv' : v ∈ X
    · simpa [φ, hu', hv'] using huv
    · obtain ⟨_, h2⟩ := hφY v hv hv'
      have : φ u = u := by simp [φ, hu']
      rw [this] at huv
      rw [← huv] at h2
      exact absurd (hnp u hu v hv hu' (hYof v hv hv')).symm h2
    · obtain ⟨_, h2⟩ := hφY u hu hu'
      have : φ v = v := by simp [φ, hv']
      rw [this] at huv
      rw [huv] at h2
      exact absurd (hnp v hv u hu hv' (hYof u hu hu')).symm h2
    · obtain ⟨h1, h2⟩ := hφY u hu hu'
      obtain ⟨_, h4⟩ := hφY v hv hv'
      rw [huv] at h1 h2
      exact hmX _ h1 u (hYof u hu hu') v (hYof v hv hv') (fun h => h2 h.symm)
        (fun h => h4 h.symm)

/-- A deficient set lying in `Z`, all of whose lists have at least `|Z|` colours, is impossible. -/
theorem not_deficient_of_subset {Z W : Finset V} {R : V → Finset C} (hW : #W ≤ #Z)
    {w : V} (hw : w ∈ W) (hwZ : w ∈ Z) (hRZ : ∀ z ∈ Z, #Z ≤ #(R z)) :
    ¬ #(W.biUnion R) < #W := by
  have : #(R w) ≤ #(W.biUnion R) := card_le_card (subset_biUnion_of_mem R hw)
  have := hRZ w hwZ
  omega

/-- Case 1 of the Deficiency Lemma: a deficient set containing no missing pair. -/
theorem deficiency_case1 (G : SimpleGraph V) {X Y : Finset V} {R : V → Finset C}
    (_hXY : Disjoint X Y) (hmX : UniqMiss G X Y) (hmY : UniqMiss G Y X)
    (hRX : ∀ x ∈ X, #X ≤ #(R x)) (hRY : ∀ y ∈ Y, #Y ≤ #(R y))
    {W : Finset V} (hW : W ⊆ X ∪ Y) (hWn : W.Nonempty) (hdef : #(W.biUnion R) < #W)
    (hnp : ∀ x ∈ W, ∀ y ∈ W, x ∈ X → y ∈ Y → G.Adj x y) :
    ∃ T ⊆ free G X Y ∪ free G Y X, (T ∩ free G X Y).Nonempty ∧ (T ∩ free G Y X).Nonempty ∧
      #(T.biUnion R) + 1 ≤ #T + #(matched G X Y) := by
  set T := W.filter fun v => v ∈ free G X Y ∨ v ∈ free G Y X with hT
  set D := W.filter fun v => ¬ (v ∈ free G X Y ∨ v ∈ free G Y X) with hD
  have hTD : #T + #D = #W := card_filter_add_card_filter_not _
  have hDW : D ⊆ W := filter_subset _ _
  have hTW : T ⊆ W := filter_subset _ _
  have hmemXY : ∀ v ∈ W, v ∈ X ∨ v ∈ Y := fun v hv => mem_union.1 (hW hv)
  -- matched vertices of `D`
  have hDX : ∀ v ∈ D, v ∈ X → v ∈ matched G X Y := by
    intro v hv hX
    rw [hD, mem_filter] at hv
    refine mem_filter.2 ⟨hX, ?_⟩
    by_contra h
    exact hv.2 (Or.inl (mem_filter.2 ⟨hX, h⟩))
  have hDY : ∀ v ∈ D, v ∈ Y → v ∈ matched G Y X := by
    intro v hv hY
    rw [hD, mem_filter] at hv
    refine mem_filter.2 ⟨hY, ?_⟩
    by_contra h
    exact hv.2 (Or.inr (mem_filter.2 ⟨hY, h⟩))
  have hnpD : ∀ x ∈ D, ∀ y ∈ D, x ∈ X → y ∈ Y → G.Adj x y :=
    fun x hx y hy => hnp x (hDW hx) y (hDW hy)
  have hD1 : #D ≤ #(matched G X Y) := by
    refine card_le_matched G hmX (hDW.trans hW) hDX ?_ hnpD
    intro v hv hY
    have := hDY v hv hY
    rw [matched, mem_filter] at this
    exact this.2
  have hD2 : #D ≤ #(matched G Y X) := by
    refine card_le_matched G hmY (hDW.trans (hW.trans (union_comm X Y).le)) hDY ?_ ?_
    · intro v hv hX
      have := hDX v hv hX
      rw [matched, mem_filter] at this
      exact this.2
    · intro y hy x hx hY hX
      exact (hnpD x hx y hy hX hY).symm
  have hcX := card_matched_add_card_free G X Y
  have hcY := card_matched_add_card_free G Y X
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hT, mem_filter] at hv
    exact mem_union.2 hv.2
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hTY : T ⊆ free G Y X := by
      intro v hv
      have hv' := hv
      rw [hT, mem_filter] at hv'
      rcases hv'.2 with h | h
      · have : v ∈ T ∩ free G X Y := mem_inter.2 ⟨hv, h⟩
        rw [hne] at this
        simp at this
      · exact h
    have hWY : #W ≤ #Y := by
      have := card_le_card hTY
      omega
    obtain ⟨w, hw⟩ := hWn
    by_cases hy : ∃ y ∈ W, y ∈ Y
    · obtain ⟨y, hyW, hyY⟩ := hy
      exact not_deficient_of_subset hWY hyW hyY hRY hdef
    · push_neg at hy
      have hWX : W ⊆ X := fun v hv => (hmemXY v hv).resolve_right (hy v hv)
      exact not_deficient_of_subset (card_le_card hWX) hw (hWX hw) hRX hdef
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hTX : T ⊆ free G X Y := by
      intro v hv
      have hv' := hv
      rw [hT, mem_filter] at hv'
      rcases hv'.2 with h | h
      · exact h
      · have : v ∈ T ∩ free G Y X := mem_inter.2 ⟨hv, h⟩
        rw [hne] at this
        simp at this
    have hWX : #W ≤ #X := by
      have := card_le_card hTX
      omega
    obtain ⟨w, hw⟩ := hWn
    by_cases hx : ∃ x ∈ W, x ∈ X
    · obtain ⟨x, hxW, hxX⟩ := hx
      exact not_deficient_of_subset hWX hxW hxX hRX hdef
    · push_neg at hx
      have hWY : W ⊆ Y := fun v hv => (hmemXY v hv).resolve_left (hx v hv)
      exact not_deficient_of_subset (card_le_card hWY) hw (hWY hw) hRY hdef
  · have := card_le_card (biUnion_subset_biUnion_of_subset_left R hTW)
    omega

theorem matched_erase (G : SimpleGraph V) {X Y : Finset V} (hmY : UniqMiss G Y X) {x y : V}
    (hx : x ∈ X) (hy : y ∈ Y) (hxy : ¬ G.Adj x y) :
    matched G (X.erase x) (Y.erase y) = (matched G X Y).erase x := by
  ext v
  simp only [matched, mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨hvx, hvX⟩, y', ⟨-, hy'⟩, hn⟩
    exact ⟨hvx, hvX, y', hy', hn⟩
  · rintro ⟨hvx, hvX, y', hy', hn⟩
    refine ⟨⟨hvx, hvX⟩, y', ⟨?_, hy'⟩, hn⟩
    rintro rfl
    exact hvx (hmY y' hy' v hvX x hx (fun h => hn h.symm) (fun h => hxy h.symm))

theorem free_erase (G : SimpleGraph V) {X Y : Finset V} (hmY : UniqMiss G Y X) {x y : V}
    (hx : x ∈ X) (hy : y ∈ Y) (hxy : ¬ G.Adj x y) :
    free G (X.erase x) (Y.erase y) = free G X Y := by
  ext v
  simp only [free, mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨hvx, hvX⟩, hn⟩
    refine ⟨hvX, ?_⟩
    rintro ⟨y', hy', hna⟩
    by_cases hyy : y' = y
    · subst hyy
      exact hvx (hmY y' hy' v hvX x hx (fun h => hna h.symm) (fun h => hxy h.symm))
    · exact hn ⟨y', ⟨hyy, hy'⟩, hna⟩
  · rintro ⟨hvX, hn⟩
    refine ⟨⟨?_, hvX⟩, ?_⟩
    · rintro rfl
      exact hn ⟨y, hy, hxy⟩
    · rintro ⟨y', ⟨-, hy'⟩, hna⟩
      exact hn ⟨y', hy', hna⟩

theorem uniqMiss_erase {G : SimpleGraph V} {X Y : Finset V} (h : UniqMiss G X Y) (x y : V) :
    UniqMiss G (X.erase x) (Y.erase y) := fun a ha b hb b' hb' =>
  h a (mem_of_mem_erase ha) b (mem_of_mem_erase hb) b' (mem_of_mem_erase hb')

/-- **Deficiency Lemma (Lemma 2.5).** Let `X`, `Y` be disjoint cliques whose missing pairs form a
matching with `n` matched vertices in `X`, and let `R` give lists of size at least `|X|` on `X` and
`|Y|` on `Y`. If `X ∪ Y` has no `R`-colouring, there is a set `T` of free vertices meeting both
sides with `|R(T)| ≤ |T| + n - 1`. -/
theorem deficiency [Nonempty C] (G : SimpleGraph V) :
    ∀ (n : ℕ) (X Y : Finset V) (R : V → Finset C), Disjoint X Y → G.IsClique (X : Set V) →
      G.IsClique (Y : Set V) → UniqMiss G X Y → UniqMiss G Y X → #(matched G X Y) = n →
      (∀ x ∈ X, #X ≤ #(R x)) → (∀ y ∈ Y, #Y ≤ #(R y)) → (¬ ∃ f, Colours G (X ∪ Y) R f) →
      ∃ T ⊆ free G X Y ∪ free G Y X, (T ∩ free G X Y).Nonempty ∧ (T ∩ free G Y X).Nonempty ∧
        #(T.biUnion R) + 1 ≤ #T + n := by
  intro n
  induction n with
  | zero =>
    intro X Y R hXY hX hY hmX hmY hn hRX hRY hno
    obtain ⟨W, hW, hWn, hdef⟩ := exists_deficient G _ R hno
    by_cases hp : ∃ x ∈ W, ∃ y ∈ W, x ∈ X ∧ y ∈ Y ∧ ¬ G.Adj x y
    · obtain ⟨x, -, y, -, hx, hy, hxy⟩ := hp
      have : x ∈ matched G X Y := mem_filter.2 ⟨hx, y, hy, hxy⟩
      rw [card_eq_zero] at hn
      rw [hn] at this
      simp at this
    · push_neg at hp
      have := deficiency_case1 G hXY hmX hmY hRX hRY hW hWn hdef
        (fun x hx y hy hxX hyY => hp x hx y hy hxX hyY)
      rwa [hn] at this
  | succ m ih =>
    intro X Y R hXY hX hY hmX hmY hn hRX hRY hno
    obtain ⟨W, hW, hWn, hdef⟩ := exists_deficient G _ R hno
    by_cases hp : ∃ x ∈ W, ∃ y ∈ W, x ∈ X ∧ y ∈ Y ∧ ¬ G.Adj x y
    · obtain ⟨x, hxW, y, hyW, hx, hy, hxy⟩ := hp
      -- a common colour of `x` and `y`
      obtain ⟨c, hc⟩ : (R x ∩ R y).Nonempty := by
        rw [nonempty_iff_ne_empty, ne_eq, ← disjoint_iff_inter_eq_empty]
        intro hdis
        have h1 := card_union_of_disjoint hdis
        have h2 : R x ∪ R y ⊆ W.biUnion R :=
          union_subset (subset_biUnion_of_mem R hxW) (subset_biUnion_of_mem R hyW)
        have h3 := card_le_card h2
        have h4 := card_le_card hW
        have h5 := card_union_of_disjoint hXY
        have := hRX x hx
        have := hRY y hy
        omega
      rw [mem_inter] at hc
      set R' : V → Finset C := fun v => (R v).erase c with hR'
      have hmx : x ∈ matched G X Y := mem_filter.2 ⟨hx, y, hy, hxy⟩
      have hn' : #(matched G (X.erase x) (Y.erase y)) = m := by
        have := card_erase_of_mem hmx
        rw [matched_erase G hmY hx hy hxy]
        omega
      have hRX' : ∀ v ∈ X.erase x, #(X.erase x) ≤ #(R' v) := by
        intro v hv
        rw [card_erase_of_mem hx]
        have := hRX v (mem_of_mem_erase hv)
        have := pred_card_le_card_erase (s := R v) (a := c)
        simp only [hR']
        omega
      have hRY' : ∀ v ∈ Y.erase y, #(Y.erase y) ≤ #(R' v) := by
        intro v hv
        rw [card_erase_of_mem hy]
        have := hRY v (mem_of_mem_erase hv)
        have := pred_card_le_card_erase (s := R v) (a := c)
        simp only [hR']
        omega
      have hno' : ¬ ∃ f, Colours G (X.erase x ∪ Y.erase y) R' f := by
        rintro ⟨f', hfL, hfP⟩
        apply hno
        refine ⟨fun v => if v = x ∨ v = y then c else f' v, ?_, ?_⟩
        · intro v hv
          by_cases h : v = x ∨ v = y
          · simp only [if_pos h]
            rcases h with rfl | rfl
            · exact hc.1
            · exact hc.2
          · simp only [if_neg h]
            push_neg at h
            have hv' : v ∈ X.erase x ∪ Y.erase y := by
              rw [mem_union] at hv ⊢
              rcases hv with hv | hv
              · exact Or.inl (mem_erase.2 ⟨h.1, hv⟩)
              · exact Or.inr (mem_erase.2 ⟨h.2, hv⟩)
            exact mem_of_mem_erase (hfL v hv')
        · intro u hu v hv huv
          have hmem : ∀ w ∈ X ∪ Y, ¬ (w = x ∨ w = y) → w ∈ X.erase x ∪ Y.erase y := by
            intro w hw h
            push_neg at h
            rw [mem_union] at hw ⊢
            rcases hw with hw | hw
            · exact Or.inl (mem_erase.2 ⟨h.1, hw⟩)
            · exact Or.inr (mem_erase.2 ⟨h.2, hw⟩)
          by_cases hu' : u = x ∨ u = y <;> by_cases hv' : v = x ∨ v = y
          · exfalso
            rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
            · exact huv.ne rfl
            · exact hxy huv
            · exact hxy huv.symm
            · exact huv.ne rfl
          · simp only [if_pos hu', if_neg hv']
            intro h
            have := hfL v (hmem v hv hv')
            rw [← h] at this
            simp [hR'] at this
          · simp only [if_neg hu', if_pos hv']
            intro h
            have := hfL u (hmem u hu hu')
            rw [h] at this
            simp [hR'] at this
          · simp only [if_neg hu', if_neg hv']
            exact hfP u (hmem u hu hu') v (hmem v hv hv') huv
      obtain ⟨T, hT, hTX, hTY, hTR⟩ := ih (X.erase x) (Y.erase y) R'
        (disjoint_of_subset_left (erase_subset _ _) (disjoint_of_subset_right (erase_subset _ _) hXY))
        (hX.subset (by simp)) (hY.subset (by simp))
        (uniqMiss_erase hmX x y) (uniqMiss_erase hmY y x) hn' hRX' hRY' hno'
      rw [free_erase G hmY hx hy hxy] at hT hTX
      rw [free_erase G hmX hy hx (fun h => hxy h.symm)] at hT hTY
      refine ⟨T, hT, hTX, hTY, ?_⟩
      have hsub : T.biUnion R ⊆ insert c (T.biUnion R') := by
        intro d hd
        rw [mem_biUnion] at hd
        obtain ⟨v, hv, hdv⟩ := hd
        by_cases hdc : d = c
        · exact hdc ▸ mem_insert_self _ _
        · exact mem_insert_of_mem (mem_biUnion.2 ⟨v, hv, mem_erase.2 ⟨hdc, hdv⟩⟩)
      have := card_le_card hsub
      have := card_insert_le c (T.biUnion R')
      omega
    · push_neg at hp
      have := deficiency_case1 G hXY hmX hmY hRX hRY hW hWn hdef
        (fun x hx y hy hxX hyY => hp x hx y hy hxX hyY)
      rwa [hn] at this

end ElemChoos
