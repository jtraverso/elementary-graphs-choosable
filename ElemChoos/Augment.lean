/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.Deficiency

/-!
# Augments of a minimal counterexample: saturation

An augment `(X, Y)` inside the current vertex set `W` of a graph `G` (Lemma 3.3 of
Narayanan–Vasudevan–Somasundaram): `X`, `Y` are disjoint cliques, every vertex of `X` has exactly
the neighbours `N_X` outside `X ∪ Y`, every vertex of `Y` exactly `N_Y`, and `N_X`, `N_Y` are
disjoint cliques. The field `crit` records the edge-maximality of the counterexample: adding any
missing `X`–`Y` pair creates a clique of size `k + 1` through it.

From `crit` we prove the Saturation Lemma 3.6 (a), (b) **without Kőnig's theorem**: the missing
pairs form a matching (a lattice argument on two critical cliques) and `k = |X| + |V|`, where `V`
is the set of free vertices of `Y`.
-/

@[expose] public section

open Finset

namespace ElemChoos

open scoped Classical

variable {V C : Type*}

theorem isClique_of {G : SimpleGraph V} {K : Finset V}
    (h : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v) : G.IsClique (K : Set V) :=
  fun u hu v hv huv => h u hu v hv huv

/-- An augment `(X, Y)` with exterior neighbourhoods `NX`, `NY` inside the vertex set `W`,
in a graph whose cliques inside `W` have at most `k` vertices and in which every missing
`X`–`Y` pair is critical. -/
structure Aug (G : SimpleGraph V) (W : Finset V) (k : ℕ) (X Y NX NY : Finset V) : Prop where
  hXW : X ⊆ W
  hYW : Y ⊆ W
  hXY : Disjoint X Y
  hX : G.IsClique (X : Set V)
  hY : G.IsClique (Y : Set V)
  hNXW : NX ⊆ W
  hNYW : NY ⊆ W
  hNXJ : ∀ w ∈ NX, w ∉ X ∧ w ∉ Y
  hNYJ : ∀ w ∈ NY, w ∉ X ∧ w ∉ Y
  hNX : ∀ x ∈ X, ∀ w ∈ W, w ∉ X → w ∉ Y → (G.Adj x w ↔ w ∈ NX)
  hNY : ∀ y ∈ Y, ∀ w ∈ W, w ∉ X → w ∉ Y → (G.Adj y w ↔ w ∈ NY)
  hNXc : G.IsClique (NX : Set V)
  hNYc : G.IsClique (NY : Set V)
  hN : Disjoint NX NY
  hω : ∀ K ⊆ W, G.IsClique (K : Set V) → #K ≤ k
  crit : ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y → ∃ K ⊆ W, x ∈ K ∧ y ∈ K ∧ k < #K ∧
    ∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ (u = x ∧ v = y) → ¬ (u = y ∧ v = x) → G.Adj u v

namespace Aug

variable {G : SimpleGraph V} {W : Finset V} {k : ℕ} {X Y NX NY : Finset V}

theorem swap (A : Aug G W k X Y NX NY) : Aug G W k Y X NY NX where
  hXW := A.hYW
  hYW := A.hXW
  hXY := A.hXY.symm
  hX := A.hY
  hY := A.hX
  hNXW := A.hNYW
  hNYW := A.hNXW
  hNXJ := fun w hw => (A.hNYJ w hw).symm
  hNYJ := fun w hw => (A.hNXJ w hw).symm
  hNX := fun y hy w hw h1 h2 => A.hNY y hy w hw h2 h1
  hNY := fun x hx w hw h1 h2 => A.hNX x hx w hw h2 h1
  hNXc := A.hNYc
  hNYc := A.hNXc
  hN := A.hN.symm
  hω := A.hω
  crit := by
    intro y hy x hx hxy
    obtain ⟨K, hKW, hxK, hyK, hk, hK⟩ := A.crit x hx y hy (fun h => hxy h.symm)
    exact ⟨K, hKW, hyK, hxK, hk, fun u hu v hv huv h1 h2 => hK u hu v hv huv h2 h1⟩

theorem ne_of_mem (A : Aug G W k X Y NX NY) {x y : V} (hx : x ∈ X) (hy : y ∈ Y) : x ≠ y := by
  rintro rfl
  exact disjoint_left.1 A.hXY hx hy

/-- A critical clique lies inside `X ∪ Y` (Lemma 3.3(c)). -/
theorem crit_subset (A : Aug G W k X Y NX NY) {x y : V} (hx : x ∈ X) (hy : y ∈ Y) {K : Finset V}
    (hKW : K ⊆ W) (hxK : x ∈ K) (hyK : y ∈ K)
    (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ (u = x ∧ v = y) → ¬ (u = y ∧ v = x) → G.Adj u v) :
    ∀ w ∈ K, w ∈ X ∨ w ∈ Y := by
  intro w hw
  by_contra h
  push_neg at h
  have hxy := A.ne_of_mem hx hy
  have hwx : x ≠ w := fun e => h.1 (e ▸ hx)
  have hwy : y ≠ w := fun e => h.2 (e ▸ hy)
  have h1 : G.Adj x w := hK x hxK w hw hwx (fun e => hwy e.2.symm) (fun e => hxy e.1)
  have h2 : G.Adj y w := hK y hyK w hw hwy (fun e => hxy e.1.symm) (fun e => hwx e.2.symm)
  have h1' := (A.hNX x hx w (hKW hw) h.1 h.2).1 h1
  have h2' := (A.hNY y hy w (hKW hw) h.1 h.2).1 h2
  exact disjoint_left.1 A.hN h1' h2'

/-- **Saturation, Lemma 3.6(a)** (one side): each vertex of `X` has at most one non-neighbour
in `Y`. -/
theorem uniqMiss (A : Aug G W k X Y NX NY) : UniqMiss G X Y := by
  intro x hx y hy y' hy' hxy hxy'
  by_contra hne
  obtain ⟨K1, hK1W, hxK1, hyK1, hk1, hK1⟩ := A.crit x hx y hy hxy
  obtain ⟨K2, hK2W, hxK2, hyK2, hk2, hK2⟩ := A.crit x hx y' hy' hxy'
  have hxy0 := A.ne_of_mem hx hy
  have hxy0' := A.ne_of_mem hx hy'
  have hS1 := A.crit_subset hx hy hK1W hxK1 hyK1 hK1
  have hS2 := A.crit_subset hx hy' hK2W hxK2 hyK2 hK2
  have hyK2 : y ∉ K2 := by
    intro h
    exact hxy (hK2 x hxK2 y h hxy0 (fun e => hne e.2) (fun e => hxy0' e.1))
  have hyK1 : y' ∉ K1 := by
    intro h
    exact hxy' (hK1 x hxK1 y' h hxy0' (fun e => hne e.2.symm) (fun e => hxy0 e.1))
  have hXnY : ∀ v ∈ X, v ∉ Y := fun v hv hv' => disjoint_left.1 A.hXY hv hv'
  set Km := (K1 ∪ K2).filter fun v => v ∈ X ∨ (v ∈ K1 ∧ v ∈ K2) with hKm
  set Kj := (K1 ∪ K2).filter fun v => v ∈ Y ∨ (v ∈ K1 ∧ v ∈ K2) with hKj
  have hunion : Km ∪ Kj = K1 ∪ K2 := by
    ext v
    simp only [hKm, hKj, mem_union, mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases h with h | h
      · rcases hS1 v h with h' | h'
        · exact Or.inl ⟨Or.inl h, Or.inl h'⟩
        · exact Or.inr ⟨Or.inl h, Or.inl h'⟩
      · rcases hS2 v h with h' | h'
        · exact Or.inl ⟨Or.inr h, Or.inl h'⟩
        · exact Or.inr ⟨Or.inr h, Or.inl h'⟩
  have hinter : Km ∩ Kj = K1 ∩ K2 := by
    ext v
    simp only [hKm, hKj, mem_inter, mem_union, mem_filter]
    constructor
    · rintro ⟨⟨-, h1⟩, -, h2⟩
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact absurd h2 (hXnY v h1)
        · exact h2
      · exact h1
    · rintro ⟨h1, h2⟩
      exact ⟨⟨Or.inl h1, Or.inr ⟨h1, h2⟩⟩, Or.inl h1, Or.inr ⟨h1, h2⟩⟩
  have hsum : #Km + #Kj = #K1 + #K2 := by
    rw [← card_union_add_card_inter, hunion, hinter, card_union_add_card_inter]
  have hKmW : Km ⊆ W := (filter_subset _ _).trans (union_subset hK1W hK2W)
  have hKjW : Kj.erase x ⊆ W := (erase_subset _ _).trans
    ((filter_subset _ _).trans (union_subset hK1W hK2W))
  -- `Km` is a clique of `G`
  have hKmc : G.IsClique (Km : Set V) := by
    refine isClique_of fun u hu v hv huv => ?_
    simp only [hKm, mem_filter, mem_union] at hu hv
    -- a cross pair `a ∈ X`, `b ∈ Y ∩ K1 ∩ K2`
    have cross : ∀ a b, (a ∈ K1 ∨ a ∈ K2) → a ∈ X → b ∈ Y → b ∈ K1 → b ∈ K2 → a ≠ b →
        G.Adj a b := by
      intro a b ha haX hbY hb1 hb2 hab
      rcases ha with ha | ha
      · exact hK1 a ha b hb1 hab (fun e => hyK2 (e.2 ▸ hb2)) (fun e => hXnY a haX (e.1 ▸ hy))
      · exact hK2 a ha b hb2 hab (fun e => hyK1 (e.2 ▸ hb1)) (fun e => hXnY a haX (e.1 ▸ hy'))
    rcases hu with ⟨hu1, hu2 | ⟨hu3, hu4⟩⟩ <;> rcases hv with ⟨hv1, hv2 | ⟨hv3, hv4⟩⟩
    · exact A.hX hu2 hv2 huv
    · rcases hS1 v hv3 with h | h
      · exact A.hX hu2 h huv
      · exact cross u v hu1 hu2 h hv3 hv4 huv
    · rcases hS1 u hu3 with h | h
      · exact A.hX h hv2 huv
      · exact (cross v u hv1 hv2 h hu3 hu4 huv.symm).symm
    · exact hK1 u hu3 v hv3 huv (fun e => hyK2 (e.2 ▸ hv4)) (fun e => hyK2 (e.1 ▸ hu4))
  -- `Kj` minus `x` is a clique of `G`
  have hKjc : G.IsClique ((Kj.erase x : Finset V) : Set V) := by
    refine isClique_of fun u hu v hv huv => ?_
    simp only [hKj, mem_erase, mem_filter, mem_union] at hu hv
    have cross : ∀ a b, a ≠ x → a ∈ X → a ∈ K1 → a ∈ K2 → (b ∈ K1 ∨ b ∈ K2) → b ∈ Y →
        a ≠ b → G.Adj a b := by
      intro a b hax haX ha1 ha2 hb hbY hab
      rcases hb with hb | hb
      · exact hK1 a ha1 b hb hab (fun e => hax e.1) (fun e => hXnY a haX (e.1 ▸ hy))
      · exact hK2 a ha2 b hb hab (fun e => hax e.1) (fun e => hXnY a haX (e.1 ▸ hy'))
    obtain ⟨hux, hu1, hu2⟩ := hu
    obtain ⟨hvx, hv1, hv2⟩ := hv
    rcases hu2 with hu2 | ⟨hu3, hu4⟩ <;> rcases hv2 with hv2 | ⟨hv3, hv4⟩
    · exact A.hY hu2 hv2 huv
    · rcases hS1 v hv3 with h | h
      · exact (cross v u hvx h hv3 hv4 hu1 hu2 huv.symm).symm
      · exact A.hY hu2 h huv
    · rcases hS1 u hu3 with h | h
      · exact cross u v hux h hu3 hu4 hv1 hv2 huv
      · exact A.hY h hv2 huv
    · exact hK1 u hu3 v hv3 huv (fun e => hux e.1) (fun e => hyK2 (e.1 ▸ hu4))
  have h1 := A.hω Km hKmW hKmc
  have h2 := A.hω _ hKjW hKjc
  have h3 := pred_card_le_card_erase (s := Kj) (a := x)
  omega

theorem uniqMiss' (A : Aug G W k X Y NX NY) : UniqMiss G Y X := A.swap.uniqMiss

/-- The free vertices of `Y` together with `X` form a clique of `G` (the clique `Q` of (B2)). -/
theorem isClique_X_free (A : Aug G W k X Y NX NY) :
    G.IsClique ((X ∪ free G Y X : Finset V) : Set V) := by
  refine isClique_of ?_
  intro u hu v hv huv
  rw [mem_union] at hu hv
  have hfree : ∀ w ∈ free G Y X, ∀ x ∈ X, G.Adj w x := by
    intro w hw x hx
    rw [free, mem_filter] at hw
    by_contra h
    exact hw.2 ⟨x, hx, h⟩
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact A.hX hu hv huv
  · exact (hfree v hv u hu).symm
  · exact hfree u hu v hv
  · exact A.hY (free_subset G Y X hu) (free_subset G Y X hv) huv

/-- The free vertices of `Y` together with `X` form a clique of `G` inside `W`. -/
theorem card_add_free_le (A : Aug G W k X Y NX NY) : #X + #(free G Y X) ≤ k := by
  have hd : Disjoint X (free G Y X) := disjoint_of_subset_right (free_subset G Y X) A.hXY
  rw [← card_union_of_disjoint hd]
  exact A.hω _ (union_subset A.hXW ((free_subset G Y X).trans A.hYW)) A.isClique_X_free

/-- **Saturation, Lemma 3.6(b)**: if some `X`–`Y` pair is missing, then `k = |X| + |V|`. -/
theorem k_eq (A : Aug G W k X Y NX NY) {x y : V} (hx : x ∈ X) (hy : y ∈ Y)
    (hxy : ¬ G.Adj x y) : #X + #(free G Y X) = k := by
  refine le_antisymm A.card_add_free_le ?_
  obtain ⟨K, hKW, hxK, hyK, hk, hK⟩ := A.crit x hx y hy hxy
  have hS := A.crit_subset hx hy hKW hxK hyK hK
  have hmX := A.uniqMiss
  have hXnY : ∀ v ∈ X, v ∉ Y := fun v hv hv' => disjoint_left.1 A.hXY hv hv'
  let keep : V → Prop := fun v => v ∈ X ∨ v ∈ free G Y X ∨ v = y
  let φ : V → V := fun v =>
    if keep v then v else if h' : ∃ x' ∈ X, ¬ G.Adj v x' then h'.choose else v
  have hφk : ∀ v, keep v → φ v = v := fun v h => if_pos h
  have hφn : ∀ v, ¬ keep v →
      φ v = if h' : ∃ x' ∈ X, ¬ G.Adj v x' then h'.choose else v := fun v h => if_neg h
  have hpart : ∀ v ∈ K, ¬ keep v → φ v ∈ X ∧ ¬ G.Adj v (φ v) ∧ φ v ∉ K := by
    intro v hv hkeep
    have hvY : v ∈ Y := (hS v hv).resolve_left (fun h => hkeep (Or.inl h))
    have h' : ∃ x' ∈ X, ¬ G.Adj v x' := by
      by_contra h
      exact hkeep (Or.inr (Or.inl (mem_filter.2 ⟨hvY, h⟩)))
    rw [hφn v hkeep, dif_pos h']
    obtain ⟨h1, h2⟩ := h'.choose_spec
    refine ⟨h1, h2, fun hK' => h2 ?_⟩
    have hvy : v ≠ y := fun e => hkeep (Or.inr (Or.inr e))
    exact hK v hv _ hK' (fun e => hXnY _ h1 (e ▸ hvY)) (fun e => hXnY x hx (e.1 ▸ hvY))
      (fun e => hvy e.1)
  have hcard : #K ≤ #(X ∪ free G Y X ∪ {y}) := by
    refine card_le_card_of_injOn φ ?_ ?_
    · intro v hv
      rw [mem_coe] at hv ⊢
      by_cases hk : keep v
      · rw [hφk v hk]
        rcases hk with h | h | h
        · exact mem_union_left _ (mem_union_left _ h)
        · exact mem_union_left _ (mem_union_right _ h)
        · exact mem_union_right _ (mem_singleton.2 h)
      · exact mem_union_left _ (mem_union_left _ (hpart v hv hk).1)
    · intro u hu v hv huv
      rw [mem_coe] at hu hv
      by_cases hku : keep u <;> by_cases hkv : keep v
      · rwa [hφk u hku, hφk v hkv] at huv
      · rw [hφk u hku] at huv
        exact absurd (huv ▸ hu) (hpart v hv hkv).2.2
      · rw [hφk v hkv] at huv
        exact absurd (huv.symm ▸ hv) (hpart u hu hku).2.2
      · obtain ⟨h1, h2, -⟩ := hpart u hu hku
        obtain ⟨-, h4, -⟩ := hpart v hv hkv
        have huY : u ∈ Y := (hS u hu).resolve_left (fun h => hku (Or.inl h))
        have hvY : v ∈ Y := (hS v hv).resolve_left (fun h => hkv (Or.inl h))
        rw [huv] at h1 h2
        exact hmX _ h1 u huY v hvY (fun h => h2 h.symm) (fun h => h4 h.symm)
  have h1 := card_union_le (X ∪ free G Y X) {y}
  have h2 := card_union_le X (free G Y X)
  rw [card_singleton] at h1
  omega

/-- `|N_X| ≤ |V|`: `X ∪ N_X` is a clique (Lemma 3.6(d)). -/
theorem card_NX_le (A : Aug G W k X Y NX NY) : #X + #NX ≤ k := by
  have hd : Disjoint X NX := disjoint_left.2 fun v hv hv' => (A.hNXJ v hv').1 hv
  rw [← card_union_of_disjoint hd]
  refine A.hω _ (union_subset A.hXW A.hNXW) (isClique_of ?_)
  intro u hu v hv huv
  rw [mem_union] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact A.hX hu hv huv
  · exact (A.hNX u hu v (A.hNXW hv) (A.hNXJ v hv).1 (A.hNXJ v hv).2).2 hv
  · exact ((A.hNX v hv u (A.hNXW hu) (A.hNXJ u hu).1 (A.hNXJ u hu).2).2 hu).symm
  · exact A.hNXc hu hv huv

/-- **Observation (B1).** A colouring `f` of `W \ (X ∪ Y)` and an `R`-colouring `g` of `X ∪ Y`
for the residual lists `R = L \ f(N_X)` on `X`, `L \ f(N_Y)` on `Y` combine to an `L`-colouring
of `W`. -/
theorem extend (A : Aug G W k X Y NX NY) {L : V → Finset C} {f g : V → C}
    (hfL : ∀ v ∈ W, v ∉ X → v ∉ Y → f v ∈ L v)
    (hfP : ∀ u ∈ W, ∀ v ∈ W, u ∉ X → u ∉ Y → v ∉ X → v ∉ Y → G.Adj u v → f u ≠ f v)
    (hg : Colours G (X ∪ Y)
      (fun v => if v ∈ X then L v \ NX.image f else L v \ NY.image f) g) :
    Colours G W L (fun v => if v ∈ X ∪ Y then g v else f v) := by
  obtain ⟨hgL, hgP⟩ := hg
  have hgX : ∀ x ∈ X, g x ∈ L x ∧ g x ∉ NX.image f := by
    intro x hx
    have := hgL x (mem_union_left _ hx)
    simp only [if_pos hx, mem_sdiff] at this
    exact this
  have hgY : ∀ y ∈ Y, g y ∈ L y ∧ g y ∉ NY.image f := by
    intro y hy
    have hnx : y ∉ X := fun h => disjoint_left.1 A.hXY h hy
    have := hgL y (mem_union_right _ hy)
    simp only [if_neg hnx, mem_sdiff] at this
    exact this
  -- a vertex of `X ∪ Y` against a vertex outside
  have cross : ∀ u ∈ W, ∀ v ∈ W, u ∈ X ∪ Y → v ∉ X ∪ Y → G.Adj u v → g u ≠ f v := by
    intro u hu v hv huJ hvJ huv
    rw [mem_union, not_or] at hvJ
    rcases mem_union.1 huJ with hX | hY
    · have hvN := (A.hNX u hX v hv hvJ.1 hvJ.2).1 huv
      intro e
      exact (hgX u hX).2 (mem_image.2 ⟨v, hvN, e.symm⟩)
    · have hvN := (A.hNY u hY v hv hvJ.1 hvJ.2).1 huv
      intro e
      exact (hgY u hY).2 (mem_image.2 ⟨v, hvN, e.symm⟩)
  refine ⟨?_, ?_⟩
  · intro v hv
    by_cases hJ : v ∈ X ∪ Y
    · simp only [if_pos hJ]
      rcases mem_union.1 hJ with h | h
      · exact (hgX v h).1
      · exact (hgY v h).1
    · simp only [if_neg hJ]
      rw [mem_union, not_or] at hJ
      exact hfL v hv hJ.1 hJ.2
  · intro u hu v hv huv
    by_cases huJ : u ∈ X ∪ Y <;> by_cases hvJ : v ∈ X ∪ Y
    · simp only [if_pos huJ, if_pos hvJ]
      exact hgP u huJ v hvJ huv
    · simp only [if_pos huJ, if_neg hvJ]
      exact cross u hu v hv huJ hvJ huv
    · simp only [if_neg huJ, if_pos hvJ]
      exact (cross v hv u hu hvJ huJ huv.symm).symm
    · simp only [if_neg huJ, if_neg hvJ]
      rw [mem_union, not_or] at huJ hvJ
      exact hfP u hu v hv huJ.1 huJ.2 hvJ.1 hvJ.2 huv

end Aug

end ElemChoos
