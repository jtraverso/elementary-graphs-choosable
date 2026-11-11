/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.Prop37
public import GalvinMultigraph.Main

/-!
# Augmentations of line graphs of bipartite multigraphs, and the main theorem

`IsAugLineGraphRep G a b hubA hubB` presents `G` as an augmentation (Maffray–Reed) of the line
graph of a bipartite multigraph `H′`: the vertex `v` of `G` is an edge of `H′` with ends
`a v ∈ A` and `b v ∈ B`. Every augment is the star of a *hub* of `H′` (an end with at most two
distinct neighbours, the two sides `X` and `Y`), inside which some `X`–`Y` pairs may be
non-adjacent; no edge of `H′` joins two hubs. This is the representation of Lemmas 3.3 and 3.8
of Narayanan–Vasudevan–Somasundaram (after multiplying the two edges of every augmented flat
edge).

`choosable_of_rep` is Theorem 3.4 for this class: clique number at most `k` implies
`k`-choosability. The proof is the paper's minimal-counterexample argument, as a strong
induction on the number of vertices and then on the number of missing pairs; when no pair is
missing the graph is a line graph of a bipartite multigraph and Galvin's theorem applies
(`GalvinMultigraph.galvin_of_degree_bound`, from the registered entry galvin-dinitz).
-/

@[expose] public section

open Finset

namespace ElemChoos

open scoped Classical

variable {V A B C : Type*}

/-- `G` is an augmentation of the line graph of the bipartite multigraph with edges
`{a v, b v}` (`v : V`), the augments sitting at the hubs `hubA ∪ hubB`. -/
def IsAugLineGraphRep (G : SimpleGraph V) (a : V → A) (b : V → B) (hubA : Set A)
    (hubB : Set B) : Prop :=
  (∀ v, ¬ (a v ∈ hubA ∧ b v ∈ hubB)) ∧
  (∀ u v w, a u = a v → a u = a w → a u ∈ hubA → b u = b v ∨ b u = b w ∨ b v = b w) ∧
  (∀ u v w, b u = b v → b u = b w → b u ∈ hubB → a u = a v ∨ a u = a w ∨ a v = a w) ∧
  (∀ u v, G.Adj u v → a u = a v ∨ b u = b v) ∧
  (∀ u v, u ≠ v → (a u = a v ∨ b u = b v) → ¬ G.Adj u v →
    (a u = a v ∧ a u ∈ hubA ∧ b u ≠ b v) ∨ (b u = b v ∧ b u ∈ hubB ∧ a u ≠ a v))

theorem IsAugLineGraphRep.swap {G : SimpleGraph V} {a : V → A} {b : V → B} {hubA : Set A}
    {hubB : Set B} (h : IsAugLineGraphRep G a b hubA hubB) :
    IsAugLineGraphRep G b a hubB hubA := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun v hv => h1 v ⟨hv.2, hv.1⟩, h3, h2, fun u v huv => (h4 u v huv).symm, ?_⟩
  intro u v huv hsh hna
  exact (h5 u v huv hsh.symm hna).symm

/-- `G` with the pair `xy` added as an edge. -/
def addEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj u v := G.Adj u v ∨ (u ≠ v ∧ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)))
  symm := ⟨fun u v h => by
    rcases h with h | ⟨hne, h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm, by tauto⟩⟩
  loopless := ⟨fun u h => by
    rcases h with h | ⟨hne, -⟩
    · exact G.loopless.irrefl u h
    · exact hne rfl⟩

theorem rep_addEdge {G : SimpleGraph V} {a : V → A} {b : V → B} {hubA : Set A} {hubB : Set B}
    (h : IsAugLineGraphRep G a b hubA hubB) {x y : V} (hsh : a x = a y ∨ b x = b y) :
    IsAugLineGraphRep (addEdge G x y) a b hubA hubB := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro u v huv
    rcases huv with huv | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact h4 u v huv
    · exact hsh
    · exact hsh.imp Eq.symm Eq.symm
  · intro u v huv hs hna
    exact h5 u v huv hs (fun h => hna (Or.inl h))

/-- The number of missing line-graph pairs inside `W`. -/
noncomputable def missing (a : V → A) (b : V → B) (G : SimpleGraph V) (W : Finset V) : ℕ :=
  #((W ×ˢ W).filter fun p => p.1 ≠ p.2 ∧ (a p.1 = a p.2 ∨ b p.1 = b p.2) ∧ ¬ G.Adj p.1 p.2)

theorem missing_addEdge_lt (a : V → A) (b : V → B) (G : SimpleGraph V) (W : Finset V) {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) (hsh : a x = a y ∨ b x = b y) (hna : ¬ G.Adj x y) :
    missing a b (addEdge G x y) W < missing a b G W := by
  unfold missing
  have hsub : (W ×ˢ W).filter (fun p => p.1 ≠ p.2 ∧ (a p.1 = a p.2 ∨ b p.1 = b p.2) ∧
      ¬ (addEdge G x y).Adj p.1 p.2) ⊆ (W ×ˢ W).filter
      (fun p => p.1 ≠ p.2 ∧ (a p.1 = a p.2 ∨ b p.1 = b p.2) ∧ ¬ G.Adj p.1 p.2) := by
    intro p hp
    simp only [mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1, fun h => hp.2.2.2 (Or.inl h)⟩
  refine card_lt_card ((ssubset_iff_of_subset hsub).2 ⟨(x, y), ?_, ?_⟩)
  · exact mem_filter.2 ⟨mem_product.2 ⟨hx, hy⟩, hxy, hsh, hna⟩
  · intro h
    exact (mem_filter.1 h).2.2.2 (Or.inr ⟨hxy, Or.inl ⟨rfl, rfl⟩⟩)

/-- The criticality statement provided by the induction on missing pairs. -/
def Critical (a : V → A) (b : V → B) (G : SimpleGraph V) (W : Finset V) (k : ℕ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → (a x = a y ∨ b x = b y) → ¬ G.Adj x y →
    ∃ K ⊆ W, x ∈ K ∧ y ∈ K ∧ k < #K ∧
      ∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ (u = x ∧ v = y) → ¬ (u = y ∧ v = x) → G.Adj u v

/-- A missing pair at a hub of `A` contradicts minimality: the augment at that hub is complete
by Proposition 3.7. -/
theorem false_of_hubA [Nonempty C] {G : SimpleGraph V} {a : V → A} {b : V → B} {hubA : Set A}
    {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) {W : Finset V} {k : ℕ}
    {L : V → Finset C} (hL : ∀ v ∈ W, k ≤ #(L v))
    (hω : ∀ K ⊆ W, G.IsClique (K : Set V) → #K ≤ k)
    (IH : ∀ W' ⊂ W, ∀ L' : V → Finset C, (∀ v ∈ W', k ≤ #(L' v)) → ∃ f, Colours G W' L' f)
    (hcrit : Critical a b G W k) (hbad : ¬ ∃ f, Colours G W L f)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hab : a x = a y) (hhub : a x ∈ hubA)
    (hbne : b x ≠ b y) (hna : ¬ G.Adj x y) : False := by
  obtain ⟨h1, h2, -, h4, h5⟩ := hG
  set c := a x
  set X := W.filter fun v => a v = c ∧ b v = b x
  set Y := W.filter fun v => a v = c ∧ b v = b y
  set NX := W.filter fun v => a v ≠ c ∧ b v = b x
  set NY := W.filter fun v => a v ≠ c ∧ b v = b y
  -- a vertex at the hub lies in `X` or `Y`
  have hcls : ∀ v, a v = c → b v = b x ∨ b v = b y := by
    intro v hv
    rcases h2 x y v hab hv.symm hhub with h | h | h
    · exact absurd h hbne
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  -- parallel vertices are adjacent
  have hpar : ∀ u v, u ≠ v → a u = a v → b u = b v → G.Adj u v := by
    intro u v huv ha hb
    by_contra hn
    rcases h5 u v huv (Or.inl ha) hn with h | h
    · exact h.2.2 hb
    · exact h.2.2 ha
  -- two vertices with a common non-hub `B`-end are adjacent
  have hBadj : ∀ u v, u ≠ v → b u = b v → b u ∉ hubB → G.Adj u v := by
    intro u v huv hb hnh
    by_contra hn
    rcases h5 u v huv (Or.inr hb) hn with h | h
    · exact h.2.2 hb
    · exact hnh h.2.1
  have hbx : b x ∉ hubB := fun h => h1 x ⟨hhub, h⟩
  have hby : b y ∉ hubB := fun h => h1 y ⟨hab ▸ hhub, h⟩
  have hA : Aug G W k X Y NX NY := by
    refine
      { hXW := filter_subset _ _
        hYW := filter_subset _ _
        hXY := ?_
        hX := ?_
        hY := ?_
        hNXW := filter_subset _ _
        hNYW := filter_subset _ _
        hNXJ := ?_
        hNYJ := ?_
        hNX := ?_
        hNY := ?_
        hNXc := ?_
        hNYc := ?_
        hN := ?_
        hω := hω
        crit := ?_ }
    · refine disjoint_left.2 fun v hv hv' => ?_
      simp only [X, Y, mem_filter] at hv hv'
      exact hbne (hv.2.2.symm.trans hv'.2.2)
    · intro u hu v hv huv
      simp only [X, coe_filter, Set.mem_setOf_eq] at hu hv
      exact hpar u v huv (hu.2.1.trans hv.2.1.symm) (hu.2.2.trans hv.2.2.symm)
    · intro u hu v hv huv
      simp only [Y, coe_filter, Set.mem_setOf_eq] at hu hv
      exact hpar u v huv (hu.2.1.trans hv.2.1.symm) (hu.2.2.trans hv.2.2.symm)
    · intro w hw
      simp only [X, Y, NX, mem_filter] at hw ⊢
      exact ⟨fun h => hw.2.1 h.2.1, fun h => hw.2.1 h.2.1⟩
    · intro w hw
      simp only [X, Y, NY, mem_filter] at hw ⊢
      exact ⟨fun h => hw.2.1 h.2.1, fun h => hw.2.1 h.2.1⟩
    · intro u hu w hw hwX hwY
      simp only [X, Y, NX, mem_filter] at hu hwX hwY ⊢
      have hwc : a w ≠ c := by
        intro hwc
        rcases hcls w hwc with h | h
        · exact hwX ⟨hw, hwc, h⟩
        · exact hwY ⟨hw, hwc, h⟩
      constructor
      · intro hadj
        refine ⟨hw, hwc, ?_⟩
        rcases h4 u w hadj with h | h
        · exact absurd (h.symm.trans hu.2.1) hwc
        · exact h.symm.trans hu.2.2
      · rintro ⟨-, -, hbw⟩
        have huw : u ≠ w := fun e => hwc (e ▸ hu.2.1)
        exact hBadj u w huw (hu.2.2.trans hbw.symm) (by rw [hu.2.2]; exact hbx)
    · intro u hu w hw hwX hwY
      simp only [X, Y, NY, mem_filter] at hu hwX hwY ⊢
      have hwc : a w ≠ c := by
        intro hwc
        rcases hcls w hwc with h | h
        · exact hwX ⟨hw, hwc, h⟩
        · exact hwY ⟨hw, hwc, h⟩
      constructor
      · intro hadj
        refine ⟨hw, hwc, ?_⟩
        rcases h4 u w hadj with h | h
        · exact absurd (h.symm.trans hu.2.1) hwc
        · exact h.symm.trans hu.2.2
      · rintro ⟨-, -, hbw⟩
        have huw : u ≠ w := fun e => hwc (e ▸ hu.2.1)
        exact hBadj u w huw (hu.2.2.trans hbw.symm) (by rw [hu.2.2]; exact hby)
    · intro u hu v hv huv
      simp only [NX, coe_filter, Set.mem_setOf_eq] at hu hv
      exact hBadj u v huv (hu.2.2.trans hv.2.2.symm) (by rw [hu.2.2]; exact hbx)
    · intro u hu v hv huv
      simp only [NY, coe_filter, Set.mem_setOf_eq] at hu hv
      exact hBadj u v huv (hu.2.2.trans hv.2.2.symm) (by rw [hu.2.2]; exact hby)
    · refine disjoint_left.2 fun v hv hv' => ?_
      simp only [NX, NY, mem_filter] at hv hv'
      exact hbne (hv.2.2.symm.trans hv'.2.2)
    · intro u hu v hv huv
      simp only [X, Y, mem_filter] at hu hv
      have hne : u ≠ v := by
        rintro rfl
        exact hbne (hu.2.2.symm.trans hv.2.2)
      exact hcrit u hu.1 v hv.1 hne (Or.inl (hu.2.1.trans hv.2.1.symm)) huv
  have hxX : x ∈ X := mem_filter.2 ⟨hx, rfl, rfl⟩
  have hyY : y ∈ Y := mem_filter.2 ⟨hy, hab.symm, rfl⟩
  exact hna (hA.complete hL IH hbad x hxX y hyY)

/-- The line-graph case: with no missing pair, Galvin's theorem colours `W`. -/
theorem colours_of_no_missing {G : SimpleGraph V} {a : V → A} {b : V → B} [Nonempty C]
    [Finite V] {W : Finset V} {k : ℕ} {L : V → Finset C} (hL : ∀ v ∈ W, k ≤ #(L v))
    (hω : ∀ K ⊆ W, G.IsClique (K : Set V) → #K ≤ k)
    (h4 : ∀ u v, G.Adj u v → a u = a v ∨ b u = b v)
    (hno : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → (a x = a y ∨ b x = b y) → G.Adj x y) :
    ∃ f, Colours G W L f := by
  let a' : W → Set.range a := fun e => ⟨a e, Set.mem_range_self _⟩
  let b' : W → Set.range b := fun e => ⟨b e, Set.mem_range_self _⟩
  have hdegA : ∀ x, Nat.card {e // a' e = x} ≤ k := by
    intro x
    have hcl := hω (W.filter fun v => a v = x.1) (filter_subset _ _) (by
      intro u hu v hv huv
      simp only [coe_filter, Set.mem_setOf_eq] at hu hv
      exact hno u hu.1 v hv.1 huv (Or.inl (hu.2.trans hv.2.symm)))
    refine le_trans ?_ hcl
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun e => ⟨e.1.1, mem_filter.2 ⟨e.1.2, congrArg Subtype.val e.2⟩⟩) ?_
    intro e e' h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have hdegB : ∀ y, Nat.card {e // b' e = y} ≤ k := by
    intro y
    have hcl := hω (W.filter fun v => b v = y.1) (filter_subset _ _) (by
      intro u hu v hv huv
      simp only [coe_filter, Set.mem_setOf_eq] at hu hv
      exact hno u hu.1 v hv.1 huv (Or.inr (hu.2.trans hv.2.symm)))
    refine le_trans ?_ hcl
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun e => ⟨e.1.1, mem_filter.2 ⟨e.1.2, congrArg Subtype.val e.2⟩⟩) ?_
    intro e e' h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  obtain ⟨c, hcL, hcP⟩ := GalvinMultigraph.galvin_of_degree_bound a' b' k hdegA hdegB
    (fun e => L e) (fun e => hL e e.2)
  refine ⟨fun v => if hv : v ∈ W then c ⟨v, hv⟩ else Classical.arbitrary C, ?_, ?_⟩
  · intro v hv
    simp only [dif_pos hv]
    exact hcL _
  · intro u hu v hv huv
    simp only [dif_pos hu, dif_pos hv]
    refine hcP _ _ (fun h => huv.ne (congrArg Subtype.val h)) ?_
    rcases h4 u v huv with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

/-- **Theorem 3.4 on a vertex subset** (minimal counterexample as a double strong induction). -/
theorem core [Nonempty C] [Finite V] {a : V → A} {b : V → B} {hubA : Set A} {hubB : Set B}
    (k : ℕ) : ∀ (n : ℕ) (W : Finset V), #W = n → ∀ (m : ℕ) (G : SimpleGraph V),
      IsAugLineGraphRep G a b hubA hubB → missing a b G W = m →
      (∀ K ⊆ W, G.IsClique (K : Set V) → #K ≤ k) →
      ∀ L : V → Finset C, (∀ v ∈ W, k ≤ #(L v)) → ∃ f, Colours G W L f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro W hWn m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro G hG hm hω L hL
  by_contra hbad
  have IH : ∀ W' ⊂ W, ∀ L' : V → Finset C, (∀ v ∈ W', k ≤ #(L' v)) →
      ∃ f, Colours G W' L' f := by
    intro W' hW' L' hL'
    exact ihn #W' (hWn ▸ card_lt_card hW') W' rfl _ G hG rfl
      (fun K hK => hω K (hK.trans hW'.subset)) L' hL'
  have hcrit : Critical a b G W k := by
    intro x hx y hy hxy hsh hna
    by_contra hK
    apply hbad
    have hω' : ∀ K ⊆ W, (addEdge G x y).IsClique (K : Set V) → #K ≤ k := by
      intro K hKW hKc
      by_contra hlt
      push_neg at hlt
      by_cases hxyK : x ∈ K ∧ y ∈ K
      · refine hK ⟨K, hKW, hxyK.1, hxyK.2, hlt, fun u hu v hv huv h1 h2 => ?_⟩
        rcases hKc hu hv huv with h | ⟨-, h⟩
        · exact h
        · tauto
      · refine (not_le.2 hlt) (hω K hKW fun u hu v hv huv => ?_)
        rcases hKc hu hv huv with h | ⟨-, h⟩
        · exact h
        · exfalso
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hxyK ⟨hu, hv⟩
          · exact hxyK ⟨hv, hu⟩
    obtain ⟨f, hfL, hfP⟩ := ihm _ (hm ▸ missing_addEdge_lt a b G W hx hy hxy hsh hna)
      (addEdge G x y) (rep_addEdge hG hsh) rfl hω' L hL
    exact ⟨f, hfL, fun u hu v hv huv => hfP u hu v hv (Or.inl huv)⟩
  by_cases hmiss : ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧ (a x = a y ∨ b x = b y) ∧ ¬ G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy, hsh, hna⟩ := hmiss
    rcases hG.2.2.2.2 x y hxy hsh hna with ⟨hab, hhub, hbne⟩ | ⟨hba, hhub, hane⟩
    · exact false_of_hubA hG hL hω IH hcrit hbad hx hy hab hhub hbne hna
    · refine false_of_hubA hG.swap hL hω IH ?_ hbad hx hy hba hhub hane hna
      intro u hu v hv huv hs hn
      exact hcrit u hu v hv huv hs.symm hn
  · push_neg at hmiss
    exact hbad (colours_of_no_missing hL hω hG.2.2.2.1 hmiss)

theorem card_le_of_cliqueFree {G : SimpleGraph V} {k : ℕ} (hω : G.CliqueFree (k + 1))
    (K : Finset V) (hK : G.IsClique (K : Set V)) : #K ≤ k := by
  by_contra h
  push_neg at h
  obtain ⟨t, htK, ht⟩ := exists_subset_card_eq (s := K) (n := k + 1) h
  exact hω t ⟨hK.subset (by simpa using htK), ht⟩

/-- **Theorem 3.4 for augmentations of line graphs of bipartite multigraphs.** If the clique
number is at most `k`, every assignment of lists of at least `k` colours admits a proper
list colouring. -/
theorem choosable_of_rep [Finite V] {G : SimpleGraph V} {a : V → A} {b : V → B} {hubA : Set A}
    {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) {k : ℕ} (hω : G.CliqueFree (k + 1))
    (L : V → Finset C) (hL : ∀ v, k ≤ (L v).card) : ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  have := Fintype.ofFinite V
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · exact ⟨SimpleGraph.Coloring.mk (fun v => isEmptyElim v) (fun {v} => isEmptyElim v),
      fun v => isEmptyElim v⟩
  have hk : 1 ≤ k := by
    by_contra h
    push_neg at h
    have : k = 0 := by omega
    subst this
    exact hω {v₀} ⟨by simp, by simp⟩
  have : Nonempty C := by
    obtain ⟨c, -⟩ := card_pos.1 (lt_of_lt_of_le hk (hL v₀))
    exact ⟨c⟩
  obtain ⟨f, hfL, hfP⟩ := core (a := a) (b := b) (hubA := hubA) (hubB := hubB) k _ univ rfl _ G
    hG rfl (fun K _ hK => card_le_of_cliqueFree hω K hK) L (fun v _ => hL v)
  exact ⟨SimpleGraph.Coloring.mk f (fun {u v} h => hfP u (mem_univ _) v (mem_univ _) h),
    fun v => hfL v (mem_univ _)⟩

end ElemChoos
