/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.Augment

/-!
# Every augment of a minimal counterexample is complete (Proposition 3.7)

`Aug.complete`: in a graph `G` on the vertex set `W` that has no `L`-colouring from lists of size
`k`, while every proper subset of `W` is colourable from any lists of size `k`, every augment
`(X, Y)` (with the criticality of `Aug.crit`) is complete.

The proof follows Narayanan–Vasudevan–Somasundaram: choose the side with the smaller value of
`m + |free|` (inequality (3)), a set `S` of free vertices of minimum surplus and `z ∈ S`; colour
`W` minus the matched vertices of `Y` with the list of `z` copied onto the matched vertices of `X`;
the Deficiency Lemma then yields a set that contradicts the injectivity of the colouring on the
`k`-clique `X ∪ V`.
-/

@[expose] public section

open Finset

namespace ElemChoos

open scoped Classical

variable {V C : Type*}

/-- The surplus `|L(S)| - |S|` of a set of vertices. -/
noncomputable def surplus (L : V → Finset C) (S : Finset V) : ℤ := #(S.biUnion L) - #S

namespace Aug

variable {G : SimpleGraph V} {W : Finset V} {k : ℕ} {X Y NX NY : Finset V}

/-- Residual lists on `X ∪ Y`. -/
noncomputable def resid (X NX NY : Finset V) (L : V → Finset C) (f : V → C) (v : V) : Finset C :=
  if v ∈ X then L v \ NX.image f else L v \ NY.image f

theorem card_resid_X (A : Aug G W k X Y NX NY) {L : V → Finset C} (hL : ∀ v ∈ W, k ≤ #(L v))
    (f : V → C) {x : V} (hx : x ∈ X) : #X ≤ #(resid X NX NY L f x) := by
  simp only [resid, if_pos hx]
  have h1 := le_card_sdiff (NX.image f) (L x)
  have h2 : #(NX.image f) ≤ #NX := card_image_le
  have h3 := A.card_NX_le
  have h4 := hL x (A.hXW hx)
  omega

theorem card_resid_Y (A : Aug G W k X Y NX NY) {L : V → Finset C} (hL : ∀ v ∈ W, k ≤ #(L v))
    (f : V → C) {y : V} (hy : y ∈ Y) : #Y ≤ #(resid X NX NY L f y) := by
  have hnx : y ∉ X := fun h => disjoint_left.1 A.hXY h hy
  simp only [resid, if_neg hnx]
  have h1 := le_card_sdiff (NY.image f) (L y)
  have h2 : #(NY.image f) ≤ #NY := card_image_le
  have h3 := A.swap.card_NX_le
  have h4 := hL y (A.hYW hy)
  omega

/-- If the residual lists colour `X ∪ Y`, then `W` is colourable. -/
theorem colours_of_resid (A : Aug G W k X Y NX NY) {L : V → Finset C} {f g : V → C}
    (hfL : ∀ v ∈ W, v ∉ X → v ∉ Y → f v ∈ L v)
    (hfP : ∀ u ∈ W, ∀ v ∈ W, u ∉ X → u ∉ Y → v ∉ X → v ∉ Y → G.Adj u v → f u ≠ f v)
    (hg : Colours G (X ∪ Y) (resid X NX NY L f) g) : ∃ h, Colours G W L h :=
  ⟨_, A.extend hfL hfP hg⟩

/-- The case where one side has no free vertex (Corollary 2.6(a)). -/
theorem false_of_free_empty [Nonempty C] (A : Aug G W k X Y NX NY) {L : V → Finset C}
    (hL : ∀ v ∈ W, k ≤ #(L v))
    (IH : ∀ W' ⊂ W, ∀ L' : V → Finset C, (∀ v ∈ W', k ≤ #(L' v)) → ∃ f, Colours G W' L' f)
    (hbad : ¬ ∃ f, Colours G W L f) {x y : V} (hx : x ∈ X) (_hy : y ∈ Y)
    (hfree : free G X Y = ∅ ∨ free G Y X = ∅) : False := by
  have hss : W.filter (fun v => v ∉ X ∧ v ∉ Y) ⊂ W := by
    refine (filter_subset _ _).ssubset_of_ne ?_
    intro h
    have hx' : x ∈ W.filter (fun v => v ∉ X ∧ v ∉ Y) := by rw [h]; exact A.hXW hx
    exact (mem_filter.1 hx').2.1 hx
  obtain ⟨f, hfL, hfP⟩ := IH _ hss L (fun v hv => hL v (mem_filter.1 hv).1)
  by_cases hg : ∃ g, Colours G (X ∪ Y) (resid X NX NY L f) g
  · obtain ⟨g, hg⟩ := hg
    exact hbad (A.colours_of_resid (fun v hv h1 h2 => hfL v (mem_filter.2 ⟨hv, h1, h2⟩))
      (fun u hu v hv h1 h2 h3 h4 => hfP u (mem_filter.2 ⟨hu, h1, h2⟩) v
        (mem_filter.2 ⟨hv, h3, h4⟩)) hg)
  · obtain ⟨T, -, hTX, hTY, -⟩ := deficiency G _ X Y (resid X NX NY L f) A.hXY A.hX A.hY
      A.uniqMiss A.uniqMiss' rfl (fun v hv => A.card_resid_X hL f hv)
      (fun v hv => A.card_resid_Y hL f hv) hg
    rcases hfree with h | h
    · rw [h, inter_empty] at hTX
      exact not_nonempty_empty hTX
    · rw [h, inter_empty] at hTY
      exact not_nonempty_empty hTY

end Aug

end ElemChoos
