/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Representations on a vertex set, and the easy induction steps

`RepOn G W e h` says that the induced subgraph `G[W]` is an augmentation of the line graph of a
bipartite multigraph: vertex `v` is the edge with ends `e true v` (side `A`) and `e false v`
(side `B`); `h σ` is the set of hubs on side `σ`. This is `IsAugLineGraphRep` restricted to `W`,
written symmetrically in the two sides.

`NormOn G W e h` is the normalization carried through the Maffray–Reed induction (it repairs the
remark on p. 143 of their paper): every hub has two classes, every vertex of its star has a
parallel copy, and the graph of cross edges of the star is connected.

Steps proved here: swapping the sides, adding a twin, disjoint unions, and the line-graph case
(an elementary colouring without "bends").
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- `G[W]` is the augmentation of a bipartite-multigraph line graph given by the ends `e`. -/
def RepOn (W : Finset V) (e : Bool → V → ℕ) (h : Bool → Set ℕ) : Prop :=
  (∀ v ∈ W, ∀ σ, e σ v ∈ h σ → e (!σ) v ∉ h (!σ)) ∧
  (∀ σ, ∀ u ∈ W, ∀ v ∈ W, ∀ w ∈ W, e σ u = e σ v → e σ u = e σ w → e σ u ∈ h σ →
      e (!σ) u = e (!σ) v ∨ e (!σ) u = e (!σ) w ∨ e (!σ) v = e (!σ) w) ∧
  (∀ u ∈ W, ∀ v ∈ W, G.Adj u v → ∃ σ, e σ u = e σ v) ∧
  (∀ u ∈ W, ∀ v ∈ W, u ≠ v → (∃ σ, e σ u = e σ v) → ¬ G.Adj u v →
      ∃ σ, e σ u = e σ v ∧ e σ u ∈ h σ ∧ e (!σ) u ≠ e (!σ) v)

/-- The star of the end `s` on side `σ`, inside `W`. -/
def star (W : Finset V) (e : Bool → V → ℕ) (σ : Bool) (s : ℕ) : Finset V :=
  W.filter fun v => e σ v = s

/-- The normalization of the hubs. -/
def NormOn (W : Finset V) (e : Bool → V → ℕ) (h : Bool → Set ℕ) : Prop :=
  ∀ σ, ∀ s ∈ h σ,
    (∀ v ∈ W, e σ v = s → ∃ w ∈ W, w ≠ v ∧ e σ w = s ∧ e (!σ) w = e (!σ) v) ∧
    (∃ u ∈ W, ∃ v ∈ W, e σ u = s ∧ e σ v = s ∧ e (!σ) u ≠ e (!σ) v) ∧
    (∀ S ⊆ star W e σ s, S.Nonempty → S ≠ star W e σ s →
      ∃ u ∈ S, ∃ v ∈ star W e σ s, v ∉ S ∧ G.Adj u v ∧ e (!σ) u ≠ e (!σ) v)

variable {G}

theorem mem_star {W : Finset V} {e : Bool → V → ℕ} {σ : Bool} {s : ℕ} {v : V} :
    v ∈ star W e σ s ↔ v ∈ W ∧ e σ v = s := mem_filter

theorem bool_cases (σ τ : Bool) : τ = σ ∨ τ = !σ := by
  cases σ <;> cases τ <;> simp

/-- Two vertices sharing a non-hub end are adjacent. -/
theorem RepOn.adj_of_nonhub {W : Finset V} {e : Bool → V → ℕ} {h : Bool → Set ℕ}
    (hR : RepOn G W e h) {u v : V} (hu : u ∈ W) (hv : v ∈ W) (huv : u ≠ v) {σ : Bool}
    (he : e σ u = e σ v) (hn : e σ u ∉ h σ) : G.Adj u v := by
  by_contra hna
  obtain ⟨τ, h1, h2, h3⟩ := hR.2.2.2 u hu v hv huv ⟨σ, he⟩ hna
  rcases bool_cases σ τ with rfl | rfl
  · exact hn h2
  · simp only [Bool.not_not] at h3
    exact h3 he

/-- Two vertices with the same two ends are adjacent. -/
theorem RepOn.adj_of_both {W : Finset V} {e : Bool → V → ℕ} {h : Bool → Set ℕ}
    (hR : RepOn G W e h) {u v : V} (hu : u ∈ W) (hv : v ∈ W) (huv : u ≠ v)
    (h1 : e true u = e true v) (h2 : e false u = e false v) : G.Adj u v := by
  by_contra hna
  obtain ⟨τ, -, -, h3⟩ := hR.2.2.2 u hu v hv huv ⟨true, h1⟩ hna
  cases τ
  · exact h3 h1
  · exact h3 h2

theorem RepOn.swap {W : Finset V} {e : Bool → V → ℕ} {h : Bool → Set ℕ} (hR : RepOn G W e h) :
    RepOn G W (fun τ => e (!τ)) (fun τ => h (!τ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  refine ⟨fun v hv σ hs => ?_, fun σ => ?_, fun u hu v hv huv => ?_, ?_⟩
  · have := h1 v hv (!σ) hs
    simpa using this
  · intro u hu v hv w hw e1 e2 e3
    have := h2 (!σ) u hu v hv w hw e1 e2 e3
    simpa using this
  · obtain ⟨σ, hσ⟩ := h3 u hu v hv huv
    exact ⟨!σ, by simpa using hσ⟩
  · intro u hu v hv huv ⟨σ, hσ⟩ hna
    obtain ⟨τ, t1, t2, t3⟩ := h4 u hu v hv huv ⟨!σ, by simpa using hσ⟩ hna
    exact ⟨!τ, by simpa using t1, by simpa using t2, by simpa using t3⟩

theorem NormOn.swap {W : Finset V} {e : Bool → V → ℕ} {h : Bool → Set ℕ}
    (hN : NormOn G W e h) : NormOn G W (fun τ => e (!τ)) (fun τ => h (!τ)) := by
  intro σ s hs
  obtain ⟨n1, n2, n3⟩ := hN (!σ) s hs
  refine ⟨fun v hv hvs => ?_, ?_, fun S hS hne hS' => ?_⟩
  · obtain ⟨w, hw, hwv, e1, e2⟩ := n1 v hv hvs
    exact ⟨w, hw, hwv, e1, by simpa using e2⟩
  · obtain ⟨u, hu, v, hv, e1, e2, e3⟩ := n2
    exact ⟨u, hu, v, hv, e1, e2, by simpa using e3⟩
  · have hst : star W (fun τ => e (!τ)) σ s = star W e (!σ) s := rfl
    rw [hst] at hS hS'
    obtain ⟨u, hu, v, hv, hvS, hadj, hne'⟩ := n3 S hS hne hS'
    exact ⟨u, hu, v, hv, hvS, hadj, by simpa using hne'⟩

/-! ### Pulling back along a map that identifies twins -/

/-- Pull a representation of `W'` back to `W` along `f : W → W'`, when `f` identifies only
adjacent vertices and preserves (non-)adjacency of the other pairs. -/
theorem RepOn.pullback {W W' : Finset V} {e : Bool → V → ℕ} {h : Bool → Set ℕ}
    (hR : RepOn G W' e h) (f : V → V) (hf : ∀ x ∈ W, f x ∈ W')
    (hadj : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → (G.Adj x y ↔ f x = f y ∨ G.Adj (f x) (f y))) :
    RepOn G W (fun τ x => e τ (f x)) h := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  refine ⟨fun v hv σ => h1 (f v) (hf v hv) σ, fun σ u hu v hv w hw => h2 σ _ (hf u hu) _
    (hf v hv) _ (hf w hw), fun u hu v hv huv => ?_, fun u hu v hv huv hsh hna => ?_⟩
  · rcases (hadj u hu v hv (G.ne_of_adj huv)).1 huv with e1 | e1
    · exact ⟨true, by simp [e1]⟩
    · exact h3 _ (hf u hu) _ (hf v hv) e1
  · have hne : f u ≠ f v := fun e1 => hna ((hadj u hu v hv huv).2 (Or.inl e1))
    have hna' : ¬ G.Adj (f u) (f v) := fun e1 => hna ((hadj u hu v hv huv).2 (Or.inr e1))
    exact h4 _ (hf u hu) _ (hf v hv) hne hsh hna'

/-- Adding a twin `v` of `u` to a represented set. -/
theorem twin_ext {W : Finset V} {u v : V} (hu : u ∈ W) (hv : v ∈ W) (huv : u ≠ v)
    (hadj : G.Adj u v) (htw : ∀ w ∈ W, w ≠ u → w ≠ v → (G.Adj w u ↔ G.Adj w v))
    {e : Bool → V → ℕ} {h : Bool → Set ℕ} (hR : RepOn G (W.erase v) e h)
    (hN : NormOn G (W.erase v) e h) :
    ∃ e' h', RepOn G W e' h' ∧ NormOn G W e' h' := by
  set f : V → V := fun x => if x = v then u else x with hfdef
  have hfW : ∀ x ∈ W, f x ∈ W.erase v := by
    intro x hx
    by_cases hxv : x = v
    · simp [hfdef, hxv, huv, hu]
    · simp [hfdef, hxv, hx]
  have hfx : ∀ x, x ≠ v → f x = x := fun x hx => by simp [hfdef, hx]
  have hfv : f v = u := by simp [hfdef]
  refine ⟨fun τ x => e τ (f x), h, hR.pullback f hfW ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxv : x = v
    · subst hxv
      rw [hfv, hfx y (Ne.symm hxy)]
      by_cases hyu : y = u
      · subst hyu
        simp [hadj.symm]
      · rw [G.adj_comm x y, ← htw y hy hyu (Ne.symm hxy), G.adj_comm y u]
        simp [Ne.symm hyu]
    · by_cases hyv : y = v
      · subst hyv
        rw [hfv, hfx x hxv]
        by_cases hxu : x = u
        · subst hxu
          simp [hadj]
        · rw [← htw x hx hxu hxv]
          simp [hxu]
      · rw [hfx x hxv, hfx y hyv]
        simp [hxy]
  · intro σ s hs
    obtain ⟨n1, n2, n3⟩ := hN σ s hs
    have hstar : ∀ x, x ∈ star W (fun τ x => e τ (f x)) σ s ↔
        (x ∈ star (W.erase v) e σ s ∨ (x = v ∧ u ∈ star (W.erase v) e σ s)) := by
      intro x
      simp only [mem_star, mem_erase]
      by_cases hxv : x = v
      · subst hxv
        simp [hfv, huv, hu, hv]
      · simp [hfx x hxv, hxv]
    refine ⟨fun x hx hxs => ?_, ?_, fun S hS hSne hSW => ?_⟩
    · by_cases hxv : x = v
      · subst hxv
        exact ⟨u, hu, huv, by simpa [hfx u huv, hfv] using hxs, by simp [hfx u huv, hfv]⟩
      · simp only [hfx x hxv] at hxs ⊢
        obtain ⟨w, hw, hwx, e1, e2⟩ := n1 x (mem_erase.2 ⟨hxv, hx⟩) hxs
        have hwv : w ≠ v := (mem_erase.1 hw).1
        exact ⟨w, (mem_erase.1 hw).2, hwx, by simp only [hfx w hwv]; exact e1,
          by simp only [hfx w hwv]; exact e2⟩
    · obtain ⟨x, hx, y, hy, e1, e2, e3⟩ := n2
      have hxv : x ≠ v := (mem_erase.1 hx).1
      have hyv : y ≠ v := (mem_erase.1 hy).1
      exact ⟨x, (mem_erase.1 hx).2, y, (mem_erase.1 hy).2, by simp only [hfx x hxv]; exact e1,
        by simp only [hfx y hyv]; exact e2, by simp only [hfx x hxv, hfx y hyv]; exact e3⟩
    · -- the cut condition
      set S' := S.erase v with hS'def
      have hS'sub : S' ⊆ star (W.erase v) e σ s := by
        intro x hx
        have hxv : x ≠ v := (mem_erase.1 hx).1
        rcases (hstar x).1 (hS (mem_erase.1 hx).2) with h' | h'
        · exact h'
        · exact absurd h'.1 hxv
      have hval : ∀ x, x ≠ v → (fun τ x => e τ (f x)) (!σ) x = e (!σ) x :=
        fun x hx => by simp [hfx x hx]
      -- the cut at `{u}` inside the old star, when `u` lies in it
      have cutu : u ∈ star (W.erase v) e σ s → ∃ y ∈ star (W.erase v) e σ s, y ≠ u ∧
          G.Adj u y ∧ e (!σ) u ≠ e (!σ) y := by
        intro hus
        have hne : ({u} : Finset V) ≠ star (W.erase v) e σ s := by
          intro heq
          obtain ⟨x, hx, y, hy, e1, e2, e3⟩ := n2
          have hx' : x ∈ ({u} : Finset V) := heq ▸ mem_star.2 ⟨hx, e1⟩
          have hy' : y ∈ ({u} : Finset V) := heq ▸ mem_star.2 ⟨hy, e2⟩
          rw [mem_singleton] at hx' hy'
          exact e3 (by rw [hx', hy'])
        obtain ⟨a, ha, y, hy, hyS, hadj', hne'⟩ :=
          n3 {u} (singleton_subset_iff.2 hus) (singleton_nonempty u) hne
        rw [mem_singleton] at ha
        subst ha
        exact ⟨y, hy, fun e1 => hyS (by simp [e1]), hadj', hne'⟩
      by_cases hS'e : S' = ∅
      · -- `S = {v}`
        have hSv : S = {v} := by
          obtain ⟨x, hx⟩ := hSne
          have : x = v := by
            by_contra hxv
            have : x ∈ S' := mem_erase.2 ⟨hxv, hx⟩
            rw [hS'e] at this
            simp at this
          subst this
          ext y
          constructor
          · intro hy
            by_contra hyv
            have : y ∈ S' := mem_erase.2 ⟨by simpa using hyv, hy⟩
            rw [hS'e] at this
            simp at this
          · intro hy
            rw [mem_singleton] at hy
            rw [hy]
            exact hx
        have hvs : v ∈ star W (fun τ x => e τ (f x)) σ s := hS (by rw [hSv]; simp)
        rcases (hstar v).1 hvs with h' | h'
        · exact absurd (mem_erase.1 (mem_star.1 h').1).1 (by simp)
        obtain ⟨y, hy, hyu, hadj', hne'⟩ := cutu h'.2
        have hyv : y ≠ v := (mem_erase.1 (mem_star.1 hy).1).1
        refine ⟨v, by rw [hSv]; simp, y, (hstar y).2 (Or.inl hy), by rw [hSv]; simpa using hyv,
          ?_, ?_⟩
        · exact ((htw y (mem_erase.1 (mem_star.1 hy).1).2 hyu hyv).1 hadj'.symm).symm
        · simp only [hfv, hfx y hyv]
          exact hne'
      by_cases hS'f : S' = star (W.erase v) e σ s
      · -- `S` is the old star, and the new star also contains `v`
        have hvS : v ∉ S := by
          intro hvS
          apply hSW
          ext x
          constructor
          · exact fun hx => hS hx
          · intro hx
            by_cases hxv : x = v
            · rw [hxv]; exact hvS
            · rcases (hstar x).1 hx with h' | h'
              · rw [← hS'f] at h'
                exact (mem_erase.1 h').2
              · exact absurd h'.1 hxv
        have hvst : v ∈ star W (fun τ x => e τ (f x)) σ s := by
          by_contra hvn
          apply hSW
          ext x
          constructor
          · exact fun hx => hS hx
          · intro hx
            have hxv : x ≠ v := fun e1 => hvn (e1 ▸ hx)
            rcases (hstar x).1 hx with h' | h'
            · rw [← hS'f] at h'
              exact (mem_erase.1 h').2
            · exact absurd h'.1 hxv
        rcases (hstar v).1 hvst with h' | h'
        · exact absurd (mem_erase.1 (mem_star.1 h').1).1 (by simp)
        obtain ⟨y, hy, hyu, hadj', hne'⟩ := cutu h'.2
        have hyv : y ≠ v := (mem_erase.1 (mem_star.1 hy).1).1
        refine ⟨y, ?_, v, hvst, hvS, ?_, ?_⟩
        · rw [← hS'f] at hy
          exact (mem_erase.1 hy).2
        · exact (htw y (mem_erase.1 (mem_star.1 hy).1).2 hyu hyv).1 hadj'.symm
        · simp only [hfv, hfx y hyv]
          exact fun e1 => hne' e1.symm
      · have hS'ne : S'.Nonempty := nonempty_iff_ne_empty.2 hS'e
        obtain ⟨x, hx, y, hy, hyS, hadj', hne'⟩ := n3 S' hS'sub hS'ne hS'f
        have hxv : x ≠ v := (mem_erase.1 hx).1
        have hyv : y ≠ v := (mem_erase.1 (mem_star.1 hy).1).1
        refine ⟨x, (mem_erase.1 hx).2, y, (hstar y).2 (Or.inl hy), fun hyS' => hyS
          (mem_erase.2 ⟨hyv, hyS'⟩), hadj', ?_⟩
        simp only [hfx x hxv, hfx y hyv]
        exact hne'

end ElemChoos.MR
