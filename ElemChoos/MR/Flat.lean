/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Easy

/-!
# Flat edges in a normalized representation

In a normalized representation (`NormOn`), a flat edge `ab` (no common neighbour) with another
neighbour of `a` or `b` has a very special form: `a` and `b` share exactly one end `s`, which is
not a hub and whose star is `{a, b}`, and their other ends are distinct non-hubs. This is the
corrected form of the remark on p. 143 of Maffray–Reed ("all edges inside an augment lie in a
triangle"), which is true for normalized augments only.
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem RepOn.adj_of_two {W : Finset V} {e : Bool → V → ℕ} {h : Bool → Set ℕ}
    (hR : RepOn G W e h) {u v : V} (hu : u ∈ W) (hv : v ∈ W) (huv : u ≠ v) {σ : Bool}
    (h1 : e σ u = e σ v) (h2 : e (!σ) u = e (!σ) v) : G.Adj u v := by
  cases σ
  · exact hR.adj_of_both hu hv huv h2 h1
  · exact hR.adj_of_both hu hv huv h1 h2

/-- The shared end of a flat edge is not a hub. -/
theorem flat_not_hub {W : Finset V} {e : Bool → V → ℕ} {h : Bool → Set ℕ}
    (hR : RepOn G W e h) (hN : NormOn G W e h) {a b : V} (ha : a ∈ W) (hb : b ∈ W)
    (hab : G.Adj a b) (hflat : ∀ w ∈ W, G.Adj w a → G.Adj w b → False) {σ : Bool}
    (hs : e σ a = e σ b) : e σ a ∉ h σ := by
  classical
  intro hhub
  have hne : a ≠ b := G.ne_of_adj hab
  obtain ⟨n1, -, n3⟩ := hN σ _ hhub
  have h2 := hR.2.1 σ
  by_cases hc : e (!σ) a = e (!σ) b
  · -- `a` and `b` in the same class
    set S := insert a ((star W e σ (e σ a)).filter fun y => G.Adj a y ∧ e (!σ) y ≠ e (!σ) a)
      with hSdef
    have hSsub : S ⊆ star W e σ (e σ a) := by
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact mem_star.2 ⟨ha, rfl⟩
      · exact (mem_filter.1 hx).1
    have hbS : b ∉ S := by
      intro hbS
      rcases mem_insert.1 hbS with h' | h'
      · exact hne h'.symm
      · exact (mem_filter.1 h').2.2 hc.symm
    obtain ⟨u, hu, v, hv, hvS, huv, hne'⟩ := n3 S hSsub (insert_nonempty _ _)
      (fun h' => hbS (h' ▸ mem_star.2 ⟨hb, hs.symm⟩))
    have hvW := (mem_star.1 hv).1
    rcases mem_insert.1 hu with rfl | hu'
    · exact hvS (mem_insert_of_mem (mem_filter.2 ⟨hv, huv, fun e' => hne' e'.symm⟩))
    · obtain ⟨huS, hau, hua⟩ := mem_filter.1 hu'
      have huW := (mem_star.1 huS).1
      have hva : v ≠ a := fun e' => hvS (e' ▸ mem_insert_self _ _)
      rcases h2 a ha u huW v hvW (mem_star.1 huS).2.symm (mem_star.1 hv).2.symm hhub with
        h' | h' | h'
      · exact hua h'.symm
      · by_cases hvb : v = b
        · subst hvb
          exact hflat u huW hau.symm huv
        · have hav : G.Adj a v := hR.adj_of_two ha hvW (Ne.symm hva) (mem_star.1 hv).2.symm h'
          have hbv : G.Adj b v := hR.adj_of_two hb hvW (Ne.symm hvb)
            (by rw [← hs]; exact (mem_star.1 hv).2.symm) (by rw [← hc]; exact h')
          exact hflat v hvW hav.symm hbv.symm
      · exact hne' h'
  · -- `a` and `b` in different classes
    obtain ⟨w, hw, hwa, e1, e2⟩ := n1 a ha rfl
    have hwb : w ≠ b := fun e' => hc (e' ▸ e2.symm)
    have hSsub : ({a, b} : Finset V) ⊆ star W e σ (e σ a) := by
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact mem_star.2 ⟨ha, rfl⟩
      · rw [mem_singleton.1 hx]; exact mem_star.2 ⟨hb, hs.symm⟩
    have hSne : ({a, b} : Finset V) ≠ star W e σ (e σ a) := by
      intro h'
      have : w ∈ ({a, b} : Finset V) := h' ▸ mem_star.2 ⟨hw, e1⟩
      simp [hwa, hwb] at this
    obtain ⟨u, hu, v, hv, hvS, huv, hne'⟩ := n3 {a, b} hSsub (insert_nonempty _ _) hSne
    have hvW := (mem_star.1 hv).1
    have hva : v ≠ a := fun e' => hvS (by simp [e'])
    have hvb : v ≠ b := fun e' => hvS (by simp [e'])
    rcases h2 a ha b hb v hvW hs (mem_star.1 hv).2.symm hhub with h' | h' | h'
    · exact hc h'
    · rcases mem_insert.1 hu with rfl | hu'
      · exact hne' h'
      · rw [mem_singleton.1 hu'] at huv hne'
        have hav : G.Adj a v := hR.adj_of_two ha hvW (Ne.symm hva) (mem_star.1 hv).2.symm h'
        exact hflat v hvW hav.symm huv.symm
    · rcases mem_insert.1 hu with rfl | hu'
      · have hbv : G.Adj b v := hR.adj_of_two hb hvW (Ne.symm hvb)
          (by rw [← hs]; exact (mem_star.1 hv).2.symm) h'
        exact hflat v hvW huv.symm hbv.symm
      · rw [mem_singleton.1 hu'] at huv hne'
        exact hne' h'

/-- **Normal form of a flat edge.** -/
theorem flat_normal {W : Finset V} {e : Bool → V → ℕ} {h : Bool → Set ℕ}
    (hR : RepOn G W e h) (hN : NormOn G W e h) {a b : V} (ha : a ∈ W) (hb : b ∈ W)
    (hab : G.Adj a b) (hflat : ∀ w ∈ W, G.Adj w a → G.Adj w b → False)
    (hext : ∃ w ∈ W, w ≠ a ∧ w ≠ b ∧ (G.Adj w a ∨ G.Adj w b)) :
    ∃ σ, e σ a = e σ b ∧ e σ a ∉ h σ ∧ (∀ v ∈ W, e σ v = e σ a → v = a ∨ v = b) ∧
      e (!σ) a ≠ e (!σ) b ∧ e (!σ) a ∉ h (!σ) ∧ e (!σ) b ∉ h (!σ) := by
  obtain ⟨σ, hs⟩ := hR.2.2.1 a ha b hb hab
  have hsn := flat_not_hub hR hN ha hb hab hflat hs
  -- the star of a non-hub shared end is `{a, b}`
  have hstar : ∀ τ, e τ a = e τ b → ∀ v ∈ W, e τ v = e τ a → v = a ∨ v = b := by
    intro τ hτ v hv hva
    have hτn := flat_not_hub hR hN ha hb hab hflat hτ
    by_contra hc
    push_neg at hc
    have h1 : G.Adj v a := hR.adj_of_nonhub hv ha hc.1 hva (by rwa [hva])
    have h2 : G.Adj v b := hR.adj_of_nonhub hv hb hc.2 (hva.trans hτ) (by rwa [hva])
    exact hflat v hv h1 h2
  have hdiff : e (!σ) a ≠ e (!σ) b := by
    intro hτ
    obtain ⟨w, hw, hwa, hwb, hadj⟩ := hext
    rcases hadj with hadj | hadj
    · obtain ⟨τ, hτ'⟩ := hR.2.2.1 w hw a ha hadj
      rcases bool_cases σ τ with rfl | rfl
      · rcases hstar τ hs w hw hτ' with h' | h' <;> contradiction
      · rcases hstar (!σ) hτ w hw hτ' with h' | h' <;> contradiction
    · obtain ⟨τ, hτ'⟩ := hR.2.2.1 w hw b hb hadj
      rcases bool_cases σ τ with rfl | rfl
      · rcases hstar τ hs w hw (hτ'.trans hs.symm) with h' | h' <;> contradiction
      · rcases hstar (!σ) hτ w hw (hτ'.trans hτ.symm) with h' | h' <;> contradiction
  have hother : ∀ x, (x = a ∨ x = b) → e (!σ) x ∉ h (!σ) := by
    intro x hx hhub
    have hxW : x ∈ W := by rcases hx with rfl | rfl <;> assumption
    obtain ⟨n1, -, -⟩ := hN (!σ) _ hhub
    obtain ⟨w, hw, hwx, e1, e2⟩ := n1 x hxW rfl
    simp only [Bool.not_not] at e2
    rcases hx with hx | hx
    · rw [hx] at e1 e2 hwx
      rcases hstar σ hs w hw e2 with h' | h'
      · exact hwx h'
      · rw [h'] at e1
        exact hdiff e1.symm
    · rw [hx] at e1 e2 hwx
      rcases hstar σ hs w hw (e2.trans hs.symm) with h' | h'
      · rw [h'] at e1
        exact hdiff e1
      · exact hwx h'
  exact ⟨σ, hs, hsn, hstar σ hs, hdiff, hother a (Or.inl rfl), hother b (Or.inr rfl)⟩

end ElemChoos.MR
