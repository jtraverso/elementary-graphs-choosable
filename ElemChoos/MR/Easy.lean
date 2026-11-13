/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Rep

/-!
# Disjoint unions and the line-graph case

* `union_rep`: representations of two vertex sets with no edges between them combine (ends of
  the first set are doubled, ends of the second are doubled plus one).
* `rep_of_noBend`: if the elementary colouring has no *bend* inside `W` (a triangle `u v w`
  with `uv`, `vw` of one colour and `uw` of the other), then "being equal or joined by a red
  edge" and "being equal or joined by a blue edge" are equivalence relations on `W`, and their
  classes are the ends of a representation of `G[W]` as the line graph of a bipartite
  multigraph (no hubs). This replaces Theorems 3 and 4 of Maffray–Reed.
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem union_rep {W1 W2 : Finset V} (hd : Disjoint W1 W2)
    (hna : ∀ u ∈ W1, ∀ v ∈ W2, ¬ G.Adj u v) {e1 e2 : Bool → V → ℕ} {h1 h2 : Bool → Set ℕ}
    (hR1 : RepOn G W1 e1 h1) (hN1 : NormOn G W1 e1 h1) (hR2 : RepOn G W2 e2 h2)
    (hN2 : NormOn G W2 e2 h2) :
    ∃ e h, RepOn G (W1 ∪ W2) e h ∧ NormOn G (W1 ∪ W2) e h := by
  classical
  let e : Bool → V → ℕ := fun τ x => if x ∈ W1 then 2 * e1 τ x else 2 * e2 τ x + 1
  let h : Bool → Set ℕ := fun τ => {n | ∃ m ∈ h1 τ, n = 2 * m} ∪ {n | ∃ m ∈ h2 τ, n = 2 * m + 1}
  have he1 : ∀ τ, ∀ x ∈ W1, e τ x = 2 * e1 τ x := fun τ x hx => by simp [e, hx]
  have he2 : ∀ τ, ∀ x ∈ W2, e τ x = 2 * e2 τ x + 1 := fun τ x hx => by
    simp [e, disjoint_right.1 hd hx]
  have hh1 : ∀ τ m, 2 * m ∈ h τ ↔ m ∈ h1 τ := by
    intro τ m
    simp only [h, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨m', hm', e'⟩ | ⟨m', -, e'⟩)
      · rwa [show m = m' by omega]
      · omega
    · exact fun hm => Or.inl ⟨m, hm, rfl⟩
  have hh2 : ∀ τ m, 2 * m + 1 ∈ h τ ↔ m ∈ h2 τ := by
    intro τ m
    simp only [h, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨m', -, e'⟩ | ⟨m', hm', e'⟩)
      · omega
      · rwa [show m = m' by omega]
    · exact fun hm => Or.inr ⟨m, hm, rfl⟩
  have cross : ∀ τ, ∀ x ∈ W1, ∀ y ∈ W2, e τ x ≠ e τ y := by
    intro τ x hx y hy
    rw [he1 τ x hx, he2 τ y hy]
    omega
  obtain ⟨a1, a2, a3, a4⟩ := hR1
  obtain ⟨b1, b2, b3, b4⟩ := hR2
  refine ⟨e, h, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro v hv σ
    rcases mem_union.1 hv with hv | hv
    · rw [he1 σ v hv, he1 (!σ) v hv, hh1, hh1]
      exact a1 v hv σ
    · rw [he2 σ v hv, he2 (!σ) v hv, hh2, hh2]
      exact b1 v hv σ
  · intro σ u hu v hv w hw
    rcases mem_union.1 hu with hu | hu <;> rcases mem_union.1 hv with hv | hv <;>
      rcases mem_union.1 hw with hw | hw
    · rw [he1 σ u hu, he1 σ v hv, he1 σ w hw, he1 (!σ) u hu, he1 (!σ) v hv, he1 (!σ) w hw,
        hh1]
      intro e1' e2' e3'
      rcases a2 σ u hu v hv w hw (by omega) (by omega) e3' with h' | h' | h' <;> omega
    all_goals first
      | (intro e1' e2' _
         first
           | exact absurd e1' (cross σ _ ‹_› _ ‹_›)
           | exact absurd e1'.symm (cross σ _ ‹_› _ ‹_›)
           | exact absurd e2' (cross σ _ ‹_› _ ‹_›)
           | exact absurd e2'.symm (cross σ _ ‹_› _ ‹_›))
      | skip
    rw [he2 σ u hu, he2 σ v hv, he2 σ w hw, he2 (!σ) u hu, he2 (!σ) v hv, he2 (!σ) w hw,
      hh2]
    intro e1' e2' e3'
    rcases b2 σ u hu v hv w hw (by omega) (by omega) e3' with h' | h' | h' <;> omega
  · intro u hu v hv huv
    rcases mem_union.1 hu with hu | hu <;> rcases mem_union.1 hv with hv | hv
    · obtain ⟨σ, hσ⟩ := a3 u hu v hv huv
      exact ⟨σ, by rw [he1 σ u hu, he1 σ v hv, hσ]⟩
    · exact absurd huv (hna u hu v hv)
    · exact absurd huv.symm (hna v hv u hu)
    · obtain ⟨σ, hσ⟩ := b3 u hu v hv huv
      exact ⟨σ, by rw [he2 σ u hu, he2 σ v hv, hσ]⟩
  · intro u hu v hv huv ⟨σ, hσ⟩ hnadj
    rcases mem_union.1 hu with hu | hu <;> rcases mem_union.1 hv with hv | hv
    · obtain ⟨τ, t1, t2, t3⟩ := a4 u hu v hv huv
        ⟨σ, by rw [he1 σ u hu, he1 σ v hv] at hσ; omega⟩ hnadj
      refine ⟨τ, by rw [he1 τ u hu, he1 τ v hv, t1], by rw [he1 τ u hu, hh1]; exact t2, ?_⟩
      rw [he1 (!τ) u hu, he1 (!τ) v hv]
      omega
    · exact absurd hσ (cross σ u hu v hv)
    · exact absurd hσ.symm (cross σ v hv u hu)
    · obtain ⟨τ, t1, t2, t3⟩ := b4 u hu v hv huv
        ⟨σ, by rw [he2 σ u hu, he2 σ v hv] at hσ; omega⟩ hnadj
      refine ⟨τ, by rw [he2 τ u hu, he2 τ v hv, t1], by rw [he2 τ u hu, hh2]; exact t2, ?_⟩
      rw [he2 (!τ) u hu, he2 (!τ) v hv]
      omega
  · intro σ s hs
    rcases hs with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    · obtain ⟨n1, n2, n3⟩ := hN1 σ m hm
      have hst : star (W1 ∪ W2) e σ (2 * m) = star W1 e1 σ m := by
        ext x
        simp only [mem_star, mem_union]
        constructor
        · rintro ⟨hx | hx, hxe⟩
          · exact ⟨hx, by rw [he1 σ x hx] at hxe; omega⟩
          · rw [he2 σ x hx] at hxe; omega
        · rintro ⟨hx, hxe⟩
          exact ⟨Or.inl hx, by rw [he1 σ x hx, hxe]⟩
      refine ⟨fun v hv hvs => ?_, ?_, fun S hS hSne hSW => ?_⟩
      · rcases mem_union.1 hv with hv | hv
        · rw [he1 σ v hv] at hvs
          obtain ⟨w, hw, hwv, e1', e2'⟩ := n1 v hv (by omega)
          exact ⟨w, mem_union_left _ hw, hwv, by rw [he1 σ w hw, e1'],
            by rw [he1 _ w hw, he1 _ v hv, e2']⟩
        · rw [he2 σ v hv] at hvs; omega
      · obtain ⟨u, hu, v, hv, e1', e2', e3'⟩ := n2
        refine ⟨u, mem_union_left _ hu, v, mem_union_left _ hv, by rw [he1 σ u hu, e1'],
          by rw [he1 σ v hv, e2'], ?_⟩
        rw [he1 _ u hu, he1 _ v hv]
        omega
      · rw [hst] at hS hSW
        obtain ⟨u, hu, v, hv, hvS, hadj, hne⟩ := n3 S hS hSne hSW
        refine ⟨u, hu, v, hst ▸ hv, hvS, hadj, ?_⟩
        rw [he1 _ u (mem_star.1 (hS hu)).1, he1 _ v (mem_star.1 hv).1]
        omega
    · obtain ⟨n1, n2, n3⟩ := hN2 σ m hm
      have hst : star (W1 ∪ W2) e σ (2 * m + 1) = star W2 e2 σ m := by
        ext x
        simp only [mem_star, mem_union]
        constructor
        · rintro ⟨hx | hx, hxe⟩
          · rw [he1 σ x hx] at hxe; omega
          · exact ⟨hx, by rw [he2 σ x hx] at hxe; omega⟩
        · rintro ⟨hx, hxe⟩
          exact ⟨Or.inr hx, by rw [he2 σ x hx, hxe]⟩
      refine ⟨fun v hv hvs => ?_, ?_, fun S hS hSne hSW => ?_⟩
      · rcases mem_union.1 hv with hv | hv
        · rw [he1 σ v hv] at hvs; omega
        · rw [he2 σ v hv] at hvs
          obtain ⟨w, hw, hwv, e1', e2'⟩ := n1 v hv (by omega)
          exact ⟨w, mem_union_right _ hw, hwv, by rw [he2 σ w hw, e1'],
            by rw [he2 _ w hw, he2 _ v hv, e2']⟩
      · obtain ⟨u, hu, v, hv, e1', e2', e3'⟩ := n2
        refine ⟨u, mem_union_right _ hu, v, mem_union_right _ hv, by rw [he2 σ u hu, e1'],
          by rw [he2 σ v hv, e2'], ?_⟩
        rw [he2 _ u hu, he2 _ v hv]
        omega
      · rw [hst] at hS hSW
        obtain ⟨u, hu, v, hv, hvS, hadj, hne⟩ := n3 S hS hSne hSW
        refine ⟨u, hu, v, hst ▸ hv, hvS, hadj, ?_⟩
        rw [he2 _ u (mem_star.1 (hS hu)).1, he2 _ v (mem_star.1 hv).1]
        omega

/-- An injection `Finset V ↪ ℕ`, used to name ends by vertex sets. -/
noncomputable def finsetCode [Fintype V] (s : Finset V) : ℕ :=
  (Fintype.equivFin (Finset V) s).val

theorem finsetCode_inj [Fintype V] {s t : Finset V} (h : finsetCode s = finsetCode t) :
    s = t := (Fintype.equivFin (Finset V)).injective (Fin.ext h)

/-- **The line-graph case.** Without bends, the red and blue classes give a representation. -/
theorem rep_of_noBend [Fintype V] (K : ECol G) (W : Finset V)
    (hnb : ∀ u ∈ W, ∀ v ∈ W, ∀ w ∈ W, G.Adj u v → G.Adj v w → G.Adj u w →
      K.c u v = K.c v w → K.c u w = K.c u v) :
    ∃ e h, RepOn G W e h ∧ NormOn G W e h := by
  classical
  let cls : ℕ → V → Finset V := fun i x => W.filter fun y => y = x ∨ (G.Adj x y ∧ K.c x y = i)
  have key : ∀ i, ∀ x ∈ W, ∀ y ∈ W, (cls i x = cls i y ↔ x = y ∨ (G.Adj x y ∧ K.c x y = i)) := by
    intro i x hx y hy
    constructor
    · intro hc
      have : y ∈ cls i x := by rw [hc]; simp [cls, hy]
      simp only [cls, mem_filter] at this
      rcases this.2 with h' | h'
      · exact Or.inl h'.symm
      · exact Or.inr h'
    · rintro (rfl | ⟨hxy, hc⟩)
      · rfl
      · -- transitivity of "equal or joined in colour `i`"
        have tr : ∀ a ∈ W, ∀ b ∈ W, ∀ d ∈ W, G.Adj a b → K.c a b = i →
            (d = a ∨ (G.Adj a d ∧ K.c a d = i)) → (d = b ∨ (G.Adj b d ∧ K.c b d = i)) := by
          intro a ha b hb d hd hab hcab hd'
          rcases hd' with rfl | ⟨had, hcad⟩
          · exact Or.inr ⟨hab.symm, by rw [K.symm]; exact hcab⟩
          · by_cases hdb : d = b
            · exact Or.inl hdb
            · have hbd : G.Adj b d := K.same_adj hab.symm had (Ne.symm hdb)
                (by rw [K.symm b a, hcab, hcad])
              refine Or.inr ⟨hbd, ?_⟩
              have := hnb b hb a ha d hd hab.symm had hbd (by rw [K.symm b a, hcab, hcad])
              rw [this, K.symm b a, hcab]
        ext d
        simp only [cls, mem_filter]
        constructor
        · rintro ⟨hd, hd'⟩
          exact ⟨hd, tr x hx y hy d hd hxy hc hd'⟩
        · rintro ⟨hd, hd'⟩
          exact ⟨hd, tr y hy x hx d hd hxy.symm (by rw [K.symm]; exact hc) hd'⟩
  let e : Bool → V → ℕ := fun τ x => finsetCode (cls (if τ then 1 else 0) x)
  have he : ∀ τ, ∀ x ∈ W, ∀ y ∈ W, e τ x = e τ y →
      x = y ∨ (G.Adj x y ∧ K.c x y = if τ then 1 else 0) := by
    intro τ x hx y hy hxy
    exact (key _ x hx y hy).1 (finsetCode_inj hxy)
  refine ⟨e, fun _ => ∅, ⟨fun v _ σ h' => absurd h' (Set.notMem_empty _),
    fun σ u _ v _ w _ _ _ h' => absurd h' (Set.notMem_empty _), ?_, ?_⟩, ?_⟩
  · intro u hu v hv huv
    have h1 := K.le_one u v
    by_cases hc : K.c u v = 1
    · exact ⟨true, congrArg finsetCode ((key 1 u hu v hv).2 (Or.inr ⟨huv, hc⟩))⟩
    · exact ⟨false, congrArg finsetCode ((key 0 u hu v hv).2 (Or.inr ⟨huv, by omega⟩))⟩
  · intro u hu v hv huv ⟨σ, hσ⟩ hna
    rcases he σ u hu v hv hσ with h' | h'
    · exact absurd h' huv
    · exact absurd h'.1 hna
  · intro σ s hs
    exact absurd hs (Set.notMem_empty _)

end ElemChoos.MR
