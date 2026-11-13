/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Max
public import ElemChoos.MR.Claim2

/-!
# The growth procedure: initial pair, one step, and a maximal pair

At the end of the procedure (a `Good` pair of maximal size) every vertex outside `C1 ∪ C2`
sees all or none of `C1` and all or none of `C2` (claim (2) of Maffray–Reed).
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} (K : ECol G)

variable {W : Finset V} {x o p1 p2 p3 p4 : V}

include K in
theorem good_init (hD : IsD G x o p1 p2 p3 p4) (hp1 : p1 ∈ W) (hp2 : p2 ∈ W) (hp3 : p3 ∈ W)
    (hp4 : p4 ∈ W) : Good G W x o p1 p2 p3 p4 {p1, p2} {p3, p4} := by
  have hD' := hD
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD'
  have e12 : p1 ≠ p2 := G.ne_of_adj d12
  have e34 : p3 ≠ p4 := G.ne_of_adj d34
  have e13 : p1 ≠ p3 := G.ne_of_adj d13
  have e14 : p1 ≠ p4 := G.ne_of_adj d14
  have e23 : p2 ≠ p3 := G.ne_of_adj d23
  have e24 : p2 ≠ p4 := fun h => no4 (h ▸ do2)
  refine ⟨?_, ?_, ?_, ⟨by simp, by simp, by simp, by simp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp only [mem_insert, mem_singleton] at hv; rcases hv with rfl | rfl <;> assumption
  · intro v hv; simp only [mem_insert, mem_singleton] at hv; rcases hv with rfl | rfl <;> assumption
  · simp [e13, e14, e23, e24, Ne.symm e13, Ne.symm e14, Ne.symm e23, Ne.symm e24]
  · intro u hu v hv huv
    simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    all_goals first | exact absurd rfl huv | exact d12 | exact d12.symm
  · intro u hu v hv huv
    simp only [mem_insert, mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    all_goals first | exact absurd rfl huv | exact d34 | exact d34.symm
  · intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨d1o, fun h => nx1 h.symm⟩
    · exact ⟨do2.symm, fun h => nx2 h.symm⟩
  · intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨fun h => no3 h.symm, fun h => nx3 h.symm⟩
    · exact ⟨fun h => no4 h.symm, fun h => nx4 h.symm⟩
  · intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨p3, by simp, d13⟩
    · exact ⟨p3, by simp, d23⟩
  · intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨p1, by simp, d13.symm⟩
    · exact ⟨p1, by simp, d14.symm⟩
  · intro u hu hu1
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact absurd rfl hu1
    · exact ⟨p4, by simp, n24⟩
  · intro u hu hu3
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact absurd rfl hu3
    · exact ⟨p2, by simp, fun h => n24 h.symm⟩
  · intro z _ hz1 hz2 hbad
    simp only [mem_insert, mem_singleton, not_or] at hz1 hz2
    exact case1 K hD hz1.1 hz1.2 hz2.1 hz2.2 hbad

include K in
theorem Good.step_left {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {m : V} (hmW : m ∈ W) (hmC1 : m ∉ C1) (hmC2 : m ∉ C2)
    (hm1 : ∀ u ∈ C1, G.Adj m u) (hm2 : ∃ u ∈ C2, G.Adj m u) (hm2' : ∃ u ∈ C2, ¬ G.Adj m u) :
    Good G W x o p1 p2 p3 p4 (insert m C1) C2 where
  sub1 := insert_subset hmW hG.sub1
  sub2 := hG.sub2
  disj := disjoint_insert_left.2 ⟨hmC2, hG.disj⟩
  mem := ⟨mem_insert_of_mem hG.mem.1, mem_insert_of_mem hG.mem.2.1, hG.mem.2.2.1, hG.mem.2.2.2⟩
  clq1 := by
    intro u hu v hv huv
    rcases mem_insert.1 hu with rfl | hu' <;> rcases mem_insert.1 hv with rfl | hv'
    · exact absurd rfl huv
    · exact hm1 v hv'
    · exact (hm1 u hu').symm
    · exact hG.clq1 u hu' v hv' huv
  clq2 := hG.clq2
  c1 := by
    intro u hu
    rcases mem_insert.1 hu with rfl | hu
    · exact hG.claim1_left K hD hmC2 hm1 hm2 hm2'
    · exact hG.c1 u hu
  c2 := hG.c2
  nb1 := by
    intro u hu
    rcases mem_insert.1 hu with rfl | hu
    · exact hm2
    · exact hG.nb1 u hu
  nb2 := fun u hu => by
    obtain ⟨v, hv, h⟩ := hG.nb2 u hu
    exact ⟨v, mem_insert_of_mem hv, h⟩
  non1 := by
    intro u hu hu1
    rcases mem_insert.1 hu with rfl | hu
    · exact hm2'
    · exact hG.non1 u hu hu1
  non2 := fun u hu hu3 => by
    obtain ⟨v, hv, h⟩ := hG.non2 u hu hu3
    exact ⟨v, mem_insert_of_mem hv, h⟩
  nobad := by
    intro z hz hz1 hz2
    exact hG.nobad_left K hD hmC1 hmC2 hm1 hm2 hm2' hz
      (fun h => hz1 (h ▸ mem_insert_self _ _)) (fun h => hz1 (mem_insert_of_mem h)) hz2

include K in
theorem Good.step_right {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {m : V} (hmW : m ∈ W) (hmC1 : m ∉ C1) (hmC2 : m ∉ C2)
    (hm2 : ∀ u ∈ C2, G.Adj m u) (hm1 : ∃ u ∈ C1, G.Adj m u) (hm1' : ∃ u ∈ C1, ¬ G.Adj m u) :
    Good G W x o p1 p2 p3 p4 C1 (insert m C2) where
  sub1 := hG.sub1
  sub2 := insert_subset hmW hG.sub2
  disj := disjoint_insert_right.2 ⟨hmC1, hG.disj⟩
  mem := ⟨hG.mem.1, hG.mem.2.1, mem_insert_of_mem hG.mem.2.2.1, mem_insert_of_mem hG.mem.2.2.2⟩
  clq1 := hG.clq1
  clq2 := by
    intro u hu v hv huv
    rcases mem_insert.1 hu with rfl | hu' <;> rcases mem_insert.1 hv with rfl | hv'
    · exact absurd rfl huv
    · exact hm2 v hv'
    · exact (hm2 u hu').symm
    · exact hG.clq2 u hu' v hv' huv
  c1 := hG.c1
  c2 := by
    intro u hu
    rcases mem_insert.1 hu with rfl | hu
    · exact hG.claim1_right K hD hmC1 hm2 hm1 hm1'
    · exact hG.c2 u hu
  nb1 := fun u hu => by
    obtain ⟨v, hv, h⟩ := hG.nb1 u hu
    exact ⟨v, mem_insert_of_mem hv, h⟩
  nb2 := by
    intro u hu
    rcases mem_insert.1 hu with rfl | hu
    · exact hm1
    · exact hG.nb2 u hu
  non1 := fun u hu hu1 => by
    obtain ⟨v, hv, h⟩ := hG.non1 u hu hu1
    exact ⟨v, mem_insert_of_mem hv, h⟩
  non2 := by
    intro u hu hu3
    rcases mem_insert.1 hu with rfl | hu
    · exact hm1'
    · exact hG.non2 u hu hu3
  nobad := by
    intro z hz hz1 hz2
    exact hG.nobad_right K hD hmC1 hmC2 hm2 hm1 hm1' hz
      (fun h => hz2 (h ▸ mem_insert_self _ _)) hz1 (fun h => hz2 (mem_insert_of_mem h))

include K in
/-- A `Good` pair that cannot be grown: every outside vertex sees all or none of each clique. -/
theorem exists_final (hD : IsD G x o p1 p2 p3 p4) (hp1 : p1 ∈ W) (hp2 : p2 ∈ W) (hp3 : p3 ∈ W)
    (hp4 : p4 ∈ W) : ∃ C1 C2, Good G W x o p1 p2 p3 p4 C1 C2 ∧
      ∀ z ∈ W, z ∉ C1 → z ∉ C2 →
        ((∀ u ∈ C1, G.Adj z u) ∨ (∀ u ∈ C1, ¬ G.Adj z u)) ∧
        ((∀ u ∈ C2, G.Adj z u) ∨ (∀ u ∈ C2, ¬ G.Adj z u)) := by
  classical
  set P := (W.powerset ×ˢ W.powerset).filter
    (fun p : Finset V × Finset V => Good G W x o p1 p2 p3 p4 p.1 p.2) with hP
  have hne : P.Nonempty := ⟨({p1, p2}, {p3, p4}), mem_filter.2 ⟨mem_product.2
    ⟨mem_powerset.2 (good_init K hD hp1 hp2 hp3 hp4).sub1,
      mem_powerset.2 (good_init K hD hp1 hp2 hp3 hp4).sub2⟩, good_init K hD hp1 hp2 hp3 hp4⟩⟩
  obtain ⟨⟨C1, C2⟩, hmem, hmax⟩ := exists_max_image P (fun p => #p.1 + #p.2) hne
  have hG : Good G W x o p1 p2 p3 p4 C1 C2 := (mem_filter.1 hmem).2
  refine ⟨C1, C2, hG, fun z hz hz1 hz2 => ?_⟩
  have inP : ∀ D1 D2, Good G W x o p1 p2 p3 p4 D1 D2 → (D1, D2) ∈ P := fun D1 D2 h =>
    mem_filter.2 ⟨mem_product.2 ⟨mem_powerset.2 h.sub1, mem_powerset.2 h.sub2⟩, h⟩
  have no1 : ¬ ((∀ u ∈ C1, G.Adj z u) ∧ (∃ u ∈ C2, G.Adj z u) ∧ ∃ u ∈ C2, ¬ G.Adj z u) := by
    rintro ⟨h1, h2, h3⟩
    have := hmax _ (inP _ _ (hG.step_left K hD hz hz1 hz2 h1 h2 h3))
    simp only [card_insert_of_notMem hz1] at this
    omega
  have no2 : ¬ ((∀ u ∈ C2, G.Adj z u) ∧ (∃ u ∈ C1, G.Adj z u) ∧ ∃ u ∈ C1, ¬ G.Adj z u) := by
    rintro ⟨h1, h2, h3⟩
    have := hmax _ (inP _ _ (hG.step_right K hD hz hz1 hz2 h1 h2 h3))
    simp only [card_insert_of_notMem hz2] at this
    omega
  have nb := hG.nobad z hz hz1 hz2
  unfold Bad at nb
  have key1 : (∃ u ∈ C1, G.Adj z u) → (∃ u ∈ C1, ¬ G.Adj z u) → False := by
    rintro ⟨u, hu, hzu⟩ ⟨u', hu', hzu'⟩
    by_cases h2 : ∀ w ∈ C2, G.Adj z w
    · exact no2 ⟨h2, ⟨u, hu, hzu⟩, ⟨u', hu', hzu'⟩⟩
    · push_neg at h2
      exact nb ⟨⟨u', hu', hzu'⟩, h2, Or.inl ⟨u, hu, hzu⟩⟩
  have key2 : (∃ u ∈ C2, G.Adj z u) → (∃ u ∈ C2, ¬ G.Adj z u) → False := by
    rintro ⟨u, hu, hzu⟩ ⟨u', hu', hzu'⟩
    by_cases h1 : ∀ w ∈ C1, G.Adj z w
    · exact no1 ⟨h1, ⟨u, hu, hzu⟩, ⟨u', hu', hzu'⟩⟩
    · push_neg at h1
      exact nb ⟨h1, ⟨u', hu', hzu'⟩, Or.inr ⟨u, hu, hzu⟩⟩
  refine ⟨?_, ?_⟩
  · by_cases h : ∀ u ∈ C1, G.Adj z u
    · exact Or.inl h
    · push_neg at h
      exact Or.inr fun u hu hzu => key1 ⟨u, hu, hzu⟩ h
  · by_cases h : ∀ u ∈ C2, G.Adj z u
    · exact Or.inl h
    · push_neg at h
      exact Or.inr fun u hu hzu => key2 ⟨u, hu, hzu⟩ h

end ElemChoos.MR
