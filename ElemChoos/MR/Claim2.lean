/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Growth

/-!
# Claim (2) of Maffray–Reed: no bad vertex appears

`case1`: initially (`C1 = {p1, p2}`, `C2 = {p3, p4}`) no vertex is bad (Case 1 of the paper).
`Good.nobad_left` / `Good.nobad_right`: adding a vertex `m` to `C1` / `C2` creates no bad vertex.
For a vertex `z` that becomes bad, either `z` sees `m` (Case 2: then `z` saw nothing before) or
`z` misses `m` (Case 3: then `z` sees all of the clique of `m`). Case 3 as printed in the paper is
inconsistent (it assumes `z` misses `m` and then uses a triangle through `z` and `m`); it is
replaced here by the colour argument recorded in `NOTES.md`, checked by brute force.
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} (K : ECol G)

variable {W : Finset V} {x o p1 p2 p3 p4 : V}

set_option maxHeartbeats 40000000 in
include K in
theorem case1_tt (hD : IsD G x o p1 p2 p3 p4) {z : V} (hz1 : z ≠ p1) (hz2 : z ≠ p2)
    (hz3 : z ≠ p3) (hz4 : z ≠ p4) (hbad : Bad G z {p1, p2} {p3, p4}) (e1 : G.Adj z p1)
    (e2 : G.Adj z p2) : False := by
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD
  simp only [Bad, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left] at hbad
  obtain ⟨h12, h34, hs⟩ := hbad
  by_cases e3 : G.Adj z p3 <;> by_cases e4 : G.Adj z p4 <;> by_cases e5 : G.Adj z o <;>
    by_cases e6 : G.Adj z x <;>
    first
    | (rcases h12 with h | h <;> contradiction)
    | (rcases h34 with h | h <;> contradiction)
    | (rcases hs with (h | h) | (h | h) <;> contradiction)
    | elem_contra K [x, o, p1, p2, p3, p4, z]

set_option maxHeartbeats 40000000 in
include K in
theorem case1_tf (hD : IsD G x o p1 p2 p3 p4) {z : V} (hz1 : z ≠ p1) (hz2 : z ≠ p2)
    (hz3 : z ≠ p3) (hz4 : z ≠ p4) (hbad : Bad G z {p1, p2} {p3, p4}) (e1 : G.Adj z p1)
    (e2 : ¬ G.Adj z p2) : False := by
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD
  simp only [Bad, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left] at hbad
  obtain ⟨h12, h34, hs⟩ := hbad
  by_cases e3 : G.Adj z p3 <;> by_cases e4 : G.Adj z p4 <;> by_cases e5 : G.Adj z o <;>
    by_cases e6 : G.Adj z x <;>
    first
    | (rcases h12 with h | h <;> contradiction)
    | (rcases h34 with h | h <;> contradiction)
    | (rcases hs with (h | h) | (h | h) <;> contradiction)
    | elem_contra K [x, o, p1, p2, p3, p4, z]

set_option maxHeartbeats 40000000 in
include K in
theorem case1_ft (hD : IsD G x o p1 p2 p3 p4) {z : V} (hz1 : z ≠ p1) (hz2 : z ≠ p2)
    (hz3 : z ≠ p3) (hz4 : z ≠ p4) (hbad : Bad G z {p1, p2} {p3, p4}) (e1 : ¬ G.Adj z p1)
    (e2 : G.Adj z p2) : False := by
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD
  simp only [Bad, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left] at hbad
  obtain ⟨h12, h34, hs⟩ := hbad
  by_cases e3 : G.Adj z p3 <;> by_cases e4 : G.Adj z p4 <;> by_cases e5 : G.Adj z o <;>
    by_cases e6 : G.Adj z x <;>
    first
    | (rcases h12 with h | h <;> contradiction)
    | (rcases h34 with h | h <;> contradiction)
    | (rcases hs with (h | h) | (h | h) <;> contradiction)
    | elem_contra K [x, o, p1, p2, p3, p4, z]

set_option maxHeartbeats 40000000 in
include K in
theorem case1_ff (hD : IsD G x o p1 p2 p3 p4) {z : V} (hz1 : z ≠ p1) (hz2 : z ≠ p2)
    (hz3 : z ≠ p3) (hz4 : z ≠ p4) (hbad : Bad G z {p1, p2} {p3, p4}) (e1 : ¬ G.Adj z p1)
    (e2 : ¬ G.Adj z p2) : False := by
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD
  simp only [Bad, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left] at hbad
  obtain ⟨h12, h34, hs⟩ := hbad
  by_cases e3 : G.Adj z p3 <;> by_cases e4 : G.Adj z p4 <;> by_cases e5 : G.Adj z o <;>
    by_cases e6 : G.Adj z x <;>
    first
    | (rcases h12 with h | h <;> contradiction)
    | (rcases h34 with h | h <;> contradiction)
    | (rcases hs with (h | h) | (h | h) <;> contradiction)
    | elem_contra K [x, o, p1, p2, p3, p4, z]

include K in
/-- **Case 1.** -/
theorem case1 (hD : IsD G x o p1 p2 p3 p4) {z : V} (hz1 : z ≠ p1) (hz2 : z ≠ p2) (hz3 : z ≠ p3)
    (hz4 : z ≠ p4) (hbad : Bad G z {p1, p2} {p3, p4}) : False := by
  by_cases e1 : G.Adj z p1 <;> by_cases e2 : G.Adj z p2
  · exact case1_tt K hD hz1 hz2 hz3 hz4 hbad e1 e2
  · exact case1_tf K hD hz1 hz2 hz3 hz4 hbad e1 e2
  · exact case1_ft K hD hz1 hz2 hz3 hz4 hbad e1 e2
  · exact case1_ff K hD hz1 hz2 hz3 hz4 hbad e1 e2

set_option maxHeartbeats 40000000 in
include K in
/-- Adding `m` to `C1` creates no bad vertex. -/
theorem Good.nobad_left {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {m : V} (hmC1 : m ∉ C1) (hmC2 : m ∉ C2)
    (hm1 : ∀ u ∈ C1, G.Adj m u) (hm2 : ∃ u ∈ C2, G.Adj m u) (hm2' : ∃ u ∈ C2, ¬ G.Adj m u)
    {z : V} (hzW : z ∈ W) (hzm : z ≠ m) (hzC1 : z ∉ C1) (hzC2 : z ∉ C2)
    (hbad : Bad G z (insert m C1) C2) : False := by
  obtain ⟨hmo, hmx⟩ := hG.claim1_left K hD hmC2 hm1 hm2 hm2'
  have hD' := hD
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD'
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hG.mem
  unfold Bad at hbad
  obtain ⟨⟨u1, hu1, hzu1⟩, ⟨l, hl, hzl⟩, hsee⟩ := hbad
  have old := hG.nobad z hzW hzC1 hzC2
  unfold Bad at old
  have hm1p1 := hm1 p1 hp1
  have hm1p2 := hm1 p2 hp2
  have hmp3' : m ≠ p3 := fun h => hmC2 (h ▸ hp3)
  have hmp4' : m ≠ p4 := fun h => hmC2 (h ▸ hp4)
  have hzl' : z ≠ l := fun h => hzC2 (h ▸ hl)
  by_cases hzm' : G.Adj z m
  · -- Case 2: `z` saw nothing of `C1 ∪ C2`
    have hu1' : u1 ∈ C1 := by
      rcases mem_insert.1 hu1 with h | h
      · rw [h] at hzu1; exact absurd hzm' hzu1
      · exact h
    have hnone : ∀ u ∈ C1 ∪ C2, ¬ G.Adj z u := by
      intro u hu hzu
      apply old
      refine ⟨⟨u1, hu1', hzu1⟩, ⟨l, hl, hzl⟩, ?_⟩
      rcases mem_union.1 hu with h | h
      · exact Or.inl ⟨u, h, hzu⟩
      · exact Or.inr ⟨u, h, hzu⟩
    have hall : ∀ r ∈ C2, G.Adj m r → ∀ s ∈ C1, G.Adj r s := by
      intro r hr hmr s hs
      by_contra hrs
      have hzr := hnone r (mem_union_right _ hr)
      have hzs := hnone s (mem_union_left _ hs)
      have hms := hm1 s hs
      have d1 := hG.ne12 hs hr
      have d2 : z ≠ r := fun h => hzC2 (h ▸ hr)
      have d3 : z ≠ s := fun h => hzC1 (h ▸ hs)
      elem_contra K [m, r, s, z]
    obtain ⟨r, hr, hmr⟩ := hm2
    have hr3 : r = p3 := by
      by_contra hr3
      obtain ⟨j, hj, hrj⟩ := hG.non2 r hr hr3
      exact hrj (hall r hr hmr j hj)
    rw [hr3] at hmr
    have hm4 : ¬ G.Adj m p4 := by
      intro h
      obtain ⟨j, hj, hj4⟩ := hG.non2 p4 hp4 (fun h' => by rw [h'] at d34; exact G.loopless.irrefl _ d34)
      exact hj4 (hall p4 hp4 h j hj)
    have z1 := hnone p1 (mem_union_left _ hp1)
    have z2 := hnone p2 (mem_union_left _ hp2)
    have z3 := hnone p3 (mem_union_right _ hp3)
    have z4 := hnone p4 (mem_union_right _ hp4)
    by_cases hzo : G.Adj z o
    · elem_contra K [o, p1, p2, p3, p4, z, m]
    · elem_contra K [o, p3, z, m]
  · -- Case 3: `z` sees all of `C1`
    have hsee' : (∃ u ∈ C1, G.Adj z u) ∨ (∃ u ∈ C2, G.Adj z u) := by
      rcases hsee with ⟨u, hu, hzu⟩ | h
      · rcases mem_insert.1 hu with h | h
        · rw [h] at hzu; exact absurd hzu hzm'
        · exact Or.inl ⟨u, h, hzu⟩
      · exact Or.inr h
    have hall1 : ∀ u ∈ C1, G.Adj z u := by
      by_contra hn
      push_neg at hn
      exact old ⟨hn, ⟨l, hl, hzl⟩, hsee'⟩
    obtain ⟨k, hk, hlk⟩ := hG.nb2 l hl
    have hzk := hall1 k hk
    have hko := (hG.c1 k hk).1
    have hkx := (hG.c1 k hk).2
    have hlo := (hG.c2 l hl).1
    have hlx := (hG.c2 l hl).2
    have hmk := hm1 k hk
    have dlk := hG.ne12 hk hl
    have dlo := hG.ne_o2 hD hl
    have dlx := hG.ne_x2 hD hl
    have dko := hG.ne_o1 hk
    have dkx := hG.ne_x1 hD hk
    have dlm : l ≠ m := fun h => hmC2 (h ▸ hl)
    by_cases hzo : G.Adj z o
    · have hzp1 := hall1 p1 hp1
      have hzx : G.Adj z x := by
        by_contra hzx
        elem_contra K [o, x, m, z]
      have hml : G.Adj m l := by
        by_contra hml
        elem_contra K [k, z, l, m]
      obtain ⟨r', hr', hmr'⟩ := hm2'
      obtain ⟨k', hk', hr'k'⟩ := hG.nb2 r' hr'
      have hzk' := hall1 k' hk'
      have hmk' := hm1 k' hk'
      have dr'm : r' ≠ m := fun h => hmC2 (h ▸ hr')
      have dzr' : z ≠ r' := fun h => hzC2 (h ▸ hr')
      have dk'r' := hG.ne12 hk' hr'
      have hzr' : G.Adj z r' := by
        by_contra hzr'
        elem_contra K [k', z, r', m]
      have hr'o := (hG.c2 r' hr').1
      have hr'x := (hG.c2 r' hr').2
      have dr'x := hG.ne_x2 hD hr'
      have dr'o := hG.ne_o2 hD hr'
      have dkr' := hG.ne12 hk hr'
      have hr'k : G.Adj r' k := by
        by_contra hr'k
        elem_contra K [z, x, r', k]
      have dlr' : l ≠ r' := fun h => hmr' (h ▸ hml)
      have hlr' : G.Adj l r' := hG.clq2 l hl r' hr' dlr'
      elem_contra K [x, o, k, l, m, r', z]
    · elem_contra K [o, k, l, z]

set_option maxHeartbeats 40000000 in
include K in
/-- Adding `m` to `C2` creates no bad vertex. -/
theorem Good.nobad_right {C1 C2 : Finset V} (hD : IsD G x o p1 p2 p3 p4)
    (hG : Good G W x o p1 p2 p3 p4 C1 C2) {m : V} (hmC1 : m ∉ C1) (hmC2 : m ∉ C2)
    (hm2 : ∀ u ∈ C2, G.Adj m u) (hm1 : ∃ u ∈ C1, G.Adj m u) (hm1' : ∃ u ∈ C1, ¬ G.Adj m u)
    {z : V} (hzW : z ∈ W) (hzm : z ≠ m) (hzC1 : z ∉ C1) (hzC2 : z ∉ C2)
    (hbad : Bad G z C1 (insert m C2)) : False := by
  obtain ⟨hmo, hmx⟩ := hG.claim1_right K hD hmC1 hm2 hm1 hm1'
  have hD' := hD
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD'
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hG.mem
  unfold Bad at hbad
  obtain ⟨⟨l, hl, hzl⟩, ⟨u2, hu2, hzu2⟩, hsee⟩ := hbad
  have old := hG.nobad z hzW hzC1 hzC2
  unfold Bad at old
  have hm2p3 := hm2 p3 hp3
  have hm2p4 := hm2 p4 hp4
  have hmp1' : m ≠ p1 := fun h => hmC1 (h ▸ hp1)
  have hmp2' : m ≠ p2 := fun h => hmC1 (h ▸ hp2)
  have hzl' : z ≠ l := fun h => hzC1 (h ▸ hl)
  by_cases hzm' : G.Adj z m
  · -- Case 2
    have hu2' : u2 ∈ C2 := by
      rcases mem_insert.1 hu2 with h | h
      · rw [h] at hzu2; exact absurd hzm' hzu2
      · exact h
    have hnone : ∀ u ∈ C1 ∪ C2, ¬ G.Adj z u := by
      intro u hu hzu
      apply old
      refine ⟨⟨l, hl, hzl⟩, ⟨u2, hu2', hzu2⟩, ?_⟩
      rcases mem_union.1 hu with h | h
      · exact Or.inl ⟨u, h, hzu⟩
      · exact Or.inr ⟨u, h, hzu⟩
    have hall : ∀ r ∈ C1, G.Adj m r → ∀ s ∈ C2, G.Adj r s := by
      intro r hr hmr s hs
      by_contra hrs
      have hzr := hnone r (mem_union_left _ hr)
      have hzs := hnone s (mem_union_right _ hs)
      have hms := hm2 s hs
      have d1 := hG.ne12 hr hs
      have d2 : z ≠ r := fun h => hzC1 (h ▸ hr)
      have d3 : z ≠ s := fun h => hzC2 (h ▸ hs)
      elem_contra K [m, r, s, z]
    obtain ⟨r, hr, hmr⟩ := hm1
    have hr1 : r = p1 := by
      by_contra hr1
      obtain ⟨j, hj, hrj⟩ := hG.non1 r hr hr1
      exact hrj (hall r hr hmr j hj)
    rw [hr1] at hmr
    have hm2' : ¬ G.Adj m p2 := by
      intro h
      obtain ⟨j, hj, hj2⟩ := hG.non1 p2 hp2 (fun h' => by rw [h'] at d12; exact G.loopless.irrefl _ d12)
      exact hj2 (hall p2 hp2 h j hj)
    have z1 := hnone p1 (mem_union_left _ hp1)
    have z2 := hnone p2 (mem_union_left _ hp2)
    have z3 := hnone p3 (mem_union_right _ hp3)
    have z4 := hnone p4 (mem_union_right _ hp4)
    by_cases hzo : G.Adj z o <;> by_cases hzx : G.Adj z x <;>
      elem_contra K [x, o, p1, p2, p3, m, z]
  · -- Case 3: `z` sees all of `C2`
    have hsee' : (∃ u ∈ C1, G.Adj z u) ∨ (∃ u ∈ C2, G.Adj z u) := by
      rcases hsee with h | ⟨u, hu, hzu⟩
      · exact Or.inl h
      · rcases mem_insert.1 hu with h | h
        · rw [h] at hzu; exact absurd hzu hzm'
        · exact Or.inr ⟨u, h, hzu⟩
    have hall2 : ∀ u ∈ C2, G.Adj z u := by
      by_contra hn
      push_neg at hn
      exact old ⟨⟨l, hl, hzl⟩, hn, hsee'⟩
    have hz3 := hall2 p3 hp3
    have hz4 := hall2 p4 hp4
    by_cases hzo : G.Adj z o
    · have hlo := (hG.c1 l hl).1
      have hlx := (hG.c1 l hl).2
      have dlx := hG.ne_x1 hD hl
      have hzx : G.Adj z x := by
        by_contra hzx
        elem_contra K [o, x, l, z]
      obtain ⟨k, hk, hlk⟩ := hG.nb1 l hl
      have hzk := hall2 k hk
      have hmk := hm2 k hk
      have dlk := hG.ne12 hl hk
      have dlm : l ≠ m := fun h => hmC1 (h ▸ hl)
      have dzk : z ≠ k := fun h => hzC2 (h ▸ hk)
      have dmk : m ≠ k := fun h => hmC2 (h ▸ hk)
      have hml : G.Adj m l := by
        by_contra hml
        elem_contra K [k, z, l, m]
      obtain ⟨r', hr', hmr'⟩ := hm1'
      obtain ⟨k', hk', hr'k'⟩ := hG.nb1 r' hr'
      have hzk' := hall2 k' hk'
      have hmk' := hm2 k' hk'
      have dr'm : r' ≠ m := fun h => hmC1 (h ▸ hr')
      have dzr' : z ≠ r' := fun h => hzC1 (h ▸ hr')
      have dk'r' := hG.ne12 hr' hk'
      have hzr' : G.Adj z r' := by
        by_contra hzr'
        elem_contra K [k', z, r', m]
      have dlr' : l ≠ r' := fun h => hmr' (h ▸ hml)
      have hlr' : G.Adj l r' := hG.clq1 l hl r' hr' dlr'
      have hr'o := (hG.c1 r' hr').1
      have hr'x := (hG.c1 r' hr').2
      have dr'x := hG.ne_x1 hD hr'
      elem_contra K [x, o, z, l, r', m, p3]
    · have hmp3 : m ≠ p3 := fun h => hmC2 (h ▸ hp3)
      by_cases e1 : G.Adj z p1
      · by_cases e2 : G.Adj m p1
        · elem_contra K [x, o, p1, p2, p3, p4, z, m]
        · by_cases e3 : G.Adj z p2 <;> elem_contra K [x, o, p1, p2, p3, p4, z, m]
      · by_cases e2 : G.Adj m p2 <;> elem_contra K [x, o, p1, p2, p3, p4, z, m]

end ElemChoos.MR
