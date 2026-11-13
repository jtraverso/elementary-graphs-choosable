/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Step
public import Mathlib.Logic.Relation

/-!
# From a `D` to a strong homogeneous pair (Maffray–Reed, pp. 146–147)

After the growth procedure the outside vertices split into `S1` (see `C1` only), `S2` (see `C2`
only), `A` (see both) and `Z` (see neither). The vertices of `A` seeing all of `S1` form `A1`,
the others `A2`; `C1 ∪ S1 ∪ A1` and `C2 ∪ S2 ∪ A2` are cliques. Adding to `C1`, `C2` the
vertices of `S1 ∪ A1`, `S2 ∪ A2` reachable from `A` along edges between these two sets gives a
strong homogeneous pair. (The paper's shortest-path argument is an induction on reachability.)
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} (K : ECol G)

variable {W : Finset V} {x o p1 p2 p3 p4 : V}

set_option maxHeartbeats 40000000 in
include K in
/-- **A `D` yields a strong homogeneous pair.** -/
theorem exists_shp_of_D (hD : IsD G x o p1 p2 p3 p4) (hxW : x ∈ W) (hoW : o ∈ W)
    (hp1 : p1 ∈ W) (hp2 : p2 ∈ W) (hp3 : p3 ∈ W) (hp4 : p4 ∈ W) :
    ∃ C1 C2, SHP G W C1 C2 := by
  classical
  obtain ⟨C1, C2, hG, hfin⟩ := exists_final K hD hp1 hp2 hp3 hp4
  have hD' := hD
  obtain ⟨dxo, do2, d23, d34, d1o, d12, d13, d14, nx1, nx2, nx3, nx4, no3, no4, n24⟩ := hD'
  obtain ⟨q1, q2, q3, q4⟩ := hG.mem
  -- the four kinds of outside vertices
  let isS1 : V → Prop := fun v => v ∈ W ∧ v ∉ C1 ∧ v ∉ C2 ∧ (∀ u ∈ C1, G.Adj v u) ∧
    ∀ u ∈ C2, ¬ G.Adj v u
  let isS2 : V → Prop := fun v => v ∈ W ∧ v ∉ C1 ∧ v ∉ C2 ∧ (∀ u ∈ C2, G.Adj v u) ∧
    ∀ u ∈ C1, ¬ G.Adj v u
  let isA : V → Prop := fun v => v ∈ W ∧ v ∉ C1 ∧ v ∉ C2 ∧ (∀ u ∈ C1, G.Adj v u) ∧
    ∀ u ∈ C2, G.Adj v u
  let isZ : V → Prop := fun v => v ∈ W ∧ v ∉ C1 ∧ v ∉ C2 ∧ (∀ u ∈ C1, ¬ G.Adj v u) ∧
    ∀ u ∈ C2, ¬ G.Adj v u
  have classify : ∀ v ∈ W, v ∉ C1 → v ∉ C2 → isS1 v ∨ isS2 v ∨ isA v ∨ isZ v := by
    intro v hv h1 h2
    rcases hfin v hv h1 h2 with ⟨a1 | b1, a2 | b2⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hv, h1, h2, a1, a2⟩))
    · exact Or.inl ⟨hv, h1, h2, a1, b2⟩
    · exact Or.inr (Or.inl ⟨hv, h1, h2, a2, b1⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hv, h1, h2, b1, b2⟩))
  have oS1 : isS1 o := ⟨hoW, fun h => hG.ne_o1 h rfl, fun h => hG.ne_o2 hD h rfl,
    fun u hu => (hG.c1 u hu).1.symm, fun u hu h => (hG.c2 u hu).1 h.symm⟩
  have xZ : isZ x := ⟨hxW, fun h => hG.ne_x1 hD h rfl, fun h => hG.ne_x2 hD h rfl,
    fun u hu h => (hG.c1 u hu).2 h.symm, fun u hu h => (hG.c2 u hu).2 h.symm⟩
  -- `S1`, `S2` are cliques
  have S1clq : ∀ s t, isS1 s → isS1 t → s ≠ t → G.Adj s t := by
    rintro s t ⟨-, -, s2, s1c, s2c⟩ ⟨-, -, t2, t1c, t2c⟩ hst
    by_contra hna
    have a1 := s1c p1 q1
    have a2 := t1c p1 q1
    have a3 := s2c p3 q3
    have a4 := t2c p3 q3
    have e1 : s ≠ p3 := fun h => s2 (h ▸ q3)
    have e2 : t ≠ p3 := fun h => t2 (h ▸ q3)
    elem_contra K [p1, s, t, p3]
  have S2clq : ∀ s t, isS2 s → isS2 t → s ≠ t → G.Adj s t := by
    rintro s t ⟨-, s1, -, s2c, s1c⟩ ⟨-, t1, -, t2c, t1c⟩ hst
    by_contra hna
    have a1 := s2c p3 q3
    have a2 := t2c p3 q3
    have a3 := s1c p1 q1
    have a4 := t1c p1 q1
    have e1 : s ≠ p1 := fun h => s1 (h ▸ q1)
    have e2 : t ≠ p1 := fun h => t1 (h ▸ q1)
    elem_contra K [p3, s, t, p1]
  -- `Z` misses `A`
  have ZA : ∀ z a, isZ z → isA a → ¬ G.Adj z a := by
    rintro z a ⟨-, z1, z2, z1c, z2c⟩ ⟨-, -, -, a1c, a2c⟩ hza
    have b1 := a1c p2 q2
    have b2 := a2c p4 q4
    have b3 := z1c p2 q2
    have b4 := z2c p4 q4
    have e1 : z ≠ p2 := fun h => z1 (h ▸ q2)
    have e2 : z ≠ p4 := fun h => z2 (h ▸ q4)
    elem_contra K [a, z, p2, p4]
  -- no vertex of `A` misses a vertex of `S1` and a vertex of `S2`
  have AS : ∀ a b c, isA a → isS1 b → isS2 c → ¬ G.Adj a b → ¬ G.Adj a c → False := by
    rintro a b c ⟨-, -, -, a1c, a2c⟩ ⟨-, b1, b2, b1c, b2c⟩ ⟨-, c1, c2, c2c, c1c⟩ hab hac
    have f1 := a1c p1 q1
    have f2 := a1c p2 q2
    have f3 := a2c p3 q3
    have f4 := a2c p4 q4
    have f5 := b1c p1 q1
    have f6 := b1c p2 q2
    have f7 := b2c p3 q3
    have f8 := b2c p4 q4
    have f9 := c2c p3 q3
    have f10 := c2c p4 q4
    have f11 := c1c p1 q1
    have f12 := c1c p2 q2
    have e1 : b ≠ p3 := fun h => b2 (h ▸ q3)
    have e2 : b ≠ p4 := fun h => b2 (h ▸ q4)
    have e3 : c ≠ p1 := fun h => c1 (h ▸ q1)
    have e4 : c ≠ p2 := fun h => c1 (h ▸ q2)
    by_cases hbc : G.Adj b c
    · elem_contra K [b, c, p4, a, p2]
    · elem_contra K [a, b, c, p1, p2, p3, p4]
  let isA1 : V → Prop := fun v => isA v ∧ ∀ s, isS1 s → G.Adj v s
  let isA2 : V → Prop := fun v => isA v ∧ ¬ ∀ s, isS1 s → G.Adj v s
  have A1clq : ∀ a b, isA1 a → isA1 b → a ≠ b → G.Adj a b := by
    intro a b ha hb hab
    by_contra hna
    have h1 := ha.2 o oS1
    have h2 := hb.2 o oS1
    have h3 := ZA x a xZ ha.1
    have h4 := ZA x b xZ hb.1
    have h5 := ha.1.2.2.2.1 p1 q1
    have h6 := hb.1.2.2.2.1 p1 q1
    elem_contra K [o, a, b, x]
  -- the pyramid step of the paper, for `a` seeing `o` and `b` missing it
  have A2aux : ∀ a b, isA2 a → isA b → G.Adj a o → ¬ G.Adj b o → ¬ G.Adj a b → False := by
    intro a b ha hb hao hbo hna
    have ha' := ha.2
    push_neg at ha'
    obtain ⟨s, hs, has⟩ := ha'
    have hs1 := hs.2.2.2.1 p1 q1
    have hs3 := hs.2.2.2.2 p3 q3
    have ha1 := ha.1.2.2.2.1 p1 q1
    have ha3 := ha.1.2.2.2.2 p3 q3
    have hb1 := hb.2.2.2.1 p1 q1
    have hb3 := hb.2.2.2.2 p3 q3
    have hxa := ZA x a xZ ha.1
    have hxb := ZA x b xZ hb
    have hso : G.Adj s o := S1clq s o hs oS1 (fun h => has (h ▸ hao))
    have hsx : G.Adj s x := by
      by_contra hsx
      elem_contra K [o, x, s, a]
    have hsb : G.Adj s b := by
      by_contra hsb
      elem_contra K [p1, s, a, b]
    elem_contra K [o, p1, s, a, b, x]
  have A2clq : ∀ a b, isA2 a → isA2 b → a ≠ b → G.Adj a b := by
    intro a b ha hb hab
    by_contra hna
    have h3 := ZA x a xZ ha.1
    have h4 := ZA x b xZ hb.1
    have h5 := ha.1.2.2.2.1 p1 q1
    have h6 := hb.1.2.2.2.1 p1 q1
    have h7 := ha.1.2.2.2.2 p3 q3
    have h8 := hb.1.2.2.2.2 p3 q3
    by_cases hao : G.Adj a o <;> by_cases hbo : G.Adj b o
    · elem_contra K [o, a, b, x]
    · exact A2aux a b ha hb.1 hao hbo hna
    · exact A2aux b a hb ha.1 hbo hao (fun h => hna h.symm)
    · elem_contra K [p1, o, a, b]
  have A2S2 : ∀ a c, isA2 a → isS2 c → G.Adj a c := by
    intro a c ha hc
    by_contra hac
    have ha' := ha.2
    push_neg at ha'
    obtain ⟨s, hs, has⟩ := ha'
    exact AS a s c ha.1 hs hc has hac
  -- the two sides
  let Q1 : V → Prop := fun v => isS1 v ∨ isA1 v
  let Q2 : V → Prop := fun v => isS2 v ∨ isA2 v
  have Xclq : ∀ u v, (u ∈ C1 ∨ Q1 u) → (v ∈ C1 ∨ Q1 v) → u ≠ v → G.Adj u v := by
    intro u v hu hv huv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
    · exact hG.clq1 u hu v hv huv
    · exact (hv.2.2.2.1 u hu).symm
    · exact (hv.1.2.2.2.1 u hu).symm
    · exact hu.2.2.2.1 v hv
    · exact S1clq u v hu hv huv
    · exact (hv.2 u hu).symm
    · exact hu.1.2.2.2.1 v hv
    · exact hu.2 v hv
    · exact A1clq u v hu hv huv
  have Yclq : ∀ u v, (u ∈ C2 ∨ Q2 u) → (v ∈ C2 ∨ Q2 v) → u ≠ v → G.Adj u v := by
    intro u v hu hv huv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
    · exact hG.clq2 u hu v hv huv
    · exact (hv.2.2.2.1 u hu).symm
    · exact (hv.1.2.2.2.2 u hu).symm
    · exact hu.2.2.2.1 v hv
    · exact S2clq u v hu hv huv
    · exact (A2S2 v u hv hu).symm
    · exact hu.1.2.2.2.2 v hv
    · exact A2S2 u v hu hv
    · exact A2clq u v hu hv huv
  -- reachability from `A`
  let H : V → V → Prop := fun u v => G.Adj u v ∧ ((Q1 u ∧ Q2 v) ∨ (Q2 u ∧ Q1 v))
  have F7 : ∀ a v, isA a → Relation.ReflTransGen H a v → ∀ z, isZ z → ¬ G.Adj z v := by
    intro a v ha hav
    induction hav with
    | refl => exact fun z hz => ZA z a hz ha
    | @tail v w _ hvw ih =>
      intro z hz hzw
      have hzv := ih z hz
      obtain ⟨hvw', hq⟩ := hvw
      obtain ⟨hzW, hz1, hz2, hz1c, hz2c⟩ := hz
      have z1 := hz1c p1 q1
      have z2 := hz1c p2 q2
      have z3 := hz2c p3 q3
      have z4 := hz2c p4 q4
      rcases hq with ⟨hv1, hw2⟩ | ⟨hv2, hw1⟩
      · rcases hw2 with hwS | hwA
        · have w1 := hwS.2.2.2.2 p1 q1
          have w2 := hwS.2.2.2.2 p2 q2
          have w3 := hwS.2.2.2.1 p3 q3
          have w4 := hwS.2.2.2.1 p4 q4
          have ew1 : w ≠ p1 := fun h => hwS.2.1 (h ▸ q1)
          have ew2 : w ≠ p2 := fun h => hwS.2.1 (h ▸ q2)
          rcases hv1 with hvS | hvA
          · have v1 := hvS.2.2.2.1 p1 q1
            have v3 := hvS.2.2.2.2 p3 q3
            have ev3 : v ≠ p3 := fun h => hvS.2.2.1 (h ▸ q3)
            have ez3 : z ≠ p3 := fun h => hz2 (h ▸ q3)
            elem_contra K [w, z, v, p3]
          · have vo := hvA.2 o oS1
            have v2 := hvA.1.2.2.2.1 p2 q2
            have v3 := hvA.1.2.2.2.2 p3 q3
            have vx := ZA x v xZ hvA.1
            by_cases hwo : G.Adj w o
            · have hwx : G.Adj w x := by
                by_contra hwx
                elem_contra K [o, p1, w, x]
              have v4 := hvA.1.2.2.2.2 p4 q4
              elem_contra K [o, v, w, x, p2, p4]
            · have hwx : ¬ G.Adj w x := by
                intro hwx
                elem_contra K [w, x, o, p2, p3]
              have hzo : ¬ G.Adj z o := by
                intro hzo
                elem_contra K [z, o, p2, p3, w]
              have hzx : ¬ G.Adj z x := by
                intro hzx
                elem_contra K [z, x, o, v, w]
              elem_contra K [v, x, o, p2, p3, w, z]
        · exact ZA z w ⟨hzW, hz1, hz2, hz1c, hz2c⟩ hwA.1 hzw
      · rcases hw1 with hwS | hwA
        · have w1 := hwS.2.2.2.1 p1 q1
          have w2 := hwS.2.2.2.1 p2 q2
          have w4 := hwS.2.2.2.2 p4 q4
          have w3 := hwS.2.2.2.2 p3 q3
          have ew4 : w ≠ p4 := fun h => hwS.2.2.1 (h ▸ q4)
          rcases hv2 with hvS | hvA
          · have v3 := hvS.2.2.2.1 p3 q3
            have v1 := hvS.2.2.2.2 p1 q1
            have ev1 : v ≠ p1 := fun h => hvS.2.1 (h ▸ q1)
            have ez1 : z ≠ p1 := fun h => hz1 (h ▸ q1)
            elem_contra K [w, z, v, p1]
          · have hvA' := hvA.2
            push_neg at hvA'
            obtain ⟨t, ht, hvt⟩ := hvA'
            have v1 := hvA.1.2.2.2.1 p1 q1
            have v2 := hvA.1.2.2.2.1 p2 q2
            have v4 := hvA.1.2.2.2.2 p4 q4
            have t1 := ht.2.2.2.1 p1 q1
            have t2 := ht.2.2.2.1 p2 q2
            have t4 := ht.2.2.2.2 p4 q4
            have et4 : t ≠ p4 := fun h => ht.2.2.1 (h ▸ q4)
            have hwt : G.Adj w t := S1clq w t hwS ht (fun h => hvt (h ▸ hvw'))
            have hzt : G.Adj z t := by
              by_contra hzt
              elem_contra K [w, v, t, z]
            elem_contra K [p1, p2, p4, v, w, t, z]
        · exact ZA z w ⟨hzW, hz1, hz2, hz1c, hz2c⟩ hwA.1 hzw
  let inT : V → Prop := fun v => ∃ a, isA a ∧ Relation.ReflTransGen H a v
  set C1' := C1 ∪ W.filter (fun v => Q1 v ∧ inT v) with hC1'
  set C2' := C2 ∪ W.filter (fun v => Q2 v ∧ inT v) with hC2'
  have mem1 : ∀ v, v ∈ C1' ↔ v ∈ C1 ∨ (v ∈ W ∧ Q1 v ∧ inT v) := fun v => by
    rw [hC1', mem_union, mem_filter]
  have mem2 : ∀ v, v ∈ C2' ↔ v ∈ C2 ∨ (v ∈ W ∧ Q2 v ∧ inT v) := fun v => by
    rw [hC2', mem_union, mem_filter]
  have Q1W : ∀ v, Q1 v → v ∈ W ∧ v ∉ C1 ∧ v ∉ C2 := by
    rintro v (h | h)
    · exact ⟨h.1, h.2.1, h.2.2.1⟩
    · exact ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩
  have Q2W : ∀ v, Q2 v → v ∈ W ∧ v ∉ C1 ∧ v ∉ C2 := by
    rintro v (h | h)
    · exact ⟨h.1, h.2.1, h.2.2.1⟩
    · exact ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩
  have Q12 : ∀ v, Q1 v → Q2 v → False := by
    rintro v (h | h) (h' | h')
    · exact h'.2.2.2.2 p1 q1 (h.2.2.2.1 p1 q1)
    · exact h.2.2.2.2 p3 q3 (h'.1.2.2.2.2 p3 q3)
    · exact h'.2.2.2.2 p1 q1 (h.1.2.2.2.1 p1 q1)
    · exact h'.2 h.2
  refine ⟨C1', C2', ⟨?_, ?_, ?_, ?_, ?_, ⟨p1, (mem1 p1).2 (Or.inl q1), p3,
    (mem2 p3).2 (Or.inl q3), d13⟩, ?_, ?_⟩⟩
  · intro v hv
    rcases (mem1 v).1 hv with h | h
    · exact hG.sub1 h
    · exact h.1
  · intro v hv
    rcases (mem2 v).1 hv with h | h
    · exact hG.sub2 h
    · exact h.1
  · rw [disjoint_left]
    intro v hv1 hv2
    rcases (mem1 v).1 hv1 with h1 | h1 <;> rcases (mem2 v).1 hv2 with h2 | h2
    · exact disjoint_left.1 hG.disj h1 h2
    · exact (Q2W v h2.2.1).2.1 h1
    · exact (Q1W v h1.2.1).2.2 h2
    · exact Q12 v h1.2.1 h2.2.1
  · intro u hu v hv huv
    have a : ∀ w ∈ C1', w ∈ C1 ∨ Q1 w := fun w hw => by
      rcases (mem1 w).1 hw with h | h
      · exact Or.inl h
      · exact Or.inr h.2.1
    exact Xclq u v (a u hu) (a v hv) huv
  · intro u hu v hv huv
    have a : ∀ w ∈ C2', w ∈ C2 ∨ Q2 w := fun w hw => by
      rcases (mem2 w).1 hw with h | h
      · exact Or.inl h
      · exact Or.inr h.2.1
    exact Yclq u v (a u hu) (a v hv) huv
  · have h1 : #({p1, p2} : Finset V) ≤ #C1' :=
      card_le_card (by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact (mem1 _).2 (Or.inl q1)
        · exact (mem1 _).2 (Or.inl q2))
    have h2 : #({p3, p4} : Finset V) ≤ #C2' :=
      card_le_card (by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact (mem2 _).2 (Or.inl q3)
        · exact (mem2 _).2 (Or.inl q4))
    rw [card_pair (G.ne_of_adj d12)] at h1
    rw [card_pair (G.ne_of_adj d34)] at h2
    omega
  · intro v hv hv1 hv2
    have hvC1 : v ∉ C1 := fun h => hv1 ((mem1 v).2 (Or.inl h))
    have hvC2 : v ∉ C2 := fun h => hv2 ((mem2 v).2 (Or.inl h))
    rcases classify v hv hvC1 hvC2 with hS | hS | hA | hZ
    · -- `v ∈ S1`, not reachable
      have hT : ¬ inT v := fun hT => hv1 ((mem1 v).2 (Or.inr ⟨hv, Or.inl hS, hT⟩))
      refine Or.inr ⟨fun u hu hvu => ?_, Or.inl fun u hu => ?_⟩
      · rcases (mem2 u).1 hu with h | ⟨-, hQ, ⟨a, ha, hau⟩⟩
        · exact hS.2.2.2.2 u h hvu
        · exact hT ⟨a, ha, hau.tail ⟨hvu.symm, Or.inr ⟨hQ, Or.inl hS⟩⟩⟩
      · have huv : u ≠ v := fun h => hv1 (h ▸ hu)
        exact Xclq v u (Or.inr (Or.inl hS)) (by
          rcases (mem1 u).1 hu with h | h
          · exact Or.inl h
          · exact Or.inr h.2.1) (Ne.symm huv)
    · -- `v ∈ S2`, not reachable
      have hT : ¬ inT v := fun hT => hv2 ((mem2 v).2 (Or.inr ⟨hv, Or.inl hS, hT⟩))
      refine Or.inl ⟨fun u hu hvu => ?_, Or.inl fun u hu => ?_⟩
      · rcases (mem1 u).1 hu with h | ⟨-, hQ, ⟨a, ha, hau⟩⟩
        · exact hS.2.2.2.2 u h hvu
        · exact hT ⟨a, ha, hau.tail ⟨hvu.symm, Or.inl ⟨hQ, Or.inl hS⟩⟩⟩
      · have huv : u ≠ v := fun h => hv2 (h ▸ hu)
        exact Yclq v u (Or.inr (Or.inl hS)) (by
          rcases (mem2 u).1 hu with h | h
          · exact Or.inl h
          · exact Or.inr h.2.1) (Ne.symm huv)
    · -- `v ∈ A` is reachable from itself
      exfalso
      by_cases h1 : ∀ s, isS1 s → G.Adj v s
      · exact hv1 ((mem1 v).2
          (Or.inr ⟨hv, Or.inr ⟨hA, h1⟩, ⟨v, hA, Relation.ReflTransGen.refl⟩⟩))
      · exact hv2 ((mem2 v).2
          (Or.inr ⟨hv, Or.inr ⟨hA, h1⟩, ⟨v, hA, Relation.ReflTransGen.refl⟩⟩))
    · -- `v ∈ Z` misses everything
      refine Or.inl ⟨fun u hu hvu => ?_, Or.inr fun u hu hvu => ?_⟩
      · rcases (mem1 u).1 hu with h | ⟨-, -, ⟨a, ha, hau⟩⟩
        · exact hZ.2.2.2.1 u h hvu
        · exact F7 a u ha hau v hZ hvu
      · rcases (mem2 u).1 hu with h | ⟨-, -, ⟨a, ha, hau⟩⟩
        · exact hZ.2.2.2.2 u h hvu
        · exact F7 a u ha hau v hZ hvu

end ElemChoos.MR
