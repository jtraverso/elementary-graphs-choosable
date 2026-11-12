/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.Basic

/-!
# Bends force a gem or a 4-wheel

A *bend* of an elementary colouring is a triangle `u v w` with `c u v = c v w ≠ c u w`. In a
twin-free graph, a bend yields an induced gem or 4-wheel. (Together with `rep_of_noBend` this
replaces Theorems 3 and 4 of Maffray–Reed: a twin-free elementary graph with no gem and no
4-wheel is the line graph of a bipartite multigraph.)
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} (K : ECol G)

/-- A gem or a 4-wheel inside `W`. -/
def GemOrWheelIn (G : SimpleGraph V) (W : Finset V) : Prop :=
  ∃ p1 ∈ W, ∃ p2 ∈ W, ∃ p3 ∈ W, ∃ p4 ∈ W, ∃ q ∈ W,
    IsGem G p1 p2 p3 p4 q ∨ IsWheel G p1 p2 p3 p4 q

theorem gemOrWheel_of_bend_aux {W : Finset V} (htf : TwinFreeOn G W) {u v w z : V}
    (hu : u ∈ W) (hv : v ∈ W) (hw : w ∈ W) (hz : z ∈ W)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hc : K.c u v = K.c v w) (hc' : K.c u w ≠ K.c u v)
    (hzu : G.Adj z u) (hzw : ¬ G.Adj z w) (hzw' : z ≠ w) : GemOrWheelIn G W := by
  have hzv : G.Adj z v := by
    by_contra hzv
    elem_contra K [u, v, w, z]
  obtain ⟨y, hy, hyu, hyv, hy'⟩ := htf u hu v hv (G.ne_of_adj huv) huv
  have hzv' : z ≠ v := G.ne_of_adj hzv
  have hzu' : z ≠ u := G.ne_of_adj hzu
  by_cases hyu' : G.Adj y u
  · have hyv' : ¬ G.Adj y v := fun h => hy' ⟨fun _ => h, fun _ => hyu'⟩
    have hyw : G.Adj y w := by
      by_contra hyw
      have hyw' : y ≠ w := fun h => hyv' (h ▸ hvw.symm)
      elem_contra K [u, v, w, y]
    have hyz : y ≠ z := fun h => hyv' (h ▸ hzv)
    have hyw' : y ≠ w := G.ne_of_adj hyw
    by_cases hyz' : G.Adj y z
    · exact ⟨y, hy, z, hz, v, hv, w, hw, u, hu, Or.inr
        ⟨hyz', hzv, hvw, hyw.symm, hyv', hzw, hyv, hzw', hyu'.symm, hzu.symm, huv, huw⟩⟩
    · exact ⟨y, hy, w, hw, v, hv, z, hz, u, hu, Or.inl
        ⟨hyw, hvw.symm, hzv.symm, hyv', hyz', fun h => hzw h.symm, hyu'.symm, huw, huv,
          hzu.symm⟩⟩
  · have hyv' : G.Adj y v := by
      by_contra h
      exact hy' ⟨fun h' => absurd h' hyu', fun h' => absurd h' h⟩
    have hyz : G.Adj y z := by
      by_contra hyz
      have hyz' : y ≠ z := fun h => hyu' (h ▸ hzu)
      have hzw'' : z ≠ w := hzw'
      elem_contra K [u, v, w, z, y]
    have hyw' : y ≠ w := fun h => hyu' (h ▸ huw.symm)
    by_cases hyw : G.Adj y w
    · exact ⟨y, hy, z, hz, u, hu, w, hw, v, hv, Or.inr
        ⟨hyz, hzu, huw, hyw.symm, hyu', hzw, hyu, hzw', hyv'.symm, hzv.symm, huv.symm, hvw⟩⟩
    · exact ⟨y, hy, z, hz, u, hu, w, hw, v, hv, Or.inl
        ⟨hyz, hzu, huw, hyu', hyw, hzw, hyv'.symm, hzv.symm, huv.symm, hvw⟩⟩

/-- **Bend lemma.** In a twin-free set, a bend yields an induced gem or 4-wheel. -/
theorem gemOrWheel_of_bend {W : Finset V} (htf : TwinFreeOn G W) {u v w : V}
    (hu : u ∈ W) (hv : v ∈ W) (hw : w ∈ W)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hc : K.c u v = K.c v w) (hc' : K.c u w ≠ K.c u v) : GemOrWheelIn G W := by
  obtain ⟨z, hz, hzu, hzw, hz'⟩ := htf u hu w hw (G.ne_of_adj huw) huw
  by_cases hzu' : G.Adj z u
  · have hzw' : ¬ G.Adj z w := fun h => hz' ⟨fun _ => h, fun _ => hzu'⟩
    exact gemOrWheel_of_bend_aux K htf hu hv hw hz huv hvw huw hc hc' hzu' hzw' hzw
  · have hzw' : G.Adj z w := by
      by_contra h
      exact hz' ⟨fun h' => absurd h' hzu', fun h' => absurd h' h⟩
    refine gemOrWheel_of_bend_aux K htf hw hv hu hz hvw.symm huv.symm huw.symm
      (by rw [K.symm w v, K.symm v u, hc]) ?_ hzw' hzu' hzu
    rw [K.symm w u, K.symm w v, ← hc]
    exact hc'

end ElemChoos.MR
