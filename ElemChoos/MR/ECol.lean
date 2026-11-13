/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card

/-!
# Elementary colourings

An elementary colouring of `G` as a `0/1`-valued symmetric function `c` on pairs of vertices such
that the two edges of every induced `P3` get different values (`c u v + c v w = 1`), and two small
lemmas used by the configuration tactic `elem_contra` (`ElemChoos/MR/Tactic.lean`).
-/

@[expose] public section

namespace ElemChoos.MR

variable {V : Type*}

/-- An elementary colouring of `G`, with values `0` (blue) and `1` (red). -/
structure ECol (G : SimpleGraph V) where
  /-- The colour of the pair `{u, v}`. -/
  c : V → V → ℕ
  le_one : ∀ u v, c u v ≤ 1
  symm : ∀ u v, c u v = c v u
  p3 : ∀ u v w, G.Adj u v → G.Adj v w → u ≠ w → ¬ G.Adj u w → c u v + c v w = 1

/-- Two vertices with different adjacency to a third one are distinct. -/
theorem ne_of_adj_nadj {G : SimpleGraph V} {u w x : V} (h1 : G.Adj u x) (h2 : ¬ G.Adj w x) :
    u ≠ w :=
  fun h => h2 (h ▸ h1)

/-- An element of a set and a non-element are distinct. -/
theorem ne_of_mem_nmem {α γ : Type*} [Membership α γ] {s : γ} {a b : α} (ha : a ∈ s) (hb : b ∉ s) :
    a ≠ b :=
  fun h => hb (h ▸ ha)

/-- Non-adjacency is symmetric. -/
theorem nadj_symm {G : SimpleGraph V} {u w : V} (h : ¬ G.Adj w u) : ¬ G.Adj u w :=
  fun h' => h h'.symm

end ElemChoos.MR
