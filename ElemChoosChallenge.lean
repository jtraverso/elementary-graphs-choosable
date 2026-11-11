/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Elementary graphs are chromatic-choosable (for the Maffray–Reed class)

Narayanan N, Nandana K. Vasudevan, K. Somasundaram, *Elementary graphs are chromatic-choosable*,
arXiv:2610.16258 (2026), Theorem 1.1: every elementary graph `G` satisfies `ch(G) = χ(G) = ω(G)`.

By the theorem of Maffray and Reed (JCTB 75 (1999)), the elementary graphs are exactly the
augmentations of line graphs of bipartite multigraphs; the paper's proof starts from that
representation. Here the representation is `IsAugLineGraphRep G a b hubA hubB`: the vertex `v` of
`G` is the edge `{a v, b v}` of a bipartite multigraph `H′` (`a v ∈ A`, `b v ∈ B`); adjacent
vertices share an end; two vertices sharing an end are adjacent unless they share exactly one end
and that end is a *hub*; a hub has at most two distinct neighbours in `H′`; and no edge of `H′`
joins two hubs. (The augment replacing a flat edge `xy` is the star of the hub `c` of the path
`x = p_X c`, `y = c p_Y`, after multiplying its two edges.)

* `ElemChoos.choosable_of_rep` (Theorem 3.4): clique number at most `k` implies `k`-choosability.
* `ElemChoos.chromaticChoosable_of_rep` (Theorem 1.1): `ch(G) = χ(G) = ω(G)`.
* `ElemChoos.isElementary_of_rep`: every graph of the class is elementary.
* `ElemChoos.rep_of_lineGraph`, `ElemChoos.rep_of_cobipartite`: line graphs of bipartite
  multigraphs and complements of bipartite graphs belong to the class.

Not formalized: the "only if" direction of Maffray–Reed (an elementary graph is such an
augmentation).
-/

@[expose] public section

namespace ElemChoos

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

/-- `G` is *elementary* (Chvátal–Sbihi): its edges can be coloured red and blue (`red` is a
symmetric relation; blue = not red) so that the two edges of every induced path on three vertices
get different colours. -/
def IsElementary (G : SimpleGraph V) : Prop :=
  ∃ red : V → V → Prop, (∀ u v, red u v ↔ red v u) ∧
    ∀ u v w, G.Adj u v → G.Adj v w → u ≠ w → ¬ G.Adj u w → (red u v ↔ ¬ red v w)

/-- `G` is `k`-choosable: every assignment of lists of at least `k` natural numbers admits a
proper colouring choosing every colour from its list. -/
def IsChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) → ∃ f : G.Coloring ℕ, ∀ v, f v ∈ L v

/-- The choice number (list chromatic number), `⊤` if no `k` works. -/
noncomputable def choiceNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨅ k ∈ Set.ofPred (IsChoosable G), (k : ℕ∞)

/-- **Theorem 3.4 for augmentations of line graphs of bipartite multigraphs.** If the clique
number is at most `k`, every assignment of lists of at least `k` colours admits a proper
list colouring. -/
theorem choosable_of_rep [Finite V] {G : SimpleGraph V} {a : V → A} {b : V → B} {hubA : Set A}
    {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) {k : ℕ} (hω : G.CliqueFree (k + 1))
    (L : V → Finset C) (hL : ∀ v, k ≤ (L v).card) : ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  sorry

/-- **Theorem 1.1 for the Maffray–Reed class.** Every augmentation of the line graph of a
bipartite multigraph is chromatic-choosable, with `ch(G) = χ(G) = ω(G)`. -/
theorem chromaticChoosable_of_rep [Finite V] {G : SimpleGraph V} {a : V → A} {b : V → B}
    {hubA : Set A} {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) :
    choiceNumber G = G.chromaticNumber ∧ G.chromaticNumber = G.cliqueNum := by
  sorry

/-- Every augmentation of the line graph of a bipartite multigraph is elementary. -/
theorem isElementary_of_rep {G : SimpleGraph V} {a : V → A} {b : V → B} {hubA : Set A}
    {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) : IsElementary G := by
  sorry

/-- Line graphs of bipartite multigraphs belong to the class (no hubs). -/
theorem rep_of_lineGraph (G : SimpleGraph V) (a : V → A) (b : V → B)
    (h : ∀ u v, G.Adj u v ↔ u ≠ v ∧ (a u = a v ∨ b u = b v)) :
    IsAugLineGraphRep G a b ∅ ∅ := by
  sorry

/-- Complements of bipartite graphs (two cliques with arbitrary edges between them) belong to
the class: a single hub. -/
theorem rep_of_cobipartite (G : SimpleGraph V) (side : V → Bool)
    (h : ∀ u v, u ≠ v → side u = side v → G.Adj u v) :
    IsAugLineGraphRep G side (fun _ => ()) ∅ Set.univ := by
  sorry

end ElemChoos
