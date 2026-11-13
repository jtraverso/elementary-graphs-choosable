# Elementary graphs are chromatic-choosable, with the Maffray–Reed characterization, in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

Narayanan N, Nandana K. Vasudevan and K. Somasundaram (*Elementary graphs are
chromatic-choosable*, arXiv:2610.16258, 2026) prove that every elementary graph `G` satisfies
`ch(G) = χ(G) = ω(G)`. A graph is elementary if its edges can be coloured red and blue so that
every induced path on three vertices has one red and one blue edge. The proof starts from the
theorem of Maffray and Reed (1999): elementary graphs are exactly the augmentations of line
graphs of bipartite multigraphs. This package formalizes both: the Maffray–Reed characterization
(both directions) and the paper's proof of `ch(G) = χ(G) = ω(G)`, so the main theorems hold for
every finite elementary graph.

## Statements (`ElemChoosChallenge.lean`, namespace `ElemChoos`)

`IsAugLineGraphRep G a b hubA hubB` says that `G` is such an augmentation. Vertex `v` of `G` is
the edge `{a v, b v}` of a bipartite multigraph `H′`. Adjacent vertices share an end. Two vertices
that share an end are adjacent unless they share exactly one end and that end is a hub. A hub has
at most two distinct neighbours in `H′`, and no edge of `H′` joins two hubs.

```lean
theorem choosable_of_rep [Finite V] {G : SimpleGraph V} {a : V → A} {b : V → B} {hubA : Set A}
    {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) {k : ℕ} (hω : G.CliqueFree (k + 1))
    (L : V → Finset C) (hL : ∀ v, k ≤ (L v).card) : ∃ f : G.Coloring C, ∀ v, f v ∈ L v

theorem chromaticChoosable_of_rep [Finite V] {G : SimpleGraph V} {a : V → A} {b : V → B}
    {hubA : Set A} {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) :
    choiceNumber G = G.chromaticNumber ∧ G.chromaticNumber = G.cliqueNum

theorem isElementary_of_rep ... (hG : IsAugLineGraphRep G a b hubA hubB) : IsElementary G
theorem rep_of_lineGraph ...   -- line graphs of bipartite multigraphs are in the class
theorem rep_of_cobipartite ... -- complements of bipartite graphs are in the class

-- Maffray–Reed (1999), Theorem 2, (i) ⇒ (iii)
theorem rep_of_isElementary [Finite V] {G : SimpleGraph V} (hG : IsElementary G) :
    ∃ (a b : V → ℕ) (hubA hubB : Set ℕ), IsAugLineGraphRep G a b hubA hubB

-- Theorems 3.4 and 1.1
theorem choosable_of_isElementary [Finite V] {G : SimpleGraph V} (hG : IsElementary G) {k : ℕ}
    (hω : G.CliqueFree (k + 1)) (L : V → Finset C) (hL : ∀ v, k ≤ (L v).card) :
    ∃ f : G.Coloring C, ∀ v, f v ∈ L v
theorem chromaticChoosable_of_isElementary [Finite V] {G : SimpleGraph V} (hG : IsElementary G) :
    choiceNumber G = G.chromaticNumber ∧ G.chromaticNumber = G.cliqueNum
```

## Proof (`ElemChoos/`)

* `Deficiency.lean`: Hall's theorem for list colourings (Mathlib's Hall) and the Deficiency
  Lemma 2.5 for `K(X, Y) − M`.
* `Augment.lean`: augments of a minimal counterexample and the Saturation Lemma 3.6. Here the
  matching property is proved without Kőnig's theorem. Missing pairs are added one at a time, and
  a lattice argument on two critical cliques does the rest.
* `MainStep.lean`, `Prop37.lean`: Proposition 3.7, every augment of a minimal counterexample is
  complete.
* `Model.lean`: the representation and the minimal-counterexample induction (on vertices, then on
  missing pairs). With no missing pair the graph is the line graph of a bipartite multigraph, and
  Galvin's theorem applies.
* `Main.lean`: elementary graphs, the choice number, and `ch = χ = ω`.
* `MR/`: the Maffray–Reed characterization. `Rep`, `Easy`: representations on vertex sets, twins,
  disjoint unions, and the case without a bend (red and blue classes are the ends; replaces MR
  Theorems 3–4). `Flat`, `Aug`, `AugMain`: the normal form of flat edges (repairs the p. 143
  remark) and augmenting back. `Bend`: twin-free with a bend gives an induced gem or 4-wheel.
  `Gem`, `Wheel`: MR Theorem 5. `Growth`, `Claim2`, `Step`, `AStep`: the growth procedure from an
  induced `D`, claims (1)–(2) (with Case 3 of claim (2) repaired) and the A-components. `Final`:
  the induction by compression of strong homogeneous pairs. Every forbidden-subgraph step is a
  parity argument on a fixed elementary colouring. Details in `NOTES.md`.

Galvin's theorem for bipartite multigraphs (`GalvinMultigraph.galvin_of_degree_bound`) comes from
PALOMAR-2026-10-18-000029 v2 (jtraverso/galvin-dinitz @ 84dcda4) as a pinned lake dependency.
No code is copied from it.

## Building

Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3`:

```
lake exe cache get
lake build
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
