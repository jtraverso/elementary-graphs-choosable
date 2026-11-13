/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import ElemChoos.Main
public import ElemChoos.MR.Final

/-!
# Proofs of the statements in `ElemChoosChallenge.lean`

The definitions `ElemChoos.IsAugLineGraphRep`, `ElemChoos.IsElementary`, `ElemChoos.IsChoosable`,
`ElemChoos.choiceNumber` and the theorems `ElemChoos.choosable_of_rep`,
`ElemChoos.chromaticChoosable_of_rep`, `ElemChoos.isElementary_of_rep`,
`ElemChoos.rep_of_lineGraph`, `ElemChoos.rep_of_cobipartite` are declared, with the statements
of the challenge, in the library `ElemChoos`:

* `ElemChoos/Deficiency.lean`: Hall's theorem for list colourings and the Deficiency Lemma 2.5;
* `ElemChoos/Augment.lean`: augments and the Saturation Lemma 3.6 (without Kőnig's theorem);
* `ElemChoos/MainStep.lean`, `ElemChoos/Prop37.lean`: Proposition 3.7 (every augment of a
  minimal counterexample is complete);
* `ElemChoos/Model.lean`: the representation, the minimal-counterexample induction and the
  line-graph case through Galvin's theorem `GalvinMultigraph.galvin_of_degree_bound`
  (jtraverso/galvin-dinitz, PALOMAR-2026-10-18-000029 v2, lake dependency);
* `ElemChoos/Main.lean`: elementary graphs, choice number, `ch = χ = ω`;
* `ElemChoos/MR/*.lean`: the Maffray–Reed theorem (every elementary graph is an augmentation of a
  bipartite-multigraph line graph), `ElemChoos.rep_of_isElementary`, and Theorems 3.4 and 1.1
  for all elementary graphs (`ElemChoos/MR/Final.lean`).
-/
