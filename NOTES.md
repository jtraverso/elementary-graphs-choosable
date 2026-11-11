# Elementary graphs are chromatic-choosable — formalization notes

Source: Narayanan N, Nandana K. Vasudevan, K. Somasundaram, *Elementary graphs are
chromatic-choosable*, arXiv:2610.16258v1 (12 Oct 2026), 13 pp. Downloaded copy (data only):
`C:\lean\elementary_choosable_downloads\paper.pdf` (+ `paper.txt`, `paper.html`).

## Definitions (paper, §1 and §3)

* **List assignment / L-colouring / k-choosable / choice number ch(G)**: standard (ERT, Vizing).
* **Chromatic-choosable**: ch(G) = χ(G).
* **Elementary** (Chvátal–Sbihi): the edges can be coloured red/blue so that every *induced* P3
  has one red and one blue edge.
* **Flat edge**: an edge in no triangle.
* **Augmentation** (Maffray–Reed, Def. 3.1): replace a flat edge xy of G0 by a cobipartite graph B
  on two nonempty cliques X, Y with at least one X–Y edge, X complete to N(x)\{y}, Y complete to
  N(y)\{x}; do this for pairwise vertex-disjoint flat edges.
* **Theorem 3.2 (Maffray–Reed 1999, JCTB 75, 134–156)**: G elementary ⇔ G is an augmentation of the
  line graph of a bipartite multigraph.

## Main statement

**Theorem 1.1.** Every elementary graph G satisfies ch(G) = χ(G) = ω(G).
Proved as **Theorem 3.4**: for every k ≥ 1, every elementary graph with ω ≤ k is k-choosable.

## The paper's proof (map to formal lemmas)

| Paper | Content | Formal |
|---|---|---|
| Lemma 2.1 / Cor 2.2 | Hall: no L-colouring ⇒ deficient set | `ElemChoos.exists_deficient` (Mathlib Hall `Finset.all_card_le_biUnion_card_iff_exists_injective`) |
| Lemma 2.3 | ω(cobipartite) = |X|+|Y|−ν (Kőnig) | **not needed** (see "Saturation without Kőnig") |
| Lemma 2.5 + Cor 2.6 | Deficiency lemma for K(X,Y)−M | `ElemChoos.deficiency` |
| Def 3.1, Thm 3.2, Lemma 3.3 | MR representation; N_X, N_Y cliques, complete to their side, disjoint | `ElemChoos.IsAugLineGraphRep` (edge model) + `ElemChoos.false_of_hubA` (builds `Aug`) |
| Lemma 3.5 | minimal counterexample (fewest vertices, most edges) | nested strong induction in `ElemChoos.core` (|W|, then # missing line-graph pairs) |
| Lemma 3.6 (a),(b) | saturation: missing X–Y pairs form a matching M, k = μ+r+s | `ElemChoos.Aug.uniqMiss`, `Aug.uniqMiss'`, `Aug.k_eq` |
| Lemma 3.6 (c),(d) | N_X ≠ ∅, r,s ≥ 1, |N_X| ≤ s, |N_Y| ≤ r | replaced by a case split U = ∅ ∨ V = ∅ (Cor 2.6(a)); `|N_X| ≤ s` from the clique X ∪ N_X |
| Prop 3.7 | every augment of the counterexample is complete | `ElemChoos.Aug.complete` (main step `Aug.main_step`) |
| Lemma 3.8 + Galvin | all augments complete ⇒ G = L(H′), Δ(H′) ≤ ω | `ElemChoos.colours_of_no_missing`, via `GalvinMultigraph.galvin_of_degree_bound` (galvin-dinitz @ 84dcda4) |

### Edge model used in Lean (the class produced by Maffray–Reed)

`IsAugLineGraphRep G a b hubA hubB` (a : V → A, b : V → B: vertex v of G is the edge a(v)b(v) of a
bipartite multigraph H′):
1. G ≤ L(H′): adjacent vertices share an end;
2. a pair sharing an end but non-adjacent in G shares exactly one end and that end is a *hub*;
3. a hub has at most two distinct neighbours in H′ (the two classes X, Y of the augment);
4. no edge of H′ joins two hubs (augmented flat edges are pairwise vertex-disjoint).

This is exactly the normalized MR representation of Lemma 3.3 + Lemma 3.8 (multiply e_X, e_Y by
|X|, |Y|; the augment at the degree-2 vertex c of H becomes the star of the hub c in H′ with some
X–Y pairs deleted). It is closed under induced subgraphs and under re-adding deleted X–Y pairs,
which is all the minimal-counterexample argument needs (the paper uses the "if" direction of MR
only for that). The condition "at least one X–Y edge" is dropped (more general; harmless).
We prove `isElementary_of_rep` (every graph of the class is elementary: colour a pair red iff it
shares its A-end, parallel pairs at an A-hub blue), so the formal theorem is about a subclass of
elementary graphs that by MR is all of them.

## Critical check of the proof

* Lemma 2.5 (Deficiency): correct. Case 1 uses an injection of the matched part of W into X0 (resp.
  Y0); Case 2 needs |W| ≤ |X|+|Y| (true). Induction is on μ with X, Y, R generalized. OK.
* Lemma 3.6(a) as written uses Lemma 2.3, i.e. **Kőnig's theorem** (ω(J⁺) = ω(J) after adding all
  non-matching missing pairs needs ν(F) = τ(F)). Correct, but avoidable: we add **one** missing
  pair xy at a time. Edge-maximality gives, for every missing pair xy, a (k+1)-clique of G + xy
  through x, y, inside J (Lemma 3.3(c)). If x has two missing partners y, y′, take the two cliques
  K1 ∋ x,y and K2 ∋ x,y′; the "lattice" sets K∧ = X∩(K1∪K2) ∪ Y∩K1∩K2 (a clique of G) and
  K∨ = X∩K1∩K2 ∪ Y∩(K1∪K2) (minus x a clique of G) have |K∧|+|K∨| = |K1|+|K2| ≥ 2k+2, but
  |K∧| ≤ k and |K∨| ≤ k+1. So missing pairs form a matching; the same critical clique for a pair of
  M gives k ≤ μ+r+s (it contains ≤ one vertex of each other pair), and X ∪ V gives ≥.
* Lemma 3.6(c) (N_X ≠ ∅) is only used to get r, s ≥ 1; if U = ∅ or V = ∅ we colour G − J by
  minimality and extend by the Deficiency Lemma (lists L \ f(N_X) have size ≥ k − s = |X| because
  X ∪ N_X is a clique). No gap, just a simplification.
* Prop 3.7: (3), (4) |S| ≥ k − m_X, (5), (B1), (B2), (C1), (C2) and the final count all check
  (verified line by line; arithmetic done in ℤ). The WLOG (3) is a genuine X↔Y symmetry.
* Proof of Lemma 3.5 is "Elementary my dear Watson!"; it is immediate (G+ elementary with ω ≤ k and
  more edges is k-choosable by maximality, hence so is its spanning subgraph G).
* **No mathematical gap found.** The only external input not formalized is the "only if"
  direction of Maffray–Reed (elementary ⇒ augmentation of a bipartite-multigraph line graph).

## The wall: Maffray–Reed

Theorem 3.2 ("only if") is a structure theorem with its own multi-page proof (JCTB 75 (1999)),
not available in Mathlib or the registry. It is not a consequence of anything formalized here (the
naive "red classes are cliques" argument fails: red paths of length 3 need not close). It is a
separate formalization project. The Lean development therefore proves the theorem for exactly the
class MR produces, and records the reduction.

## Status (2026-11-11)

All modules compile (lean v4.35.0-rc3, Mathlib c55e6e7, galvin-dinitz @ 84dcda4); no sorry;
axioms propext, Classical.choice, Quot.sound; Challenge and Solution statements and definitions
identical under `pp.all`. Proved statements: `ElemChoos.choosable_of_rep`,
`chromaticChoosable_of_rep`, `isElementary_of_rep`, `rep_of_lineGraph`, `rep_of_cobipartite`.
