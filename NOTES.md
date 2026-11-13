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

## Maffray–Reed "only if" (elementary ⇒ augmentation): planning, 2026-11-11

### Source access
* doi:10.1006/jctb.1998.1872 is Elsevier "bronze" open archive, but only through
  sciencedirect.com, which answers 403 to curl/WebFetch and shows a CAPTCHA in the browser
  (not bypassed). OpenAlex and Semantic Scholar list no other copy; HAL and arXiv have none.
* Gravier–Maffray–Pastor, arXiv:1506.02576 (Thm 1.8), restates MR with the normalization
  "every augment has a non-adjacent pair and its X–Y edge graph is connected", **without proof**.
  Downloaded to `C:\lean\elementary_choosable_downloads\gmp.pdf`.
* The structure proof therefore has to be reconstructed. No reconstruction is complete yet.

### Planned self-contained route (target: `IsElementary G → ∃ a b hubA hubB, IsAugLineGraphRep …`)
1. **Twin reduction (proved on paper, easy).** If `u ≠ v` are adjacent with `N[u] = N[v]`, a
   representation of `G - v` extends by giving `v` the ends of `u` (`a v := a u`, `b v := b u`).
   All five conditions of `IsAugLineGraphRep` transfer. So by induction we may assume `G` has no
   true twins. Then every edge lies in an induced P3, i.e. in a component of the Gallai graph.
2. **Candidate representation for twin-free `G` with a fixed red/blue colouring.**
   `a v` = red component of `v`, `b v` = blue component; `hubA` / `hubB` = components that are
   not "red (blue) cliques" (some pair inside not joined by an edge of that colour).
   Condition (4) is then automatic. The others reduce to:
   * (N1) two non-adjacent vertices are never in the same red component and the same blue component;
   * (N2) a red (blue) hub component meets at most two blue (red) components;
   * (N3) no vertex lies in both a red hub and a blue hub.
   Checked on examples: in the 2+2 augment with a perfect matching of missing pairs, the swapped
   colouring makes the construction return the line graph of C4 plus two pendant edges, a valid
   alternative representation. (N1)–(N3) **fail without twin reduction**: K5 minus an edge with a
   valid colouring gives a vertex in two hubs.
3. **Core structural lemma needed (open).** In a twin-free elementary graph, every vertex has a
   monochromatic red neighbourhood R(v) and a monochromatic blue neighbourhood B(v) ("MN"). Then a
   red component is either a red clique or bipartite in red with blue-clique sides X, Y lying in
   two different blue components that are blue cliques, and (N1)–(N3) follow by short arguments.
   Facts proved so far toward MN: R(v), B(v) are cliques. Equal colours on uv, vw force u ~ w. If
   R(v) is mixed there are a, b, c ∈ R(v) with ab red and ac blue, and then
   N(a)∖N[v] = N(c)∖N[v] (all blue). Every distinguisher of a, c lies in B(v). A distinguisher
   z ∈ B(v) of a, c reproduces the same mixed pattern at a (R(a) ∋ v, b, z with vb red, vz blue).
   The pattern propagates, so MN needs a global or extremal argument, and that is not found.
   Model graphs satisfy MN (inside a non-hub star, twin-freeness puts all internal edges in one
   Gallai component), but proving that for an arbitrary valid colouring is equivalent to the
   theorem.

### Estimate
* With a correct paper proof in hand: twin reduction ~300 lines; MN and the component lemmas
  ~1.5–3k lines of case analysis; assembly ~500 lines; new headline theorems ~150 lines. In
  total ~2.5–4k lines, within the 5k budget.
* The blocking item is not size. It is the missing proof of MN (the content of MR's theorem), and
  the original source cannot be reached from this machine.

## Maffray–Reed with the paper in hand (2026-11-11, later)

Source: `C:\lean\elementary_choosable_downloads\mr.pdf` / `mr.txt` (JCTB 75 (1999) 134–156).

### What MR actually prove, and how
* Theorem 2: (i) elementary ⇔ (ii) claw-free, Berge and no "wonder" (pyramid, lighthouse,
  mausoleum, garden, colossus) ⇔ (iii) augmentation of an LGB graph. The proof of the direction
  we need is **(i) ⇒ (ii) ⇒ (iii)**, entirely through forbidden induced subgraphs. It is not a
  colouring argument.
  * (ii) ⇒ (iii) needs Theorem 3 (L(bipartite) = no claw, diamond or odd hole; root built from
    maximal cliques, bipartite because there is no odd hole), Theorem 4 (multigraph version:
    gem, 4-wheel) and Theorem 5 (no claw, odd hole, odd antihole, D or pyramid ⇒ LGB or
    cobipartite).
  * Then the main procedure: from a D, grow a strong homogeneous pair (C1, C2) with labelled
    insertion. Claims (1) and (2) are proved by minimal-label case analysis (Cases 1–3, about
    15 forbidden-subgraph contradictions). After that comes the A-component modification, and
    induction by compression.
* Section 4 (skeleton) normalizes augments: there is a non-adjacent pair, and the X–Y graph is
  connected (Lemma 1, (3), (4)). Theorem 6 then shows that, for G not cobipartite, in **every**
  elementary colouring the colour components are complete multipartite (cliques of atoms) or
  exactly the incomplete bipartite X_i–Y_i graphs. That is the construction of the previous
  section, applied to atoms, but MR derive it from Theorem 2, not independently.

### Gap found in the paper (minor, fixable)
* p. 143 (proof of (ii) ⇒ (iii)): "if a compression G′ of G has the structure required in
  (iii) then so does G: we simply augment along the edge ab. (Note that the flat edge ab cannot
  be within some augment of G′, because all edges inside an augment lie in a triangle)."
* As stated, the parenthetical is false. Take the augment X = {x1, x2}, Y = {y1} with only
  x1y1, replacing an isolated edge xy. Then x1x2 is an edge inside the augment that lies in no
  triangle.
* It becomes true once the induction hypothesis is the normalized form of Section 4 (each augment
  has a non-adjacent pair and a connected X–Y graph; then every edge inside an augment lies in a
  triangle). That normalization comes later in the paper (skeleton minimality), so the induction
  should carry it. It is a presentation gap, not a wrong theorem.

### Computer evidence (scripts in `C:\lean\elementary_choosable_deps\search\`)
* **MN is false in general.** In the twin-free cobipartite graph G = complement of (P4 + K2 + K1)
  (7 vertices) some valid colourings give mixed red neighbourhoods, and the "red/blue component"
  construction fails (one red and one blue component contain everything).
* For **connected, twin-free, non-cobipartite** elementary graphs the construction (a = red
  component, b = blue component, hubs = components that are not monochromatic cliques) satisfied
  `IsAugLineGraphRep` and MN in every test:
  * all 29 such graphs with ≤ 7 vertices (atlas), all colourings;
  * about 43,000 random (graph, colouring) pairs from random augmentations of bipartite-multigraph
    line graphs, up to roughly 15 vertices.

  This matches MR's Theorem 6, but a direct proof is not known (MR derive it from Theorem 2).
  Cobipartite components are covered by `rep_of_cobipartite`.

### Route options and estimates
1. **Faithful MR route** ((i) ⇒ (ii) ⇒ (iii) plus the Section 4 normalization).
   * Forbidden subgraphs from elementarity: about 600 lines (claw, odd hole, odd antihole, five
     wonders, D).
   * Theorems 3–5 (or a colouring replacement for 3–4): about 1.3–1.8k.
   * Main procedure (labelled growth, claims (1)–(2), A-components): about 1.5–2k.
   * Compression/augmentation induction with normalization, conversion to `IsAugLineGraphRep`:
     about 1–1.5k.
   * Atoms/twins, components, assembly: about 0.4k.
   * **Total about 5–6.5k lines**, the main risk being the labelled-insertion procedure.
2. **Colouring route** (twins → components → Theorem-6-type statement for non-cobipartite
   components). Probably shorter (2.5–4k), but it needs a new proof of "MN failure ⇒
   cobipartite" for connected twin-free elementary graphs. Mixed configurations seen so far are
   K4's {v,a,b,c} with a, c in one clique and v, b in the other, but no proof yet.

## Route decision, 2026-11-11 (coordinator: (b) bounded, then (a))

### (b) "mixed colouring ⇒ cobipartite": no proof found (time box used)
* Evidence for it is strong: no counterexample among connected twin-free graphs with ≤ 7 vertices
  (atlas), about 40k random colourings of random augmentations up to roughly 15 vertices, and
  about 3k random cobipartite graphs.
* No candidate cobipartition was found in terms of the configuration vertices. No pair among
  R[x], B[x] for x ∈ {v, a, b, c} always covers V; the mixed vertex sets are spread over both
  cliques (a, c in one, v, b in the other, the rest decided globally). It is a global
  statement and I have no proof.
* Equivalent target found and tested ("Theorem R"): in a connected, twin-free, non-cobipartite
  elementary graph, every red component that is not a red clique is red-bipartite with clique
  sides X, Y, and (X, Y) is a strong homogeneous pair. 0 failures in all tests. It **fails with
  twins** (atlas: 93 non-bipartite, 11 non-homogeneous). Also unproved.

### Proved on paper (usable in either route)
* **Twin-free + bend ⇒ induced gem or 4-wheel.** Take a bend u R v R w with uw blue. A
  distinguisher z of u, w gives a diamond z-{u,v}-w. A distinguisher y of u, v is then blue to
  w (or to z) and closes a gem (y ≁ z) or a 4-wheel (y ~ z) centred at u (or at v). Hence
  **twin-free with no gem and no 4-wheel ⇒ no bend ⇒ red and blue are equivalence relations ⇒
  LGB** with a = red class and b = blue class, and no hubs. This replaces MR's Theorems 3–4.
* **No odd antihole:** in C̄_n (n odd, n ≥ 7) the P3s i–j–(i+1) force
  col{j, j+2} ≠ col{j−2, j}. The step-2 cycle has odd length n, so this is a contradiction.
* **Compression with the corrected ordering.** Carry the invariant Norm through the induction:
  every hub has two classes, each of size ≥ 2, and a connected, incomplete cross graph.
  * Under Norm, a flat edge ab is a = (s, t_a), b = (s, t_b) with star(s) = {a, b} and
    s, t_a, t_b non-hubs.
  * Augmenting a strong homogeneous pair (C1, C2): give every vertex of C1 the ends (γ_j, t_a)
    and every vertex of C2 the ends (γ_j, t_b), with a fresh γ_j for each connected component j
    of the C1–C2 graph. γ_j is a hub iff that component is incomplete. Norm is preserved.
    Twins (parallel copies) and disjoint unions preserve Norm.

### (a) Faithful MR: a second, real gap in the source
* p. 145–146, Case 3 of claim (2) is internally inconsistent as printed. Case 3 assumes
  "z misses m", but the text then says "If 0 is not in T then (since z sees all of K_i) m and a
  vertex j of K_{3−i} are in T", with T a triangle containing z. It also says "Since G has no
  odd antihole this cycle must be a triangle" (an odd hole is meant). The "odd induced cycle
  containing z" built from "an odd path from m to l in B0" is not specified: z sees neither m
  nor l, and the cycle is induced in an auxiliary bipartite graph, not in G.
* Repair in progress, using colours. After claim (1): all C1–C2 edges are red and all 0–C1
  edges are blue (P3s x–0–c and 0–c1–c2), and every K-vertex has a cross neighbour of smaller
  label.
  * i = 1, z ≁ 0: z is red to all of K_1 (P3 z–k–0). A cross neighbour of l forces blue.
    Contradiction. **Proved.**
  * i = 1, z ~ 0: z0 is red, so x ~ z. Claws at the neighbours of l and r′ (r′ ∈ K_2 missed by
    m) force m ~ l, z ~ r′ and r′ complete to K_1. Then m is blue to K_1 (P3 m–k–r′), z is red
    to K_1, against zk blue for a neighbour k of l. **Proved.**
  * i = 2, z ~ 0: again x ~ z, and zr′ is blue via x. Then r′l is red (P3 z–r′–l), so ml
    would be blue (P3 m–l–r′). But ml is a cross edge, hence red. **Proved.**
  * i = 2, z ≁ 0: **proved (later the same day).**
    * z is red to every c ∈ K_1 that it sees (P3 z–c–0).
    * For k ∈ K_2: if zk is red then N(k)∩K_1 = N(z)∩K_1 (P3 z–k–c and P3 c–z–k), and if mk
      is red then N(k)∩K_1 = N(m)∩K_1 (P3 m–k–c and P3 c–m–k).
    * P3 z–k–m makes exactly one of zk, mk red, so every K_2-vertex has K_1-neighbourhood
      N(z)∩K_1 or N(m)∩K_1.
    * Vertex 2 separates 3 from 4, so these two sets are N(3)∩K_1 and N(4)∩K_1. Hence 1 sees
      both z and m, and {1; 0, z, m} is a claw.
  * **Case 3 is fully repaired**, using only claw-freeness, the P3 rule and claim (1).
* Not yet checked in detail: claim (1) cases (a)–(d), Case 1, Case 2, the A-component
  modification (pp. 146–147) and Theorem 5 (gem and 4-wheel cases), each with its
  forbidden-subgraph steps redone as colour contradictions.

### Estimate (unchanged order of magnitude)
About 6–8k Lean lines once the remaining subcase is repaired: forbidden-subgraph and colour
lemmas, Theorem 5, the growth procedure as a maximal valid list, claims (1)–(2), A-components,
compression with Norm, atoms and components, and the final assembly to `IsAugLineGraphRep`.

### Blueprint for the formalization (route (a), repaired)
Fix a valid colouring `col` once. Work with vertex sets W ⊆ V (Finset) inside a fixed type,
as in `ElemChoos.core`. The statement is P(W): ∃ a b : V → ℕ, hubA hubB, `RepOn W` ∧
`NormOn W` (`IsAugLineGraphRep` restricted to W, plus Norm). Prove it by strong induction on |W|.
1. `Elem.p3`: col u v ↔ ¬ col v w for every induced P3 in W. Derived: claw-free; no odd hole;
   no odd antihole (step-2 cycle); explicit small contradictions as needed.
2. Twins in W (adjacent, N[u]∩W = N[v]∩W): recurse on W∖{v}, give v the ends of u.
3. W disconnected: recurse on both parts, interleave ends (2n, 2n+1).
4. W connected and twin-free:
   * (no gem and no 4-wheel) ⇒ no bend (gem/4-wheel lemma) ⇒ LGB: a, b = least index in the
     red (blue) class, no hubs.
   * (gem or 4-wheel) and no D ⇒ cobipartite (MR Theorem 5, gem and 4-wheel cases; the odd
     antihole step uses item 1) ⇒ rep with one fresh hub per component of the cross graph
     (Norm).
   * D present ⇒ strong homogeneous pair. The growth procedure is a maximal valid list
     (finite: nodup lists). Claims (1)–(2) by minimal index: (1) as in MR; (2) Cases 1–2 as in
     MR, each forbidden subgraph replaced by a colour/claw contradiction; Case 3 as repaired
     above. Then the A-component modification (pp. 146–147). Compress to
     W′ = W∖(C1∪C2) ∪ {a, b}, recurse, and augment by the Norm construction.
5. Final: P(univ) with any elementary colouring, then `choosable_of_rep` /
   `chromaticChoosable_of_rep` give Theorem 1.1 for every elementary graph.
Before formalizing each forbidden-subgraph step, check it with a brute-force colouring search
on the named vertices (scripts in `elementary_choosable_deps\search`).

## Maffray–Reed formalized (2026-11-12): `ElemChoos/MR/*.lean`

### Statements added
* `ElemChoos.rep_of_isElementary` — every finite elementary graph has an `IsAugLineGraphRep`
  (MR Theorem 2, (i) ⇒ (iii)), with ends in `ℕ`.
* `ElemChoos.choosable_of_isElementary`, `ElemChoos.chromaticChoosable_of_isElementary` —
  Theorems 3.4 and 1.1 for all finite elementary graphs (via `choosable_of_rep`,
  `chromaticChoosable_of_rep`). The old statements are kept unchanged.

### Route actually formalized (all inside one fixed elementary colouring `ECol`)
* `MR/Basic.lean`: `ECol` (0/1 colour `c`, `c u v + c v w = 1` on induced P3s) and the tactic
  `elem_contra K [v₁,…,vₙ]`: it adds every P3 equation among the listed vertices whose
  (non-)adjacencies are hypotheses, the symmetry equations, and calls `omega` (odd Gallai cycle
  = parity contradiction). Every forbidden configuration used by MR (claw, 5-hole, pyramid,
  lighthouse, mausoleum, garden, colossus) is refuted this way; no wonder is defined.
* `MR/Rep.lean`, `MR/Easy.lean`: `RepOn`/`NormOn` on a vertex set (sides indexed by `Bool`),
  side swap, twins (`twin_ext`), disjoint unions (`union_rep`), and the no-bend case
  (`rep_of_noBend`: red/blue classes are the ends, no hubs; replaces MR Theorems 3–4).
* `MR/Flat.lean`: under `NormOn`, a flat edge `ab` with another neighbour has the normal form
  (shared non-hub end with star `{a,b}`, other ends distinct non-hubs) — this is the corrected
  p. 143 remark. `MR/Aug.lean`, `MR/AugMain.lean`: augmenting back (`aug_rep`), one fresh end
  per connected component of the cross graph, a hub iff both sides of the component have ≥ 2
  vertices; `NormOn` is preserved.
* `MR/Bend.lean`: twin-free + bend ⇒ induced gem or 4-wheel.
* `MR/Gem.lean`, `MR/Wheel.lean`: MR Theorem 5 (gem without D; 4-wheel without gem) ⇒
  cobipartite ⇒ strong homogeneous pair. The "no stable set of size 3 + no odd antihole"
  step is replaced by the colouring: a vertex seeing all four path/square vertices goes to the
  side given by one edge colour (same colour ⇒ adjacent by the P3 rule).
* `MR/Growth.lean`, `MR/Claim2.lean`, `MR/Step.lean`: the growth procedure as an invariant
  `Good` preserved by one addition (no labels): claim (1), "every vertex of Ci has a
  neighbour in C(3−i), and a non-neighbour there unless it is p1/p3" (the only use of the
  labels), and claim (2) as "no bad vertex". A `Good` pair of maximal size is final.
* `MR/AStep.lean`: S1/S2/A/Z, A1/A2, the cliques, and the A-components as reachability; the
  paper's shortest-path argument becomes an induction on `Relation.ReflTransGen`.
* `MR/Final.lean`: induction on `W` (twins / disconnected / bend ⇒ D or gem or wheel ⇒ SHP ⇒
  compress and augment / no bend ⇒ line graph), then the conversion to `IsAugLineGraphRep`.

### Verification of the remaining parts of MR (claim (1), Cases 1–2, A-step, Theorem 5)
All checked by brute force (`elementary_choosable_deps/search/checks_mr.py`, `checks_t5.py`,
`t5detail.py`, `t5wdetail.py`, `wheelgems.py`, `gemclq.py`, `gemsplit.py`, `c3split.py`,
`c2lists.py`, checker `cfgcheck.py`): every named configuration is non-elementary (or contains
a D / gem where the paper uses D-freeness / gem-freeness), for every completion of the unknown
adjacencies. Findings:
* Claim (1) (a)–(d), Case 1, Case 2, the A-component step (pp. 146–147) and both cases of
  Theorem 5: **correct as stated** (modulo the following remarks).
* Theorem 5, gem case: the paper's "K1 is a clique" uses a D for `C12` vs `C123`; that pair is
  in fact non-elementary (no D needed). D-freeness is needed only for the traces {1}, {4}
  without the centre and for a vertex of Z adjacent to C12 or C34 (four explicit D's).
* Theorem 5, 4-wheel case: vertices with three of the square must also see the centre (the
  paper does not say it; it is not needed either). Gem-freeness is used for the traces 12, 14,
  23, 34 and for C123–C124, C134–C234 and A–C (explicit gems in `Wheel.lean`).
* Case 3 of claim (2): the repair recorded above (2026-11-11) is the one formalized; the i = 2,
  z ≁ 0 subcase needs a 5-leaf case split on z~1, m~1, z~2, m~2 (`c3split.py`).
* p. 143 gap: handled by the `NormOn` invariant (see above).
No further gap found.
