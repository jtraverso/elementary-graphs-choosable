/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.Model

/-!
# Elementary graphs, choice number, and chromatic-choosability

* `isElementary_of_rep`: every augmentation of the line graph of a bipartite multigraph is
  elementary (the "if" direction of Maffray–Reed, for the representation used here).
* `rep_of_lineGraph`, `rep_of_cobipartite`: line graphs of bipartite multigraphs and
  complements of bipartite graphs belong to the class.
* `chromaticChoosable_of_rep`: `ch(G) = χ(G) = ω(G)` for the class (Theorem 1.1 of
  Narayanan–Vasudevan–Somasundaram, for the class that the Maffray–Reed theorem produces).
-/

@[expose] public section

open Finset

namespace ElemChoos

variable {V A B : Type*}

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

/-- Every augmentation of the line graph of a bipartite multigraph is elementary: colour a pair
red when it shares its `A`-end, except parallel pairs at an `A`-hub. -/
theorem isElementary_of_rep {G : SimpleGraph V} {a : V → A} {b : V → B} {hubA : Set A}
    {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) : IsElementary G := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG
  refine ⟨fun u v => a u = a v ∧ (b u ≠ b v ∨ a u ∉ hubA), ?_, ?_⟩
  · intro u v
    constructor
    · rintro ⟨hab, h⟩
      exact ⟨hab.symm, h.imp (fun h' e => h' e.symm) (fun h' e => h' (hab ▸ e))⟩
    · rintro ⟨hab, h⟩
      exact ⟨hab.symm, h.imp (fun h' e => h' e.symm) (fun h' e => h' (hab ▸ e))⟩
  · intro u v w huv hvw huw hn
    have missA : a u = a w → a u ∈ hubA ∧ b u ≠ b w := by
      intro e
      rcases h5 u w huw (Or.inl e) hn with h | h
      · exact ⟨h.2.1, h.2.2⟩
      · exact absurd e h.2.2
    have missB : b u = b w → b u ∈ hubB ∧ a u ≠ a w := by
      intro e
      rcases h5 u w huw (Or.inr e) hn with h | h
      · exact absurd e h.2.2
      · exact ⟨h.2.1, h.2.2⟩
    by_cases hA1 : a u = a v <;> by_cases hA2 : a v = a w
    · obtain ⟨hhub, hbne⟩ := missA (hA1.trans hA2)
      rcases h2 u v w hA1 (hA1.trans hA2) hhub with e | e | e
      · have hbvw : b v ≠ b w := fun e' => hbne (e.trans e')
        constructor
        · rintro ⟨-, h | h⟩
          · exact absurd e h
          · exact absurd hhub h
        · intro h
          exact (h ⟨hA2, Or.inl hbvw⟩).elim
      · exact absurd e hbne
      · have hbuv : b u ≠ b v := fun e' => hbne (e'.trans e)
        have hv : a v ∈ hubA := hA1 ▸ hhub
        constructor
        · rintro - ⟨-, h | h⟩
          · exact h e
          · exact h hv
        · intro _
          exact ⟨hA1, Or.inl hbuv⟩
    · have hB2 : b v = b w := (h4 v w hvw).resolve_left hA2
      constructor
      · rintro - ⟨h, -⟩
        exact hA2 h
      · intro _
        refine ⟨hA1, ?_⟩
        by_cases hB1 : b u = b v
        · right
          intro hu
          exact h1 u ⟨hu, (missB (hB1.trans hB2)).1⟩
        · exact Or.inl hB1
    · have hB1 : b u = b v := (h4 u v huv).resolve_left hA1
      constructor
      · rintro ⟨h, -⟩
        exact absurd h hA1
      · intro hn'
        exfalso
        apply hn'
        refine ⟨hA2, ?_⟩
        by_cases hB2 : b v = b w
        · right
          intro hv
          exact h1 v ⟨hv, hB1 ▸ (missB (hB1.trans hB2)).1⟩
        · exact Or.inl hB2
    · have hB1 : b u = b v := (h4 u v huv).resolve_left hA1
      have hB2 : b v = b w := (h4 v w hvw).resolve_left hA2
      obtain ⟨hhub, hane⟩ := missB (hB1.trans hB2)
      rcases h3 u v w hB1 (hB1.trans hB2) hhub with e | e | e
      · exact absurd e hA1
      · exact absurd e hane
      · exact absurd e hA2

/-- Line graphs of bipartite multigraphs belong to the class (no hubs). -/
theorem rep_of_lineGraph (G : SimpleGraph V) (a : V → A) (b : V → B)
    (h : ∀ u v, G.Adj u v ↔ u ≠ v ∧ (a u = a v ∨ b u = b v)) :
    IsAugLineGraphRep G a b ∅ ∅ := by
  refine ⟨fun v hv => hv.1, fun u v w _ _ hh => absurd hh (Set.notMem_empty _),
    fun u v w _ _ hh => absurd hh (Set.notMem_empty _), fun u v huv => ((h u v).1 huv).2, ?_⟩
  intro u v huv hsh hna
  exact absurd ((h u v).2 ⟨huv, hsh⟩) hna

/-- Complements of bipartite graphs (two cliques with arbitrary edges between them) belong to
the class: a single hub. -/
theorem rep_of_cobipartite (G : SimpleGraph V) (side : V → Bool)
    (h : ∀ u v, u ≠ v → side u = side v → G.Adj u v) :
    IsAugLineGraphRep G side (fun _ => ()) ∅ Set.univ := by
  refine ⟨fun v hv => hv.1, fun u v w _ _ hh => absurd hh (Set.notMem_empty _), ?_,
    fun _ _ _ => Or.inr rfl, ?_⟩
  · intro u v w _ _ _
    cases side u <;> cases side v <;> cases side w <;> simp
  · intro u v huv _ hna
    exact Or.inr ⟨rfl, Set.mem_univ _, fun e => hna (h u v huv e)⟩

/-- **Theorem 1.1 for the Maffray–Reed class.** Every augmentation of the line graph of a
bipartite multigraph is chromatic-choosable, with `ch(G) = χ(G) = ω(G)`. -/
theorem chromaticChoosable_of_rep [Finite V] {G : SimpleGraph V} {a : V → A} {b : V → B}
    {hubA : Set A} {hubB : Set B} (hG : IsAugLineGraphRep G a b hubA hubB) :
    choiceNumber G = G.chromaticNumber ∧ G.chromaticNumber = G.cliqueNum := by
  have hfree : G.CliqueFree (G.cliqueNum + 1) := by
    intro t ht
    have := ht.isClique.card_le_cliqueNum
    rw [ht.card_eq] at this
    omega
  have hch : IsChoosable G G.cliqueNum := fun L hL => choosable_of_rep hG hfree L hL
  have h1 : choiceNumber G ≤ G.cliqueNum := iInf₂_le _ hch
  have h2 : G.chromaticNumber ≤ choiceNumber G := by
    refine le_iInf₂ fun k hk => ?_
    have hk' : IsChoosable G k := hk
    obtain ⟨f, hf⟩ := hk' (fun _ => range k) (fun _ => by simp)
    exact SimpleGraph.Colorable.chromaticNumber_le
      ⟨SimpleGraph.Coloring.mk (fun v => ⟨f v, mem_range.1 (hf v)⟩)
        (fun h e => f.valid h (congrArg Fin.val e))⟩
  have h3 : (G.cliqueNum : ℕ∞) ≤ G.chromaticNumber := G.cliqueNum_le_chromaticNumber
  exact ⟨le_antisymm (h1.trans h3) h2, le_antisymm (h2.trans h1) h3⟩

end ElemChoos
