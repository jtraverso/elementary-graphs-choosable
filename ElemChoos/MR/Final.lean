/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ElemChoos.MR.AStep
public import ElemChoos.MR.Wheel
public import ElemChoos.MR.Bend
public import ElemChoos.MR.AugMain
public import ElemChoos.Main

/-!
# Maffray–Reed: every elementary graph is an augmentation of a bipartite-multigraph line graph

The induction on the vertex set `W` (all inside one fixed elementary colouring):

* twins: represent `W` minus one twin and copy the ends (`twin_ext`);
* disconnected `W`: represent the parts (`union_rep`);
* connected, twin-free `W` with a bend: a `D` gives a strong homogeneous pair
  (`exists_shp_of_D`); otherwise the bend gives a gem or a 4-wheel (`gemOrWheel_of_bend`) and
  `W` is cobipartite (`shp_of_gem`, `shp_of_wheel`), again a strong homogeneous pair. The pair
  is compressed to an edge `ab`, the compressed set is represented by induction, `ab` is a flat
  edge in normal form (`flat_normal`), and the representation is augmented back (`aug_rep`);
* no bend: the colour classes give a line-graph representation (`rep_of_noBend`).
-/

@[expose] public section

open Finset

namespace ElemChoos.MR

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (K : ECol G)

/-- A strong homogeneous pair in a connected twin-free set with a bend. -/
theorem shp_of_bend {W : Finset V} (hconn : ConnOn G W) (htf : TwinFreeOn G W) {u v w : V}
    (hu : u ∈ W) (hv : v ∈ W) (hw : w ∈ W) (huv : G.Adj u v) (hvw : G.Adj v w)
    (huw : G.Adj u w) (hc : K.c u v = K.c v w) (hc' : K.c u w ≠ K.c u v) :
    ∃ C1 C2, SHP G W C1 C2 := by
  by_cases hD : ∃ x ∈ W, ∃ o ∈ W, ∃ p1 ∈ W, ∃ p2 ∈ W, ∃ p3 ∈ W, ∃ p4 ∈ W,
      IsD G x o p1 p2 p3 p4
  · obtain ⟨x, hx, o, ho, p1, h1, p2, h2, p3, h3, p4, h4, hD⟩ := hD
    exact exists_shp_of_D K hD hx ho h1 h2 h3 h4
  · have hnoD : NoDIn G W := fun x hx o ho p1 h1 p2 h2 p3 h3 p4 h4 h =>
      hD ⟨x, hx, o, ho, p1, h1, p2, h2, p3, h3, p4, h4, h⟩
    obtain ⟨p1, h1, p2, h2, p3, h3, p4, h4, q, hq, hgw⟩ :=
      gemOrWheel_of_bend K htf hu hv hw huv hvw huw hc hc'
    by_cases hgem : ∃ p1 ∈ W, ∃ p2 ∈ W, ∃ p3 ∈ W, ∃ p4 ∈ W, ∃ q ∈ W, IsGem G p1 p2 p3 p4 q
    · obtain ⟨p1, h1, p2, h2, p3, h3, p4, h4, q, hq, hg⟩ := hgem
      exact shp_of_gem K hconn hnoD h1 h2 h3 h4 hq hg
    · have hng : NoGemIn G W := fun p1 h1 p2 h2 p3 h3 p4 h4 q hq h =>
        hgem ⟨p1, h1, p2, h2, p3, h3, p4, h4, q, hq, h⟩
      rcases hgw with hg | hw
      · exact absurd ⟨p1, h1, p2, h2, p3, h3, p4, h4, q, hq, hg⟩ hgem
      · exact shp_of_wheel K hconn hng h1 h2 h3 h4 hq hw

omit [Fintype V] in
/-- The representation of a single edge (or of one of its ends). -/
theorem rep_pair {a b : V} (hab : G.Adj a b) {W : Finset V} (hW : W ⊆ {a, b}) :
    RepOn G W (fun τ v => bif τ then 0 else if v = a then 0 else 1) (fun _ => ∅) ∧
      NormOn G W (fun τ v => bif τ then 0 else if v = a then 0 else 1) (fun _ => ∅) := by
  refine ⟨⟨fun v _ σ h => absurd h (Set.notMem_empty _),
    fun σ u _ v _ w _ _ _ h => absurd h (Set.notMem_empty _),
    fun u _ v _ _ => ⟨true, rfl⟩, ?_⟩, fun σ s h => absurd h (Set.notMem_empty _)⟩
  intro u hu v hv huv _ hna
  exfalso
  have hu' := hW hu
  have hv' := hW hv
  simp only [mem_insert, mem_singleton] at hu' hv'
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact huv rfl
  · exact hna hab
  · exact hna hab.symm
  · exact huv rfl

/-- Compressing a strong homogeneous pair in a connected set. -/
theorem rep_of_shp {W C1 C2 : Finset V} (hconn : ConnOn G W) (hP : SHP G W C1 C2)
    (ih : ∀ W' ⊂ W, ∃ e h, RepOn G W' e h ∧ NormOn G W' e h) :
    ∃ e h, RepOn G W e h ∧ NormOn G W e h := by
  obtain ⟨a, ha, b, hb, hab⟩ := hP.edge
  set C := C1 ∪ C2 with hC
  set W' := W \ C ∪ {a, b} with hW'
  have haW := hP.sub1 ha
  have hbW := hP.sub2 hb
  have hCW : C ⊆ W := union_subset hP.sub1 hP.sub2
  by_cases hrest : W \ C = ∅
  · have hW'2 : W' ⊆ {a, b} := by rw [hW', hrest, empty_union]
    obtain ⟨hR, hN⟩ := rep_pair hab hW'2
    exact aug_rep hP ha hb hR hN rfl (Set.notMem_empty _)
      (fun v hv _ => by simpa using hW'2 hv) (by simp [G.ne_of_adj hab, (G.ne_of_adj hab).symm])
      (Set.notMem_empty _) (Set.notMem_empty _)
  · have hsub : W' ⊂ W := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨union_subset sdiff_subset (by
        intro v hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption), fun h => ?_⟩
      have h1 : #W' ≤ #(W \ C) + 2 := (card_union_le _ _).trans (by
        have : #({a, b} : Finset V) ≤ 2 := (card_insert_le _ _).trans (by simp)
        omega)
      have h2 : #(W \ C) + #C = #W := card_sdiff_add_card_eq_card hCW
      have h3 : #C = #C1 + #C2 := card_union_of_disjoint hP.disj
      have h4 := hP.three
      rw [h] at h1
      omega
    obtain ⟨e, h, hR, hN⟩ := ih W' hsub
    have haW' : a ∈ W' := mem_union_right _ (by simp)
    have hbW' : b ∈ W' := mem_union_right _ (by simp)
    have hflat : ∀ w ∈ W', G.Adj w a → G.Adj w b → False := by
      intro w hw hwa hwb
      rcases mem_union.1 hw with hw | hw
      · obtain ⟨hwW, hwC⟩ := mem_sdiff.1 hw
        have h1 : w ∉ C1 := fun h' => hwC (mem_union_left _ h')
        have h2 : w ∉ C2 := fun h' => hwC (mem_union_right _ h')
        exact (hP.out1 hwW h1 h2 ha hwa).2 b hb hwb
      · simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact G.loopless.irrefl _ hwa
        · exact G.loopless.irrefl _ hwb
    have hext : ∃ w ∈ W', w ≠ a ∧ w ≠ b ∧ (G.Adj w a ∨ G.Adj w b) := by
      have hne : C.Nonempty := ⟨a, mem_union_left _ ha⟩
      have hCne : C ≠ W := fun h' => hrest (by rw [h']; exact Finset.sdiff_self _)
      obtain ⟨u, hu, v, hv, hvC, huv⟩ := hconn C hCW hne hCne
      have h1 : v ∉ C1 := fun h' => hvC (mem_union_left _ h')
      have h2 : v ∉ C2 := fun h' => hvC (mem_union_right _ h')
      refine ⟨v, mem_union_left _ (mem_sdiff.2 ⟨hv, hvC⟩), fun h' => hvC (h' ▸
        mem_union_left _ ha), fun h' => hvC (h' ▸ mem_union_right _ hb), ?_⟩
      rcases mem_union.1 hu with hu | hu
      · exact Or.inl ((hP.out1 hv h1 h2 hu huv.symm).1 a ha)
      · exact Or.inr ((hP.out2 hv h1 h2 hu huv.symm).1 b hb)
    obtain ⟨σ, hs, hsn, hstar, hne, hta, htb⟩ := flat_normal hR hN haW' hbW' hab hflat hext
    cases σ
    · have hR' := hR.swap
      have hN' := hN.swap
      exact aug_rep hP ha hb hR' hN' hs hsn hstar hne hta htb
    · exact aug_rep hP ha hb hR hN hs hsn hstar hne hta htb

include K in
/-- **Every vertex set of an elementary graph has a normalized representation.** -/
theorem exists_rep_on (W : Finset V) : ∃ e h, RepOn G W e h ∧ NormOn G W e h := by
  induction W using Finset.strongInduction with
  | H W ih =>
  by_cases htw : ∃ u ∈ W, ∃ v ∈ W, u ≠ v ∧ G.Adj u v ∧
      ∀ w ∈ W, w ≠ u → w ≠ v → (G.Adj w u ↔ G.Adj w v)
  · obtain ⟨u, hu, v, hv, huv, hadj, htw⟩ := htw
    obtain ⟨e, h, hR, hN⟩ := ih (W.erase v) (erase_ssubset hv)
    exact twin_ext hu hv huv hadj htw hR hN
  have htf : TwinFreeOn G W := by
    intro u hu v hv huv hadj
    by_contra hn
    push_neg at hn
    exact htw ⟨u, hu, v, hv, huv, hadj, fun w hw h1 h2 => hn w hw h1 h2⟩
  by_cases hconn : ConnOn G W
  · by_cases hb : ∃ u ∈ W, ∃ v ∈ W, ∃ w ∈ W, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        K.c u v = K.c v w ∧ K.c u w ≠ K.c u v
    · obtain ⟨u, hu, v, hv, w, hw, huv, hvw, huw, hc, hc'⟩ := hb
      obtain ⟨C1, C2, hP⟩ := shp_of_bend K hconn htf hu hv hw huv hvw huw hc hc'
      exact rep_of_shp hconn hP ih
    · refine rep_of_noBend K W fun u hu v hv w hw huv hvw huw hc => ?_
      by_contra hc'
      exact hb ⟨u, hu, v, hv, w, hw, huv, hvw, huw, hc, hc'⟩
  · unfold ConnOn at hconn
    push_neg at hconn
    obtain ⟨S, hSW, hSne, hSW', hcut⟩ := hconn
    have h1 : S ⊂ W := Finset.ssubset_iff_subset_ne.2 ⟨hSW, hSW'⟩
    have h2 : W \ S ⊂ W := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨sdiff_subset, fun h => ?_⟩
      obtain ⟨s, hs⟩ := hSne
      have : s ∈ W \ S := by rw [h]; exact hSW hs
      exact (mem_sdiff.1 this).2 hs
    obtain ⟨e1, h1', hR1, hN1⟩ := ih S h1
    obtain ⟨e2, h2', hR2, hN2⟩ := ih (W \ S) h2
    have := union_rep disjoint_sdiff (fun u hu v hv => hcut u hu v (mem_sdiff.1 hv).1
      (mem_sdiff.1 hv).2) hR1 hN1 hR2 hN2
    rwa [union_sdiff_of_subset hSW] at this

end ElemChoos.MR

namespace ElemChoos

variable {V A B C : Type*}

/-- **Maffray–Reed (1999), Theorem 2, (i) ⇒ (iii).** Every finite elementary graph is an
augmentation of the line graph of a bipartite multigraph. -/
theorem rep_of_isElementary [Finite V] {G : SimpleGraph V} (hG : IsElementary G) :
    ∃ (a b : V → ℕ) (hubA hubB : Set ℕ), IsAugLineGraphRep G a b hubA hubB := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨red, hsymm, hp3⟩ := hG
  let K : MR.ECol G :=
    { c := fun u v => if red u v then 1 else 0
      le_one := fun u v => by split_ifs <;> omega
      symm := fun u v => by simp only [hsymm u v]
      p3 := fun u v w huv hvw huw hn => by
        have := hp3 u v w huv hvw huw hn
        by_cases h1 : red u v <;> by_cases h2 : red v w <;> simp_all }
  obtain ⟨e, h, hR, -⟩ := MR.exists_rep_on K (Finset.univ : Finset V)
  obtain ⟨r1, r2, r3, r4⟩ := hR
  refine ⟨e true, e false, h true, h false, fun v hv => ?_, fun u v w e1 e2 e3 => ?_,
    fun u v w e1 e2 e3 => ?_, fun u v huv => ?_, fun u v huv hsh hna => ?_⟩
  · exact r1 v (Finset.mem_univ _) true hv.1 hv.2
  · simpa using r2 true u (Finset.mem_univ _) v (Finset.mem_univ _) w (Finset.mem_univ _) e1 e2 e3
  · simpa using r2 false u (Finset.mem_univ _) v (Finset.mem_univ _) w (Finset.mem_univ _) e1 e2 e3
  · obtain ⟨σ, hσ⟩ := r3 u (Finset.mem_univ _) v (Finset.mem_univ _) huv
    cases σ
    · exact Or.inr hσ
    · exact Or.inl hσ
  · obtain ⟨σ, h1, h2, h3⟩ := r4 u (Finset.mem_univ _) v (Finset.mem_univ _) huv
      (hsh.elim (fun h' => ⟨true, h'⟩) (fun h' => ⟨false, h'⟩)) hna
    cases σ
    · exact Or.inr ⟨h1, h2, by simpa using h3⟩
    · exact Or.inl ⟨h1, h2, by simpa using h3⟩

/-- **Theorem 3.4 for all elementary graphs.** -/
theorem choosable_of_isElementary [Finite V] {G : SimpleGraph V}
    (hG : IsElementary G) {k : ℕ} (hω : G.CliqueFree (k + 1)) (L : V → Finset C)
    (hL : ∀ v, k ≤ (L v).card) : ∃ f : G.Coloring C, ∀ v, f v ∈ L v := by
  obtain ⟨a, b, hubA, hubB, hrep⟩ := rep_of_isElementary hG
  exact choosable_of_rep hrep hω L hL

/-- **Theorem 1.1.** Every elementary graph satisfies `ch(G) = χ(G) = ω(G)`. -/
theorem chromaticChoosable_of_isElementary [Finite V] {G : SimpleGraph V}
    (hG : IsElementary G) :
    choiceNumber G = G.chromaticNumber ∧ G.chromaticNumber = G.cliqueNum := by
  obtain ⟨a, b, hubA, hubB, hrep⟩ := rep_of_isElementary hG
  exact chromaticChoosable_of_rep hrep

end ElemChoos
