import KNConjectures.Question8Defs

/-!
# Kozma--Nitzan Question 8: elementary cases and the zero-score support lemma

This file proves the singleton, `b = o`, and degenerate cases, then proves the finite-product
support-atom characterization and uses it to establish the support-graph lemma from the note.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

/-- With one relay, the two sides of display (41) agree. -/
theorem q8_singleton {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (o b a : Fin n) : q8L w {a} o b a = q8R w {a} o b := by
  unfold q8L q8R
  congr 1
  ext ω
  simp only [U, Finset.mem_singleton, iUnion_iUnion_eq_left, mem_inter_iff]
  constructor
  · rintro ⟨hab, hoa⟩
    exact ⟨hoa.trans hab, hoa⟩
  · rintro ⟨hob, hoa⟩
    exact ⟨hoa.symm.trans hob, hoa⟩

/-- If the target is the observer, display (41) holds for every relay. -/
theorem q8_bEqO {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (o a : Fin n) : q8L w A o o a ≤ q8R w A o o := by
  unfold q8L q8R
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨_, hU⟩
  exact ⟨SimpleGraph.Reachable.refl o, hU⟩

/-- On `P(o ↮ A) = 0`, every relay has score zero and hence is a minimiser. -/
theorem q8_degenerate_allMin {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (o b : Fin n)
    (hD : (prodBernoulli w).real (U A o)ᶜ = 0) :
    ∀ a ∈ A, IsQ8Min w A o b a := by
  have hzero : ∀ x : Fin n, q8Score w A o b x = 0 := by
    intro x
    apply le_antisymm
    · exact (measureReal_mono inter_subset_right (measure_ne_top _ _)).trans_eq hD
    · exact measureReal_nonneg
  intro a ha
  refine ⟨ha, ?_⟩
  intro x hx
  rw [hzero a, hzero x]

/-! ### Product support -/

/--
A configuration has positive atom mass exactly when it contains every weight-one pair and no
weight-zero pair.  Coordinates of weight strictly between zero and one are unrestricted.
-/
theorem q8_support_atom_pos_iff {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (ω : BondConfig (Fin n)) :
    0 < (prodBernoulli w).real {ω} ↔
      (∀ e, w e = 1 → e ∈ ω) ∧ (∀ e, w e = 0 → e ∉ ω) := by
  classical
  have hcyl := prodBernoulli_real_setOf_forall_iff
    (p := w) (Finset.univ : Finset (Sym2 (Fin n))) (fun e ↦ e ∈ ω)
  have hset :
      {η : BondConfig (Fin n) | ∀ e ∈ (Finset.univ : Finset (Sym2 (Fin n))),
        (e ∈ η ↔ e ∈ ω)} = {ω} := by
    ext η
    simp only [Finset.mem_univ, forall_const, mem_setOf_eq, mem_singleton_iff]
    exact ⟨fun h ↦ Set.ext h, fun h e ↦ by subst η; rfl⟩
  rw [hset] at hcyl
  rw [hcyl]
  constructor
  · intro hprod
    constructor
    · intro e he1
      by_contra heω
      have hfactor : (if e ∈ ω then (w e : ℝ) else 1 - w e) = 0 := by
        rw [if_neg heω]
        have : (w e : ℝ) = 1 := by simpa using congrArg Subtype.val he1
        rw [this, sub_self]
      have hz : ∏ i ∈ (Finset.univ : Finset (Sym2 (Fin n))),
          (if i ∈ ω then (w i : ℝ) else 1 - w i) = 0 := by
        exact Finset.prod_eq_zero (Finset.mem_univ e) hfactor
      linarith
    · intro e he0 heω
      have hfactor : (if e ∈ ω then (w e : ℝ) else 1 - w e) = 0 := by
        rw [if_pos heω]
        simpa using congrArg Subtype.val he0
      have hz : ∏ i ∈ (Finset.univ : Finset (Sym2 (Fin n))),
          (if i ∈ ω then (w i : ℝ) else 1 - w i) = 0 := by
        exact Finset.prod_eq_zero (Finset.mem_univ e) hfactor
      linarith
  · rintro ⟨hone, hzero⟩
    refine Finset.prod_pos fun e _ ↦ ?_
    by_cases heω : e ∈ ω
    · rw [if_pos heω]
      have hne : w e ≠ 0 := fun h ↦ hzero e h heω
      have hne' : (w e : ℝ) ≠ 0 := by
        intro h
        exact hne (Subtype.ext h)
      exact lt_of_le_of_ne (w e).2.1 hne'.symm
    · rw [if_neg heω]
      have hne : w e ≠ 1 := fun h ↦ heω (hone e h)
      have hne' : (w e : ℝ) ≠ 1 := by
        intro h
        exact hne (Subtype.ext h)
      have hlt : (w e : ℝ) < 1 := lt_of_le_of_ne (w e).2.2 hne'
      linarith

/-- The support condition appearing in `q8_support_atom_pos_iff`. -/
def q8Support {n : ℕ} (w : Sym2 (Fin n) → unitInterval) :
    Set (BondConfig (Fin n)) :=
  {ω | (∀ e, w e = 1 → e ∈ ω) ∧ (∀ e, w e = 0 → e ∉ ω)}

/-- The product measure is concentrated on `q8Support w`. -/
theorem q8Support_compl_null {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) :
    prodBernoulli w (q8Support w)ᶜ = 0 := by
  classical
  let F : Finset (BondConfig (Fin n)) :=
    Finset.univ.filter (fun ω ↦ ω ∈ (q8Support w)ᶜ)
  have hF : (↑F : Set (BondConfig (Fin n))) = (q8Support w)ᶜ := by
    ext ω
    simp [F]
  have hsum := sum_measureReal_singleton (μ := prodBernoulli w) F
  have hzero : ∀ ω ∈ F, (prodBernoulli w).real {ω} = 0 := by
    intro ω hω
    have hnot : ω ∉ q8Support w := by
      have : ω ∈ (q8Support w)ᶜ := by simpa [F] using hω
      exact this
    apply le_antisymm
    · exact not_lt.mp (fun hp ↦ hnot ((q8_support_atom_pos_iff w ω).1 hp))
    · exact measureReal_nonneg
  have hreal : (prodBernoulli w).real (q8Support w)ᶜ = 0 := by
    rw [← hF, ← hsum, Finset.sum_eq_zero hzero]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hreal

/-! ### The support-graph lemma -/

/--
If avoidance has positive probability and the score of `a` is zero, then `L_a ≤ R`.

The proof works atom by atom.  Starting from a supported `a`--`b` walk, retain only its edges and
the forced-open edges.  If this smaller supported configuration joined `o` to `A`, it would either
use only forced edges (contradicting a supported avoidance configuration) or meet the retained
walk (and hence join `o` to `b`).  The smaller configuration is therefore a positive-mass member
of the allegedly zero score event.
-/
theorem q8_zeroScore {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (o b a : Fin n) (ha : a ∈ A)
    (hD : 0 < (prodBernoulli w).real (U A o)ᶜ)
    (hscore : q8Score w A o b a = 0) :
    q8L w A o b a ≤ q8R w A o b := by
  classical
  let μ : Measure (BondConfig (Fin n)) := prodBernoulli w
  -- Positive avoidance contains a positive atom because the configuration space is finite.
  have exists_pos_atom {S : Set (BondConfig (Fin n))} (hS : 0 < μ.real S) :
      ∃ ω ∈ S, 0 < μ.real {ω} := by
    let F : Finset (BondConfig (Fin n)) := Finset.univ.filter (fun ω ↦ ω ∈ S)
    have hF : (↑F : Set (BondConfig (Fin n))) = S := by ext ω; simp [F]
    have hsum := sum_measureReal_singleton (μ := μ) F
    by_contra hnone
    have hnone' : ∀ ω ∈ S, μ.real {ω} ≤ 0 := by
      intro ω hω
      exact le_of_not_gt (fun hp ↦ hnone ⟨ω, hω, hp⟩)
    have hz : ∀ ω ∈ F, μ.real {ω} = 0 := by
      intro ω hω
      apply le_antisymm
      · exact hnone' ω (by simpa [F] using hω)
      · exact measureReal_nonneg
    have : μ.real S = 0 := by rw [← hF, ← hsum, Finset.sum_eq_zero hz]
    linarith
  obtain ⟨ωD, hωD_D, hωD_pos⟩ := exists_pos_atom (by simpa [μ] using hD)
  have hωD_supp := (q8_support_atom_pos_iff w ωD).1 (by simpa [μ] using hωD_pos)

  -- Every supported `a`--`b` configuration must also join `o` to `b`.
  have hsupported_conn : ∀ ω ∈ q8Support w,
      ω ∈ (openConn a b : Set (BondConfig (Fin n))) →
        ω ∈ (openConn o b : Set (BondConfig (Fin n))) := by
    intro ω hωsupp hab
    by_contra hnob
    obtain ⟨p⟩ := hab
    let η : BondConfig (Fin n) := {e | w e = 1 ∨ e ∈ p.edges}
    have hηω : η ⊆ ω := by
      intro e he
      rcases he with he1 | hep
      · exact hωsupp.1 e he1
      · have he' := p.edges_subset_edgeSet hep
        rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at he'
        exact he'.1
    have hηsupp : η ∈ q8Support w := by
      constructor
      · intro e he1
        exact Or.inl he1
      · intro e he0 heη
        exact hωsupp.2 e he0 (hηω heη)
    have hηpos : 0 < (prodBernoulli w).real {η} :=
      (q8_support_atom_pos_iff w η).2 hηsupp
    have hpη : ∀ e ∈ p.edges, e ∈ (openGraph η).edgeSet := by
      intro e he
      rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨Or.inr he, SimpleGraph.not_isDiag_of_mem_edgeSet _ (p.edges_subset_edgeSet he)⟩
    have habη : η ∈ (openConn a b : Set (BondConfig (Fin n))) :=
      ⟨p.transfer (openGraph η) hpη⟩
    have hηD : η ∈ (U A o)ᶜ := by
      intro hηU
      obtain ⟨x, hxA, hox⟩ := mem_iUnion₂.1 hηU
      obtain ⟨q⟩ := hox
      by_cases hmeet : ∃ v, v ∈ q.support ∧ v ∈ p.support
      · obtain ⟨v, hvq, hvp⟩ := hmeet
        have hovη : (openGraph η).Reachable o v := (q.takeUntil v hvq).reachable
        have hovω : (openGraph ω).Reachable o v := by
          exact hovη.mono (SimpleGraph.fromEdgeSet_mono hηω)
        have hvbω : (openGraph ω).Reachable v b := (p.dropUntil v hvp).reachable
        exact hnob (hovω.trans hvbω)
      · have hqD : ∀ e ∈ q.edges, e ∈ (openGraph ωD).edgeSet := by
          intro e he
          have heη := q.edges_subset_edgeSet he
          rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at heη ⊢
          refine ⟨?_, heη.2⟩
          rcases heη.1 with he1 | hep
          · exact hωD_supp.1 e he1
          · exfalso
            induction e using Sym2.ind with
            | _ u v =>
                exact hmeet ⟨u, q.fst_mem_support_of_mem_edges he,
                  p.fst_mem_support_of_mem_edges hep⟩
        have hoxD : (openGraph ωD).Reachable o x :=
          ⟨q.transfer (openGraph ωD) hqD⟩
        exact hωD_D (mem_iUnion₂.2 ⟨x, hxA, hoxD⟩)
    have hηevent : η ∈
        (openConn a b ∩ (U A o)ᶜ : Set (BondConfig (Fin n))) := ⟨habη, hηD⟩
    have hmono : (prodBernoulli w).real {η} ≤
        (prodBernoulli w).real
          (openConn a b ∩ (U A o)ᶜ : Set (BondConfig (Fin n))) := by
      exact measureReal_mono (by simpa only [singleton_subset_iff]) (measure_ne_top _ _)
    have : 0 < q8Score w A o b a := by
      unfold q8Score
      exact hηpos.trans_le hmono
    linarith

  have hsub :
      (openConn a b ∩ U A o : Set (BondConfig (Fin n))) ∩ q8Support w ⊆
        (openConn o b ∩ U A o : Set (BondConfig (Fin n))) ∩ q8Support w := by
    rintro ω ⟨⟨hab, hU⟩, hsupp⟩
    have hob := hsupported_conn ω hsupp hab
    have hoa : (openGraph ω).Reachable o a := hob.trans hab.symm
    have hU' : ω ∈ U A o := mem_iUnion₂.2 ⟨a, ha, hoa⟩
    exact ⟨⟨hob, hU'⟩, hsupp⟩
  have hconull := q8Support_compl_null w
  have hL := measure_inter_conull (μ := prodBernoulli w)
    (s := (openConn a b ∩ U A o : Set (BondConfig (Fin n)))) hconull
  have hR := measure_inter_conull (μ := prodBernoulli w)
    (s := (openConn o b ∩ U A o : Set (BondConfig (Fin n)))) hconull
  unfold q8L q8R
  calc
    (prodBernoulli w).real (openConn a b ∩ U A o) =
        (prodBernoulli w).real ((openConn a b ∩ U A o) ∩ q8Support w) := by
      simpa only [measureReal_def] using congrArg ENNReal.toReal hL |>.symm
    _ ≤ (prodBernoulli w).real ((openConn o b ∩ U A o) ∩ q8Support w) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ = (prodBernoulli w).real (openConn o b ∩ U A o) := by
      simpa only [measureReal_def] using congrArg ENNReal.toReal hR

end KNAll

end


#print axioms KNAll.q8_singleton
#print axioms KNAll.q8_bEqO
#print axioms KNAll.q8_degenerate_allMin
#print axioms KNAll.q8_support_atom_pos_iff
#print axioms KNAll.q8Support_compl_null
#print axioms KNAll.q8_zeroScore
