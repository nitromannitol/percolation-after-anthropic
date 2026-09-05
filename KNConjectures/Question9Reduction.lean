import KNConjectures.Statements9

/-!
# Question 9 from the set-source fixed-minimizer inequality

Expose the complete star of `o`.  On each star configuration the cluster of `o` is the
set-source cluster in the graph whose star has been deleted.  The product law factors over the
exposed star and its complement, so the desired difference is a nonnegative weighted sum of the
set-source gaps.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity
open scoped Classical

variable {V : Type*} [Fintype V]

/-- The complete set of pairs incident to `o` (including the irrelevant diagonal pair). -/
private def starPairs (o : V) : Set (Sym2 V) := {e | o ∈ e}

/-- Deleting `starPairs o` from a configuration does not change its star event. -/
private lemma starEvent_inter_starPairs_iff (o : V) (B : Set V) (ω : BondConfig V) :
    ω ∩ starPairs o ∈ starEvent o B ↔ ω ∈ starEvent o B := by
  simp only [starEvent, mem_setOf_eq]
  refine forall_congr' fun u ↦ forall_congr' fun huo ↦ ?_
  have he : s(o, u) ∈ starPairs o := Sym2.mem_mk_left o u
  simp only [mem_inter_iff, he, and_true]

/-- Product Fubini at the star.  A function of the configuration with the star removed is
independent of the exposed star event; the remaining integral is precisely for the weighting
whose star has been set to zero. -/
private theorem setIntegral_starEvent_comp_delete (w w₀ : Sym2 V → unitInterval) (o : V)
    (hzero : ∀ e ∈ starPairs o, w₀ e = 0)
    (hkeep : ∀ e ∉ starPairs o, w₀ e = w e)
    (B : Set V) (g : BondConfig V → ℝ) :
    ∫ ω in starEvent o B, g (ω \ starPairs o) ∂(prodBernoulli w) =
      (prodBernoulli w).real (starEvent o B) *
        ∫ ω, g ω ∂(prodBernoulli w₀) := by
  classical
  let p : Sym2 V → ℝ := fun e ↦ (w e : ℝ)
  let σ : Set (BondConfig V) := starEvent o B
  let D : Set (Sym2 V) := starPairs o
  have hm : ∑ ω : Set (Sym2 V), BHK2006.weight p ω = 1 := by
    have hmass := BHK2006.integral_prodBernoulli_eq_sum w (fun _ ↦ (1 : ℝ))
    simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one, p] using hmass.symm
  have hσ : ∀ ω : Set (Sym2 V),
      Percolation.Literature.DecisionTree.ind σ (ω ∩ D) =
        Percolation.Literature.DecisionTree.ind σ ω := by
    intro ω
    have hi : ω ∩ D ∈ σ ↔ ω ∈ σ := starEvent_inter_starPairs_iff o B ω
    by_cases hω : ω ∈ σ
    · rw [Percolation.Literature.DecisionTree.ind_of_mem hω,
        Percolation.Literature.DecisionTree.ind_of_mem (hi.2 hω)]
    · rw [Percolation.Literature.DecisionTree.ind_of_not_mem hω,
        Percolation.Literature.DecisionTree.ind_of_not_mem (mt hi.1 hω)]
  let Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η ↦
    g η * Percolation.Literature.DecisionTree.ind σ ζ
  have hblock := BHK2006.blockFubini p D Φ
  simp only [hm, one_mul, Φ, hσ] at hblock
  rw [Percolation.Literature.LonePortSum.setIntegral_eq_sum,
    Percolation.Literature.LonePortSum.measureReal_eq_sum]
  change (∑ ω, BHK2006.weight p ω *
      (g (ω \ D) * Percolation.Literature.DecisionTree.ind σ ω)) = _
  calc
    (∑ ω, BHK2006.weight p ω *
        (g (ω \ D) * Percolation.Literature.DecisionTree.ind σ ω)) =
        ∑ ω, BHK2006.weight p ω * ∑ ω', BHK2006.weight p ω' *
          (g (ω' \ D) * Percolation.Literature.DecisionTree.ind σ ω) := hblock
    _ = ∑ ω, (BHK2006.weight p ω *
          Percolation.Literature.DecisionTree.ind σ ω) *
        (∑ ω', BHK2006.weight p ω' * g (ω' \ D)) := by
      refine Finset.sum_congr rfl fun ω _ ↦ ?_
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω' _ ↦ by ring
    _ = (∑ ω, BHK2006.weight p ω *
          Percolation.Literature.DecisionTree.ind σ ω) *
        (∑ ω', BHK2006.weight p ω' * g (ω' \ D)) := by
      rw [Finset.sum_mul]
    _ = (∑ ω, BHK2006.weight p ω *
          Percolation.Literature.DecisionTree.ind σ ω) *
        ∫ ω, g (ω \ D) ∂(prodBernoulli w) := by
      rw [BHK2006.integral_prodBernoulli_eq_sum]
    _ = (∑ ω, BHK2006.weight p ω *
          Percolation.Literature.DecisionTree.ind σ ω) *
        ∫ ω, g ω ∂(prodBernoulli w₀) := by
      have hzeroD : ∀ e ∈ D, w₀ e = 0 := by simpa only [D] using hzero
      have hkeepD : ∀ e ∉ D, w₀ e = w e := by simpa only [D] using hkeep
      rw [BHK2006.integral_comp_sdiff_prodBernoulli' w w₀ D hzeroD hkeepD]

/-! ## Pointwise star/source identities -/

/-- On a fixed star event, the cluster of the star centre is the union of the clusters rooted at
the centre and its open star-neighbours, computed after deleting the star. -/
private theorem openCluster_eq_sourceCluster_of_starEvent {ω : BondConfig V} {o : V}
    {B : Set V} (hσ : ω ∈ starEvent o B) :
    openCluster ω o = sourceCluster (ω \ starPairs o) (insert o B) := by
  let η : BondConfig V := ω \ starPairs o
  have hηω : η ⊆ ω := sdiff_subset
  have hmono : openGraph η ≤ openGraph ω := openGraph_mono hηω
  have hwalk : ∀ {x y : V},
      (∃ r ∈ insert o B, (openGraph η).Reachable r x) →
        (openGraph ω).Walk x y →
          ∃ r ∈ insert o B, (openGraph η).Reachable r y := by
    intro x y hx p
    induction p with
    | nil => exact hx
    | cons hadj p ih =>
        apply ih
        rename_i x z y
        have he : s(x, z) ∈ ω ∧ x ≠ z := (openGraph_adj ω x z).1 hadj
        by_cases heD : s(x, z) ∈ starPairs o
        · have ho : o ∈ s(x, z) := heD
          rcases Sym2.mem_iff.1 ho with hox | hoz
          · subst x
            have hzo : z ≠ o := he.2.symm
            have hzB : z ∈ B := ((mem_starEvent_iff o B ω).1 hσ z hzo).1 he.1
            exact ⟨z, Or.inr hzB, SimpleGraph.Reachable.refl z⟩
          · subst z
            exact ⟨o, Or.inl rfl, SimpleGraph.Reachable.refl o⟩
        · obtain ⟨r, hr, hrx⟩ := hx
          have hadjη : (openGraph η).Adj x z :=
            (openGraph_adj η x z).2 ⟨⟨he.1, heD⟩, he.2⟩
          exact ⟨r, hr, hrx.trans hadjη.reachable⟩
  ext y
  constructor
  · intro hoy
    obtain ⟨p⟩ := (hoy : (openGraph ω).Reachable o y)
    obtain ⟨r, hr, hry⟩ := hwalk
      ⟨o, Or.inl rfl, SimpleGraph.Reachable.refl o⟩ p
    exact Set.mem_iUnion₂.2 ⟨r, hr, hry⟩
  · intro hy
    obtain ⟨r, hr, hry⟩ := Set.mem_iUnion₂.1 hy
    have hry' : (openGraph ω).Reachable r y := hry.mono hmono
    rcases hr with rfl | hrB
    · exact hry'
    · by_cases hro : r = o
      · subst r
        exact hry'
      · have hor : s(o, r) ∈ ω := ((mem_starEvent_iff o B ω).1 hσ r hro).2 hrB
        have hadj : (openGraph ω).Adj o r :=
          (openGraph_adj ω o r).2 ⟨hor, Ne.symm hro⟩
        exact hadj.reachable.trans hry'

/-- The event that the centre hits `A` is, on a fixed star event, the event that the corresponding
source set hits `A` after the star is deleted. -/
private theorem star_hits_iff {ω : BondConfig V} {o : V} {B : Set V}
    (hσ : ω ∈ starEvent o B) (A : Finset V) :
    ω ∈ (⋃ x ∈ A, openConn o x : Set (BondConfig V)) ↔
      ∃ s ∈ insert o B, ∃ t ∈ A, (openGraph (ω \ starPairs o)).Reachable s t := by
  have hC := openCluster_eq_sourceCluster_of_starEvent hσ
  constructor
  · intro hω
    obtain ⟨t, htA, hot⟩ := Set.mem_iUnion₂.1 hω
    have htC : t ∈ openCluster ω o := hot
    rw [hC] at htC
    obtain ⟨s, hs, hst⟩ := Set.mem_iUnion₂.1 htC
    exact ⟨s, hs, t, htA, hst⟩
  · rintro ⟨s, hs, t, htA, hst⟩
    have htC : t ∈ sourceCluster (ω \ starPairs o) (insert o B) :=
      Set.mem_iUnion₂.2 ⟨s, hs, hst⟩
    rw [← hC] at htC
    exact Set.mem_iUnion₂.2 ⟨t, htA, htC⟩

/-- If the deleted-star source avoids `a`, then restoring that fixed star does not change the
cluster of `a`.  Indeed, any first use of a star pair would already join `a` to a source vertex. -/
private theorem openCluster_eq_delete_of_sourceAvoid {ω : BondConfig V} {o a : V}
    {B : Set V} (hσ : ω ∈ starEvent o B)
    (hav : ∀ s ∈ insert o B, ¬ (openGraph (ω \ starPairs o)).Reachable s a) :
    openCluster ω a = openCluster (ω \ starPairs o) a := by
  let η : BondConfig V := ω \ starPairs o
  have hηω : η ⊆ ω := sdiff_subset
  have hmono : openGraph η ≤ openGraph ω := openGraph_mono hηω
  have hwalk : ∀ {x y : V}, (openGraph η).Reachable a x →
      (openGraph ω).Walk x y → (openGraph η).Reachable a y := by
    intro x y hax p
    induction p with
    | nil => exact hax
    | cons hadj p ih =>
        apply ih
        rename_i x z y
        have he : s(x, z) ∈ ω ∧ x ≠ z := (openGraph_adj ω x z).1 hadj
        by_cases heD : s(x, z) ∈ starPairs o
        · have ho : o ∈ s(x, z) := heD
          rcases Sym2.mem_iff.1 ho with hox | hoz
          · subst x
            exact False.elim (hav o (Or.inl rfl) hax.symm)
          · subst z
            have hxo : x ≠ o := he.2
            have hoxEdge : s(o, x) ∈ ω := by
              rw [Sym2.eq_swap]
              exact he.1
            have hxB : x ∈ B := ((mem_starEvent_iff o B ω).1 hσ x hxo).1 hoxEdge
            exact False.elim (hav x (Or.inr hxB) hax.symm)
        · have hadjη : (openGraph η).Adj x z :=
            (openGraph_adj η x z).2 ⟨⟨he.1, heD⟩, he.2⟩
          exact hax.trans hadjη.reachable
  ext y
  constructor
  · intro hay
    obtain ⟨p⟩ := (hay : (openGraph ω).Reachable a y)
    exact hwalk (SimpleGraph.Reachable.refl a) p
  · intro hay
    exact (hay : (openGraph η).Reachable a y).mono hmono

/-! ## The exact integrand on one star slice -/

private def centreHits (o : V) (A : Finset V) : Set (BondConfig V) :=
  ⋃ x ∈ A, openConn o x

private def sourceAvoidFin (S : Finset V) (a : V) : Set (BondConfig V) :=
  {ω | ∀ s ∈ S, ¬ (openGraph ω).Reachable s a}

private def sourceHitsFin (S T : Finset V) : Set (BondConfig V) :=
  {ω | ∃ s ∈ S, ∃ t ∈ T, (openGraph ω).Reachable s t}

private def sourceGap (F : Set V → ℝ) (S : Finset V) (a : V)
    (ω : BondConfig V) : ℝ :=
  F (sourceCluster ω (↑S : Set V)) - F (openCluster ω a)

/-- On a fixed star configuration, the full-graph difference on `{o ↔ A}` is exactly the
deleted-star set-source gap on `{S ↮ a, S ↔ A \ {a}}`. -/
private theorem star_gap_pointwise (ω : BondConfig V) (o a : V)
    (A B S T : Finset V) (F : Set V → ℝ)
    (hS : ∀ x, x ∈ S ↔ x = o ∨ x ∈ B)
    (hT : ∀ x, x ∈ T ↔ x ∈ A ∧ x ≠ a)
    (hσ : ω ∈ starEvent o (↑B : Set V)) :
    (centreHits o A).indicator
        (fun ξ ↦ F (openCluster ξ o) - F (openCluster ξ a)) ω =
      (sourceAvoidFin S a ∩ sourceHitsFin S T).indicator
        (sourceGap F S a) (ω \ starPairs o) := by
  let η : BondConfig V := ω \ starPairs o
  by_cases hconn : ∃ s ∈ S, (openGraph η).Reachable s a
  · obtain ⟨s, hsS, hsa⟩ := hconn
    have hsSet : s ∈ insert o (↑B : Set V) := by
      rcases (hS s).1 hsS with rfl | hsB
      · exact Or.inl rfl
      · exact Or.inr (Finset.mem_coe.2 hsB)
    have haSource : a ∈ sourceCluster η (insert o (↑B : Set V)) :=
      Set.mem_iUnion₂.2 ⟨s, hsSet, hsa⟩
    have hoa : (openGraph ω).Reachable o a := by
      change a ∈ openCluster ω o
      rw [openCluster_eq_sourceCluster_of_starEvent hσ]
      exact haSource
    have hclusters : openCluster ω o = openCluster ω a :=
      Percolation.Literature.KNPreFKG.openCluster_eq_of_reachable hoa
    have hnotE : η ∉ sourceAvoidFin S a ∩ sourceHitsFin S T := by
      intro hE
      exact hE.1 s hsS hsa
    rw [Set.indicator_of_notMem hnotE]
    have hgap : F (openCluster ω o) - F (openCluster ω a) = 0 := by
      rw [hclusters, sub_self]
    by_cases hU : ω ∈ centreHits o A
    · rw [Set.indicator_of_mem hU, hgap]
    · rw [Set.indicator_of_notMem hU]
  · have hav : ∀ s ∈ S, ¬ (openGraph η).Reachable s a := by
      intro s hs hsa
      exact hconn ⟨s, hs, hsa⟩
    have hSset : (↑S : Set V) = insert o (↑B : Set V) := by
      ext x
      simp only [Finset.mem_coe, hS, mem_insert_iff]
    have hCo : openCluster ω o = sourceCluster η (↑S : Set V) := by
      rw [hSset]
      exact openCluster_eq_sourceCluster_of_starEvent hσ
    have hCa : openCluster ω a = openCluster η a := by
      apply openCluster_eq_delete_of_sourceAvoid hσ
      intro s hs
      apply hav s
      apply (hS s).2
      rcases hs with rfl | hsB
      · exact Or.inl rfl
      · exact Or.inr (Finset.mem_coe.1 hsB)
    have hhit : ω ∈ centreHits o A ↔
        ∃ s ∈ S, ∃ t ∈ A, (openGraph η).Reachable s t := by
      have hraw := star_hits_iff hσ A
      constructor
      · intro hU
        obtain ⟨s, hs, t, ht, hst⟩ := hraw.1 hU
        refine ⟨s, ?_, t, ht, hst⟩
        apply (hS s).2
        rcases hs with rfl | hsB
        · exact Or.inl rfl
        · exact Or.inr (Finset.mem_coe.1 hsB)
      · rintro ⟨s, hs, t, ht, hst⟩
        apply hraw.2
        refine ⟨s, ?_, t, ht, hst⟩
        rcases (hS s).1 hs with rfl | hsB
        · exact Or.inl rfl
        · exact Or.inr (Finset.mem_coe.2 hsB)
    have hEvent : ω ∈ centreHits o A ↔
        η ∈ sourceAvoidFin S a ∩ sourceHitsFin S T := by
      rw [hhit]
      simp only [sourceAvoidFin, sourceHitsFin, mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨s, hs, t, htA, hst⟩
        refine ⟨hav, s, hs, t, (hT t).2 ⟨htA, ?_⟩, hst⟩
        intro hta
        subst t
        exact (hav s hs) hst
      · rintro ⟨_, s, hs, t, htT, hst⟩
        exact ⟨s, hs, t, ((hT t).1 htT).1, hst⟩
    by_cases hU : ω ∈ centreHits o A
    · rw [Set.indicator_of_mem hU, Set.indicator_of_mem (hEvent.1 hU), sourceGap,
        hCo, hCa]
    · rw [Set.indicator_of_notMem hU,
        Set.indicator_of_notMem (mt hEvent.2 hU)]

/-- Exact integral decomposition on one deterministic star slice. -/
private theorem integral_star_slice_eq (w w₀ : Sym2 V → unitInterval) (o a : V)
    (hzero : ∀ e ∈ starPairs o, w₀ e = 0)
    (hkeep : ∀ e ∉ starPairs o, w₀ e = w e)
    (A B S T : Finset V) (F : Set V → ℝ)
    (hS : ∀ x, x ∈ S ↔ x = o ∨ x ∈ B)
    (hT : ∀ x, x ∈ T ↔ x ∈ A ∧ x ≠ a) :
    ∫ ω in centreHits o A ∩ starEvent o (↑B : Set V),
        (F (openCluster ω o) - F (openCluster ω a)) ∂(prodBernoulli w) =
      (prodBernoulli w).real (starEvent o (↑B : Set V)) *
        ∫ η in sourceAvoidFin S a ∩ sourceHitsFin S T,
          sourceGap F S a η ∂(prodBernoulli w₀) := by
  let U : Set (BondConfig V) := centreHits o A
  let σ : Set (BondConfig V) := starEvent o (↑B : Set V)
  let E : Set (BondConfig V) := sourceAvoidFin S a ∩ sourceHitsFin S T
  let gap : BondConfig V → ℝ := fun ω ↦
    F (openCluster ω o) - F (openCluster ω a)
  let gapH : BondConfig V → ℝ := sourceGap F S a
  have hrewrite : ∫ ω in U ∩ σ, gap ω ∂(prodBernoulli w) =
      ∫ ω in σ, E.indicator gapH (ω \ starPairs o) ∂(prodBernoulli w) := by
    calc
      (∫ ω in U ∩ σ, gap ω ∂(prodBernoulli w)) =
          ∫ ω in σ, U.indicator gap ω ∂(prodBernoulli w) := by
        rw [← integral_indicator (MeasurableSet.of_discrete : MeasurableSet (U ∩ σ)),
          ← integral_indicator (MeasurableSet.of_discrete : MeasurableSet σ),
          Set.indicator_indicator, inter_comm σ U]
      _ = ∫ ω in σ, E.indicator gapH (ω \ starPairs o) ∂(prodBernoulli w) := by
        refine setIntegral_congr_fun MeasurableSet.of_discrete fun ω hω ↦ ?_
        simpa only [U, σ, E, gap, gapH] using
          star_gap_pointwise ω o a A B S T F hS hT hω
  change (∫ ω in U ∩ σ, gap ω ∂(prodBernoulli w)) =
    (prodBernoulli w).real σ * ∫ η in E, gapH η ∂(prodBernoulli w₀)
  rw [hrewrite]
  change (∫ ω in starEvent o (↑B : Set V),
      E.indicator gapH (ω \ starPairs o) ∂(prodBernoulli w)) = _
  rw [setIntegral_starEvent_comp_delete w w₀ o hzero hkeep (↑B : Set V)
      (fun η ↦ E.indicator gapH η),
    integral_indicator (MeasurableSet.of_discrete : MeasurableSet E)]

/-! ## Reduction -/

/-- **Kozma--Nitzan Question 9 follows from the set-source fixed-minimizer inequality.**
The hypothesis is explicit: this theorem adds no conjectural axiom. -/
theorem question9_of_setSourceFixedMin (h : SetSourceFixedMin) : Question9 := by
  classical
  intro n w A o b a haA hmin
  set μ := prodBernoulli w with hμ
  set μH := prodBernoulli (deleteAt w o) with hμH
  set U : Set (BondConfig (Fin n)) := centreHits o A with hU
  set F : Set (Fin n) → ℝ := fun K ↦ if b ∈ K then 1 else 0 with hF
  have hFmono : Monotone F := by
    intro K L hKL
    simp only [hF]
    by_cases hbK : b ∈ K
    · rw [if_pos hbK, if_pos (hKL hbK)]
    · rw [if_neg hbK]
      split_ifs <;> norm_num
  have hFind : ∀ x : Fin n, (fun ω : BondConfig (Fin n) ↦ F (openCluster ω x)) =
      (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
    intro x
    funext ω
    simp only [hF]
    by_cases hω : ω ∈ (openConn x b : Set (BondConfig (Fin n)))
    · rw [Set.indicator_of_mem hω, Pi.one_apply,
        if_pos (show b ∈ openCluster ω x from hω)]
    · rw [Set.indicator_of_notMem hω,
        if_neg (show b ∉ openCluster ω x from hω)]
  have hmean : ∀ x ∈ A,
      (∫ ω, F (openCluster ω a) ∂μH) ≤ ∫ ω, F (openCluster ω x) ∂μH := by
    intro x hx
    have heq : ∀ z : Fin n,
        (∫ ω, F (openCluster ω z) ∂μH) = μH.real (openConn z b) := by
      intro z
      rw [hFind z, integral_indicator_one MeasurableSet.of_discrete]
    rw [heq, heq]
    rw [hμH]
    exact hmin x hx
  have hgapH : ∀ B : Finset (Fin n),
      0 ≤ ∫ η in sourceAvoidFin (insert o B) a ∩
          sourceHitsFin (insert o B) (A.erase a),
        sourceGap F (insert o B) a η ∂μH := by
    intro B
    have hB := h n (deleteAt w o) A (insert o B) a F haA hFmono
      (by simpa only [hμH] using hmean)
    simpa only [sourceAvoidFin, sourceHitsFin, sourceGap, hμH] using hB
  have hdelete_zero : ∀ e ∈ starPairs o, deleteAt w o e = 0 := by
    intro e he
    change o ∈ e at he
    unfold deleteAt
    rw [if_pos he]
  have hdelete_keep : ∀ e ∉ starPairs o, deleteAt w o e = w e := by
    intro e he
    change o ∉ e at he
    unfold deleteAt
    rw [if_neg he]
  have hgap : 0 ≤ ∫ ω in U,
      (F (openCluster ω o) - F (openCluster ω a)) ∂μ := by
    let V₀ : Finset (Fin n) := Finset.univ.erase o
    have hoV₀ : o ∉ V₀ := by simp [V₀]
    have hiso : ∀ u : Fin n, u ≠ o → u ∉ V₀ → w s(o, u) = 0 := by
      intro u huo hu
      exact False.elim (hu (Finset.mem_erase.2 ⟨huo, Finset.mem_univ u⟩))
    have hpart := Percolation.Literature.KNPreFKG.setIntegral_eq_sum_inter_starEvent
      w V₀ o hoV₀ hiso U
        (fun ω ↦ F (openCluster ω o) - F (openCluster ω a))
    rw [hμ, hpart]
    refine Finset.sum_nonneg fun B hBV₀ ↦ ?_
    rw [show U = centreHits o A from hU]
    have hSB : ∀ x, x ∈ insert o B ↔ x = o ∨ x ∈ B := fun x ↦ Finset.mem_insert
    have hTa : ∀ x, x ∈ A.erase a ↔ x ∈ A ∧ x ≠ a := by
      intro x
      rw [Finset.mem_erase]
      tauto
    rw [integral_star_slice_eq w (deleteAt w o) o a hdelete_zero hdelete_keep
      A B (insert o B) (A.erase a) F hSB hTa]
    exact mul_nonneg measureReal_nonneg (by simpa only [hμH] using hgapH B)
  have hint : ∀ x : Fin n,
      (∫ ω in U, F (openCluster ω x) ∂μ) =
        μ.real (openConn x b ∩ U) := by
    intro x
    rw [hFind x, ← integral_indicator (MeasurableSet.of_discrete : MeasurableSet U),
      Set.indicator_indicator,
      integral_indicator_one (MeasurableSet.of_discrete :
        MeasurableSet (U ∩ openConn x b)), inter_comm U]
  rw [integral_sub (Integrable.of_finite).integrableOn
    (Integrable.of_finite).integrableOn, hint, hint] at hgap
  rw [hμ, hU, centreHits] at hgap
  linarith

end KNAll

end

#print axioms KNAll.question9_of_setSourceFixedMin
