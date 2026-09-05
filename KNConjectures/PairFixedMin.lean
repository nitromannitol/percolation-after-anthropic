
import KNConjectures.PairSource

import KNConjectures.GuardedDefs
import KNConjectures.GuardedBasic
import KNConjectures.GuardedKernel
import KNConjectures.GuardedDecoy
import KNConjectures.GuardedTwoCluster
import KNConjectures.PairGuardedCSH
import KNConjectures.PairSurplus
import KNConjectures.PairSurplusClosure
set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH

/-- Spec item 47: FM2 when the pair source is disjoint from all relays. -/
theorem pair_fixedMin_disjoint {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (v w' a : Fin n) (F : Set (Fin n) → ℝ)
    (ha : a ∈ A) (hdis : Disjoint ({v, w'} : Set (Fin n)) (↑A : Set (Fin n)))
    (hF : Monotone F)
    (hmin : ∀ x ∈ A,
      (∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
        ∫ ω, F (openCluster ω x) ∂(prodBernoulli w)) :
    0 ≤ pairFixedMinGap w A v w' a F := by
  letI : DecidableEq (Fin n) := Classical.decEq _
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S :=
    fun _ => MeasurableSet.of_discrete
  have hn := fun (S : Set (BondConfig (Fin n))) =>
    (measureReal_nonneg : 0 ≤ μ.real S)
  have hint : ∀ (g : BondConfig (Fin n) → ℝ) (S : Set (BondConfig (Fin n))),
      IntegrableOn g S μ := fun _ _ => (Integrable.of_finite).integrableOn
  set Φ : Set (Fin n) → ℝ := projFunA w a F with hΦ
  have hΦmono : Monotone Φ := monotone_projFunA w a F hF
  set T : Finset (Fin n) := (A.erase a).filter (fun x =>
    0 < μ.real {ω : BondConfig (Fin n) |
      ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y}) with hT
  have hTA : ∀ x ∈ T, x ∈ A.erase a :=
    fun x hx => (Finset.mem_filter.1 hx).1
  have hTY : Disjoint (↑T : Set (Fin n)) ({a} : Set (Fin n)) := by
    rw [Set.disjoint_left]
    intro x hxT hxa
    exact Finset.ne_of_mem_erase (hTA x hxT) (mem_singleton_iff.1 hxa)
  have hactRaw : ∀ x ∈ T, 0 < μ.real
      {ω : BondConfig (Fin n) |
        ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} :=
    fun x hx => (Finset.mem_filter.1 hx).2
  have hact : ∀ x ∈ T, 0 < μ.real
      (sourceAvoid ({x} : Set (Fin n)) ({a} : Set (Fin n))) := by
    intro x hx
    have heq : sourceAvoid ({x} : Set (Fin n)) ({a} : Set (Fin n)) =
        {ω : BondConfig (Fin n) |
          ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} := by
      ext ω
      simp [sourceAvoid]
    rw [heq]
    exact hactRaw x hx
  have hmean : ∀ x ∈ T, 0 ≤ condMean w ({a} : Set (Fin n)) Φ x := by
    intro x hx
    unfold condMean
    refine div_nonneg ?_ (hn _)
    rw [hΦ, KNAll.setIntegral_projFunA_avoid w a x F]
    exact sub_nonneg.2 (hmin x (Finset.mem_of_mem_erase (hTA x hx)))
  obtain ⟨r, hr, hcompat⟩ :=
    AGloc.exists_rank_compat T (condMean w ({a} : Set (Fin n)) Φ)
  have hsource : Disjoint ({v, w'} : Set (Fin n))
      (({a} : Set (Fin n)) ∪ (↑T : Set (Fin n))) := by
    apply hdis.mono_right
    intro x hx
    rcases hx with hxa | hxT
    · have hxa' : x = a := by simpa using hxa
      simpa [hxa'] using ha
    · exact Finset.mem_coe.2 (Finset.mem_of_mem_erase (hTA x hxT))
  have hsag := pairSource_surplusY_all w ({a} : Set (Fin n)) T r v w' Φ
    hsource hTY hact hΦmono hr hcompat
  have hsum0 : 0 ≤ ∑ x ∈ T, μ.real
      (sourceFirstPattern ({v, w'} : Set (Fin n)) ({a} : Set (Fin n)) T r x) *
        condMean w ({a} : Set (Fin n)) Φ x :=
    Finset.sum_nonneg fun x hx => mul_nonneg (hn _) (hmean x hx)
  have hproj : 0 ≤ ∫ ω in
      sourceAvoid ({v, w'} : Set (Fin n)) ({a} : Set (Fin n)) ∩
        sourceConn ({v, w'} : Set (Fin n)) (↑T : Set (Fin n)),
      Φ (sourceCluster ω ({v, w'} : Set (Fin n))) ∂μ := by
    unfold sourceSurplusY at hsag
    linarith
  rw [KNAll.Guarded.sourceAvoid_pair, KNAll.Guarded.sourceConn_pair] at hproj
  simp_rw [KNAll.Guarded.sourceCluster_pair] at hproj
  have hactive : 0 ≤ ∫ ω in pairAvoid v w' a ∩ pairConn v w' T,
      (F (pairCluster ω v w') - F (openCluster ω a)) ∂μ := by
    rw [KNAll.setIntegral_sub_eq_projFunA_pair_conn w v w' a F T]
    simpa [hΦ] using hproj
  set E : Set (BondConfig (Fin n)) :=
    pairAvoid v w' a ∩ pairConn v w' (A.erase a) with hE
  set ET : Set (BondConfig (Fin n)) :=
    pairAvoid v w' a ∩ pairConn v w' T with hET
  set g : BondConfig (Fin n) → ℝ := fun ω =>
    F (pairCluster ω v w') - F (openCluster ω a) with hg
  have hETE : ET ⊆ E := by
    intro ω hω
    refine ⟨hω.1, ?_⟩
    obtain ⟨x, hxT, hx⟩ := hω.2
    exact ⟨x, hTA x hxT, hx⟩
  have hnull : μ (E \ ET) = 0 := by
    have hsub : E \ ET ⊆ ⋃ x ∈ (A.erase a).filter (fun x =>
        ¬ 0 < μ.real {ω : BondConfig (Fin n) |
          ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y}),
        {ω : BondConfig (Fin n) |
          ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} := by
      intro ω hω
      obtain ⟨⟨havoid, hconn⟩, hnot⟩ := hω
      obtain ⟨x, hxA, hvx | hwx⟩ := hconn
      · have hxT : x ∉ T := fun hxT => hnot
          ⟨havoid, ⟨x, hxT, Or.inl hvx⟩⟩
        have hinact : ¬ 0 < μ.real {ω : BondConfig (Fin n) |
            ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} :=
          fun hp => hxT (Finset.mem_filter.2 ⟨hxA, hp⟩)
        refine mem_iUnion₂.2 ⟨x, Finset.mem_filter.2 ⟨hxA, hinact⟩, ?_⟩
        intro y hy hxy
        have hya : y = a := by simpa using hy
        subst y
        exact havoid.1 (hvx.trans hxy)
      · have hxT : x ∉ T := fun hxT => hnot
          ⟨havoid, ⟨x, hxT, Or.inr hwx⟩⟩
        have hinact : ¬ 0 < μ.real {ω : BondConfig (Fin n) |
            ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} :=
          fun hp => hxT (Finset.mem_filter.2 ⟨hxA, hp⟩)
        refine mem_iUnion₂.2 ⟨x, Finset.mem_filter.2 ⟨hxA, hinact⟩, ?_⟩
        intro y hy hxy
        have hya : y = a := by simpa using hy
        subst y
        exact havoid.2 (hwx.trans hxy)
    refine measure_mono_null hsub
      (measure_biUnion_null_iff (Finset.countable_toSet _) |>.2 fun x hx => ?_)
    have h0 : μ.real {ω : BondConfig (Fin n) |
        ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} = 0 :=
      le_antisymm (not_lt.1 (Finset.mem_filter.1 hx).2) (hn _)
    rwa [Measure.real, ENNReal.toReal_eq_zero_iff,
      or_iff_left (measure_ne_top _ _)] at h0
  have hsplit : ∫ ω in E, g ω ∂μ = ∫ ω in ET, g ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas ET) (hint g E),
      inter_eq_right.2 hETE, Measure.restrict_eq_zero.2 hnull,
      integral_zero_measure, add_zero]
  have hEpos : 0 ≤ ∫ ω in E, g ω ∂μ := by
    rw [hsplit]
    exact hactive
  rw [hE, hg, hμ] at hEpos
  simpa only [KNAll.pairFixedMinGap] using hEpos

/-- Spec item 48: FM2 vanishes when the minimizing relay is a source endpoint. -/
theorem pair_fixedMin_of_minimizer_mem {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (v w' a : Fin n) (F : Set (Fin n) → ℝ)
    (haS : a = v ∨ a = w') :
    pairFixedMinGap w A v w' a F = 0 := by
  rcases haS with hav | haw
  · subst a
    have hzero : pairAvoid v w' v = (∅ : Set (BondConfig (Fin n))) := by
      ext ω
      simp [pairAvoid]
    simp [pairFixedMinGap, hzero]
  · subst a
    have hzero : pairAvoid v w' w' = (∅ : Set (BondConfig (Fin n))) := by
      ext ω
      simp [pairAvoid]
    simp [pairFixedMinGap, hzero]

/-- Spec item 49: overlap with a non-minimizing relay is handled by conditional BHK. -/
theorem pair_fixedMin_overlap {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (v w' a : Fin n) (F : Set (Fin n) → ℝ)
    (hover : v ∈ A.erase a ∨ w' ∈ A.erase a) (hF : Monotone F)
    (hmin : ∀ x ∈ A,
      (∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
        ∫ ω, F (openCluster ω x) ∂(prodBernoulli w)) :
    0 ≤ pairFixedMinGap w A v w' a F := by
  rcases hover with hv | hw'
  · have hconn : pairConn v w' (A.erase a) =
        (Set.univ : Set (BondConfig (Fin n))) := by
      apply eq_univ_of_forall
      intro ω
      exact ⟨v, hv, Or.inl (SimpleGraph.Reachable.refl v)⟩
    have hevent : pairAvoid v w' a ∩ pairConn v w' (A.erase a) =
        pairAvoid v w' a := by
      calc
        _ = pairAvoid v w' a ∩ (Set.univ : Set (BondConfig (Fin n))) :=
          congrArg (pairAvoid v w' a ∩ ·) hconn
        _ = _ := inter_univ _
    have hintEq := congrArg (fun U : Set (BondConfig (Fin n)) =>
      ∫ ω in U, F (pairCluster ω v w') - F (openCluster ω a)
        ∂(prodBernoulli w)) hevent
    have hpos : 0 ≤ ∫ ω in pairAvoid v w' a ∩ pairConn v w' (A.erase a),
        F (pairCluster ω v w') - F (openCluster ω a) ∂(prodBernoulli w) :=
      hintEq.symm ▸ KNAll.overlap_pair w v w' a F hF
        (hmin v (Finset.mem_of_mem_erase hv))
    unfold pairFixedMinGap
    convert hpos using 1
    apply setIntegral_congr_set
    exact Filter.Eventually.of_forall fun ω => by simp [pairConn]
  · have hconn : pairConn v w' (A.erase a) =
        (Set.univ : Set (BondConfig (Fin n))) := by
      apply eq_univ_of_forall
      intro ω
      exact ⟨w', hw', Or.inr (SimpleGraph.Reachable.refl w')⟩
    have hevent : pairAvoid v w' a ∩ pairConn v w' (A.erase a) =
        pairAvoid v w' a := by
      calc
        _ = pairAvoid v w' a ∩ (Set.univ : Set (BondConfig (Fin n))) :=
          congrArg (pairAvoid v w' a ∩ ·) hconn
        _ = _ := inter_univ _
    have hintEq := congrArg (fun U : Set (BondConfig (Fin n)) =>
      ∫ ω in U, F (pairCluster ω v w') - F (openCluster ω a)
        ∂(prodBernoulli w)) hevent
    have hoverlap : 0 ≤ ∫ ω in pairAvoid v w' a,
        F (pairCluster ω v w') - F (openCluster ω a) ∂(prodBernoulli w) := by
      simpa [pairCluster, pairAvoid, Set.union_comm, and_comm] using
        KNAll.overlap_pair w w' v a F hF
          (hmin w' (Finset.mem_of_mem_erase hw'))
    have hpos : 0 ≤ ∫ ω in pairAvoid v w' a ∩ pairConn v w' (A.erase a),
        F (pairCluster ω v w') - F (openCluster ω a) ∂(prodBernoulli w) :=
      hintEq.symm ▸ hoverlap
    unfold pairFixedMinGap
    convert hpos using 1
    apply setIntegral_congr_set
    exact Filter.Eventually.of_forall fun ω => by simp [pairConn]

/-- Spec item 50: FM2 in all coincidence and overlap cases. -/
theorem pair_fixedMin {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (v w' a : Fin n) (F : Set (Fin n) → ℝ)
    (ha : a ∈ A) (hF : Monotone F)
    (hmin : ∀ x ∈ A,
      (∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
        ∫ ω, F (openCluster ω x) ∂(prodBernoulli w)) :
    0 ≤ pairFixedMinGap w A v w' a F := by
  by_cases haS : a = v ∨ a = w'
  · rw [pair_fixedMin_of_minimizer_mem w A v w' a F haS]
  by_cases hover : v ∈ A.erase a ∨ w' ∈ A.erase a
  · exact pair_fixedMin_overlap w A v w' a F hover hF hmin
  apply pair_fixedMin_disjoint w A v w' a F ha
  · rw [Set.disjoint_left]
    intro x hxS hxA
    rcases hxS with hxv | hxw
    · have hvA : v ∈ A := hxv ▸ hxA
      have hva : v ≠ a := by
        intro hva
        exact haS (Or.inl (hva.symm))
      exact hover (Or.inl (Finset.mem_erase.2 ⟨hva, hvA⟩))
    · have hwA : w' ∈ A := hxw ▸ hxA
      have hwa : w' ≠ a := by
        intro hwa
        exact haS (Or.inr (hwa.symm))
      exact hover (Or.inr (Finset.mem_erase.2 ⟨hwa, hwA⟩))
  · exact hF
  · exact hmin

end KNAll.Guarded

end
