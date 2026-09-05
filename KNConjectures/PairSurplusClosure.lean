
import KNConjectures.GuardedDefs
import KNConjectures.GuardedBasic
import KNConjectures.GuardedKernel
import KNConjectures.GuardedDecoy
import KNConjectures.GuardedTwoCluster
import KNConjectures.PairGuardedCSH
import KNConjectures.PairSurplus
set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open Percolation.Literature.BHK2006 (weight integral_prodBernoulli_eq_sum continuous_weight)
open scoped Classical

variable {V : Type*} [Fintype V]

private theorem sourceInf_eq_of_mem_pattern (T : Finset V) (r : V → ℕ)
    (m : V → ℝ) (R Y : Set V) (a : V) (ha : a ∈ T)
    (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → m b ≤ m b')
    (ω : BondConfig V) (hω : ω ∈ sourceFirstPattern R Y T r a)
    (hne : (sourceReached R T ω).Nonempty) :
    (sourceReached R T ω).inf' hne m = m a := by
  have haF : a ∈ sourceReached R T ω := by
    exact Finset.mem_filter.2 ⟨ha, hω.2.1⟩
  refine le_antisymm (Finset.inf'_le m haF) (Finset.le_inf' hne m fun b hb => ?_)
  rw [sourceReached, Finset.mem_filter] at hb
  have hnot : ¬ r b < r a := by
    intro hlt
    have hno := mem_iInter₂.1 hω.2.2 b (Finset.mem_filter.2 ⟨hb.1, hlt⟩)
    exact hno hb.2
  rcases (not_lt.1 hnot).lt_or_eq with hlt | heq
  · exact hcompat a ha b hb.1 hlt
  · rw [hr ha hb.1 heq]

/-- Spec item 44: compatible ranks give the rank-free minimum formula. -/
theorem sourceSurplusY_eq_sourceMinFormY (w : Sym2 V → unitInterval)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (R : Set V)
    (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    sourceSurplusY w Y T r F R = sourceMinFormY w Y T F R := by
  set μ := prodBernoulli w with hμ
  set m : V → ℝ := fun a => condMean w Y F a with hm
  set g : BondConfig V → ℝ := fun ω =>
    if h : (sourceReached R T ω).Nonempty then
      (sourceReached R T ω).inf' h m
    else 0 with hg
  set U : Set (BondConfig V) :=
    sourceAvoid R Y ∩ sourceConn R (↑T : Set V) with hU
  have hmeas : ∀ S : Set (BondConfig V), MeasurableSet S :=
    fun _ => MeasurableSet.of_discrete
  have hint : ∀ (q : BondConfig V → ℝ) (S : Set (BondConfig V)),
      IntegrableOn q S μ := fun _ _ => (Integrable.of_finite).integrableOn
  have hg_pat : ∀ a ∈ T, ∀ ω ∈ sourceFirstPattern R Y T r a,
      g ω = m a := by
    intro a ha ω hω
    have hne : (sourceReached R T ω).Nonempty :=
      ⟨a, Finset.mem_filter.2 ⟨ha, hω.2.1⟩⟩
    simp only [hg, hne, dif_pos]
    exact sourceInf_eq_of_mem_pattern T r m R Y a ha hr hcompat ω hω hne
  have hsum :
      ∑ a ∈ T, μ.real (sourceFirstPattern R Y T r a) * m a =
        ∫ ω in U, g ω ∂μ := by
    rw [hU, ← sourceFirstPattern_cover R Y T r,
      integral_biUnion_finset T
        (fun a _ => hmeas (sourceFirstPattern R Y T r a))
        (sourceFirstPattern_disjoint R Y T r hr)
        (fun a _ => hint g (sourceFirstPattern R Y T r a))]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [setIntegral_congr_fun (hmeas _) (hg_pat a ha),
      setIntegral_const, smul_eq_mul]
  unfold sourceSurplusY sourceMinFormY
  change (∫ ω in U, F (sourceCluster ω R) ∂μ) -
      ∑ a ∈ T, μ.real (sourceFirstPattern R Y T r a) * m a =
    ∫ ω in U, F (sourceCluster ω R) - g ω ∂μ
  rw [integral_sub (hint _ _) (hint _ _), ← hsum]

private theorem continuousAt_setIntegral_source
    {n : ℕ} (U : Set (BondConfig (Fin n)))
    (q : (Sym2 (Fin n) → unitInterval) → BondConfig (Fin n) → ℝ)
    (w : Sym2 (Fin n) → unitInterval)
    (hq : ∀ ω, ContinuousAt (fun p => q p ω) w) :
    ContinuousAt (fun p : Sym2 (Fin n) → unitInterval =>
      ∫ ω in U, q p ω ∂(prodBernoulli p)) w := by
  have hU : MeasurableSet U := MeasurableSet.of_discrete
  have he : (fun p : Sym2 (Fin n) → unitInterval =>
      ∫ ω in U, q p ω ∂(prodBernoulli p)) =
      fun p => ∑ ω : Set (Sym2 (Fin n)),
        weight (fun e => (p e : ℝ)) ω * U.indicator (q p) ω := by
    funext p
    rw [← integral_indicator hU, integral_prodBernoulli_eq_sum]
  rw [he]
  refine tendsto_finsetSum Finset.univ fun ω _ =>
    (continuous_weight ω).continuousAt.mul ?_
  by_cases hω : ω ∈ U
  · simp only [indicator_of_mem hω]
    exact hq ω
  · simp only [indicator_of_notMem hω]
    exact continuousAt_const

/-- Spec item 45: continuity of the rank-free source minimum form. -/
theorem continuousAt_sourceMinFormY {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n))
    (T : Finset (Fin n)) (F : Set (Fin n) → ℝ) (R : Set (Fin n))
    (hact : ∀ a ∈ T, 0 < (prodBernoulli w).real
      (sourceAvoid ({a} : Set (Fin n)) Y)) :
    ContinuousAt (fun p => sourceMinFormY p Y T F R) w := by
  unfold sourceMinFormY
  refine continuousAt_setIntegral_source _ _ w fun ω => continuousAt_const.sub ?_
  by_cases hne : (sourceReached R T ω).Nonempty
  · simp only [hne, dif_pos]
    exact ContinuousAt.finset_inf'_apply hne fun a ha =>
      KNAll.continuousAt_condMean Y F a w (by
        have haT := (Finset.mem_filter.1 ha).1
        have hraw :
            {ω : BondConfig (Fin n) |
              ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y} =
              sourceAvoid ({a} : Set (Fin n)) Y := by
          ext ω
          simp [sourceAvoid]
        rw [hraw]
        exact hact a haT)
  · simp only [hne, dif_neg, not_false_eq_true]
    exact continuousAt_const

/-- Spec item 46: the pair-source first-relay inequality for arbitrary weights. -/
theorem pairSource_surplusY_all {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n))
    (T : Finset (Fin n)) (r : Fin n → ℕ) (s₁ s₂ : Fin n)
    (F : Set (Fin n) → ℝ)
    (hdis : Disjoint ({s₁, s₂} : Set (Fin n)) (Y ∪ (↑T : Set (Fin n))))
    (hTY : Disjoint (↑T : Set (Fin n)) Y)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli w).real
      (sourceAvoid ({a} : Set (Fin n)) Y))
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set (Fin n)))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ sourceSurplusY w Y T r F ({s₁, s₂} : Set (Fin n)) := by
  have hmin : 0 ≤ sourceMinFormY w Y T F ({s₁, s₂} : Set (Fin n)) := by
    apply KNAll.weights_le_of_forall_pos_lt_one_at w continuousAt_const
      (continuousAt_sourceMinFormY w Y T F ({s₁, s₂} : Set (Fin n)) hact)
    intro p hp
    obtain ⟨r', hr', hc'⟩ :=
      AGloc.exists_rank_compat T (fun a => condMean p Y F a)
    have h := pairSource_surplusY_nondegenerate p hp Y T r' s₁ s₂ F
      hdis hTY hF hr' hc'
    rwa [sourceSurplusY_eq_sourceMinFormY p Y T r' F
      ({s₁, s₂} : Set (Fin n)) hr' hc'] at h
  rw [sourceSurplusY_eq_sourceMinFormY w Y T r F
    ({s₁, s₂} : Set (Fin n)) hr hcompat]
  exact hmin

end KNAll.Guarded

end
