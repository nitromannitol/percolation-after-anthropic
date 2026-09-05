import KNConjectures.AvoidedPeelTools

/-!
# Closure of the avoided surplus-transfer inequality

The avoided ranked surplus agrees with a rank-free minimum form whenever the
rank is compatible with the avoided conditional relay means.  At weights for
which every relay's avoidance event is active, that minimum form is continuous.
This permits passage from nondegenerate weights to arbitrary weights.
-/

noncomputable section

namespace KNAll

open MeasureTheory Set
open Percolation.Literature.LatticeModels
open Percolation.Literature
open Percolation.Literature.BHK2006 (weight integral_prodBernoulli_eq_sum continuous_weight)
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {n : ℕ}

/-- The avoided ranked surplus equals its rank-free minimum form for an
injective rank compatible with the avoided conditional relay means. -/
theorem surplusY_eq_minForm (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n))
    (T : Finset (Fin n)) (r : Fin n → ℕ) (F : Set (Fin n) → ℝ) (x : Fin n)
    (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → condMean w Y F b ≤ condMean w Y F b') :
    surplusY w Y T r F x =
      ∫ ω in { ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y } ∩
          ⋃ a ∈ T, openConn x a,
        (F (openCluster ω x) -
          (if h : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty then
            (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' h
              (fun b => condMean w Y F b)
          else 0)) ∂(prodBernoulli w) := by
  set μ := prodBernoulli w with hμ
  set m : Fin n → ℝ := fun b => condMean w Y F b with hm
  set g : BondConfig (Fin n) → ℝ := fun ω =>
    if h : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty then
      (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' h m
    else 0 with hg
  set Av : Set (BondConfig (Fin n)) :=
    {ω | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y} with hAv
  set pat : Fin n → Set (BondConfig (Fin n)) := fun a =>
    (openConn x a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn x a')ᶜ :
      Set (BondConfig (Fin n))) with hpat
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S :=
    fun _ => MeasurableSet.of_discrete
  have hint : ∀ (f : BondConfig (Fin n) → ℝ) (S : Set (BondConfig (Fin n))),
      IntegrableOn f S μ := fun _ _ => (Integrable.of_finite).integrableOn
  have hg_pat : ∀ a ∈ T, ∀ ω ∈ Av ∩ pat a, g ω = m a := by
    intro a ha ω hω
    have hne : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty :=
      ⟨a, Finset.mem_filter.2 ⟨ha, hω.2.1⟩⟩
    simp only [hg, hne, dif_pos]
    exact CSH.inf'_eq_of_mem_pattern T r m x a ha hr hcompat ω hω.2 hne
  have hdisj : Set.PairwiseDisjoint (↑T : Set (Fin n)) (fun a => Av ∩ pat a) := by
    intro a ha b hb hab
    exact (AGloc.firstRank_disjoint T r x hr ha hb hab).mono inter_subset_right inter_subset_right
  have hsum : ∑ a ∈ T, μ.real (Av ∩ pat a) * m a =
      ∫ ω in Av ∩ ⋃ a ∈ T, openConn x a, g ω ∂μ := by
    rw [← AGloc.firstRank_cover T r x, inter_iUnion₂,
      integral_biUnion_finset T (fun a _ => hmeas (Av ∩ pat a)) hdisj
        (fun a _ => hint g (Av ∩ pat a))]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [setIntegral_congr_fun (hmeas (Av ∩ pat a)) (hg_pat a ha),
      setIntegral_const, smul_eq_mul]
  unfold surplusY
  rw [integral_sub (hint _ _) (hint _ _), ← hsum]

/-- The avoided conditional relay mean is continuous at every weight where its
conditioning event has positive probability. -/
theorem continuousAt_condMean (Y : Set (Fin n)) (F : Set (Fin n) → ℝ) (a : Fin n)
    (w : Sym2 (Fin n) → unitInterval)
    (hw : 0 < (prodBernoulli w).real
      {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}) :
    ContinuousAt (fun p : Sym2 (Fin n) → unitInterval => condMean p Y F a) w := by
  unfold condMean
  have hnum : ContinuousAt (fun p : Sym2 (Fin n) → unitInterval =>
      ∫ ω in {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y},
        F (openCluster ω a) ∂(prodBernoulli p)) w :=
    (CSH.continuous_setIntegral_weights
      {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}
      (fun _ ω => F (openCluster ω a)) (fun _ => continuous_const)).continuousAt
  have hden : ContinuousAt (fun p : Sym2 (Fin n) → unitInterval =>
      (prodBernoulli p).real
        {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}) w :=
    (prodBernoulli_real_continuous _).continuousAt
  exact ContinuousAt.div₀ hnum hden hw.ne'

private theorem continuousAt_setIntegral_weightsY (U : Set (BondConfig (Fin n)))
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

/-- The avoided minimum form is continuous at weights for which all relays are
active. -/
theorem continuousAt_minFormY (Y : Set (Fin n)) (T : Finset (Fin n))
    (F : Set (Fin n) → ℝ) (x : Fin n) (w : Sym2 (Fin n) → unitInterval)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli w).real
      {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}) :
    ContinuousAt (fun p : Sym2 (Fin n) → unitInterval =>
      ∫ ω in { ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y } ∩
          ⋃ a ∈ T, openConn x a,
        (F (openCluster ω x) -
          (if h : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty then
            (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' h
              (fun b => condMean p Y F b)
          else 0)) ∂(prodBernoulli p)) w := by
  refine continuousAt_setIntegral_weightsY _ _ w fun ω => continuousAt_const.sub ?_
  by_cases hne : (T.filter fun b => ω ∈
      (openConn x b : Set (BondConfig (Fin n)))).Nonempty
  · simp only [hne, dif_pos]
    exact ContinuousAt.finset_inf'_apply hne fun b hb =>
      continuousAt_condMean Y F b w (hact b (Finset.mem_filter.1 hb).1)
  · simp only [hne, dif_neg, not_false_eq_true]
    exact continuousAt_const

/-- Pointwise closure principle using continuity only at the target weight. -/
theorem weights_le_of_forall_pos_lt_one_at
    {f g : (Sym2 (Fin n) → unitInterval) → ℝ} (w : Sym2 (Fin n) → unitInterval)
    (hf : ContinuousAt f w) (hg : ContinuousAt g w)
    (h : ∀ p, (∀ e, 0 < p e ∧ p e < 1) → f p ≤ g p) : f w ≤ g w := by
  let N : Set (Sym2 (Fin n) → unitInterval) :=
    {p | ∀ e, 0 < p e ∧ p e < 1}
  have hN : Dense N := by
    simpa only [N] using
      (dense_setOf_weights_pos_lt_one : Dense
        {p : Sym2 (Fin n) → unitInterval | ∀ e, 0 < p e ∧ p e < 1})
  have hwN : w ∈ closure N := by
    rw [hN.closure_eq]
    exact mem_univ w
  letI : Filter.NeBot (nhdsWithin w N) := mem_closure_iff_nhdsWithin_neBot.1 hwN
  have hft : Filter.Tendsto f (nhdsWithin w N) (nhds (f w)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hgt : Filter.Tendsto g (nhdsWithin w N) (nhds (g w)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  have hfg : ∀ᶠ p in nhdsWithin w N, f p ≤ g p :=
    eventually_nhdsWithin_of_forall fun p hp => h p hp
  exact le_of_tendsto_of_tendsto hft hgt hfg

/-- The avoided surplus-transfer inequality for arbitrary weights follows from
the corresponding assertion for nondegenerate weights, provided all relays are
active at the target weight. -/
theorem surplusTransferY_of_nondegenerate (Y : Set (Fin n)) (T : Finset (Fin n))
    (o v : Fin n) (F : Set (Fin n) → ℝ)
    (h : ∀ p : Sym2 (Fin n) → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ r : Fin n → ℕ, Set.InjOn r ↑T →
        (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
          condMean p Y F a ≤ condMean p Y F a') →
        (prodBernoulli p).real
            ({ω : BondConfig (Fin n) |
                ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
              surplusY p Y T r F v ≤
          (prodBernoulli p).real
              {ω : BondConfig (Fin n) |
                ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} *
              surplusY p Y T r F o)
    (w : Sym2 (Fin n) → unitInterval)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli w).real
      {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y})
    (r : Fin n → ℕ) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    (prodBernoulli w).real
        ({ω : BondConfig (Fin n) |
            ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
          surplusY w Y T r F v ≤
      (prodBernoulli w).real
          {ω : BondConfig (Fin n) |
            ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} *
          surplusY w Y T r F o := by
  set S : Fin n → (Sym2 (Fin n) → unitInterval) → ℝ := fun x p =>
    ∫ ω in {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y} ∩
        ⋃ a ∈ T, openConn x a,
      (F (openCluster ω x) -
        (if h : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty then
          (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' h
            (fun b => condMean p Y F b)
        else 0)) ∂(prodBernoulli p) with hS
  set f : (Sym2 (Fin n) → unitInterval) → ℝ := fun p =>
    (prodBernoulli p).real
        ({ω : BondConfig (Fin n) |
            ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
      S v p with hf
  set g : (Sym2 (Fin n) → unitInterval) → ℝ := fun p =>
    (prodBernoulli p).real
        {ω : BondConfig (Fin n) |
          ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} *
      S o p with hg
  have hfc : ContinuousAt f w := by
    simp only [hf, hS]
    exact
      ((prodBernoulli_real_continuous
            ({ω : BondConfig (Fin n) |
                ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} ∩ openConn o v)).continuousAt.mul
          (continuousAt_minFormY Y T F v w hact)).congr
        (Filter.Eventually.of_forall fun _ => rfl)
  have hgc : ContinuousAt g w := by
    simp only [hg, hS]
    exact
      ((prodBernoulli_real_continuous
            {ω : BondConfig (Fin n) |
              ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a}).continuousAt.mul
          (continuousAt_minFormY Y T F o w hact)).congr
        (Filter.Eventually.of_forall fun _ => rfl)
  have hfg : ∀ p : Sym2 (Fin n) → unitInterval,
      (∀ e, 0 < p e ∧ p e < 1) → f p ≤ g p := by
    intro p hp
    obtain ⟨r', hr', hc'⟩ := AGloc.exists_rank_compat T (fun a => condMean p Y F a)
    have key := h p hp r' hr' hc'
    rw [surplusY_eq_minForm p Y T r' F v hr' hc',
      surplusY_eq_minForm p Y T r' F o hr' hc'] at key
    exact key
  have hwfg := weights_le_of_forall_pos_lt_one_at w hfc hgc hfg
  simp only [hf, hg, hS] at hwfg
  rw [surplusY_eq_minForm w Y T r F v hr hcompat,
    surplusY_eq_minForm w Y T r F o hr hcompat]
  exact hwfg

end KNAll

end
