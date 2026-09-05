import KNConjectures.AvoidedDefs

/-!
# Avoided peeling: tools

The four identities of `Percolation/Continuity/CSH/PeelTools.lean` with a base avoided set `Y`:
* `surplusY_erase_add` — Lemma P: peeling the rank-maximal relay `k`;
* `kappaY_le_surplusY` — Lemma κ with conditional means;
* `covD_clusterFun_eq'`, `covD_psiIso'` — the `covD` identities for an arbitrary avoided set.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH Percolation.Literature.KNPreFKG
open scoped Classical

variable {n : ℕ}

/-- `∫_{a ↮ Y} F(C_a) = m_a^Y · P(a ↮ Y)` (also when the denominator vanishes). -/
theorem setIntegral_eq_condMean_mul (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (F : Set (Fin n) → ℝ) (a : (Fin n)) :
    ∫ ω in {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}, F (openCluster ω a) ∂(prodBernoulli w) =
      condMean w Y F a * (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y} := by
  unfold condMean
  by_cases h0 : (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y} = 0
  · rw [h0, mul_zero]
    have : (prodBernoulli w) {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y} = 0 := by
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h0
    rw [Measure.restrict_eq_zero.2 this, integral_zero_measure]
  · rw [div_mul_cancel₀ _ h0]

/-- The avoided first-in-rank patterns of `T` have total measure `P(u ↮ Y, u ↔ T)`. -/
theorem sum_measureReal_avoid_firstRank (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (T : Finset (Fin n)) (r : (Fin n) → ℕ) (u : (Fin n))
    (hr : Set.InjOn r ↑T) :
    ∑ a ∈ T, (prodBernoulli w).real
        ({ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable u y} ∩
          (openConn u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn u a')ᶜ) : Set (BondConfig (Fin n))) =
      (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable u y} ∩ ⋃ a ∈ T, openConn u a) := by
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun S => (Set.toFinite S).measurableSet
  have hdisj : Set.PairwiseDisjoint (↑T : Set (Fin n)) (fun a =>
      ({ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable u y} ∩
        (openConn u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn u a')ᶜ) : Set (BondConfig (Fin n)))) := by
    intro a ha b hb hab
    exact (AGloc.firstRank_disjoint T r u hr ha hb hab).mono inter_subset_right inter_subset_right
  rw [← AGloc.firstRank_cover T r u, inter_iUnion₂,
    measureReal_biUnion_finset hdisj (fun a _ => hmeas _) (fun _ _ => measure_ne_top _ _)]

/-- **Lemma P with avoided set**: for the rank-maximal relay `k ∈ T`, `T' = T.erase k`, `D_k = {k ↮ Y ∪ T'}` and every `u`,
`Sur^Y_u(T) = Sur^Y_u(T') + (∫_{D_k ∩ {k↔u}} F(C_k) − P(D_k ∩ {k↔u})·m_k^Y)`. -/
theorem surplusY_erase_add (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (T : Finset (Fin n)) (r : (Fin n) → ℕ) (F : Set (Fin n) → ℝ)
    {k : (Fin n)} (hkT : k ∈ T) (hlt : ∀ a ∈ T.erase k, r a < r k) (u : (Fin n)) :
    surplusY w Y T r F u = surplusY w Y (T.erase k) r F u +
      ((∫ ω in {ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑(T.erase k) : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩ openConn k u,
          F (openCluster ω k) ∂(prodBernoulli w)) -
        (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑(T.erase k) : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩
          openConn k u) * condMean w Y F k) := by
  set μ := prodBernoulli w with hμ
  set T' := T.erase k with hT'
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun S => (Set.toFinite S).measurableSet
  have hint : ∀ (g : BondConfig (Fin n) → ℝ) (S : Set (BondConfig (Fin n))), IntegrableOn g S μ :=
    fun g S => (Integrable.of_finite).integrableOn
  set f₀ : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω u) with hf₀
  set fk : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω k) with hfk
  set Av : Set (BondConfig (Fin n)) := {ω | ∀ y ∈ Y, ¬ (openGraph ω).Reachable u y} with hAv
  set UT : Set (BondConfig (Fin n)) := ⋃ a ∈ T', openConn u a with hUT
  set Ok : Set (BondConfig (Fin n)) := openConn u k with hOk
  set Dk : Set (BondConfig (Fin n)) := {ω | ∀ a ∈ Y ∪ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} with hDk
  have hfiltT : ∀ a ∈ T', T.filter (fun a' => r a' < r a) = T'.filter (fun a' => r a' < r a) := by
    intro a ha
    rw [hT', AGloc.filter_erase_of_not]
    exact fun h => lt_asymm h (hlt a ha)
  have hfiltk : T.filter (fun a' => r a' < r k) = T' := by
    ext a
    simp only [Finset.mem_filter, hT', Finset.mem_erase]
    constructor
    · rintro ⟨ha, h⟩; exact ⟨fun hak => lt_irrefl _ (hak ▸ h), ha⟩
    · rintro ⟨hak, ha⟩; exact ⟨ha, hlt a (Finset.mem_erase.2 ⟨hak, ha⟩)⟩
  -- the avoided `k`-pattern is `Dk ∩ {k ↔ u}`
  have hPk : (Av ∩ (openConn u k ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r k), (openConn u a')ᶜ) : Set (BondConfig (Fin n))) =
      Dk ∩ openConn k u := by
    rw [hfiltk]
    ext ω
    simp only [hAv, hDk, mem_inter_iff, mem_iInter, mem_compl_iff, openConn, mem_setOf_eq, Finset.mem_coe, mem_union]
    constructor
    · rintro ⟨hY, hk', h⟩
      refine ⟨fun a ha hka => ?_, hk'.symm⟩
      rcases ha with ha | ha
      · exact hY a ha (hk'.trans hka)
      · exact h a ha (hk'.trans hka)
    · rintro ⟨h, hk'⟩
      exact ⟨fun y hy hoy => h y (Or.inl hy) (hk'.trans hoy), hk'.symm, fun a ha hoa => h a (Or.inr ha) (hk'.trans hoa)⟩
  have hsumT : ∑ a ∈ T, μ.real (Av ∩ (openConn u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn u a')ᶜ) :
        Set (BondConfig (Fin n))) * condMean w Y F a =
      ∑ a ∈ T', μ.real (Av ∩ (openConn u a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn u a')ᶜ) :
        Set (BondConfig (Fin n))) * condMean w Y F a + μ.real (Dk ∩ openConn k u) * condMean w Y F k := by
    rw [← Finset.add_sum_erase T _ hkT, hPk, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hfiltT a ha]
  have hUA : (Av ∩ ⋃ a ∈ T, (openConn u a : Set (BondConfig (Fin n)))) = (Av ∩ UT) ∪ (Av ∩ Ok) := by
    ext ω
    simp only [hUT, hOk, mem_inter_iff, mem_iUnion, mem_union, exists_prop, hT', Finset.mem_erase]
    constructor
    · rintro ⟨hA, a, ha, h⟩
      by_cases hak : a = k
      · exact Or.inr ⟨hA, hak ▸ h⟩
      · exact Or.inl ⟨hA, a, ⟨hak, ha⟩, h⟩
    · rintro (⟨hA, a, ⟨_, ha⟩, h⟩ | ⟨hA, h⟩)
      · exact ⟨hA, a, ha, h⟩
      · exact ⟨hA, k, hkT, h⟩
  have h0k : ∀ ω ∈ Dk ∩ openConn k u, f₀ ω = fk ω := fun ω hω => by
    simp only [hf₀, hfk]
    rw [openCluster_eq_of_reachable ((hω.2 : (openGraph ω).Reachable k u).symm)]
  have hdiff : ((Av ∩ UT) ∪ (Av ∩ Ok)) \ (Av ∩ UT) = Dk ∩ openConn k u := by
    ext ω
    simp only [hUT, hOk, hDk, hAv, mem_sdiff, mem_union, mem_iUnion, mem_inter_iff, exists_prop, not_exists, not_and, openConn,
      mem_setOf_eq, Finset.mem_coe]
    constructor
    · rintro ⟨⟨hA, h⟩ | ⟨hA, h⟩, hno⟩
      · obtain ⟨a, ha, h'⟩ := h; exact absurd h' (hno hA a ha)
      · refine ⟨fun a ha hka => ?_, h.symm⟩
        rcases ha with ha | ha
        · exact hA a ha (h.trans hka)
        · exact hno hA a ha (h.trans hka)
    · rintro ⟨hd, hk'⟩
      refine ⟨Or.inr ⟨fun y hy hoy => hd y (Or.inl hy) (hk'.trans hoy), hk'.symm⟩, fun _ a ha hoa => hd a (Or.inr ha) (hk'.trans hoa)⟩
  have hsplit : ∫ ω in (Av ∩ UT) ∪ (Av ∩ Ok), f₀ ω ∂μ = ∫ ω in Av ∩ UT, f₀ ω ∂μ + ∫ ω in Dk ∩ openConn k u, fk ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas (Av ∩ UT)) (hint f₀ _), inter_eq_right.2 subset_union_left, hdiff,
      setIntegral_congr_fun (hmeas _) fun ω hω => h0k ω hω]
  unfold surplusY
  rw [hsumT, hUA, hsplit]
  ring

/-- **Lemma κ with avoided set**: with `D_k = {k ↮ Y ∪ T'}` and `m_k^Y` maximal (`m_a^Y ≤ m_k^Y` for `a ∈ T'`),
`κ_k = m_k^Y · P(D_k) − ∫_{D_k} F(C_k) ≤ Sur^Y_k(T')`. -/
theorem kappaY_le_surplusY (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (T' : Finset (Fin n)) (r : (Fin n) → ℕ) (F : Set (Fin n) → ℝ)
    (k : (Fin n)) (hrT : Set.InjOn r ↑T') (hmle : ∀ a ∈ T', condMean w Y F a ≤ condMean w Y F k) :
    condMean w Y F k * (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} -
      ∫ ω in {ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a}, F (openCluster ω k) ∂(prodBernoulli w) ≤
      surplusY w Y T' r F k := by
  unfold surplusY
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun S => (Set.toFinite S).measurableSet
  have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
  set fk : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω k) with hfk
  set mk : ℝ := condMean w Y F k with hmk
  set Ak : Set (BondConfig (Fin n)) := {ω | ∀ y ∈ Y, ¬ (openGraph ω).Reachable k y} with hAk
  set Dk : Set (BondConfig (Fin n)) := {ω | ∀ a ∈ Y ∪ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} with hDk
  set Wk : Set (BondConfig (Fin n)) := ⋃ a ∈ T', openConn k a with hWk
  have hDW : Dk = Ak \ Wk := by
    ext ω
    simp only [hDk, hAk, hWk, mem_sdiff, mem_setOf_eq, mem_iUnion, openConn, not_exists, exists_prop, not_and, mem_union,
      Finset.mem_coe]
    constructor
    · intro h; exact ⟨fun y hy => h y (Or.inl hy), fun a ha => h a (Or.inr ha)⟩
    · rintro ⟨h1, h2⟩ a ha
      rcases ha with ha | ha
      · exact h1 a ha
      · exact h2 a ha
  have hAint : ∫ ω in Ak, fk ω ∂μ = ∫ ω in Ak ∩ Wk, fk ω ∂μ + ∫ ω in Dk, fk ω ∂μ := by
    rw [hDW]; exact (integral_inter_add_sdiff (hmeas Wk) (Integrable.of_finite.integrableOn)).symm
  have hAμ : μ.real Ak = μ.real (Ak ∩ Wk) + μ.real Dk := by
    rw [hDW]; exact (measureReal_inter_add_sdiff (s := Ak) (h := measure_ne_top _ _) (hmeas Wk)).symm
  have hmA : ∫ ω in Ak, fk ω ∂μ = mk * μ.real Ak := setIntegral_eq_condMean_mul w Y F k
  rw [hAμ, mul_add] at hmA
  have hWsum : ∑ a ∈ T', μ.real (Ak ∩ (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ) :
      Set (BondConfig (Fin n))) = μ.real (Ak ∩ Wk) := sum_measureReal_avoid_firstRank w Y T' r k hrT
  have hsum : ∑ a ∈ T', μ.real (Ak ∩ (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ) :
        Set (BondConfig (Fin n))) * condMean w Y F a ≤ mk * μ.real (Ak ∩ Wk) := by
    have : ∑ a ∈ T', μ.real (Ak ∩ (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ) :
          Set (BondConfig (Fin n))) * condMean w Y F a ≤
        ∑ a ∈ T', μ.real (Ak ∩ (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ) :
          Set (BondConfig (Fin n))) * mk :=
      Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hmle a ha) (hn _)
    rw [← Finset.sum_mul, hWsum] at this
    linarith
  change mk * μ.real Dk - ∫ ω in Dk, fk ω ∂μ ≤ (∫ ω in Ak ∩ Wk, fk ω ∂μ) -
    ∑ a ∈ T', μ.real (Ak ∩ (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ) :
      Set (BondConfig (Fin n))) * condMean w Y F a
  linarith [hsum, hAint, hAμ, hmA]

/-- **The top-relay term against `covD`, arbitrary avoided set `A` and arbitrary constant `m`.** With `F̂(C) = F(span_k C)`,
`D = {k ↮ A}`: `P(D)·(∫_{D ∩ {k↔u}} F(C_k) − P(D ∩ {k↔u})·m) = covD(k; A; F̂)(u) − (m·P(D) − ∫_D F(C_k))·P(D ∩ {k↔u})`. -/
theorem covD_clusterFun_eq' (w : Sym2 (Fin n) → unitInterval) (A : Set (Fin n)) (F : Set (Fin n) → ℝ) (k u : (Fin n)) (m : ℝ) :
    (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} *
        ((∫ ω in {ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} ∩ openConn k u,
            F (openCluster ω k) ∂(prodBernoulli w)) -
          (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} ∩ openConn k u) * m) =
      covD w k A (fun C => F {a | a = k ∨ ∃ e ∈ C, a ∈ e}) u -
        (m * (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} -
          ∫ ω in {ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a}, F (openCluster ω k) ∂(prodBernoulli w)) *
        (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} ∩ openConn k u) := by
  unfold covD
  simp only [clusterFun_openEdgeCluster]
  ring

/-- **The `Ψ_iso` identity, arbitrary avoided set**: for `u ≠ k`,
`covD(k; A; Ψ_iso)(u) = P(D ∩ {C_k = ∅}) · P(D ∩ {k↔u})`, `D = {k ↮ A}`. -/
theorem covD_psiIso' (w : Sym2 (Fin n) → unitInterval) (A : Set (Fin n)) (k u : (Fin n)) (huk : u ≠ k) :
    covD w k A psiIso u =
      (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} ∩ {ω | openEdgeCluster ω k = ∅}) *
        (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} ∩ openConn k u) := by
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun S => (Set.toFinite S).measurableSet
  set Dk : Set (BondConfig (Fin n)) := {ω | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} with hDk
  have h1 : ∫ ω in Dk ∩ openConn k u, psiIso (openEdgeCluster ω k) ∂μ = μ.real (Dk ∩ openConn k u) := by
    rw [setIntegral_congr_fun (hmeas _) (fun ω hω => psiIso_eq_one_of_reachable huk hω.2), setIntegral_const, smul_eq_mul,
      mul_one]
  have h2 : ∫ ω in Dk, psiIso (openEdgeCluster ω k) ∂μ = μ.real Dk - μ.real (Dk ∩ {ω | openEdgeCluster ω k = ∅}) := by
    have hsplit := (integral_inter_add_sdiff (hmeas {ω : BondConfig (Fin n) | openEdgeCluster ω k = ∅})
      ((Integrable.of_finite (f := fun ω => psiIso (openEdgeCluster ω k)) (μ := μ)).integrableOn (s := Dk))).symm
    rw [hsplit]
    have ha : ∫ ω in Dk ∩ {ω | openEdgeCluster ω k = ∅}, psiIso (openEdgeCluster ω k) ∂μ = 0 := by
      rw [setIntegral_congr_fun (hmeas _) (fun ω hω => by
        show psiIso (openEdgeCluster ω k) = (0 : ℝ)
        unfold psiIso; rw [if_pos (show openEdgeCluster ω k = ∅ from hω.2)])]
      simp
    have hb : ∫ ω in Dk \ {ω | openEdgeCluster ω k = ∅}, psiIso (openEdgeCluster ω k) ∂μ =
        μ.real (Dk \ {ω | openEdgeCluster ω k = ∅}) := by
      rw [setIntegral_congr_fun (hmeas _) (fun ω hω => by
        show psiIso (openEdgeCluster ω k) = (1 : ℝ)
        unfold psiIso; rw [if_neg (show ¬ (openEdgeCluster ω k = ∅) from hω.2)]), setIntegral_const, smul_eq_mul, mul_one]
    rw [ha, hb, zero_add]
    have := measureReal_inter_add_sdiff (μ := μ) (s := Dk) (h := measure_ne_top _ _)
      (hmeas {ω : BondConfig (Fin n) | openEdgeCluster ω k = ∅})
    linarith
  unfold covD
  rw [← hDk, h1, h2]
  ring

end KNAll

end
