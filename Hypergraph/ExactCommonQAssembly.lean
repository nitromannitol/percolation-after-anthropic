import Hypergraph.ExactInitialCoreFromTheta
import Hypergraph.ExactMacroStepFromTheta
import Hypergraph.ExactReachablePercolation
import Hypergraph.ExactQuarterOuterPrototypeStability
import Hypergraph.ExactStoppedPrototypeStability

/-!
# Common-parameter assembly for the exact reachable interpreter

This file performs the quantifier-sensitive last step.  All finite objects are frozen at a
percolating parameter `p0`; one common parameter `q < p0` is then chosen inside the left
stability neighbourhoods of the initial, quarter, outer, and stopped leaf families.  At that
same `q`, the exact local step and reachable-state interpreter give site percolation.

The explicitly displayed stopped-family neighbourhood hypothesis in
`exists_smaller_thetaSite_pos_of_stopped_stability` is precisely the interface supplied by the
fixed stopped prototype family.  It produces the concrete stopped children consumed by
`ExactMacroStepFromTheta.localAcceptedSuccess`; there is no proposition-valued certificate field
and no assertion about arbitrary plans.
-/

noncomputable section

namespace KNAll.Site.ExactCommonQAssembly

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

private theorem deltaC_le_one (d : Nat) : ExactMacroNumerics.deltaC d ≤ 1 := by
  calc
    ExactMacroNumerics.deltaC d ≤ ExactMacroNumerics.rho / 2 :=
      ExactMacroNumerics.deltaC_le_rho_half d
    _ ≤ 1 := by linarith [ExactMacroNumerics.rho_le_half]

/-! ## Compatible frozen scales -/

/-- The initial scheme and stopped depth may be frozen before the spatial scales.  Enlarging one
auxiliary radius to dominate the initial, quarter, outer, and stopped radii, and then using the
fixed-depth numerical constructor, supplies every scale inequality used below.  This proves in
particular that the fixed-scale assembly's arithmetic hypotheses are jointly satisfiable. -/
theorem exists_frozen_initial_and_macro_scales
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) (K stoppedR : Nat) (hK : 20 ≤ K) :
    ∃ (F : ExactLongBoxVariablePlan.SchemeFamily d p0
          (ExactMacroNumerics.deltaC d) 6) (s r t : Nat),
      0 < s ∧ 0 < r ∧ r = K * s ∧ 44 ≤ r ∧ 5 * r ≤ t ∧
      10 * s * K ≤ 10 * r ∧
      100 * (d + 1) *
        (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta + 1) < r ∧
      200 *
        ((ExactQuarterOuterPrototypeStability.frozenOuterData p0 hp0 hp1 htheta).radius + 1) ≤ r ∧
      2 * stoppedR ≤ s ∧
      ExactInitialCoreFromTheta.InitialPlan.requiredMacroScale F ≤
        ExactInitialCoreFromTheta.InitialPlan.macroScale r := by
  let F : ExactLongBoxVariablePlan.SchemeFamily d p0 (ExactMacroNumerics.deltaC d) 6 :=
    Classical.choice
      (ExactLongBoxVariablePlan.exists_schemeFamily_of_thetaSite_pos
        p0 hp0 hp1 htheta (ExactMacroNumerics.deltaC d)
        (ExactMacroNumerics.deltaC_pos d) (deltaC_le_one d) 6 (by omega))
  let R := ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta +
    (ExactQuarterOuterPrototypeStability.frozenOuterData p0 hp0 hp1 htheta).radius +
    stoppedR +
    ExactInitialCoreFromTheta.InitialPlan.requiredMacroScale F
  obtain ⟨s, r, t, hs, hr, hrEq, hRs, hbudget, -, -, -, -, -, -, ht, hr44,
      hsepR, houterR⟩ :=
    ExactMacroNumerics.exists_spatial_scales_for_fixed_depth d 0 0 R K hK
  have hquarterR : ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta ≤ R := by
    dsimp [R]
    omega
  have houterRadiusR :
      (ExactQuarterOuterPrototypeStability.frozenOuterData p0 hp0 hp1 htheta).radius ≤ R := by
    dsimp [R]
    omega
  have hstoppedR : stoppedR ≤ R := by
    dsimp [R]
    omega
  have hinitialR : ExactInitialCoreFromTheta.InitialPlan.requiredMacroScale F ≤ R := by
    dsimp [R]
    omega
  have hsep : 100 * (d + 1) *
      (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta + 1) < r := by
    exact (Nat.mul_le_mul_left (100 * (d + 1)) (Nat.add_le_add_right hquarterR 1)).trans_lt
      hsepR
  have houterScale :
      200 *
        ((ExactQuarterOuterPrototypeStability.frozenOuterData p0 hp0 hp1 htheta).radius + 1) ≤ r := by
    exact (Nat.mul_le_mul_left 200 (Nat.add_le_add_right houterRadiusR 1)).trans houterR
  have hstoppedScale : 2 * stoppedR ≤ s := by
    exact (Nat.mul_le_mul_left 2 hstoppedR).trans hRs
  have hinitialScale :
      ExactInitialCoreFromTheta.InitialPlan.requiredMacroScale F ≤
        ExactInitialCoreFromTheta.InitialPlan.macroScale r := by
    unfold ExactInitialCoreFromTheta.InitialPlan.macroScale
    omega
  exact ⟨F, s, r, t, hs, hr, hrEq, hr44, ht, hbudget,
    hsep, houterScale, hstoppedScale, hinitialScale⟩

/-! ## The already-closed quarter family -/

/-- The finite centred quarter prototypes give one left neighbourhood for the literal
`quarterAt` family used by the exact macro step, uniformly over every macro centre. -/
theorem exists_quarterAt_left_nhds
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) (r : Nat)
    (hsep : 100 * (d + 1) *
      (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta + 1) < r) :
    ∃ e : Real, 0 < e ∧ ∀ q : unitInterval,
      0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
      |(q : Real) - (p0 : Real)| < e → ∀ z i,
        ((ExactMacroStepFromTheta.quarterAt p0 hp0 hp1 htheta r z hsep).quarter i).ValidAt q := by
  let S := ExactMacroStepFromTheta.frozenSchemes p0 hp0 hp1 htheta
  let R := ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta
  have hR0 : ∀ i, (S i).numbers.R0 ≤ R := fun i =>
    ExactQuarterPlanExtraction.arithmeticRadius_le_commonRadius S i
  have hlocal : ∀ i, (S i).scales.localRadius < R := fun i =>
    ExactQuarterPlanExtraction.localRadius_lt_commonRadius S i
  obtain ⟨e, he, hleft⟩ :=
    ExactQuarterOuterPrototypeStability.exists_left_nhds_quarter hp0 hp1
      (fun i => ExactMacroNumerics.eta_pos d i.succ)
      (fun i => ExactMacroNumerics.eta_le_one d i.succ)
      S r R hR0 hlocal hsep
  refine ⟨e, he, ?_⟩
  intro q hq0 hqp hdist z i
  exact hleft q hq0 hqp hdist (MacroExp.ctr d r z) i

/-! ## Fixed-scale common-q assembly -/

/-- At fixed frozen data and fixed admissible macro scales, left stability of the concrete stopped
family is the only remaining input.  The initial, quarter, and outer neighbourhoods are
constructed here, a single smaller `q` is chosen in all four neighbourhoods, and the reachable
interpreter is run at that same `q`. -/
theorem exists_smaller_thetaSite_pos_of_stopped_stability
    (hd : 3 ≤ d) (p0 : unitInterval)
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (ExactMacroNumerics.deltaC d) 6)
    (K s r t : Nat)
    (hK : 20 ≤ K) (hs : 0 < s) (hr : 0 < r) (hrEq : r = K * s)
    (hr44 : 44 ≤ r) (ht : 5 * r ≤ t)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsep : 100 * (d + 1) *
      (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta + 1) < r)
    (houterScale : 200 *
      ((ExactQuarterOuterPrototypeStability.frozenOuterData p0 hp0 hp1 htheta).radius + 1) ≤ r)
    (hinitialScale :
      ExactInitialCoreFromTheta.InitialPlan.requiredMacroScale F ≤
        ExactInitialCoreFromTheta.InitialPlan.macroScale r)
    (hpow : (1 - AtomTower.f (ExactMacroNumerics.deltaC d)) ^ K ≤
      ExactMacroNumerics.rho / 16)
    (hstoppedLeft : ∃ e : Real, 0 < e ∧ ∀ q : unitInterval,
      0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
      |(q : Real) - (p0 : Real)| < e →
      ∀ (z y : Site 2) (i : Fin d) (sigma : Int)
        (hsigma : sigma = 1 ∨ sigma = -1)
        (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma),
        ∃ G : ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma
            (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d),
          ∀ a, (G.plan a).ValidAt q) :
    ∃ q : unitInterval, (q : Real) < (p0 : Real) ∧ 0 < thetaSite d q := by
  obtain ⟨eI, heI, hI⟩ :=
    ExactInitialCoreFromTheta.InitialPlan.exists_initialCoreBounds_left_nhds_ofScheme
      hp0 hp1 (ExactMacroNumerics.deltaC_pos d) (deltaC_le_one d) F hd hr
      (by omega : 3 * r ≤ t) hinitialScale
  let O := ExactQuarterOuterPrototypeStability.frozenOuterData p0 hp0 hp1 htheta
  obtain ⟨eQO, heQO, hQO⟩ :=
    ExactQuarterOuterPrototypeStability.exists_left_nhds_quarter_outer hp0 hp1
      (by linarith [ExactMacroNumerics.rho_pos] : 0 < ExactMacroNumerics.rho / 16)
      (by linarith [ExactMacroNumerics.rho_le_half] : ExactMacroNumerics.rho / 16 ≤ 1)
      O
      (fun a => ExactMacroNumerics.eta_pos d a.succ)
      (fun a => ExactMacroNumerics.eta_le_one d a.succ)
      (ExactMacroStepFromTheta.frozenSchemes p0 hp0 hp1 htheta)
      r t (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta)
      (fun a => ExactQuarterPlanExtraction.arithmeticRadius_le_commonRadius _ a)
      (fun a => ExactQuarterPlanExtraction.localRadius_lt_commonRadius _ a)
      (by omega : 2 ≤ d) hr44 ht hsep houterScale
      (ExactMacroNumerics.eta_step d) (ExactMacroNumerics.eta_last d)
  obtain ⟨eS, heS, hS⟩ := hstoppedLeft
  let e := min eI (min eQO eS)
  have he : 0 < e := by
    dsimp [e]
    exact lt_min heI (lt_min heQO heS)
  obtain ⟨q, hq0, hqp, hdist⟩ :=
    ExactQuarterOuterPrototypeStability.exists_lt_of_left_nhds hp0 he
  have hqle : (q : Real) ≤ (p0 : Real) := hqp.le
  have hdistI : |(q : Real) - (p0 : Real)| < eI :=
    lt_of_lt_of_le hdist (min_le_left _ _)
  have hdistQO : |(q : Real) - (p0 : Real)| < eQO :=
    lt_of_lt_of_le hdist (le_trans (min_le_right _ _) (min_le_left _ _))
  have hdistS : |(q : Real) - (p0 : Real)| < eS :=
    lt_of_lt_of_le hdist
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hinit := hI q hq0 hqle hdistI
  obtain ⟨hquarterRaw, houterRaw⟩ := hQO q hq0 hqle hdistQO
  have hquarter : ∀ z i,
      ((ExactMacroStepFromTheta.quarterAt p0 hp0 hp1 htheta r z hsep).quarter i).ValidAt q := by
    intro z i
    rw [ExactQuarterOuterPrototypeStability.quarterAt_quarter p0 hp0 hp1 htheta r z hsep i]
    exact hquarterRaw (MacroExp.ctr d r z) i
  have houter : ∀ (h : ExactMacroGeometry.Tr d) (w z y : Site 2)
      (i : Fin d) (sigma : Int) (hwz : w ≠ z)
      (hsigma : sigma = 1 ∨ sigma = -1)
      (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma),
      ∃ A : ExactMacroGeometry.OuterStage p0 (ExactMacroNumerics.eta d) r t h w z
          (ExactMacroStepFromTheta.quarterAt p0 hp0 hp1 htheta r z hsep) y i sigma
          ExactMacroNumerics.rho,
        A.plan.ValidAt q := by
    intro h w z y i sigma hwz hsigma hemb
    obtain ⟨A, -, -, hA⟩ := houterRaw h w z y i sigma
      (ExactMacroStepFromTheta.quarterAt p0 hp0 hp1 htheta r z hsep)
      hwz hsigma hemb rfl (hquarter z)
    exact ⟨A, hA⟩
  have hstopped := hS q hq0 hqle hdistS
  have hsucc := ExactMacroStepFromTheta.localAcceptedSuccess hd p0 q hp0 hp1 htheta
    r t s K hr hr44 hK ht hs hbudget hrEq hsep hpow
    hquarter houter hstopped
  have hqtheta :=
    ExactReachablePercolation.thetaSite_pos_of_initialCoreBounds_and_localAcceptedSuccess
      hd r t s K q hr ht hs hbudget hq0 hinit hsucc
  exact ⟨q, hqp, hqtheta⟩

/-! ## Closed common-q and strict-descent endpoints -/

/-- Positive percolation below parameter `1` produces percolation at one strictly smaller
parameter.  The stopped depth is chosen first, the stopped prototype radius is then frozen, and
only afterwards are the common spatial scales chosen.  Thus all four finite families are fixed
before their left-neighbourhood radii and the common `q` are selected. -/
theorem exists_smaller_thetaSite_pos
    (hd : 3 ≤ d) (p0 : unitInterval)
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) :
    ∃ q : unitInterval, (q : Real) < (p0 : Real) ∧ 0 < thetaSite d q := by
  obtain ⟨K, hK, hpow⟩ := ExactMacroNumerics.exists_K_pow_exhaustion
    ExactMacroNumerics.rho_pos ExactMacroNumerics.rho_le_half
    (ExactMacroNumerics.deltaC_pos d) (ExactMacroNumerics.deltaC_le_rho_half d)
  obtain ⟨stoppedR, -, hstoppedFamily⟩ :=
    ExactStoppedPrototypeStability.exists_left_nhds_frozen_stoppedChildren_of_thetaSite_pos
      p0 hp0 hp1 htheta hK
  obtain ⟨F, s, r, t, hs, hr, hrEq, hr44, ht, hbudget, hsep, houterScale,
      hstoppedScale, hinitialScale⟩ :=
    exists_frozen_initial_and_macro_scales p0 hp0 hp1 htheta K stoppedR hK
  obtain ⟨eS, heS, hS⟩ := hstoppedFamily r s hs hrEq hstoppedScale
  have hstoppedLeft : ∃ e : Real, 0 < e ∧ ∀ q : unitInterval,
      0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
      |(q : Real) - (p0 : Real)| < e →
      ∀ (z y : Site 2) (i : Fin d) (sigma : Int)
        (hsigma : sigma = 1 ∨ sigma = -1)
        (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma),
        ∃ G : ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma
            (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d),
          ∀ a, (G.plan a).ValidAt q := by
    refine ⟨eS, heS, ?_⟩
    intro q hq0 hqp hdist z y i sigma hsigma hemb
    exact hS q hq0 hqp hdist t ht z y i sigma hsigma hemb
  exact exists_smaller_thetaSite_pos_of_stopped_stability hd p0 hp0 hp1 htheta
    F K s r t hK hs hr hrEq hr44 ht hbudget hsep houterScale hinitialScale hpow
    hstoppedLeft

/-- Every percolating site parameter in dimension at least three admits a strictly smaller
percolating parameter.  The endpoint `p = 1` uses the standard existence of a percolating
parameter below one; every `p < 1` uses the common finite-family construction above. -/
theorem strictParameterDescent (hd : 3 ≤ d) : StrictParameterDescent d := by
  intro p hp
  have hp0 : 0 < (p : Real) :=
    lt_of_lt_of_le hp (thetaSiteOn_le_coe (zdGraph d) (0 : Site d) p)
  by_cases hp1 : (p : Real) < 1
  · exact exists_smaller_thetaSite_pos hd p hp0 hp1 hp
  · have hpEq : (p : Real) = 1 := le_antisymm p.2.2 (not_lt.mp hp1)
    obtain ⟨q, hq1, hqpos⟩ := exists_thetaSite_pos d (by omega : 2 ≤ d)
    exact ⟨q, by rwa [hpEq], hqpos⟩

/-- Absence of site percolation at the critical parameter, obtained by strict parameter descent
through the exact reachable macro interpreter. -/
theorem site_no_percolation_at_criticality (hd : 3 ≤ d) :
    thetaSite d (criticalProbSiteI d) = 0 :=
  KNAll.Site.siteCriticality_of_strictParameterDescent d (strictParameterDescent hd)

#print axioms KNAll.Site.ExactCommonQAssembly.exists_quarterAt_left_nhds
#print axioms KNAll.Site.ExactCommonQAssembly.exists_frozen_initial_and_macro_scales
#print axioms KNAll.Site.ExactCommonQAssembly.exists_smaller_thetaSite_pos_of_stopped_stability
#print axioms KNAll.Site.ExactCommonQAssembly.exists_smaller_thetaSite_pos
#print axioms KNAll.Site.ExactCommonQAssembly.strictParameterDescent
#print axioms KNAll.Site.ExactCommonQAssembly.site_no_percolation_at_criticality

end KNAll.Site.ExactCommonQAssembly

end
