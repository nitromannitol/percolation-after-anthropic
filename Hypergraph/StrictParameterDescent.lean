import Hypergraph.ExactTargetPlanStability
import Hypergraph.CoreReachableSafe

/-!
# The strict-parameter-descent endpoint

This module isolates the last logical step of the finite-plan strategy.  The still-open work is
kept as an explicit interface: extraction produces an actual finite `ExactTargetPlan.Plan`, and
soundness is asserted only for plans carrying the caller's concrete eligibility predicate.  It is
not asserted for every syntactically well-formed plan.

Finite validity is stable to the left by `ExactTargetPlan.Plan.exists_smaller_valid`.  Consequently
an extracted eligible plan that is sound at every parameter where it remains valid turns
percolation at `p` into percolation at a strictly smaller `q`.  Such strict descent immediately
excludes percolation at the infimum defining the site critical parameter.

The last section connects this abstract endpoint to the reachable-state adaptive soundness already
proved in `CoreReachableSafe`.  Its sole premise is the concrete interpreter construction still to
be supplied; physical correctness is required only on reachable histories.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-- Every percolating parameter can be beaten by a strictly smaller percolating parameter. -/
def StrictParameterDescent (d : Nat) : Prop :=
  ∀ p : unitInterval, 0 < thetaSite d p →
    ∃ q : unitInterval, (q : Real) < (p : Real) ∧ 0 < thetaSite d q

/-- Strict parameter descent rules out percolation at the infimum in the definition of
`criticalProbSite`.  No continuity theorem and no slab-criticality input is used. -/
theorem siteCriticality_of_strictParameterDescent (d : Nat)
    (hdescent : StrictParameterDescent d) : SiteCriticality d := by
  by_contra hne
  have hpcpos : 0 < thetaSite d (criticalProbSiteI d) :=
    lt_of_le_of_ne (thetaSiteOn_nonneg _ _ _) (Ne.symm hne)
  obtain ⟨q, hqpc, hqpos⟩ := hdescent (criticalProbSiteI d) hpcpos
  have hpcq : criticalProbSite d ≤ (q : Real) :=
    criticalProbSite_le_of_pos d q hqpos
  exact (not_lt_of_ge hpcq) (by simpa using hqpc)

namespace ExactTargetPlan

variable {d : Nat}

/-- The extraction half of a finite macro-plan interface.  `Eligible` is where the caller records
the deterministic compatibility data distinguishing plans built by the macro construction from
arbitrary `WellFormed` plans.  The witness itself is the concrete finite T1--T6 datum.  Extraction
is asked only at `p < 1`: asking at `p = 1` would contradict the plan clause `p0 < 1` together with
`ValidAt p`, and strict descent from `1` is already supplied by a known percolating parameter below
one. -/
def FiniteMacroPlanExtraction
    (Eligible : ExactTargetPlan.Plan d → Prop) : Prop :=
  ∀ p : unitInterval, (p : Real) < 1 → 0 < thetaSite d p →
    ∃ C : ExactTargetPlan.Plan d,
      Eligible C ∧ C.WellFormed ∧ C.ValidAt p

/-- The soundness half of the interface, restricted to the plans selected by `Eligible`.
This is deliberately a proposition supplied to the endpoint, not a field of the finite plan. -/
def FiniteMacroPlanSoundness
    (Eligible : ExactTargetPlan.Plan d → Prop) : Prop :=
  ∀ (C : ExactTargetPlan.Plan d) (q : unitInterval),
    Eligible C → C.WellFormed → C.ValidAt q → 0 < thetaSite d q

/-- A slab-valued form of finite macro-plan soundness.  It is often the natural conclusion of a
reachable exploration; inclusion of the slab into the full lattice gives whole-lattice soundness. -/
def FiniteMacroPlanSlabSoundness [NeZero d]
    (Eligible : ExactTargetPlan.Plan d → Prop) : Prop :=
  ∀ (C : ExactTargetPlan.Plan d) (q : unitInterval),
    Eligible C → C.WellFormed → C.ValidAt q →
      ∃ k : Nat, 0 < thetaSiteOn (slabGraph d k) (slabOrigin d k) q

/-- The extraction premise cannot be satisfied by an empty eligibility class at any percolating
parameter.  This is the basic non-vacuity check for the two-part interface. -/
theorem exists_eligible_of_finiteMacroPlanExtraction
    {Eligible : ExactTargetPlan.Plan d → Prop}
    (hextract : FiniteMacroPlanExtraction Eligible)
    (p : unitInterval) (hp1 : (p : Real) < 1) (hp : 0 < thetaSite d p) :
    ∃ C : ExactTargetPlan.Plan d, Eligible C := by
  obtain ⟨C, hC, -, -⟩ := hextract p hp1 hp
  exact ⟨C, hC⟩

/-- In dimensions with a known percolating parameter below one, an extraction interface has an
actual eligible plan.  Thus the paired extraction/soundness premises cannot close the endpoint by
choosing an empty eligibility predicate. -/
theorem finiteMacroPlanExtraction_nonvacuous [NeZero d] (hd : 2 ≤ d)
    {Eligible : ExactTargetPlan.Plan d → Prop}
    (hextract : FiniteMacroPlanExtraction Eligible) :
    ∃ C : ExactTargetPlan.Plan d, Eligible C := by
  obtain ⟨p, hp1, hp⟩ := exists_thetaSite_pos d hd
  exact exists_eligible_of_finiteMacroPlanExtraction hextract p hp1 hp

/-- Slab soundness implies the whole-lattice soundness interface. -/
theorem finiteMacroPlanSoundness_of_slab [NeZero d]
    {Eligible : ExactTargetPlan.Plan d → Prop}
    (hsound : FiniteMacroPlanSlabSoundness Eligible) :
    FiniteMacroPlanSoundness Eligible := by
  intro C q hEligible hC hvalid
  obtain ⟨k, hk⟩ := hsound C q hEligible hC hvalid
  exact lt_of_lt_of_le hk (thetaSiteOn_slab_le d k q)

/-- **Finite exact macro-plans imply strict parameter descent.**

Positivity of `thetaSite d p` first implies `p > 0`, because an infinite cluster requires the
origin to be open.  Exact finite validity then survives at a strictly smaller positive parameter,
and soundness of the same eligible plan gives percolation there. -/
theorem strictParameterDescent_of_finiteMacroPlan [NeZero d] (hd : 2 ≤ d)
    {Eligible : ExactTargetPlan.Plan d → Prop}
    (hextract : FiniteMacroPlanExtraction Eligible)
    (hsound : FiniteMacroPlanSoundness Eligible) :
    StrictParameterDescent d := by
  intro p hp
  have hp0 : 0 < (p : Real) :=
    lt_of_lt_of_le hp (thetaSiteOn_le_coe (zdGraph d) (0 : Site d) p)
  by_cases hp1 : (p : Real) < 1
  · obtain ⟨C, hEligible, hC, hvalid⟩ := hextract p hp1 hp
    obtain ⟨q, -, hqp, hqvalid⟩ := C.exists_smaller_valid hp0 hvalid
    exact ⟨q, hqp, hsound C q hEligible hC hqvalid⟩
  · have hpEq : (p : Real) = 1 := le_antisymm p.2.2 (not_lt.mp hp1)
    obtain ⟨q, hq1, hqpos⟩ := exists_thetaSite_pos d hd
    exact ⟨q, by rwa [hpEq], hqpos⟩

/-- The final critical-point conclusion from the explicit finite extraction and soundness
interfaces.  This statement is slightly stronger than the intended `d ≥ 3` use: the logical
endpoint needs only `d ≥ 2`; the intended macro soundness construction is where `d ≥ 3` enters. -/
theorem siteCriticality_of_finiteMacroPlan [NeZero d] (hd : 2 ≤ d)
    {Eligible : ExactTargetPlan.Plan d → Prop}
    (hextract : FiniteMacroPlanExtraction Eligible)
    (hsound : FiniteMacroPlanSoundness Eligible) :
    SiteCriticality d :=
  siteCriticality_of_strictParameterDescent d
    (strictParameterDescent_of_finiteMacroPlan hd hextract hsound)

/-- Slab-valued soundness is sufficient for the same exact-plan capstone. -/
theorem siteCriticality_of_finiteMacroPlanSlab [NeZero d] (hd : 2 ≤ d)
    {Eligible : ExactTargetPlan.Plan d → Prop}
    (hextract : FiniteMacroPlanExtraction Eligible)
    (hsound : FiniteMacroPlanSlabSoundness Eligible) :
    SiteCriticality d :=
  siteCriticality_of_finiteMacroPlan hd hextract
    (finiteMacroPlanSoundness_of_slab hsound)

end ExactTargetPlan

/-! ## Existing certificate and reachable-adaptive bridges -/

section ReachableBridge

variable {d : Nat} [NeZero d]

/-- Existing finite `Certificate2` soundness implies whole-lattice strict descent.  The endpoint
at `p < 1` is the proved certificate stability/reduction; at `p = 1`, the already proved existence
of a percolating site parameter below one supplies the strict improvement. -/
theorem strictParameterDescent_of_certificateSound2 (hd : 3 ≤ d)
    (hsound : LeftImp2.CertificateSound2 d) : StrictParameterDescent d := by
  intro p hp
  have hp0 : 0 < (p : Real) :=
    lt_of_lt_of_le hp (thetaSiteOn_le_coe (zdGraph d) (0 : Site d) p)
  by_cases hp1 : (p : Real) < 1
  · have hred := LeftImp2.siteSlabReductionBelow_of_certificateSound2 d hsound
    obtain ⟨k, q, hqp, hqslab⟩ := hred p hp0 hp1 hp
    exact ⟨q, hqp, lt_of_lt_of_le hqslab (thetaSiteOn_slab_le d k q)⟩
  · have hpEq : (p : Real) = 1 := le_antisymm p.2.2 (not_lt.mp hp1)
    obtain ⟨q, hq1, hqpos⟩ := exists_thetaSite_pos d (by omega)
    exact ⟨q, by rwa [hpEq], hqpos⟩

/-- The direct critical endpoint from `Certificate2` soundness, now explicitly factored through
whole-lattice strict parameter descent. -/
theorem siteCriticality_of_certificateSound2_via_strictDescent (hd : 3 ≤ d)
    (hsound : LeftImp2.CertificateSound2 d) : SiteCriticality d :=
  siteCriticality_of_strictParameterDescent d
    (strictParameterDescent_of_certificateSound2 hd hsound)

/-- The exact open interpreter construction consumed by reachable-state soundness.  It contains
no theorem field and no arbitrary-state physical assertion: certificates are required only for
states literally reached by the run. -/
def ReachableAdaptiveMacroPlanSoundness : Prop :=
  ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval),
    C.WellFormed → C.ValidAt2 q →
    ∃ (r t : Nat)
      (h0 : CoreReachSafe.Tr (Site d) (Site 2))
      (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
        (box 2 n) 0 (MacroExp.tgt n)),
      0 < r ∧ 2 * t ≤ C.width ∧
      h0.base = MacroExp.start d r t ∧ h0.failed = ∅ ∧
      (∀ n, (E n).density = fun _ : Site d => q) ∧
      (∀ n, (E n).Admissible h0) ∧
      (∀ n k, CoreReachSafe.Reachable (E n) h0 k → CoreReachSafe.Physical d r t k) ∧
      (∀ n h, (E n).Admissible h →
        ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
        (CoreSafe.successParam : Real) ≤
          h.prob (fun _ : Site d => q) ((E n).success h))

/-- The reachable adaptive interface discharges the existing finite-certificate soundness
proposition. -/
theorem certificateSound2_of_reachableAdaptiveMacroPlan (hd : 3 ≤ d)
    (hmacro : ReachableAdaptiveMacroPlanSoundness (d := d)) :
    LeftImp2.CertificateSound2 d :=
  CoreReachSafe.certificateSound2_of_reachable_adaptive_safe hd hmacro

/-- A reachable, physically certified adaptive macro interpreter gives strict descent. -/
theorem strictParameterDescent_of_reachableAdaptiveMacroPlan (hd : 3 ≤ d)
    (hmacro : ReachableAdaptiveMacroPlanSoundness (d := d)) :
    StrictParameterDescent d :=
  strictParameterDescent_of_certificateSound2 hd
    (certificateSound2_of_reachableAdaptiveMacroPlan hd hmacro)

/-- **Reachable adaptive macro-plan capstone.**  Supplying the one explicit interpreter interface
proves absence of site percolation at the critical point in every dimension `d ≥ 3`. -/
theorem siteCriticality_of_reachableAdaptiveMacroPlan (hd : 3 ≤ d)
    (hmacro : ReachableAdaptiveMacroPlanSoundness (d := d)) :
    thetaSite d (criticalProbSiteI d) = 0 :=
  siteCriticality_of_strictParameterDescent d
    (strictParameterDescent_of_reachableAdaptiveMacroPlan hd hmacro)

end ReachableBridge

#print axioms KNAll.Site.siteCriticality_of_strictParameterDescent
#print axioms KNAll.Site.ExactTargetPlan.strictParameterDescent_of_finiteMacroPlan
#print axioms KNAll.Site.ExactTargetPlan.siteCriticality_of_finiteMacroPlan
#print axioms KNAll.Site.strictParameterDescent_of_reachableAdaptiveMacroPlan
#print axioms KNAll.Site.siteCriticality_of_reachableAdaptiveMacroPlan

end KNAll.Site

end
