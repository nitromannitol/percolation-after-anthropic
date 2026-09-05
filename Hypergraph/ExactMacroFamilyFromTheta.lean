import Hypergraph.ExactMacroFamilyExtraction
import Hypergraph.ExactOuterStageExtraction

/-!
# Exact macro-family extraction from positive percolation

The quarter construction is common to all outgoing heads at one centre.  We first extract it once,
reset its lower-scale parameter to its actual scale, and reuse that same finite table for every
member of the actual `Head h z` subtype.  A separate dependent-choice lemma then combines honest
outer- and stopped-child existence results without placing validity in a new data structure.
-/

noncomputable section

namespace KNAll.Site.ExactMacroFamilyFromTheta

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

abbrev Head (h : MacroExp.Tr d) (z : Site 2) :=
  ExactMacroGeometry.Head (d := d) h z

/-- Regard a quarter family at its actual scale.  This changes only the lower-bound parameter;
all schemes, instantiations, plans, and proofs are literally reused. -/
def quarterAtOwnScale
    {p0 : unitInterval} {epsilon : Fin d → Real} {c : Site d} {rmin : Nat}
    (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0 epsilon c rmin) :
    ExactQuarterPlanExtraction.QuarterStageFamily p0 epsilon c Q.scale where
  radius := Q.radius
  scale := Q.scale
  scheme := Q.scheme
  instantiation := Q.instantiation
  quarter := Q.quarter
  radius_pos := Q.radius_pos
  scale_pos := Q.scale_pos
  scale_floor := le_rfl
  separation := Q.separation
  instantiation_source := Q.instantiation_source
  instantiation_active := Q.instantiation_active
  instantiation_target := Q.instantiation_target
  instantiation_radius := Q.instantiation_radius
  quarter_wellFormed := Q.quarter_wellFormed
  quarter_validAt := Q.quarter_validAt
  quarter_source := Q.quarter_source
  quarter_active := Q.quarter_active
  quarter_target := Q.quarter_target
  quarter_radius := Q.quarter_radius
  quarter_epsilon := Q.quarter_epsilon
  quarter_geometry := Q.quarter_geometry

@[simp] theorem quarterAtOwnScale_scale
    {p0 : unitInterval} {epsilon : Fin d → Real} {c : Site d} {rmin : Nat}
    (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0 epsilon c rmin) :
    (quarterAtOwnScale Q).scale = Q.scale := rfl

@[simp] theorem quarterAtOwnScale_quarter
    {p0 : unitInterval} {epsilon : Fin d → Real} {c : Site d} {rmin : Nat}
    (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0 epsilon c rmin)
    (a : Fin d) : (quarterAtOwnScale Q).quarter a = Q.quarter a := rfl

/-- Positive percolation produces one common quarter table for every actual outgoing head.  The
macro scale is returned explicitly and is at least the requested deterministic floor. -/
theorem exists_quarterTable
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (h : MacroExp.Tr d) (z : Site 2) (rmin : Nat) :
    ∃ r : Nat, rmin ≤ r ∧ 0 < r ∧
      ∃ quarter : ∀ Y : Head h z,
          ExactQuarterPlanExtraction.QuarterStageFamily p0
            (fun a : Fin d => ExactMacroNumerics.eta d a.succ)
            (MacroExp.ctr d r z) r,
        (∀ Y, (quarter Y).scale = r) ∧
          ∀ Y a, ((quarter Y).quarter a).ValidAt p0 := by
  let epsilon : Fin d → Real := fun i => ExactMacroNumerics.eta d i.succ
  let schemes : ∀ i, ExactTargetScheme.OrthantScheme d p0 (epsilon i) := fun i =>
    Classical.choice
      (ExactTargetScheme.exists_orthantScheme_of_thetaSite_pos p0 hp0 hp1 htheta
        (epsilon i) (ExactMacroNumerics.eta_pos d i.succ)
        (ExactMacroNumerics.eta_le_one d i.succ))
  let R : Nat := ExactQuarterPlanExtraction.commonRadius schemes
  let r : Nat := ExactQuarterPlanExtraction.commonScale rmin R d
  let c : Site d := MacroExp.ctr d r z
  have hlocal : ∀ i, (schemes i).scales.localRadius < R :=
    fun i => ExactQuarterPlanExtraction.localRadius_lt_commonRadius schemes i
  have hR0 : ∀ i, (schemes i).numbers.R0 ≤ R :=
    fun i => ExactQuarterPlanExtraction.arithmeticRadius_le_commonRadius schemes i
  have hsep : 100 * (d + 1) * (R + 1) < r :=
    ExactQuarterPlanExtraction.separation_commonScale rmin R d
  let instantiation : ∀ i, ExactTargetScheme.OrthantInstantiation (schemes i) :=
    fun i => ExactQuarterPlanExtraction.crossInstantiation (schemes i) c r R i
      (hR0 i) (hlocal i) hsep
  let plan : Fin d → ExactTargetPlan.Plan d := fun i =>
    ExactQuarterPlanExtraction.crossPlan (schemes i) c r R i
      (hR0 i) (hlocal i) hsep
  let Q : ExactQuarterPlanExtraction.QuarterStageFamily p0 epsilon c r :=
    { radius := R
      scale := r
      scheme := schemes
      instantiation := instantiation
      quarter := plan
      radius_pos := by
        unfold R ExactQuarterPlanExtraction.commonRadius
        omega
      scale_pos := by
        exact lt_of_lt_of_le (by norm_num : 0 < 44)
          (ExactQuarterPlanExtraction.fortyFour_le_commonScale rmin R d)
      scale_floor := le_rfl
      separation := hsep
      instantiation_source := fun i =>
        ExactQuarterPlanExtraction.crossInstantiation_sourceBox
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      instantiation_active := fun i =>
        ExactQuarterPlanExtraction.crossInstantiation_activeBox
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      instantiation_target := fun i =>
        ExactQuarterPlanExtraction.crossInstantiation_target
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      instantiation_radius := fun i =>
        ExactQuarterPlanExtraction.crossInstantiation_radius
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      quarter_wellFormed := fun i =>
        ExactQuarterPlanExtraction.crossPlan_wellFormed hp0 hp1
          (ExactMacroNumerics.eta_pos d i.succ)
          (ExactMacroNumerics.eta_le_one d i.succ)
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      quarter_validAt := fun i =>
        ExactQuarterPlanExtraction.crossPlan_validAt hp0 hp1
          (ExactMacroNumerics.eta_pos d i.succ)
          (ExactMacroNumerics.eta_le_one d i.succ)
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      quarter_source := fun i =>
        ExactQuarterPlanExtraction.crossPlan_source
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      quarter_active := fun i =>
        ExactQuarterPlanExtraction.crossPlan_active
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      quarter_target := fun i =>
        ExactQuarterPlanExtraction.crossPlan_target
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      quarter_radius := fun i =>
        ExactQuarterPlanExtraction.crossPlan_radius
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      quarter_epsilon := fun i =>
        ExactQuarterPlanExtraction.crossPlan_epsilon
          (schemes i) c r R i (hR0 i) (hlocal i) hsep
      quarter_geometry := fun i =>
        ExactQuarterPlanExtraction.crossPlan_faceTarget
          (schemes i) c r R i (hR0 i) (hlocal i) hsep }
  refine ⟨r, ExactQuarterPlanExtraction.minScale_le_commonScale rmin R d,
    Q.scale_pos, fun _ => Q, ?_, ?_⟩
  · intro Y
    rfl
  · intro Y a
    exact Q.quarter_validAt a

/-! ## Dependent finite choice over the actual heads -/

/-- Combine honest per-head existence theorems.  The two validity conclusions remain separate,
matching the exact inputs of `ExactMacroFamilyExtraction.acceptedExploration_success`. -/
theorem exists_family_of_children
    {p0 q : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (quarter : ∀ Y : Head h z,
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
    (hquarter : ∀ Y a, ((quarter Y).quarter a).ValidAt q)
    (houter : ∀ Y : Head h z,
      ∃ A : ExactMacroGeometry.OuterStage p0 eta r t h w z (quarter Y) Y.1
          (axis z Y.1) (sign z Y.1) rho,
        A.plan.ValidAt q)
    (hstopped : ∀ Y : Head h z,
      ∃ G : ExactMacroGeometry.StoppedChildren r t s K z Y.1
          (axis z Y.1) (sign z Y.1) deltaC delta2,
        ∀ a, (G.plan a).ValidAt q) :
    ∃ F : ExactMacroGeometry.Family p0 eta r t s K h w z axis sign
        rho deltaC delta2,
      (∀ Y, (F.outer Y).corridor.ValidAt q) ∧
        (∀ Y a, ((F.stopped Y).plan a).ValidAt q) ∧
          F.toPlan.ValidAt q := by
  let outer : ∀ Y : Head h z,
      ExactMacroGeometry.OuterStage p0 eta r t h w z (quarter Y) Y.1
        (axis z Y.1) (sign z Y.1) rho :=
    fun Y => Classical.choose (houter Y)
  have houterValid : ∀ Y, (outer Y).plan.ValidAt q :=
    fun Y => Classical.choose_spec (houter Y)
  let stopped : ∀ Y : Head h z,
      ExactMacroGeometry.StoppedChildren r t s K z Y.1
        (axis z Y.1) (sign z Y.1) deltaC delta2 :=
    fun Y => Classical.choose (hstopped Y)
  have hstoppedValid : ∀ Y a, ((stopped Y).plan a).ValidAt q :=
    fun Y => Classical.choose_spec (hstopped Y)
  let F := ExactMacroFamilyExtraction.assemble quarter outer stopped
  have hcorridor : ∀ Y, (F.outer Y).corridor.ValidAt q := by
    intro Y
    exact ExactOuterStageExtraction.corridor_validAt (outer Y)
      (houterValid Y) (hquarter Y)
  refine ⟨F, hcorridor, hstoppedValid, ?_⟩
  exact ExactMacroGeometry.Family.toPlan_validAt F hcorridor hstoppedValid

#print axioms KNAll.Site.ExactMacroFamilyFromTheta.exists_quarterTable
#print axioms KNAll.Site.ExactMacroFamilyFromTheta.exists_family_of_children

end KNAll.Site.ExactMacroFamilyFromTheta

end
