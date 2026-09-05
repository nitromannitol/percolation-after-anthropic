import Hypergraph.ExactMacroFamilyFromTheta
import Hypergraph.ExactStoppedChildrenExtraction
import Hypergraph.ExactReachableMacroInterpreter

/-!
# One exact accepted macro step from positive percolation

The target schemes and quarter plans are frozen at `p0`.  The conclusion is at an independently
specified `q`; consequently validity at `q` of every frozen quarter, outer, and stopped leaf is an
explicit finite premise.  The outer and stopped geometry is assembled by the concrete extraction
modules, and the result has exactly the `LocalAcceptedSuccess` type used by the reachable macro
interpreter.
-/

noncomputable section

namespace KNAll.Site.ExactMacroStepFromTheta

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

/-- Freeze the `d` target schemes once at `p0`. -/
def frozenSchemes (p0 : unitInterval) (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0) :
    ∀ i : Fin d, ExactTargetScheme.OrthantScheme d p0
      (ExactMacroNumerics.eta d i.succ) := fun i =>
  Classical.choice
    (ExactTargetScheme.exists_orthantScheme_of_thetaSite_pos p0 hp0 hp1 htheta
      (ExactMacroNumerics.eta d i.succ)
      (ExactMacroNumerics.eta_pos d i.succ)
      (ExactMacroNumerics.eta_le_one d i.succ))

/-- The common radius of the frozen quarter schemes. -/
def quarterRadius (p0 : unitInterval) (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0) : Nat :=
  ExactQuarterPlanExtraction.commonRadius (frozenSchemes p0 hp0 hp1 htheta)

/-- The same frozen schemes instantiated at an arbitrary centre and any macro scale satisfying
their explicit separation inequality. -/
def quarterAt (p0 : unitInterval) (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0)
    (r : Nat) (z : Site 2)
    (hsep : 100 * (d + 1) * (quarterRadius p0 hp0 hp1 htheta + 1) < r) :
    ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun i : Fin d => ExactMacroNumerics.eta d i.succ)
      (MacroExp.ctr d r z) r := by
  let S := frozenSchemes p0 hp0 hp1 htheta
  let R := quarterRadius p0 hp0 hp1 htheta
  let c := MacroExp.ctr d r z
  have hlocal : ∀ i, (S i).scales.localRadius < R :=
    fun i => ExactQuarterPlanExtraction.localRadius_lt_commonRadius S i
  have hR0 : ∀ i, (S i).numbers.R0 ≤ R :=
    fun i => ExactQuarterPlanExtraction.arithmeticRadius_le_commonRadius S i
  let I : ∀ i, ExactTargetScheme.OrthantInstantiation (S i) := fun i =>
    ExactQuarterPlanExtraction.crossInstantiation (S i) c r R i
      (hR0 i) (hlocal i) hsep
  let C : Fin d → ExactTargetPlan.Plan d := fun i =>
    ExactQuarterPlanExtraction.crossPlan (S i) c r R i
      (hR0 i) (hlocal i) hsep
  exact
    { radius := R
      scale := r
      scheme := S
      instantiation := I
      quarter := C
      radius_pos := by
        unfold R quarterRadius ExactQuarterPlanExtraction.commonRadius
        omega
      scale_pos := by omega
      scale_floor := le_rfl
      separation := hsep
      instantiation_source := fun i =>
        ExactQuarterPlanExtraction.crossInstantiation_sourceBox
          (S i) c r R i (hR0 i) (hlocal i) hsep
      instantiation_active := fun i =>
        ExactQuarterPlanExtraction.crossInstantiation_activeBox
          (S i) c r R i (hR0 i) (hlocal i) hsep
      instantiation_target := fun i =>
        ExactQuarterPlanExtraction.crossInstantiation_target
          (S i) c r R i (hR0 i) (hlocal i) hsep
      instantiation_radius := fun i =>
        ExactQuarterPlanExtraction.crossInstantiation_radius
          (S i) c r R i (hR0 i) (hlocal i) hsep
      quarter_wellFormed := fun i =>
        ExactQuarterPlanExtraction.crossPlan_wellFormed hp0 hp1
          (ExactMacroNumerics.eta_pos d i.succ)
          (ExactMacroNumerics.eta_le_one d i.succ)
          (S i) c r R i (hR0 i) (hlocal i) hsep
      quarter_validAt := fun i =>
        ExactQuarterPlanExtraction.crossPlan_validAt hp0 hp1
          (ExactMacroNumerics.eta_pos d i.succ)
          (ExactMacroNumerics.eta_le_one d i.succ)
          (S i) c r R i (hR0 i) (hlocal i) hsep
      quarter_source := fun i =>
        ExactQuarterPlanExtraction.crossPlan_source
          (S i) c r R i (hR0 i) (hlocal i) hsep
      quarter_active := fun i =>
        ExactQuarterPlanExtraction.crossPlan_active
          (S i) c r R i (hR0 i) (hlocal i) hsep
      quarter_target := fun i =>
        ExactQuarterPlanExtraction.crossPlan_target
          (S i) c r R i (hR0 i) (hlocal i) hsep
      quarter_radius := fun i =>
        ExactQuarterPlanExtraction.crossPlan_radius
          (S i) c r R i (hR0 i) (hlocal i) hsep
      quarter_epsilon := fun i =>
        ExactQuarterPlanExtraction.crossPlan_epsilon
          (S i) c r R i (hR0 i) (hlocal i) hsep
      quarter_geometry := fun i =>
        ExactQuarterPlanExtraction.crossPlan_faceTarget
          (S i) c r R i (hR0 i) (hlocal i) hsep }

@[simp] theorem quarterAt_scale
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) (r : Nat) (z : Site 2)
    (hsep : 100 * (d + 1) * (quarterRadius p0 hp0 hp1 htheta + 1) < r) :
    (quarterAt p0 hp0 hp1 htheta r z hsep).scale = r := rfl

/-! ## Frozen outer and stopped constructors -/

/-- The single frozen stopped prototype used by both stability and macro instantiation. -/
def stoppedData
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0)
    (K : Nat) (hK : 20 ≤ K) :
    ExactStoppedChildrenExtraction.Concrete.FrozenStoppedData d p0 K :=
  Classical.choice
    (ExactStoppedChildrenExtraction.Concrete.exists_frozenStoppedData_of_thetaSite_pos
      (d := d) p0 hp0 hp1 htheta K (by omega))

/-- The scale radius of the shared stopped prototype. -/
def stoppedRadius
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0)
    (K : Nat) (hK : 20 ≤ K) : Nat :=
  (stoppedData p0 hp0 hp1 htheta K hK).radius

/-- The concrete stopped children instantiated from the shared frozen prototype. -/
def stoppedAt
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0)
    {K r t s : Nat} (hK : 20 ≤ K) (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s)
    (hlarge : 2 * stoppedRadius p0 hp0 hp1 htheta K hK ≤ s) (ht : 5 * r ≤ t)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma
      (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d) :=
  ExactStoppedChildrenExtraction.Concrete.FrozenStoppedData.children hp0 hp1
    (stoppedData p0 hp0 hp1 htheta K hK) hK z y i sigma hs hr hlarge ht hsigma hemb

/-! ## Exact one-step probability theorem -/

/-- Positive percolation at `p0`, explicit v15 scales, and validity at `q` of the frozen quarter
family together with literal exact outer/stopped children give the local accepted-state success
premise of the reachable interpreter.  The last two inputs are precisely the concrete existential
outputs of the finite prototype-stability theorems; no arbitrary-plan soundness is assumed. -/
theorem localAcceptedSuccess
    (hd : 3 ≤ d) (p0 q : unitInterval)
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (r t s K : Nat) (hr : 0 < r) (hr44 : 44 ≤ r) (hK : 20 ≤ K)
    (ht : 5 * r ≤ t) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hrEq : r = K * s)
    (hsep : 100 * (d + 1) * (quarterRadius p0 hp0 hp1 htheta + 1) < r)
    (hpow : (1 - AtomTower.f (ExactMacroNumerics.deltaC d)) ^ K ≤
      ExactMacroNumerics.rho / 16)
    (hquarterValid : ∀ z i,
      ((quarterAt p0 hp0 hp1 htheta r z hsep).quarter i).ValidAt q)
    (houterValid : ∀ (h : ExactMacroGeometry.Tr d) (w z y : Site 2)
      (i : Fin d) (sigma : Int) (hwz : w ≠ z)
      (hsigma : sigma = 1 ∨ sigma = -1)
      (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma),
      ∃ A : ExactMacroGeometry.OuterStage p0 (ExactMacroNumerics.eta d) r t h w z
          (quarterAt p0 hp0 hp1 htheta r z hsep) y i sigma ExactMacroNumerics.rho,
        A.plan.ValidAt q)
    (hstoppedValid : ∀ (z y : Site 2) (i : Fin d) (sigma : Int)
      (hsigma : sigma = 1 ∨ sigma = -1)
      (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma),
      ∃ G : ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma
          (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d),
        ∀ a, (G.plan a).ValidAt q) :
    ExactReachableMacro.LocalAcceptedSuccess (d := d) (by omega : 2 ≤ d)
      r t s K q (ExactMacroNumerics.deltaC d) hr
      (by omega : 2 * r ≤ t) hs hbudget := by
  apply ExactReachableMacro.localAcceptedSuccess_of_families_v15
    hd r t s K p0 q (ExactMacroNumerics.deltaC d) hr ht hs hbudget
    (ExactMacroNumerics.deltaC_pos d) (ExactMacroNumerics.deltaC_le_rho_half d)
    (ExactMacroNumerics.deltaC_le_beta d) (ExactMacroNumerics.deltaC_le_eta_zero d) hpow
  intro n base hadm hactive hz
  let z := CoreStoppedReveal.centre n base
  let Q := quarterAt p0 hp0 hp1 htheta r z hsep
  let quarter : ∀ Y : ExactMacroGeometry.Head base.base z,
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun i : Fin d => ExactMacroNumerics.eta d i.succ)
        (MacroExp.ctr d r z) r := fun _ => Q
  have hquarter : ∀ Y a, ((quarter Y).quarter a).ValidAt q :=
    fun _ a => hquarterValid z a
  have hgeom := CoreAcceptedTransition.outgoing_geometry_of_preReveal
    (by omega : 2 ≤ d) hr hadm.preReveal hz
  have houter : ∀ Y : ExactMacroGeometry.Head base.base z,
      ∃ A : ExactMacroGeometry.OuterStage p0 (ExactMacroNumerics.eta d)
          r t base.base (CoreAcceptedTransition.owner hadm.preReveal.frontier z hz)
          z (quarter Y) Y.1
          (ExactDirectionMaps.axis (by omega : 2 ≤ d) z Y.1)
          (ExactDirectionMaps.sign z Y.1) ExactMacroNumerics.rho,
        A.plan.ValidAt q := by
    intro Y
    have hsigma := ExactDirectionMaps.signFrom_newHead (d := d)
      (by omega : 2 ≤ d) Y.2
    have hemb := ExactDirectionMaps.emb_sub_eq_single_newHead (d := d)
      (by omega : 2 ≤ d) Y.2
    exact houterValid base.base
      (CoreAcceptedTransition.owner hadm.preReveal.frontier z hz) z Y.1
      (ExactDirectionMaps.axis (by omega : 2 ≤ d) z Y.1)
      (ExactDirectionMaps.sign z Y.1) hgeom.1 hsigma hemb
  have hstopped : ∀ Y : ExactMacroGeometry.Head base.base z,
      ∃ G : ExactMacroGeometry.StoppedChildren r t s K z Y.1
          (ExactDirectionMaps.axis (by omega : 2 ≤ d) z Y.1)
          (ExactDirectionMaps.sign z Y.1)
          (ExactMacroNumerics.deltaC d) (AtomTower.f (ExactMacroNumerics.deltaC d)),
        ∀ a, (G.plan a).ValidAt q := by
    intro Y
    have hsigma := ExactDirectionMaps.signFrom_newHead (d := d)
      (by omega : 2 ≤ d) Y.2
    have hemb := ExactDirectionMaps.emb_sub_eq_single_newHead (d := d)
      (by omega : 2 ≤ d) Y.2
    exact hstoppedValid z Y.1
      (ExactDirectionMaps.axis (by omega : 2 ≤ d) z Y.1)
      (ExactDirectionMaps.sign z Y.1) hsigma hemb
  obtain ⟨F, hcorridor, hstoppedValid, _⟩ :=
    ExactMacroFamilyFromTheta.exists_family_of_children quarter hquarter houter hstopped
  exact ⟨F, hcorridor, hstoppedValid⟩

#print axioms KNAll.Site.ExactMacroStepFromTheta.quarterAt
#print axioms KNAll.Site.ExactMacroStepFromTheta.localAcceptedSuccess

end KNAll.Site.ExactMacroStepFromTheta

end
