import Hypergraph.ExactMacroGeometry
import Hypergraph.ExactMacroNumerics
import Hypergraph.ExactDirectionMaps

/-!
# Finite assembly of an exact macro family

This module is the deterministic seam between the three finite child extractors and the accepted
macro interpreter.  It neither stores nor assumes a macro-level probability estimate: validity is
proved directly from the validity of the finitely indexed target plans.
-/

noncomputable section

namespace KNAll.Site.ExactMacroFamilyExtraction

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

abbrev Head (h : MacroExp.Tr d) (z : Site 2) :=
  ExactMacroGeometry.Head (d := d) h z

/-- Assemble the three concrete child tables.  All dependencies on the current owner, centre,
head, axis, and sign occur in the types of the supplied functions. -/
def assemble
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (quarter : ∀ Y : Head h z,
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
    (outer : ∀ Y : Head h z,
      ExactMacroGeometry.OuterStage p0 eta r t h w z (quarter Y) Y.1
        (axis z Y.1) (sign z Y.1) rho)
    (stopped : ∀ Y : Head h z,
      ExactMacroGeometry.StoppedChildren r t s K z Y.1
        (axis z Y.1) (sign z Y.1) deltaC delta2) :
    ExactMacroGeometry.Family p0 eta r t s K h w z axis sign rho deltaC delta2 :=
  { quarter := quarter, outer := outer, stopped := stopped }

@[simp] theorem assemble_quarter
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (quarter : ∀ Y : Head h z,
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
    (outer : ∀ Y : Head h z,
      ExactMacroGeometry.OuterStage p0 eta r t h w z (quarter Y) Y.1
        (axis z Y.1) (sign z Y.1) rho)
    (stopped : ∀ Y : Head h z,
      ExactMacroGeometry.StoppedChildren r t s K z Y.1
        (axis z Y.1) (sign z Y.1) deltaC delta2)
    (Y : Head h z) :
    (assemble quarter outer stopped).quarter Y = quarter Y := rfl

@[simp] theorem assemble_outer
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (quarter : ∀ Y : Head h z,
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
    (outer : ∀ Y : Head h z,
      ExactMacroGeometry.OuterStage p0 eta r t h w z (quarter Y) Y.1
        (axis z Y.1) (sign z Y.1) rho)
    (stopped : ∀ Y : Head h z,
      ExactMacroGeometry.StoppedChildren r t s K z Y.1
        (axis z Y.1) (sign z Y.1) deltaC delta2)
    (Y : Head h z) :
    (assemble quarter outer stopped).outer Y = outer Y := rfl

@[simp] theorem assemble_stopped
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (quarter : ∀ Y : Head h z,
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
    (outer : ∀ Y : Head h z,
      ExactMacroGeometry.OuterStage p0 eta r t h w z (quarter Y) Y.1
        (axis z Y.1) (sign z Y.1) rho)
    (stopped : ∀ Y : Head h z,
      ExactMacroGeometry.StoppedChildren r t s K z Y.1
        (axis z Y.1) (sign z Y.1) deltaC delta2)
    (Y : Head h z) :
    (assemble quarter outer stopped).stopped Y = stopped Y := rfl

/-- Validity of each assembled corridor is exactly validity of its `d` quarter leaves and its
one outer leaf.  `Fin.lastCases` makes the endpoint split exhaustive, including dimension zero. -/
theorem corridor_validAt
    {p0 q : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (quarter : ∀ Y : Head h z,
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
    (outer : ∀ Y : Head h z,
      ExactMacroGeometry.OuterStage p0 eta r t h w z (quarter Y) Y.1
        (axis z Y.1) (sign z Y.1) rho)
    (stopped : ∀ Y : Head h z,
      ExactMacroGeometry.StoppedChildren r t s K z Y.1
        (axis z Y.1) (sign z Y.1) deltaC delta2)
    (hquarter : ∀ Y a, ((quarter Y).quarter a).ValidAt q)
    (houter : ∀ Y, (outer Y).plan.ValidAt q) :
    ∀ Y, ((assemble quarter outer stopped).outer Y).corridor.ValidAt q := by
  intro Y u
  change (outer Y).corridor.stage u |>.ValidAt q
  rw [ExactMacroGeometry.OuterStage.corridor_stage]
  exact Fin.lastCases
    (by simpa using houter Y)
    (fun a => by simpa using hquarter Y a) u

/-- Direct finite validity package for the exact macro plan. -/
theorem toPlan_validAt
    {p0 q : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (quarter : ∀ Y : Head h z,
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
    (outer : ∀ Y : Head h z,
      ExactMacroGeometry.OuterStage p0 eta r t h w z (quarter Y) Y.1
        (axis z Y.1) (sign z Y.1) rho)
    (stopped : ∀ Y : Head h z,
      ExactMacroGeometry.StoppedChildren r t s K z Y.1
        (axis z Y.1) (sign z Y.1) deltaC delta2)
    (hquarter : ∀ Y a, ((quarter Y).quarter a).ValidAt q)
    (houter : ∀ Y, (outer Y).plan.ValidAt q)
    (hstopped : ∀ Y a, ((stopped Y).plan a).ValidAt q) :
    (assemble quarter outer stopped).toPlan.ValidAt q :=
  ExactMacroGeometry.Family.toPlan_validAt _
    (corridor_validAt quarter outer stopped hquarter houter) hstopped

/-! ## Canonical numerical and direction specialization -/

/-- The smallest current per-transcript bridge: once the three finite extractors provide their
actual children and leaf-validity proofs, all direction and real-valued v15 premises are
discharged by the explicit maps and numerical cascade. -/
theorem acceptedExploration_success
    (p0 q : unitInterval) (r t s K n : Nat)
    (hd : 3 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hpow : (1 - AtomTower.f (ExactMacroNumerics.deltaC d)) ^ K ≤
      ExactMacroNumerics.rho / 16)
    (base : BDDom.Transcript (Site d) (Site 2))
    (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q
      (ExactMacroNumerics.deltaC d) base)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hz : CoreFrontier.Frontier base.base (CoreStoppedReveal.centre n base))
    (quarter : ∀ Y : Head base.base (CoreStoppedReveal.centre n base),
      ExactQuarterPlanExtraction.QuarterStageFamily p0
        (fun a : Fin d => ExactMacroNumerics.eta d a.succ)
        (MacroExp.ctr d r (CoreStoppedReveal.centre n base)) r)
    (outer : ∀ Y : Head base.base (CoreStoppedReveal.centre n base),
      ExactMacroGeometry.OuterStage p0 (ExactMacroNumerics.eta d) r t base.base
        (CoreAcceptedTransition.owner hadm.preReveal.frontier
          (CoreStoppedReveal.centre n base) hz)
        (CoreStoppedReveal.centre n base) (quarter Y) Y.1
        (ExactDirectionMaps.axis (by omega : 2 ≤ d)
          (CoreStoppedReveal.centre n base) Y.1)
        (ExactDirectionMaps.sign (CoreStoppedReveal.centre n base) Y.1)
        ExactMacroNumerics.rho)
    (stopped : ∀ Y : Head base.base (CoreStoppedReveal.centre n base),
      ExactMacroGeometry.StoppedChildren r t s K
        (CoreStoppedReveal.centre n base) Y.1
        (ExactDirectionMaps.axis (by omega : 2 ≤ d)
          (CoreStoppedReveal.centre n base) Y.1)
        (ExactDirectionMaps.sign (CoreStoppedReveal.centre n base) Y.1)
        (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d))
    (hquarter : ∀ Y a, ((quarter Y).quarter a).ValidAt q)
    (houter : ∀ Y, (outer Y).plan.ValidAt q)
    (hstopped : ∀ Y a, ((stopped Y).plan a).ValidAt q) :
    (CoreSafe.successParam : Real) ≤
      base.prob (fun _ : Site d => q)
        ((CoreAcceptedAssembly.exploration r t s K n q
          (ExactMacroNumerics.deltaC d)
          (ExactDirectionMaps.axis (by omega : 2 ≤ d)) ExactDirectionMaps.sign
          (by omega : 2 ≤ d) hr (by omega : 2 * r ≤ t) hs hbudget
          (ExactDirectionMaps.scheduler_sign (d := d) (by omega : 2 ≤ d))
          (ExactDirectionMaps.scheduler_emb (d := d) (by omega : 2 ≤ d))).success base) := by
  let F := assemble quarter outer stopped
  have hcorridor : ∀ Y, (F.outer Y).corridor.ValidAt q :=
    corridor_validAt quarter outer stopped hquarter houter
  exact ExactMacroGeometry.Family.acceptedExploration_success_v15
    p0 q (ExactMacroNumerics.eta d) r t s K n ExactMacroNumerics.rho
    (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d)
    (ExactDirectionMaps.axis (by omega : 2 ≤ d)) ExactDirectionMaps.sign
    hd hr ht hs hbudget
    (ExactDirectionMaps.scheduler_sign (d := d) (by omega : 2 ≤ d))
    (ExactDirectionMaps.scheduler_emb (d := d) (by omega : 2 ≤ d))
    base hadm hactive hz F
    (ExactMacroNumerics.deltaC_le_eta_zero d) (by rfl)
    hcorridor hstopped ExactMacroNumerics.rho_pos ExactMacroNumerics.rho_le_half
    (ExactMacroNumerics.deltaC_pos d) (ExactMacroNumerics.deltaC_le_rho_half d)
    (ExactMacroNumerics.deltaC_le_beta d) hpow
    ExactMacroNumerics.successParam_le_one_sub_rho

#print axioms KNAll.Site.ExactMacroFamilyExtraction.corridor_validAt
#print axioms KNAll.Site.ExactMacroFamilyExtraction.toPlan_validAt
#print axioms KNAll.Site.ExactMacroFamilyExtraction.acceptedExploration_success

end KNAll.Site.ExactMacroFamilyExtraction

end
