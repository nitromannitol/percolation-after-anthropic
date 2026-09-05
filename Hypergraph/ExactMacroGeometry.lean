import Hypergraph.ExactMacroPlan
import Hypergraph.ExactQuarterPlanExtraction

/-!
# Deterministic geometry for a finite exact macro step

This module packages an actual quarter-stage family, one supplied exact outer long stage, and the
`K` supplied aspect-`2K` stopped children into `ExactMacroPlan.Plan`.  It proves the runtime
`DirectionCompatible` facts from finite set geometry and the accepted pre-reveal invariant.

There are no probability assumptions here.  `ValidAt` remains a separate finite leaf check.
-/

noncomputable section

namespace KNAll.Site.ExactMacroGeometry

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open ExactTargetArithmetic
open scoped Classical

variable {d : Nat} [NeZero d]

abbrev Tr (d : Nat) := MacroExp.Tr d
abbrev Head (h : Tr d) (z : Site 2) := ExactMacroPlan.Head (d := d) h z

/-- The fixed finite domain used by every exact corridor stage for one outgoing head. -/
def narrowDom (r t : Nat) (h : Tr d) (w z y : Site 2)
    (i : Fin d) (sigma : Int) : Finset (Site d) :=
  h.inspected ∪ MacroExp.E d r t w z ∪
    Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)

/-! ## Correct stopped-prefix containment and freshness -/

/-- A prefix is in the actual level domain.  Its part on `Q_z` is already in the incoming
transcript; only the part beyond `Q_z` is charged to `E(z,y)`. -/
theorem stub_subset_levelDomain
    (hd : 2 ≤ d) {r t s j : Nat} (hr : 0 < r)
    (hrt : 2 * r ≤ t)
    {h : Tr d} {w z y : Site 2} (hwz : w ≠ z)
    {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hdepth : 10 * s * (j + 1) ≤ 17 * r)
    (outer xi : SiteConfig (Site d)) :
    Stopped.stub (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)) ⊆
      (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
        z i sigma j xi).inspected ∪ MacroExp.E d r t z y := by
  intro x hx
  have hx' := Stopped.stub_subset_Q_union_E (d := d) (t := t)
    hr hdepth hrt hsigma hemb hx
  rcases Finset.mem_union.1 hx' with hxQ | hxE
  · apply Finset.mem_union_left
    rw [Stopped.levelTr_inspected, AtomTower.incomingTr_inspected]
    exact Finset.mem_union_left _
      (Finset.mem_union_right _ (CorrMove.Q_subset_E hd r t hr hwz hxQ))
  · exact Finset.mem_union_right _ hxE

/-- Static separation of the active stopped box from the already exposed prefix gives freshness
at every actual `levelTr`.  The result is independent of the values of the two configurations. -/
theorem levelTr_disjoint_active
    {r t s j : Nat} {h : Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {D : Finset (Site d)}
    (hincomingFresh : Disjoint (h.inspected ∪ MacroExp.E d r t w z)
      (MacroExp.E d r t z y))
    (hDE : D ⊆ MacroExp.E d r t z y)
    (hprefix : Disjoint
      (Stopped.stub (MacroExp.ctr d r z) i sigma r t (10 * s * j)) D)
    (outer xi : SiteConfig (Site d)) :
    Disjoint
      (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
        z i sigma j xi).inspected D := by
  rw [Stopped.levelTr_inspected, AtomTower.incomingTr_inspected,
    Finset.disjoint_union_left]
  exact ⟨hincomingFresh.mono_right hDE, hprefix⟩

/-! ## Exact corridor assembly -/

/-- A concrete outer long stage attached to an actual quarter family.  These are only finite
shape and arithmetic facts; `ValidAt` is intentionally absent. -/
structure OuterStage
    (p0 : unitInterval) (eta : Fin (d + 1) → Real)
    (r t : Nat) (h : Tr d) (w z : Site 2)
    (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
    (y : Site 2) (i : Fin d) (sigma : Int) (rho : Real) where
  scale_eq : Q.scale = r
  eta_step : ∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc
  plan : ExactTargetPlan.Plan d
  wellFormed : plan.WellFormed
  source_eq : plan.source = Q.boxes (Fin.last d)
  target_eq : plan.target =
    CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int))
  longTarget : CorrMove.LongTarget (plan.radius : Int) i sigma
    plan.active plan.source plan.target
  delta_eq : plan.delta = eta (Fin.last d)
  epsilon_eq : plan.epsilon = rho / 16
  active_subset_narrow : plan.active ⊆
    narrowDom r t h w z y i sigma
  active_subset_fresh_region : plan.active ⊆
    MacroExp.Q d r t z ∪ MacroExp.E d r t z y

/-- The exact corridor assembled from the `d` quarter children and the supplied outer stage.
Every stage uses the same finite narrow domain as its `past` set. -/
def OuterStage.corridor
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho) :
    ExactCorridorPlan.Plan d :=
  Q.toCorridorPlan (MacroExp.ctr d r y) A.plan i sigma
    (fun _ => narrowDom r t h w z y i sigma) eta (rho / 16)

@[simp] theorem OuterStage.corridor_stage
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho) (u : Fin (d + 1)) :
    A.corridor.stage u = Q.stagesWith A.plan u := by
  exact ExactCorridorPlan.Plan.stage_ofStageFamily _ _ _ _ _ _ _ _ _ _ u

/-- Every stage active box is contained in the common narrow domain. -/
theorem OuterStage.stage_active_subset_narrow
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho)
    (hd : 2 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hwz : w ≠ z) :
    ∀ u, ((A.corridor).stage u).active ⊆ narrowDom r t h w z y i sigma := by
  intro u
  refine Fin.lastCases ?_ (fun a => ?_) u
  · rw [A.corridor_stage, ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_last]
    exact A.active_subset_narrow
  · have hcubeQ : CorrMove.cube (MacroExp.ctr d r z) (5 * (r : Int)) ⊆
        MacroExp.Q d r t z := CorrMove.cube_subset_Q ht z
    have hQE : MacroExp.Q d r t z ⊆ MacroExp.E d r t w z :=
      CorrMove.Q_subset_E hd r t hr hwz
    rw [A.corridor_stage, ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_castSucc,
      Q.quarter_active, A.scale_eq]
    exact hcubeQ.trans (hQE.trans
      (le_trans Finset.subset_union_right Finset.subset_union_left))

/-- All stages are fresh from the old transcript when the protected quarter/outer regions are. -/
theorem OuterStage.stage_disjoint_inspected
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho)
    (ht : 5 * r ≤ t)
    (hfresh : Disjoint h.inspected
      (MacroExp.Q d r t z ∪ MacroExp.E d r t z y)) :
    ∀ u, Disjoint h.inspected ((A.corridor).stage u).active := by
  intro u
  refine Fin.lastCases ?_ (fun a => ?_) u
  · rw [A.corridor_stage, ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_last]
    exact hfresh.mono_right A.active_subset_fresh_region
  · have hcubeQ : CorrMove.cube (MacroExp.ctr d r z) (5 * (r : Int)) ⊆
        MacroExp.Q d r t z := CorrMove.cube_subset_Q ht z
    rw [A.corridor_stage, ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_castSucc,
      Q.quarter_active, A.scale_eq]
    exact hfresh.mono_right (hcubeQ.trans Finset.subset_union_left)

/-- The quarter family and one concrete outer stage form an actual well-formed exact corridor. -/
theorem OuterStage.corridor_wellFormed
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho)
    (hd : 2 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hwz : w ≠ z)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    A.corridor.WellFormed := by
  apply ExactCorridorPlan.Plan.wellFormed_ofStageFamily
  · exact Q.scale_pos
  · intro u
    exact Fin.lastCases
      (by simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using A.wellFormed)
      (fun a => by simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using
        Q.quarter_wellFormed a) u
  · intro u
    refine Fin.lastCases ?_ (fun a => ?_) u
    · simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using A.source_eq
    · simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using
        Q.quarter_source_box a
  · exact Q.boxes_zero
  · intro a
    simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using
      Q.quarter_target_box a
  · intro a
    simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using
      Q.quarter_geometry a
  · rw [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_last, A.target_eq,
      A.scale_eq]
  · exact hsigma
  · simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using A.longTarget
  · intro u
    refine Fin.lastCases ?_ (fun a => ?_) u
    · simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using A.delta_eq
    · rw [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_castSucc,
        Q.quarter_delta, A.eta_step a]
  · intro a
    simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using
      Q.quarter_epsilon a
  · simpa [ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith] using A.epsilon_eq
  · intro a
    have hleft : (Q.stagesWith A.plan a.castSucc).active ⊆
        narrowDom r t h w z y i sigma := by
      rw [← A.corridor_stage]
      exact A.stage_active_subset_narrow hd hr ht hwz a.castSucc
    have hright : (Q.stagesWith A.plan a.succ).active ⊆
        narrowDom r t h w z y i sigma := by
      rw [← A.corridor_stage]
      exact A.stage_active_subset_narrow hd hr ht hwz a.succ
    rw [Finset.union_eq_left.2 hleft, Finset.union_eq_left.2 hright]

/-! ## Exact stopped children -/

/-- The `K` concrete aspect-`2K` stopped target plans and their literal G2 shapes.  In the
eventual extractor, `source_eq` is `B_j = F^{j+1}`, `active_subset_outgoing` is the containment
`D_j ⊆ E(z,y)`, and `prefix_disjoint_active` is the one-layer gap before `D_j`. -/
structure StoppedChildren (r t s K : Nat) (z y : Site 2)
    (i : Fin d) (sigma : Int) (deltaC delta2 : Real) where
  plan : Fin K → ExactTargetPlan.Plan d
  wellFormed : ∀ a, (plan a).WellFormed
  active_subset_outgoing : ∀ a,
    (plan a).active ⊆ MacroExp.E d r t z y
  prefix_disjoint_active : ∀ a, Disjoint
    (Stopped.stub (MacroExp.ctr d r z) i sigma r t (10 * s * a.val))
    (plan a).active
  source_eq : ∀ a, (plan a).source =
    Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))
  target_subset : ∀ a, (plan a).target ⊆ CoreRes.target (d := d) r y
  input_tolerance : ∀ a, delta2 ≤ (plan a).delta
  output_error : ∀ a, (plan a).epsilon ≤ deltaC

/-! ## Per-head assembly at an accepted state -/

/-- All finite child data for one accepted examination.  The index types are the actual finite
new-head subtype and `Fin K`; no child is generated from a configuration or a history. -/
structure Family
    (p0 : unitInterval) (eta : Fin (d + 1) → Real)
    (r t s K : Nat) (h : Tr d) (w z : Site 2)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (rho deltaC delta2 : Real) where
  quarter : Head h z → ExactQuarterPlanExtraction.QuarterStageFamily p0
    (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r
  outer : ∀ Y : Head h z, OuterStage p0 eta r t h w z (quarter Y) Y.1
    (axis z Y.1) (sign z Y.1) rho
  stopped : ∀ Y : Head h z,
    StoppedChildren r t s K z Y.1 (axis z Y.1) (sign z Y.1)
    deltaC delta2

/-- Forget the shape witnesses and retain exactly the finite child tables consumed by the
probability interpreter. -/
def Family.toPlan
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (F : Family p0 eta r t s K h w z axis sign rho deltaC delta2) :
    ExactMacroPlan.Plan h z K where
  corridor Y := (F.outer Y).corridor
  stopped Y := (F.stopped Y).plan

@[simp] theorem Family.toPlan_corridor
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (F : Family p0 eta r t s K h w z axis sign rho deltaC delta2)
    (Y : Head h z) :
    (F.toPlan.corridor Y) = (F.outer Y).corridor := rfl

@[simp] theorem Family.toPlan_stopped
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (F : Family p0 eta r t s K h w z axis sign rho deltaC delta2)
    (Y : Head h z) (a : Fin K) :
    (F.toPlan.stopped Y a) = (F.stopped Y).plan a := rfl

/-- Child validity stays a separate finite premise and gives exactly `Plan.ValidAt`. -/
theorem Family.toPlan_validAt
    {p0 q : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (F : Family p0 eta r t s K h w z axis sign rho deltaC delta2)
    (hcorridor : ∀ Y, (F.outer Y).corridor.ValidAt q)
    (hstopped : ∀ Y a, ((F.stopped Y).plan a).ValidAt q) :
    F.toPlan.ValidAt q := ⟨hcorridor, hstopped⟩

/-- Deterministic well-formedness of the finite child table. -/
theorem Family.toPlan_wellFormed
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (F : Family p0 eta r t s K h w z axis sign rho deltaC delta2)
    (hd : 2 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hwz : w ≠ z)
    (hsigma : ∀ Y : Head h z, sign z Y.1 = 1 ∨ sign z Y.1 = -1) :
    F.toPlan.WellFormed := by
  constructor
  · intro Y
    exact (F.outer Y).corridor_wellFormed hd hr ht hwz (hsigma Y)
  · intro Y a
    exact (F.stopped Y).wellFormed a

/-! ## Exact deterministic compatibility -/

@[simp] theorem OuterStage.corridor_beta
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho) :
    A.corridor.beta = eta 0 := rfl

@[simp] theorem OuterStage.corridor_alpha
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho) :
    A.corridor.alpha = rho / 16 := rfl

@[simp] theorem OuterStage.corridor_past
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho) (u : Fin (d + 1)) :
    A.corridor.past u = narrowDom r t h w z y i sigma := rfl

theorem OuterStage.corridor_domain_eq_narrow
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : OuterStage p0 eta r t h w z Q y i sigma rho)
    (hd : 2 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hwz : w ≠ z)
    (u : Fin (d + 1)) :
    A.corridor.domain u = narrowDom r t h w z y i sigma := by
  rw [ExactCorridorPlan.Plan.domain, A.corridor_past,
    Finset.union_eq_left.2 (A.stage_active_subset_narrow hd hr ht hwz u)]

/-- Accepted pre-reveal geometry proves every field of the exact interpreter compatibility
record.  The stopped active-box premises are the literal G2 containments supplied by the
aspect-`2K` child constructor. -/
theorem Family.directionCompatible
    {p0 q : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : Tr d} {z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (hpre : CoreAcceptedTransition.PreReveal r t q deltaC h)
    (hz : CoreFrontier.Frontier h z)
    (F : Family p0 eta r t s K h
      (CoreAcceptedTransition.owner hpre.frontier z hz) z axis sign rho deltaC delta2)
    (hd : 2 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hdepth : 10 * s * K ≤ 13 * r)
    (hsigma : ∀ Y : Head h z, sign z Y.1 = 1 ∨ sign z Y.1 = -1)
    (hemb : ∀ Y : Head h z,
      (MacroExp.emb (Y.1 - z) : Site d) =
        Pi.single (axis z Y.1) (sign z Y.1))
    (hbeta : deltaC ≤ eta 0)
    (hfdelta : AtomTower.f deltaC ≤ delta2)
    (Y : Head h z) :
    ExactMacroPlan.DirectionCompatible (r := r) (t := t) (s := s)
      (w := CoreAcceptedTransition.owner hpre.frontier z hz)
      (e := deltaC) (deltaC := deltaC) (rho := rho) axis sign F.toPlan Y := by
  let w := CoreAcceptedTransition.owner hpre.frontier z hz
  have hgeom := CoreAcceptedTransition.outgoing_geometry_of_preReveal hd hr hpre hz
  have hwz : w ≠ z := hgeom.1
  have hY := hgeom.2.2 Y.1 Y.2
  have hstageFresh := (F.outer Y).stage_disjoint_inspected ht hY.2.1
  refine {
    sign_unit := hsigma Y
    emb_direction := hemb Y
    head_ne_zero := hY.1
    outgoing_fresh := hY.2.2.2
    corridor_beta := by simpa only [Family.toPlan_corridor,
      OuterStage.corridor_beta] using hbeta
    corridor_alpha := by simp
    corridor_exterior := ?_
    corridor_first_domain := ?_
    corridor_first_source := ?_
    corridor_last_domain := ?_
    corridor_last_target := ?_
    stopped_active := ?_
    stopped_fresh := ?_
    stopped_stub_domain := ?_
    stopped_source := ?_
    stopped_target := ?_
    stopped_delta := ?_
    stopped_epsilon := ?_ }
  · intro u x hx
    rw [ExactTargetPlan.exterior, Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [Family.toPlan_corridor, (F.outer Y).corridor_past]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · intro hxactive
      exact Finset.disjoint_left.1 (hstageFresh u) hx hxactive
  · rw [Family.toPlan_corridor,
      (F.outer Y).corridor_domain_eq_narrow hd hr ht hwz]
    exact fun x hx => Finset.mem_union_left _ hx
  · rw [Family.toPlan_corridor, OuterStage.corridor,
      ExactCorridorPlan.Plan.initialCore]
    change CoreRes.target (d := d) r z ⊆
      CorrMove.cube (MacroExp.ctr d r z) (3 * ((F.quarter Y).scale : Int))
    rw [(F.outer Y).scale_eq]
    exact CoreRes.target_subset_sourceCube r z
  · rw [Family.toPlan_corridor,
      (F.outer Y).corridor_domain_eq_narrow hd hr ht hwz]
    exact fun _ hx => hx
  · rw [Family.toPlan_corridor, OuterStage.corridor,
      ExactCorridorPlan.Plan.innerTarget]
    change CorrMove.cube (MacroExp.ctr d r Y.1) (2 * ((F.quarter Y).scale : Int)) ⊆
      CoreRes.target (d := d) r Y.1
    rw [(F.outer Y).scale_eq]
    exact CorrMove.ibox_mono (fun _ => by omega)
  · intro outer a xi x hx
    exact Finset.mem_union_right _ ((F.stopped Y).active_subset_outgoing a hx)
  · intro outer a xi
    exact levelTr_disjoint_active hY.2.2.2
      ((F.stopped Y).active_subset_outgoing a)
      ((F.stopped Y).prefix_disjoint_active a) outer xi
  · intro outer a xi
    apply stub_subset_levelDomain hd hr (by omega : 2 * r ≤ t) hwz
      (hsigma Y) (hemb Y)
    · have ha : a.val + 1 ≤ K := Nat.succ_le_iff.2 a.isLt
      calc
        10 * s * (a.val + 1) ≤ 10 * s * K := Nat.mul_le_mul_left _ ha
        _ ≤ 13 * r := hdepth
        _ ≤ 17 * r := by omega
  · intro a
    rw [Family.toPlan_stopped, (F.stopped Y).source_eq a]
  · intro a
    simpa only [Family.toPlan_stopped] using (F.stopped Y).target_subset a
  · intro a
    exact hfdelta.trans (by simpa only [Family.toPlan_stopped] using
      (F.stopped Y).input_tolerance a)
  · intro a
    simpa only [Family.toPlan_stopped] using (F.stopped Y).output_error a

/-! ## Probability interpretation and accepted-scheduler packaging -/

/-- The concrete quarter/outer/stopped family supplies the exact one-owner batch estimate at an
accepted pre-reveal state.  All probabilistic input is confined to the finite `ValidAt` checks;
the remaining premises are deterministic geometry and the v15 numerical budget. -/
theorem Family.prob_batchFailure_le_v15
    {p0 q : unitInterval} {eta : Fin (d + 1) → Real}
    {r t s K : Nat} {h : Tr d} {z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {rho deltaC delta2 : Real}
    (hpre : CoreAcceptedTransition.PreReveal r t q deltaC h)
    (hz : CoreFrontier.Frontier h z)
    (F : Family p0 eta r t s K h
      (CoreAcceptedTransition.owner hpre.frontier z hz) z axis sign rho deltaC delta2)
    (hd : 3 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ Y : Head h z, sign z Y.1 = 1 ∨ sign z Y.1 = -1)
    (hemb : ∀ Y : Head h z,
      (MacroExp.emb (Y.1 - z) : Site d) =
        Pi.single (axis z Y.1) (sign z Y.1))
    (hbeta : deltaC ≤ eta 0)
    (hfdelta : AtomTower.f deltaC ≤ delta2)
    (hcorridor : ∀ Y, (F.outer Y).corridor.ValidAt q)
    (hstopped : ∀ Y a, ((F.stopped Y).plan a).ValidAt q)
    (hrho0 : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (hdeltaC0 : 0 < deltaC) (hdeltaC : deltaC ≤ rho / 2)
    (heBeta : deltaC ≤ AtomTower.beta (2 * rho) d)
    (hpow : (1 - AtomTower.f deltaC) ^ K ≤ rho / 16) :
    h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h
        (CoreAcceptedTransition.owner hpre.frontier z hz)
        z (axis z) (sign z) q deltaC) ≤ rho := by
  have hgeom := CoreAcceptedTransition.outgoing_geometry_of_preReveal
    (by omega : 2 ≤ d) hr hpre hz
  have hMwf := F.toPlan_wellFormed (by omega : 2 ≤ d) hr ht hgeom.1 hsigma
  have hMvalid := F.toPlan_validAt hcorridor hstopped
  have hcompat : ∀ Y : Head h z,
      ExactMacroPlan.DirectionCompatible (r := r) (t := t) (s := s)
        (w := CoreAcceptedTransition.owner hpre.frontier z hz)
        (e := deltaC) (deltaC := deltaC) (rho := rho)
        axis sign F.toPlan Y :=
    F.directionCompatible hpre hz (by omega : 2 ≤ d) hr ht
      (by omega : 10 * s * K ≤ 13 * r)
      hsigma hemb hbeta hfdelta
  have hincoming := (CoreAcceptedTransition.owner_spec hpre.frontier z hz).2.2
  exact F.toPlan.prob_batchFailure_le axis sign hMwf hMvalid hcompat
    hd hr ht hs hbudget hgeom.2.1 hrho0 hrhoHalf hdeltaC0 hdeltaC heBeta hpow
    hincoming (h.openSites_subset hpre.origin_open) hpre.origin_open

/-- Package the concrete per-head family into the actual accepted-only stopped exploration.
The family is indexed by the accepted invariant's owner; proof-independent-owner equality moves
its batch estimate to the scheduler's owner. -/
theorem Family.acceptedExploration_success_v15
    (p0 q : unitInterval) (eta : Fin (d + 1) → Real)
    (r t s K n : Nat) (rho deltaC delta2 : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 3 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q deltaC base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q deltaC base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y))
    (base : BDDom.Transcript (Site d) (Site 2))
    (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n)
      r t q deltaC base)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hz : CoreFrontier.Frontier base.base (CoreStoppedReveal.centre n base))
    (F : Family p0 eta r t s K base.base
      (CoreAcceptedTransition.owner hadm.preReveal.frontier
        (CoreStoppedReveal.centre n base) hz)
      (CoreStoppedReveal.centre n base) axis sign rho deltaC delta2)
    (hbeta : deltaC ≤ eta 0)
    (hfdelta : AtomTower.f deltaC ≤ delta2)
    (hcorridor : ∀ Y, (F.outer Y).corridor.ValidAt q)
    (hstopped : ∀ Y a, ((F.stopped Y).plan a).ValidAt q)
    (hrho0 : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (hdeltaC0 : 0 < deltaC) (hdeltaC : deltaC ≤ rho / 2)
    (heBeta : deltaC ≤ AtomTower.beta (2 * rho) d)
    (hpow : (1 - AtomTower.f deltaC) ^ K ≤ rho / 16)
    (hparam : (CoreSafe.successParam : Real) ≤ 1 - rho) :
    (CoreSafe.successParam : Real) ≤
      base.prob (fun _ : Site d => q)
        ((CoreAcceptedAssembly.exploration r t s K n q deltaC axis sign
          (by omega : 2 ≤ d) hr (by omega : 2 * r ≤ t)
          hs hbudget hsigma hemb).success base) := by
  have hfail := F.prob_batchFailure_le_v15 hadm.preReveal hz hd hr ht hs
    hbudget
    (fun Y => hsigma base hadm hactive Y.1 Y.2)
    (fun Y => hemb base hadm hactive Y.1 Y.2)
    hbeta hfdelta hcorridor hstopped hrho0 hrhoHalf hdeltaC0 hdeltaC heBeta hpow
  have howner := CoreStoppedReveal.owner_eq_of_invariant hadm.preReveal.frontier hz
  have hfail' : base.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K base.base
        (CoreStoppedReveal.owner r t q deltaC n base)
        (CoreStoppedReveal.centre n base)
        (axis (CoreStoppedReveal.centre n base))
        (sign (CoreStoppedReveal.centre n base)) q deltaC) ≤ rho := by
    rw [howner]
    exact hfail
  exact ExactMacroPlan.acceptedExploration_success_of_batchFailure_v15
    r t s K n q deltaC rho axis sign (by omega : 2 ≤ d) hr
    (by omega : 2 * r ≤ t) hs hbudget
    hsigma hemb base hparam hfail'

#print axioms KNAll.Site.ExactMacroGeometry.stub_subset_levelDomain
#print axioms KNAll.Site.ExactMacroGeometry.OuterStage.corridor_wellFormed
#print axioms KNAll.Site.ExactMacroGeometry.Family.toPlan_wellFormed
#print axioms KNAll.Site.ExactMacroGeometry.Family.directionCompatible
#print axioms KNAll.Site.ExactMacroGeometry.Family.prob_batchFailure_le_v15
#print axioms KNAll.Site.ExactMacroGeometry.Family.acceptedExploration_success_v15

end KNAll.Site.ExactMacroGeometry

end
