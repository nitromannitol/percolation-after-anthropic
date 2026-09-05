import Hypergraph.ExactMacroGeometry
import Hypergraph.ExactLongBoxHitBridge

/-!
# Extraction of the outer stage of an exact macro corridor

`ExactMacroGeometry.OuterStage` is the last node of the exact corridor attached to one outgoing
macro head.  It bundles

* the two scale/error bookkeeping equations `scale_eq` and `eta_step`,
* one honest `ExactTargetPlan.Plan d` together with its `WellFormed` certificate,
* the four literal equations `source_eq`, `target_eq`, `delta_eq`, `epsilon_eq`, and
* the three deterministic geometry facts `longTarget`, `active_subset_narrow`,
  `active_subset_fresh_region`.

This module is the extraction layer that produces such a stage.  It has two levels.

## 1.  The parametric constructor

`outerStage` takes an exact target plan whose source is the corridor's last cross-section box,
whose active set *contains* the long slab `D'` of (7.7) and is contained in the narrow domain and
in the fresh region, and whose target *contains* the radius-`2r` cube at the neighbouring macro
centre.  It proves `longTarget` from `CorrMove.longTarget_cube` and returns the `OuterStage`.
Nothing here is probabilistic and nothing is assumed about the plan beyond its own `WellFormed`;
in particular no designated open site and no hit certificate is taken as input.

The active-set containment is deliberately one-sided.  The aspect-`88`
move of `CorrMove.longTarget_cube` reaches the radius-`2r` cube at `c_y` from inside the slab
`D' = dbox c_z i σ [-2r, 22r] × Λ_{2r}`, and `CorrMove.LongTarget` is monotone in both its allowed
set and its target (`longTarget_mono`).  The exact target is the literal radius-`2r` cube, which
fits in `D'`.  Corridor soundness subsequently enlarges this event to the radius-`3r` recursive
reservation core.

## 2.  The aspect-`88` bridge layer

`KN.ExactLongBoxHitBridge.RankOne` builds an ordinary `ExactTargetPlan.Plan d` out of the exact
variable-aspect long-box chain, whose only non-canonical leaves are whole aspect-`A` set-source
cylinders.  `outerInstantiation` places that rank-one plan on the outer boxes, and
`exists_outerLongPlan_of_thetaSite_pos` runs it from `0 < thetaSite d p₀` alone.  Combining it
with the parametric constructor gives `exists_outerStage_of_thetaSite_pos`: the outer stage, and
the corridor's `WellFormed` and `ValidAt p₀`, from supercriticality plus frozen numerics.
`exists_outerStage_slab_of_thetaSite_pos` specialises the active box to `D'` itself and discharges
every remaining box obligation, using `cube_two_subset_outerSlab`, `outerSlab_subset_narrowDom`
and `outerSlab_subset_Q_union_E`; `not_coreTarget_subset_outerSlab` records, for the record, that
the radius-`3 r` reservation core is the one target that would *not* fit in `D'`.

## 3.  `WellFormed` / `ValidAt` exports

`ValidAt` is never a field of `OuterStage`.  The corridor built from a quarter family and an outer
stage is valid at a parameter exactly when the outer plan and the `d` quarter plans are;
`corridor_validAt` and `corridor_validAt_p0` record this, and `corridor_wellFormed` restates the
deterministic side.
-/

noncomputable section

namespace KNAll.Site.ExactOuterStageExtraction

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open ExactTargetArithmetic
open scoped Classical

variable {d : Nat} [NeZero d]

/-! ## Literal integer boxes used by the outer stage -/

/-- Half-width of the corridor source cube `Q.boxes (Fin.last d)`. -/
def sourceHalfWidth (d scale radius : Nat) : Int :=
  (CorrMove.hw scale : Int) + (d : Int) * (radius : Int)

/-- `CorrMove.cube v l` as an `IntBox`. -/
def cubeBox (v : Site d) (l : Int) : ExactTargetPlan.IntBox d where
  lower j := v j - l
  upper j := v j + l

omit [NeZero d] in
@[simp] theorem cubeBox_sites (v : Site d) (l : Int) :
    (cubeBox v l).sites = CorrMove.cube v l := by
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, CorrMove.mem_cube]
  refine forall_congr' fun j => ?_
  rw [abs_le]
  simp only [cubeBox]
  omega

omit [NeZero d] in
theorem cubeBox_ordered (v : Site d) {l : Int} (hl : 0 ≤ l) : (cubeBox v l).Ordered := by
  intro j
  simp only [cubeBox]
  omega

omit [NeZero d] in
/-- Inflating a cube box by `R` is the cube box of radius `l + R`. -/
theorem cubeBox_inflate_sites (v : Site d) (l : Int) (R : Nat) :
    ((cubeBox v l).inflate R).sites = CorrMove.cube v (l + (R : Int)) := by
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, CorrMove.mem_cube]
  refine forall_congr' fun j => ?_
  rw [abs_le]
  simp only [ExactTargetPlan.IntBox.inflate, cubeBox]
  omega

/-- `CorrMove.dbox c i sigma lo hi w` as an `IntBox`. -/
def dboxBox (c : Site d) (i : Fin d) (sigma lo hi w : Int) : ExactTargetPlan.IntBox d where
  lower j := if j = i then (if sigma = 1 then c j + lo else c j - hi) else c j - w
  upper j := if j = i then (if sigma = 1 then c j + hi else c j - lo) else c j + w

omit [NeZero d] in
theorem dboxBox_sites (c : Site d) (i : Fin d) {sigma lo hi w : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) :
    (dboxBox c i sigma lo hi w).sites = CorrMove.dbox c i sigma lo hi w := by
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, CorrMove.mem_dbox hsigma]
  constructor
  · intro hx
    have hxi := hx i
    simp only [dboxBox] at hxi
    refine ⟨?_, fun j hji => ?_⟩
    · rcases hsigma with rfl | rfl <;> norm_num at hxi ⊢ <;> omega
    · have hxj := hx j
      simp only [dboxBox, if_neg hji] at hxj
      rw [abs_le]
      omega
  · rintro ⟨hxi, hoff⟩ j
    by_cases hji : j = i
    · subst hji
      simp only [dboxBox]
      rcases hsigma with rfl | rfl <;> norm_num at hxi ⊢ <;> omega
    · simp only [dboxBox, if_neg hji]
      have := abs_le.1 (hoff j hji)
      omega

omit [NeZero d] in
theorem dboxBox_ordered (c : Site d) (i : Fin d) {sigma lo hi w : Int}
    (hlohi : lo ≤ hi) (hw : 0 ≤ w) : (dboxBox c i sigma lo hi w).Ordered := by
  intro j
  simp only [dboxBox]
  split_ifs <;> omega

/-- The long slab `D'` of (7.7): signed longitudinal interval `[-2r, 22r]`, transverse half-width
`2 r`.  This is the smallest active set the outer stage can use. -/
def outerSlab (r : Nat) (z : Site 2) (i : Fin d) (sigma : Int) : Finset (Site d) :=
  CorrMove.dbox (MacroExp.ctr d r z) i sigma
    (-(2 * (r : Int))) (22 * (r : Int)) (2 * (r : Int))

/-- `outerSlab` as an `IntBox`. -/
def outerSlabBox (r : Nat) (z : Site 2) (i : Fin d) (sigma : Int) :
    ExactTargetPlan.IntBox d :=
  dboxBox (MacroExp.ctr d r z) i sigma
    (-(2 * (r : Int))) (22 * (r : Int)) (2 * (r : Int))

omit [NeZero d] in
@[simp] theorem outerSlabBox_sites (r : Nat) (z : Site 2) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) :
    (outerSlabBox (d := d) r z i sigma).sites = outerSlab (d := d) r z i sigma :=
  dboxBox_sites _ _ hsigma

omit [NeZero d] in
theorem outerSlabBox_ordered (r : Nat) (z : Site 2) (i : Fin d) (sigma : Int) :
    (outerSlabBox (d := d) r z i sigma).Ordered :=
  dboxBox_ordered _ _ (by omega) (by omega)

omit [NeZero d] in
/-- The corridor's last cross-section box is the literal cube of radius
`sourceHalfWidth d Q.scale Q.radius`. -/
theorem boxes_last_eq_cube {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat}
    (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0 epsilon c rmin) :
    Q.boxes (Fin.last d) = CorrMove.cube c (sourceHalfWidth d Q.scale Q.radius) := by
  show ExactQuarterPlanExtraction.crossBox c Q.scale Q.radius (Fin.last d).val = _
  rw [Fin.val_last]
  exact CorrMove.Bx_dim c _ _ _

/-! ## The slab is inside the narrow domain and the fresh region -/

/-- `D'` is inside the common narrow domain: the smallest admissible `active_subset_narrow`. -/
theorem outerSlab_subset_narrowDom (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r) (ht : 5 * r ≤ t)
    (h : MacroExp.Tr d) {w z : Site 2} (hwz : w ≠ z) (y : Site 2) {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) :
    outerSlab (d := d) r z i sigma ⊆
      ExactMacroGeometry.narrowDom r t h w z y i sigma :=
  CorrMove.dbox_subset_narrowDom hd hr ht h hwz hsigma

/-- `D'` is inside `Q z ∪ E z y`: the smallest admissible `active_subset_fresh_region`. -/
theorem outerSlab_subset_Q_union_E {r t : Nat} (hr : 0 < r) (ht : 5 * r ≤ t)
    {z y : Site 2} {i : Fin d} {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    outerSlab (d := d) r z i sigma ⊆ MacroExp.Q d r t z ∪ MacroExp.E d r t z y :=
  CorrMove.dbox_subset_Q_union_E hr ht hsigma hemb

/-! ## The aspect-`88` long-target relation, stated monotonically -/

omit [NeZero d] in
/-- `CorrMove.LongTarget` is monotone in its allowed set and in its target. -/
theorem longTarget_mono {R : Int} {i : Fin d} {sigma : Int}
    {Sub Sub' Bset T T' : Finset (Site d)}
    (hS : Sub ⊆ Sub') (hT : T ⊆ T')
    (hlong : CorrMove.LongTarget R i sigma Sub Bset T) :
    CorrMove.LongTarget R i sigma Sub' Bset T' := by
  intro v hv
  obtain ⟨l, hl, hbox, hface⟩ := hlong v hv
  exact ⟨l, hl, hbox.trans hS, hface.trans hT⟩

omit [NeZero d] in
/-- The radius-`2r` cube at `c_y` -- the set the aspect-`88` move actually lands in -- is inside
the reservation core `CoreRes.target r y`.  This makes the reservation core an admissible outer
target under either the radius-`2r` or the radius-`3r` convention for `CoreRes.target`. -/
theorem cube_two_subset_coreTarget (r : Nat) (y : Site 2) :
    CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ⊆ CoreRes.target (d := d) r y := by
  rw [CoreRes.target]
  refine CorrMove.ibox_mono fun _ => ?_
  have : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
  omega

/-- **The slab `D'` can no longer be the active set of a well-formed outer plan.**  With
`CoreRes.target` the radius-`3 r` cube, the outer target reaches signed longitudinal coordinate
`23 r`, while `D'` stops at `22 r`.  Since `T1` of `ExactTargetPlan.Plan.WellFormed` demands
`target ⊆ active`, every admissible outer active set is strictly larger than `D'`.  This is why
`outerStage` takes the active set as a parameter instead of fixing it to `D'`. -/
theorem not_coreTarget_subset_outerSlab {r : Nat} (hr : 0 < r) {z y : Site 2}
    {i : Fin d} {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    ¬ (CoreRes.target (d := d) r y ⊆ outerSlab (d := d) r z i sigma) := by
  intro hsub
  have hr' : (1 : Int) ≤ (r : Int) := by exact_mod_cast hr
  have hsq : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
  refine absurd
    (hsub (x := MacroExp.ctr d r z + Pi.single i (sigma * (23 * (r : Int)))) ?_) ?_
  · rw [CoreRes.target, CorrMove.ctr_add_dir (d := d) r hemb, CorrMove.mem_cube]
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.single_eq_same]
      have heq : (MacroExp.ctr d r z : Site d) j + sigma * (23 * (r : Int)) -
          ((MacroExp.ctr d r z : Site d) j + sigma * (20 * (r : Int))) =
            sigma * (3 * (r : Int)) := by ring
      rw [heq, CorrMove.abs_signed hsigma,
        abs_of_nonneg (by omega : (0 : Int) ≤ 3 * (r : Int))]
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero, sub_self, abs_zero]
      omega
  · rw [outerSlab, CorrMove.mem_dbox hsigma]
    rintro ⟨⟨-, hhi⟩, -⟩
    simp only [Pi.add_apply, Pi.single_eq_same] at hhi
    have hval : sigma * ((MacroExp.ctr d r z : Site d) i + sigma * (23 * (r : Int)) -
        (MacroExp.ctr d r z : Site d) i) = 23 * (r : Int) := by
      have hs : (MacroExp.ctr d r z : Site d) i + sigma * (23 * (r : Int)) -
          (MacroExp.ctr d r z : Site d) i = sigma * (23 * (r : Int)) := by ring
      rw [hs, ← mul_assoc, hsq, one_mul]
    rw [hval] at hhi
    omega

/-- **`T1` containment `target ⊆ active` at the literal outer boxes.**  The radius-`2 r` cube at
`c_y` occupies signed longitudinal coordinates `[18 r, 22 r]` and transverse coordinates within
`2 r`, so it sits inside the slab `D'`. -/
theorem cube_two_subset_outerSlab {r : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ⊆
      outerSlab (d := d) r z i sigma := by
  intro x hx
  rw [CorrMove.ctr_add_dir (d := d) r hemb, CorrMove.mem_cube] at hx
  rw [outerSlab, CorrMove.mem_dbox hsigma]
  have hr0 : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
  refine ⟨?_, fun j hj => ?_⟩
  · have hxi := hx i
    simp only [Pi.add_apply, Pi.single_eq_same] at hxi
    rw [abs_le] at hxi
    rcases hsigma with rfl | rfl <;> constructor <;> omega
  · have hxj := hx j
    simpa only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero] using hxj

/-- **`T1` containment `sourcePlus ⊆ active` at the literal outer boxes.**  The `89`-inequality is
exactly what makes the inflated corridor source cube fit in the slab `D'`. -/
theorem sourcePlus_subset_outerSlab {r R : Nat} {z : Site 2} {i : Fin d} {sigma : Int}
    {H : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (h89 : 89 * (H + (R : Int)) ≤ 156 * (r : Int)) :
    ((cubeBox (MacroExp.ctr d r z) H).inflate R).sites ⊆
      outerSlab (d := d) r z i sigma := by
  rw [cubeBox_inflate_sites]
  have hr0 : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
  exact CorrMove.cube_subset_dbox _ hsigma (by omega)

/-- **The aspect-`88` long-target relation of the outer stage.**  From the corridor source cube
`c_z + Λ_H` the long move lands inside any target above the radius-`2r` cube at `c_y`, staying in
any allowed set above the slab `D'`.  This is `CorrMove.longTarget_cube` with the neighbouring
centre named by `CorrMove.ctr_add_dir`, then relaxed by `longTarget_mono`. -/
theorem outerLongTarget {r : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    {Sub T : Finset (Site d)} {R H : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hR : 1 ≤ R) (hr : 44 ≤ (r : Int))
    (h89 : 89 * (H + R) ≤ 156 * (r : Int))
    (hRr : 88 * R + 88 ≤ 20 * (r : Int) - (H + R))
    (hSub : outerSlab (d := d) r z i sigma ⊆ Sub)
    (hT : CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ⊆ T) :
    CorrMove.LongTarget R i sigma Sub (CorrMove.cube (MacroExp.ctr d r z) H) T := by
  have hbase := CorrMove.longTarget_cube (MacroExp.ctr d r z) i sigma hsigma R H (r : Int)
    hR hr h89 hRr
  rw [CorrMove.ctr_add_dir (d := d) r hemb] at hT
  exact longTarget_mono hSub hT hbase

/-! ## The numerical side conditions are satisfiable, not vacuous

The two aspect-`88` integer inequalities relate the corridor source half-width `H`, the plan
radius `R` and the macro scale `r`.  Both are *consequences* of the quarter family's own
`separation` field once the outer radius is small compared to `r`, so the constructors below are
never applied to an empty hypothesis set. -/

omit [NeZero d] in
theorem two_mul_hw_le (s : Nat) : 2 * CorrMove.hw s ≤ 3 * s + 1 := by
  have h : (s + 1) / 2 * 2 ≤ s + 1 := Nat.div_mul_le_self (s + 1) 2
  unfold CorrMove.hw
  omega

omit [NeZero d] in
/-- **The aspect-`88` inequalities follow from the quarter family's separation.**  If the quarter
family's scale is the macro scale `r` and the outer radius satisfies `200 (R+1) ≤ r`, both
numerical hypotheses of `outerStage` hold. -/
theorem numeric_side_conditions {r R radius : Nat}
    (hr : 44 ≤ r)
    (hsep : 100 * (d + 1) * (radius + 1) < r)
    (hRsmall : 200 * (R + 1) ≤ r) :
    89 * (sourceHalfWidth d r radius + (R : Int)) ≤ 156 * (r : Int) ∧
      88 * (R : Int) + 88 ≤
        20 * (r : Int) - (sourceHalfWidth d r radius + (R : Int)) := by
  have hhw : 2 * CorrMove.hw r ≤ 3 * r + 1 := two_mul_hw_le r
  have hdr : 100 * (d * radius) < r := by
    have hle : d * radius ≤ (d + 1) * (radius + 1) :=
      Nat.mul_le_mul (Nat.le_succ d) (Nat.le_succ radius)
    calc 100 * (d * radius) ≤ 100 * ((d + 1) * (radius + 1)) :=
          Nat.mul_le_mul_left 100 hle
      _ < r := by rw [← Nat.mul_assoc]; exact hsep
  unfold sourceHalfWidth
  have hcast : ((d : Int)) * ((radius : Int)) = ((d * radius : Nat) : Int) := by push_cast; ring
  rw [hcast]
  constructor
  · zify at hhw hdr hRsmall hr
    omega
  · zify at hhw hdr hRsmall hr
    omega

omit [NeZero d] in
/-- A completely explicit witness: `d = 2`, `r = 1000`, `scale = 1000`, `radius = 1`, `R = 1`
satisfies the quarter separation and both aspect-`88` inequalities.  This rules out the
possibility that `numeric_side_conditions` has an unsatisfiable hypothesis set. -/
theorem numeric_side_conditions_nonvacuous :
    100 * (2 + 1) * (1 + 1) < 1000 ∧ 200 * (1 + 1) ≤ 1000 ∧ (44 : Nat) ≤ 1000 ∧
      89 * (sourceHalfWidth 2 1000 1 + (1 : Int)) ≤ 156 * (1000 : Int) ∧
      88 * (1 : Int) + 88 ≤ 20 * (1000 : Int) - (sourceHalfWidth 2 1000 1 + (1 : Int)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · unfold sourceHalfWidth CorrMove.hw
      norm_num

/-! ## The parametric outer-stage constructor -/

/-- **The parametric outer stage.**  Every hypothesis is either a literal equation about the
supplied exact target plan, a one-sided containment of its active set and target, an integer
inequality between the frozen numerical parameters, or a standing macro-geometry side condition.
The three geometry fields of `OuterStage` are proved, not assumed. -/
def outerStage
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t R : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    {C : ExactTargetPlan.Plan d}
    (hr : 44 ≤ r) (hR : 1 ≤ R)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (h89 : 89 * (sourceHalfWidth d Q.scale Q.radius + (R : Int)) ≤ 156 * (r : Int))
    (hRr : 88 * (R : Int) + 88 ≤
      20 * (r : Int) - (sourceHalfWidth d Q.scale Q.radius + (R : Int)))
    (hscale : Q.scale = r)
    (heta : ∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc)
    (hwf : C.WellFormed)
    (hsource : C.source = Q.boxes (Fin.last d))
    (hslab : outerSlab (d := d) r z i sigma ⊆ C.active)
    (hnarrow : C.active ⊆ ExactMacroGeometry.narrowDom r t h w z y i sigma)
    (hfresh : C.active ⊆ MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (htarget : C.target = CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)))
    (hradius : C.radius = R)
    (hdelta : C.delta = eta (Fin.last d))
    (hepsilon : C.epsilon = rho / 16) :
    ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho :=
  have hcube : C.source = CorrMove.cube (MacroExp.ctr d r z)
      (sourceHalfWidth d Q.scale Q.radius) := by
    rw [hsource, boxes_last_eq_cube]
  have hTsub : CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ⊆ C.target := by
    rw [htarget]
  have hlong : CorrMove.LongTarget (C.radius : Int) i sigma C.active C.source C.target := by
    rw [hcube, hradius]
    exact outerLongTarget hsigma hemb (by exact_mod_cast hR) (by exact_mod_cast hr)
      h89 hRr hslab hTsub
  { scale_eq := hscale
    eta_step := heta
    plan := C
    wellFormed := hwf
    source_eq := hsource
    target_eq := htarget
    longTarget := hlong
    delta_eq := hdelta
    epsilon_eq := hepsilon
    active_subset_narrow := hnarrow
    active_subset_fresh_region := hfresh }

/-! ## Exported `WellFormed` and `ValidAt` facts -/

/-- Every stage of the assembled corridor is one of the `d` quarter plans or the supplied outer
plan. -/
theorem corridor_stage_cases
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho)
    (u : Fin (d + 1)) :
    A.corridor.stage u = A.plan ∨ ∃ a : Fin d, A.corridor.stage u = Q.quarter a := by
  refine Fin.lastCases ?_ (fun a => ?_) u
  · exact Or.inl (by
      rw [A.corridor_stage, ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_last])
  · exact Or.inr ⟨a, by
      rw [A.corridor_stage, ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_castSucc]⟩

/-- **`WellFormed` export.**  The corridor built from a quarter family and any outer stage is a
well-formed exact corridor plan. -/
theorem corridor_wellFormed
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho)
    (hd : 2 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hwz : w ≠ z)
    (hsigma : sigma = 1 ∨ sigma = -1) :
    A.corridor.WellFormed :=
  A.corridor_wellFormed hd hr ht hwz hsigma

/-- **`ValidAt` export at a general parameter.**  Corridor validity is exactly the conjunction of
the finite leaf checks of the outer plan and of the `d` quarter plans.  No geometry is used. -/
theorem corridor_validAt
    {p0 q : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho)
    (hplan : A.plan.ValidAt q)
    (hquarter : ∀ a : Fin d, (Q.quarter a).ValidAt q) :
    A.corridor.ValidAt q := by
  intro u
  rcases corridor_stage_cases A u with hu | ⟨a, hu⟩
  · rw [hu]; exact hplan
  · rw [hu]; exact hquarter a

/-- **`ValidAt` export at the extraction parameter.**  The quarter plans are valid at `p0` by
construction, so only the outer plan carries a probabilistic obligation. -/
theorem corridor_validAt_p0
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho)
    (hplan : A.plan.ValidAt p0) :
    A.corridor.ValidAt p0 :=
  corridor_validAt A hplan Q.quarter_validAt

/-- **One-shot extraction.**  From the plan equations, the containments and the numerical side
conditions, produce the outer stage together with the two facts the macro assembly needs about
the corridor it generates.  The only probabilistic input is `hvalid : C.ValidAt p0`, a finite
table of cylinder inequalities about `C` alone. -/
theorem exists_outerStage
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t R : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    {C : ExactTargetPlan.Plan d}
    (hd : 2 ≤ d) (hr : 44 ≤ r) (ht : 5 * r ≤ t) (hwz : w ≠ z) (hR : 1 ≤ R)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (h89 : 89 * (sourceHalfWidth d Q.scale Q.radius + (R : Int)) ≤ 156 * (r : Int))
    (hRr : 88 * (R : Int) + 88 ≤
      20 * (r : Int) - (sourceHalfWidth d Q.scale Q.radius + (R : Int)))
    (hscale : Q.scale = r)
    (heta : ∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc)
    (hwf : C.WellFormed) (hvalid : C.ValidAt p0)
    (hsource : C.source = Q.boxes (Fin.last d))
    (hslab : outerSlab (d := d) r z i sigma ⊆ C.active)
    (hnarrow : C.active ⊆ ExactMacroGeometry.narrowDom r t h w z y i sigma)
    (hfresh : C.active ⊆ MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (htarget : C.target = CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)))
    (hradius : C.radius = R)
    (hdelta : C.delta = eta (Fin.last d))
    (hepsilon : C.epsilon = rho / 16) :
    ∃ A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho,
      A.plan = C ∧ A.corridor.WellFormed ∧ A.corridor.ValidAt p0 := by
  refine ⟨outerStage (t := t) (h := h) (w := w) (y := y) (rho := rho)
    hr hR hsigma hemb h89 hRr hscale heta hwf hsource hslab hnarrow hfresh htarget hradius
    hdelta hepsilon, rfl, ?_, ?_⟩
  · exact corridor_wellFormed _ hd (by omega) ht hwz hsigma
  · exact corridor_validAt_p0 _ hvalid

/-- **Separation-driven extraction.**  The two aspect-`88` integer inequalities are replaced by
the single natural-number condition `200 (R+1) ≤ r`; they are then derived from the quarter
family's own `separation` field. -/
theorem exists_outerStage_of_separation
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t R : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    {C : ExactTargetPlan.Plan d}
    (hd : 2 ≤ d) (hr : 44 ≤ r) (ht : 5 * r ≤ t) (hwz : w ≠ z) (hR : 1 ≤ R)
    (hRsmall : 200 * (R + 1) ≤ r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hscale : Q.scale = r)
    (heta : ∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc)
    (hwf : C.WellFormed) (hvalid : C.ValidAt p0)
    (hsource : C.source = Q.boxes (Fin.last d))
    (hslab : outerSlab (d := d) r z i sigma ⊆ C.active)
    (hnarrow : C.active ⊆ ExactMacroGeometry.narrowDom r t h w z y i sigma)
    (hfresh : C.active ⊆ MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (htarget : C.target = CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)))
    (hradius : C.radius = R)
    (hdelta : C.delta = eta (Fin.last d))
    (hepsilon : C.epsilon = rho / 16) :
    ∃ A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho,
      A.plan = C ∧ A.corridor.WellFormed ∧ A.corridor.ValidAt p0 := by
  have hsep : 100 * (d + 1) * (Q.radius + 1) < r := by
    have hs := Q.separation
    rwa [hscale] at hs
  obtain ⟨h89, hRr⟩ :=
    numeric_side_conditions (d := d) (R := R) (radius := Q.radius) hr hsep hRsmall
  have hEq : sourceHalfWidth d Q.scale Q.radius = sourceHalfWidth d r Q.radius := by
    rw [hscale]
  have h89' : 89 * (sourceHalfWidth d Q.scale Q.radius + (R : Int)) ≤ 156 * (r : Int) := by
    rw [hEq]; exact h89
  have hRr' : 88 * (R : Int) + 88 ≤
      20 * (r : Int) - (sourceHalfWidth d Q.scale Q.radius + (R : Int)) := by
    rw [hEq]; exact hRr
  exact exists_outerStage (t := t) (h := h) (w := w) (y := y) (rho := rho)
    hd hr ht hwz hR hsigma hemb h89' hRr' hscale heta hwf hvalid hsource hslab hnarrow hfresh
    htarget hradius hdelta hepsilon

/-! ## The aspect-`88` rank-one plan of `KN.ExactLongBoxHitBridge` -/

open ExactLongBoxHitBridge.RankOne in
/-- Place the bridge's rank-one plan on the outer boxes.  `Dbox` is any integer box above the
slab `D'` and `T` any target above the radius-`2 r` cube at `c_y` that fits inside `Dbox`; both
are supplied by the caller, so the construction is independent of the current radius convention
for `CoreRes.target`. -/
def outerInstantiation
    {p0 : unitInterval} {alpha : Real} {R : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) 88)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha (sourceRadius F))
    {r : Nat} {z y : Site 2} {i : Fin d} {sigma : Int} {H : Int}
    (Dbox : ExactTargetPlan.IntBox d) (T : Finset (Site d))
    (hH : 0 ≤ H) (hr : 44 ≤ r) (hR : 1 ≤ R)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (h89 : 89 * (H + (R : Int)) ≤ 156 * (r : Int))
    (hRr : 88 * (R : Int) + 88 ≤ 20 * (r : Int) - (H + (R : Int)))
    (hDord : Dbox.Ordered)
    (hslab : outerSlab (d := d) r z i sigma ⊆ Dbox.sites)
    (hTne : T.Nonempty) (hTactive : T ⊆ Dbox.sites)
    (hTsup : CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ⊆ T) :
    Instantiation F N R i sigma where
  sourceBox := cubeBox (MacroExp.ctr d r z) H
  activeBox := Dbox
  target := T
  source_ordered := cubeBox_ordered _ hH
  active_ordered := hDord
  target_nonempty := hTne
  target_subset_active := hTactive
  longTarget := by
    show CorrMove.LongTarget (R : Int) i sigma Dbox.sites
      (cubeBox (MacroExp.ctr d r z) H).sites T
    rw [cubeBox_sites]
    exact outerLongTarget hsigma hemb (by exact_mod_cast hR) (by exact_mod_cast hr)
      h89 hRr hslab hTsup

/-- The literal specification of the exact target plan the outer stage consumes. -/
structure OuterLongPlanSpec (p0 : unitInterval) (r R : Nat) (z : Site 2)
    (i : Fin d) (sigma : Int) (H : Int) (rho : Real)
    (Dbox : ExactTargetPlan.IntBox d) (T : Finset (Site d))
    (C : ExactTargetPlan.Plan d) : Prop where
  wellFormed : C.WellFormed
  validAt : C.ValidAt p0
  sourceBox_eq : C.sourceBox = cubeBox (MacroExp.ctr d r z) H
  activeBox_eq : C.activeBox = Dbox
  target_eq : C.target = T
  radius_eq : C.radius = R
  epsilon_eq : C.epsilon = rho / 16

/-- **The aspect-`88` outer plan from supercriticality.**  `0 < thetaSite d p₀` produces a finite
radius threshold `R0` such that, for every macro scale and every outer box pair satisfying the
frozen numerical inequalities, an exact target plan with exactly the outer boxes exists, is
well formed, and is valid at `p₀`.  All leaves are honest cylinder bounds coming from the exact
long-box chain; there is no designated open site and no theorem-valued certificate. -/
theorem exists_outerLongPlan_of_thetaSite_pos
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) {rho : Real} (hrho0 : 0 < rho) (hrho1 : rho ≤ 16) :
    ∃ R0 : Nat, 1 ≤ R0 ∧
      ∀ (r R : Nat) (z y : Site 2) (i : Fin d) (sigma : Int) (H : Int)
        (Dbox : ExactTargetPlan.IntBox d) (T : Finset (Site d)),
        R0 ≤ R → 0 ≤ H → 44 ≤ r →
        (sigma = 1 ∨ sigma = -1) →
        ((MacroExp.emb (y - z) : Site d) = Pi.single i sigma) →
        89 * (H + (R : Int)) ≤ 156 * (r : Int) →
        88 * (R : Int) + 88 ≤ 20 * (r : Int) - (H + (R : Int)) →
        Dbox.Ordered →
        outerSlab (d := d) r z i sigma ⊆ Dbox.sites →
        T.Nonempty → T ⊆ Dbox.sites →
        CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ⊆ T →
        ∃ C : ExactTargetPlan.Plan d,
          OuterLongPlanSpec p0 r R z i sigma H rho Dbox T C := by
  have ha0 : 0 < rho / 16 := by linarith
  have ha1 : rho / 16 ≤ 1 := by linarith
  have hb0 : 0 < etaOf (rho / 16) := by
    unfold etaOf deltaOf deltaCOf
    positivity
  have hb1 : etaOf (rho / 16) ≤ 1 := by
    unfold etaOf deltaOf deltaCOf
    have hd0 : 0 ≤ (rho / 16) ^ 2 / 64 := by positivity
    have hd1 : (rho / 16) ^ 2 / 64 ≤ 1 := by nlinarith [sq_nonneg (rho / 16)]
    have hdc0 : 0 ≤ (rho / 16) / 4 := by positivity
    have hdc1 : (rho / 16) / 4 ≤ 1 := by linarith
    have hd2 : ((rho / 16) ^ 2 / 64) ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1
    nlinarith [mul_le_mul hd2 hdc1 hdc0 (by positivity : (0 : Real) ≤ 1)]
  obtain ⟨F⟩ := ExactLongBoxVariablePlan.exists_schemeFamily_of_thetaSite_pos
    p0 hp0 hp1 htheta (etaOf (rho / 16)) hb0 hb1 88 (by omega)
  have hm : 0 < ExactLongBoxHitBridge.RankOne.sourceRadius F := by
    unfold ExactLongBoxHitBridge.RankOne.sourceRadius
    omega
  obtain ⟨N⟩ := ExactTargetSchemeNumbers.exists_numbers (d := d) p0 hp0 hp1 (rho / 16) ha0 ha1
    (ExactLongBoxHitBridge.RankOne.sourceRadius F) hm
  refine ⟨max 1 (max N.R0 (8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F)),
    le_max_left _ _, ?_⟩
  intro r R z y i sigma H Dbox T hR0 hH hr hsigma hemb h89 hRr hDord hslab hTne hTactive hTsup
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR0
  have hRN : N.R0 ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR0
  have hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR0
  refine ⟨ExactLongBoxHitBridge.RankOne.buildPlan hp0 hp1 ha0 ha1 (by omega : 1 ≤ 88) F N
    i sigma hsigma hlarge
    (outerInstantiation (y := y) F N Dbox T hH hr hR1 hsigma hemb h89 hRr hDord hslab
      hTne hTactive hTsup), ?_⟩
  exact
    { wellFormed := ExactLongBoxHitBridge.RankOne.buildPlan_wellFormed hp0 hp1 ha0 ha1
        (by omega : 1 ≤ 88) F N i sigma hsigma hRN hlarge _
      validAt := ExactLongBoxHitBridge.RankOne.buildPlan_validAt hp0 hp1 ha0 ha1
        (by omega : 1 ≤ 88) F N i sigma hsigma hRN hlarge _
      sourceBox_eq := rfl
      activeBox_eq := rfl
      target_eq := rfl
      radius_eq := rfl
      epsilon_eq := rfl }

/-! ## The closed extraction: outer stage from `0 < thetaSite d p₀` -/

/-- **Consumption of the bridge plan.**  Given the spec of the outer plan, the outer stage exists
and the corridor it generates is well formed and valid at `p0`.  `hetaLast` pins the last corridor
tolerance to the value forced by `ExactTargetPlan.Plan.delta`. -/
theorem exists_outerStage_of_spec
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t R : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    {C : ExactTargetPlan.Plan d} {Dbox : ExactTargetPlan.IntBox d}
    (hd : 2 ≤ d) (hr : 44 ≤ r) (ht : 5 * r ≤ t) (hwz : w ≠ z) (hR : 1 ≤ R)
    (hRsmall : 200 * (R + 1) ≤ r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hscale : Q.scale = r)
    (heta : ∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc)
    (hetaLast : eta (Fin.last d) = deltaOf (rho / 16))
    (hslab : outerSlab (d := d) r z i sigma ⊆ Dbox.sites)
    (hnarrow : Dbox.sites ⊆ ExactMacroGeometry.narrowDom r t h w z y i sigma)
    (hfresh : Dbox.sites ⊆ MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (hspec : OuterLongPlanSpec p0 r R z i sigma
      (sourceHalfWidth d Q.scale Q.radius) rho Dbox
        (CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int))) C) :
    ∃ A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho,
      A.plan = C ∧ A.corridor.WellFormed ∧ A.corridor.ValidAt p0 := by
  have hsource : C.source = Q.boxes (Fin.last d) := by
    rw [ExactTargetPlan.Plan.source, hspec.sourceBox_eq, cubeBox_sites, boxes_last_eq_cube]
  have hactive : C.active = Dbox.sites := by
    rw [ExactTargetPlan.Plan.active, hspec.activeBox_eq]
  have hdelta : C.delta = eta (Fin.last d) := by
    rw [hetaLast, ExactTargetPlan.Plan.delta, hspec.epsilon_eq]
    rfl
  exact exists_outerStage_of_separation (t := t) (h := h) (w := w) (y := y) (rho := rho)
    hd hr ht hwz hR hRsmall hsigma hemb hscale heta hspec.wellFormed hspec.validAt
    hsource (by rw [hactive]; exact hslab) (by rw [hactive]; exact hnarrow)
    (by rw [hactive]; exact hfresh) hspec.target_eq hspec.radius_eq hdelta hspec.epsilon_eq

/-- **The closed outer-stage extraction.**  From `0 < thetaSite d p₀` alone, together with the
frozen numerical inputs and the deterministic macro geometry of the chosen active box, the outer
stage of the exact macro corridor exists and its corridor is well formed and valid at `p₀`. -/
theorem exists_outerStage_of_thetaSite_pos
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) {rho : Real} (hrho0 : 0 < rho) (hrho1 : rho ≤ 16) :
    ∃ R0 : Nat, 1 ≤ R0 ∧
      ∀ (eta : Fin (d + 1) → Real) (r t R : Nat) (h : ExactMacroGeometry.Tr d)
        (w z y : Site 2) (i : Fin d) (sigma : Int)
        (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
          (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r)
        (Dbox : ExactTargetPlan.IntBox d),
        2 ≤ d → 44 ≤ r → 5 * r ≤ t → w ≠ z → R0 ≤ R → 200 * (R + 1) ≤ r →
        (sigma = 1 ∨ sigma = -1) →
        ((MacroExp.emb (y - z) : Site d) = Pi.single i sigma) →
        Q.scale = r →
        (∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc) →
        eta (Fin.last d) = deltaOf (rho / 16) →
        Dbox.Ordered →
        outerSlab (d := d) r z i sigma ⊆ Dbox.sites →
        Dbox.sites ⊆ ExactMacroGeometry.narrowDom r t h w z y i sigma →
        Dbox.sites ⊆ MacroExp.Q d r t z ∪ MacroExp.E d r t z y →
        CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ⊆ Dbox.sites →
        ∃ A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho,
          A.corridor.WellFormed ∧ A.corridor.ValidAt p0 := by
  obtain ⟨R0, hR0pos, hplan⟩ :=
    exists_outerLongPlan_of_thetaSite_pos (d := d) hp0 hp1 htheta hrho0 hrho1
  refine ⟨R0, hR0pos, ?_⟩
  intro eta r t R h w z y i sigma Q Dbox hd hr ht hwz hR0 hRsmall hsigma hemb hscale heta
    hetaLast hDord hslab hnarrow hfresh hTactive
  have hR1 : 1 ≤ R := le_trans hR0pos hR0
  have hsep : 100 * (d + 1) * (Q.radius + 1) < r := by
    have hs := Q.separation
    rwa [hscale] at hs
  obtain ⟨h89, hRr⟩ :=
    numeric_side_conditions (d := d) (R := R) (radius := Q.radius) hr hsep hRsmall
  have hEq : sourceHalfWidth d Q.scale Q.radius = sourceHalfWidth d r Q.radius := by
    rw [hscale]
  have hTne : (CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int))).Nonempty := by
    refine ⟨MacroExp.ctr d r y, ?_⟩
    rw [CorrMove.mem_cube]
    intro j
    have h0 : (MacroExp.ctr d r y : Site d) j - (MacroExp.ctr d r y : Site d) j = 0 := by ring
    rw [h0, abs_zero]
    have : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
    omega
  obtain ⟨C, hspec⟩ := hplan r R z y i sigma (sourceHalfWidth d Q.scale Q.radius) Dbox
    (CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int))) hR0
    (by rw [hEq]; unfold sourceHalfWidth; positivity) hr hsigma hemb
    (by rw [hEq]; exact h89) (by rw [hEq]; exact hRr)
    hDord hslab hTne hTactive Finset.Subset.rfl
  obtain ⟨A, _, hwfC, hvalidC⟩ :=
    exists_outerStage_of_spec (t := t) (h := h) (w := w) (rho := rho) (Dbox := Dbox)
      hd hr ht hwz hR1 hRsmall hsigma hemb hscale heta hetaLast hslab hnarrow hfresh hspec
  exact ⟨A, hwfC, hvalidC⟩

/-- **The closed outer-stage extraction on the slab `D'`.**  Specialising the active box to the
long slab `D'` of (7.7) discharges every box obligation of `exists_outerStage_of_thetaSite_pos`:
`D'` is ordered, contains itself, is inside both the narrow domain and the fresh region, and
contains the radius-`2 r` target.  Nothing is left for the caller beyond `0 < thetaSite d p₀`, the
frozen numerics, and the standing macro side conditions. -/
theorem exists_outerStage_slab_of_thetaSite_pos
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) {rho : Real} (hrho0 : 0 < rho) (hrho1 : rho ≤ 16) :
    ∃ R0 : Nat, 1 ≤ R0 ∧
      ∀ (eta : Fin (d + 1) → Real) (r t R : Nat) (h : ExactMacroGeometry.Tr d)
        (w z y : Site 2) (i : Fin d) (sigma : Int)
        (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
          (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r),
        2 ≤ d → 44 ≤ r → 5 * r ≤ t → w ≠ z → R0 ≤ R → 200 * (R + 1) ≤ r →
        (sigma = 1 ∨ sigma = -1) →
        ((MacroExp.emb (y - z) : Site d) = Pi.single i sigma) →
        Q.scale = r →
        (∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc) →
        eta (Fin.last d) = deltaOf (rho / 16) →
        ∃ A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho,
          A.corridor.WellFormed ∧ A.corridor.ValidAt p0 := by
  obtain ⟨R0, hR0pos, hstage⟩ :=
    exists_outerStage_of_thetaSite_pos (d := d) hp0 hp1 htheta hrho0 hrho1
  refine ⟨R0, hR0pos, ?_⟩
  intro eta r t R h w z y i sigma Q hd hr ht hwz hR0 hRsmall hsigma hemb hscale heta hetaLast
  have hbox : (outerSlabBox (d := d) r z i sigma).sites = outerSlab (d := d) r z i sigma :=
    outerSlabBox_sites _ _ _ hsigma
  refine hstage eta r t R h w z y i sigma Q (outerSlabBox (d := d) r z i sigma)
    hd hr ht hwz hR0 hRsmall hsigma hemb hscale heta hetaLast
    (outerSlabBox_ordered _ _ _ _) (by rw [hbox]) ?_ ?_ ?_
  · rw [hbox]
    exact outerSlab_subset_narrowDom hd (by omega) ht h hwz y hsigma
  · rw [hbox]
    exact outerSlab_subset_Q_union_E (by omega) ht hsigma hemb
  · rw [hbox]
    exact cube_two_subset_outerSlab hsigma hemb

/-! ## Nonvacuity of the extracted stage

The outer stage is not a vacuous or impossible object: its plan's source, active set and target
are all nonempty.  These follow from `C.WellFormed` alone. -/

omit [NeZero d] in
theorem source_nonempty
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho) :
    A.plan.source.Nonempty := A.wellFormed.source_nonempty

omit [NeZero d] in
theorem target_nonempty
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho) :
    (CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int))).Nonempty := by
  have hne := A.wellFormed.target_nonempty
  rwa [A.target_eq] at hne

omit [NeZero d] in
theorem active_nonempty
    {p0 : unitInterval} {eta : Fin (d + 1) → Real}
    {r t : Nat} {h : ExactMacroGeometry.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0
      (fun a : Fin d => eta a.succ) (MacroExp.ctr d r z) r}
    (A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho) :
    A.plan.active.Nonempty := A.wellFormed.active_nonempty

#print axioms KNAll.Site.ExactOuterStageExtraction.boxes_last_eq_cube
#print axioms KNAll.Site.ExactOuterStageExtraction.longTarget_mono
#print axioms KNAll.Site.ExactOuterStageExtraction.cube_two_subset_coreTarget
#print axioms KNAll.Site.ExactOuterStageExtraction.not_coreTarget_subset_outerSlab
#print axioms KNAll.Site.ExactOuterStageExtraction.outerLongTarget
#print axioms KNAll.Site.ExactOuterStageExtraction.numeric_side_conditions
#print axioms KNAll.Site.ExactOuterStageExtraction.numeric_side_conditions_nonvacuous
#print axioms KNAll.Site.ExactOuterStageExtraction.outerStage
#print axioms KNAll.Site.ExactOuterStageExtraction.corridor_wellFormed
#print axioms KNAll.Site.ExactOuterStageExtraction.corridor_validAt
#print axioms KNAll.Site.ExactOuterStageExtraction.corridor_validAt_p0
#print axioms KNAll.Site.ExactOuterStageExtraction.exists_outerStage
#print axioms KNAll.Site.ExactOuterStageExtraction.exists_outerStage_of_separation
#print axioms KNAll.Site.ExactOuterStageExtraction.outerInstantiation
#print axioms KNAll.Site.ExactOuterStageExtraction.exists_outerLongPlan_of_thetaSite_pos
#print axioms KNAll.Site.ExactOuterStageExtraction.exists_outerStage_of_spec
#print axioms KNAll.Site.ExactOuterStageExtraction.cube_two_subset_outerSlab
#print axioms KNAll.Site.ExactOuterStageExtraction.sourcePlus_subset_outerSlab
#print axioms KNAll.Site.ExactOuterStageExtraction.exists_outerStage_of_thetaSite_pos
#print axioms KNAll.Site.ExactOuterStageExtraction.exists_outerStage_slab_of_thetaSite_pos
#print axioms KNAll.Site.ExactOuterStageExtraction.target_nonempty

end KNAll.Site.ExactOuterStageExtraction

end
