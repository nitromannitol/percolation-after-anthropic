import Hypergraph.ExactStoppedG2Geometry
import Hypergraph.ExactLongBoxHitBridge

/-!
# The translated aspect-`2K` stopped plan

`ExactLongBoxVariablePlan` and `LongBoxVariable` describe the aspect-`A` chain based at the
origin.  A stopped child, however, must run the aspect-`2K` long move from a
configuration-dependent source-plus site `v` on the corrected stub face `F^{j+1}_{z,y}`.  This
module is the translation seam.

The translation itself is already available: `ExactLongBoxHitBridge.RankOne` builds one
transparent exact target plan out of *arbitrary* source and active `IntBox`es, and its
`T4` table is filled by `VariableBridge.translated_hit`, the translate of the centered
long-box cylinder to every point of `sourceBox^{+R}`.  What is missing is exactly the finite
geometry that places those boxes at the literal (G2) shapes of `ExactStoppedG2`.  So no
extraction is duplicated here: the boxes are translated and the existing rank-one constructor is
wrapped.

## Contents

* `Inputs` : the non-geometric data of the rank-one constructor — one extracted aspect-`2K`
  scheme family, its numerical `Numbers`, and an admissible extraction radius.
  `exists_inputs_of_thetaSite_pos` produces it from supercriticality alone; no new probability
  assumption is introduced.
* `coreTarget_subset_Dbox` : the radius-`3r` recursive core sits inside every stopped active box
  `D_j`; the core's rear face is at `17 r` and `D_j` starts no later than `15 r`.
* `instantiation` : the literal (G2) placement — source box `faceIntBox` (`= F^{j+1}`), active
  box `DIntBox` (`= D_j`), target `CoreRes.target r y` (radius `3r`) — whose long-target field is
  `ExactStoppedG2.longTargetAspect_stubFace_core`.
* `plan`, `planFamily` : the resulting exact target plans, with `source`, `active`, `target`,
  `radius`, `epsilon` and `delta` all readable off, plus `WellFormed` and `ValidAt`.
* `stoppedChildren` : the assembled `ExactMacroGeometry.StoppedChildren`, produced by
  `ExactStoppedG2.stoppedChildren` from exactly the equalities above.  Its argument list is the
  one `ExactStoppedChildrenExtraction.assemble` consumes.
* `exists_stoppedChildren_of_thetaSite_pos` : the closing form.  A single extraction radius `R`
  is chosen first; every macro scale with `2 R ≤ s` and `r = K s` then carries the full stopped
  family.

Everything below is deterministic finite geometry plus the two recorded tolerance comparisons.
No probability hypothesis, theorem-valued field, or designated-open-site condition occurs.
-/

noncomputable section

namespace KNAll.Site.ExactLongBoxTranslatedPlan

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-! ## §1.  The extracted, non-geometric inputs -/

/-- The data of the transparent rank-one constructor that is *not* deterministic geometry: an
aspect-`2K` scheme family at the internal tolerance `etaOf alpha`, the numerical target-scheme
data at the output tolerance `alpha`, and one extraction radius admissible for both. -/
structure Inputs (d : Nat) [NeZero d] (p0 : unitInterval) (alpha : Real) (K : Nat) where
  family : ExactLongBoxVariablePlan.SchemeFamily d p0
    (ExactTargetArithmetic.etaOf alpha) (2 * K)
  numbers : ExactTargetSchemeNumbers.Numbers d p0 alpha
    (ExactLongBoxHitBridge.RankOne.sourceRadius family)
  radius : Nat
  radius_ge : numbers.R0 ≤ radius
  radius_large : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold family ≤ radius

namespace Inputs

variable {p0 : unitInterval} {alpha : Real} {K : Nat}

theorem radius_pos (In : Inputs d p0 alpha K) : 0 < In.radius := by
  have hlarge := In.radius_large
  have h8 : 8 ≤ ExactLongBoxHitBridge.RankOne.scaleThreshold In.family := by
    simp only [ExactLongBoxHitBridge.RankOne.scaleThreshold]
    omega
  omega

end Inputs

/-- The internal chain tolerance is a legitimate tolerance. -/
theorem etaOf_pos {alpha : Real} (ha0 : 0 < alpha) :
    0 < ExactTargetArithmetic.etaOf alpha := by
  unfold ExactTargetArithmetic.etaOf ExactTargetArithmetic.deltaOf
    ExactTargetArithmetic.deltaCOf
  positivity

theorem etaOf_le_one {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) :
    ExactTargetArithmetic.etaOf alpha ≤ 1 := by
  unfold ExactTargetArithmetic.etaOf ExactTargetArithmetic.deltaOf
    ExactTargetArithmetic.deltaCOf
  have hd0 : 0 ≤ alpha ^ 2 / 64 := by positivity
  have hd1 : alpha ^ 2 / 64 ≤ 1 := by nlinarith [sq_nonneg alpha]
  have hdc0 : 0 ≤ alpha / 4 := by positivity
  have hdc1 : alpha / 4 ≤ 1 := by linarith
  have hd2 : (alpha ^ 2 / 64) ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1
  nlinarith [mul_le_mul hd2 hdc1 hdc0 (by positivity : (0 : Real) ≤ 1)]

/-- **All non-geometric inputs come from supercriticality.**  The scheme family is the one
already extracted by `ExactLongBoxVariablePlan`, the numbers are the purely arithmetic choices of
`ExactTargetSchemeNumbers`, and the radius is the maximum of the two recorded thresholds.  No new
probability assumption is made. -/
theorem exists_inputs_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {K : Nat} (hK : 1 ≤ K) :
    Nonempty (Inputs d p0 alpha K) := by
  obtain ⟨F⟩ := ExactLongBoxVariablePlan.exists_stoppedSchemeFamily_of_thetaSite_pos
    (d := d) p0 hp0 hp1 htheta (ExactTargetArithmetic.etaOf alpha)
    (etaOf_pos ha0) (etaOf_le_one ha0 ha1) K hK
  obtain ⟨N⟩ := ExactTargetSchemeNumbers.exists_numbers (d := d) p0 hp0 hp1 alpha ha0 ha1
    (ExactLongBoxHitBridge.RankOne.sourceRadius F)
    (by simp only [ExactLongBoxHitBridge.RankOne.sourceRadius]; omega)
  exact ⟨{
    family := F
    numbers := N
    radius := max N.R0 (8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F)
    radius_ge := le_max_left _ _
    radius_large := le_max_right _ _ }⟩

/-! ## §2.  The translated boxes -/

/-- **The radius-`3r` recursive core lies in every stopped active box.**  Axially the core
occupies `[17 r, 23 r]`, while `D_j` is `[5 r + 10 s j + 1, 25 r]` and `5 r + 10 s j ≤ 15 r - 10 s`;
transversally the core has half-width `3 r` and `D_j` has half-width `5 r`. -/
theorem coreTarget_subset_Dbox {K r s j : Nat} (hs : 0 < s) (hr : r = K * s) (hj : j < K)
    {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    CoreRes.target (d := d) r y ⊆
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s j := by
  have hsigma2 : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
  have hrz : (0 : Int) ≤ (r : Int) := by positivity
  have hcy : (MacroExp.ctr d r y : Site d) =
      MacroExp.ctr d r z + Pi.single i (sigma * (20 * (r : Int))) :=
    CorrMove.ctr_add_dir r hemb
  have hax := ExactStoppedG2.axial_add_five_le (K := K) hr hj
  have hsplit := ExactStoppedG2.tail_split s j
  have hloNat : 5 * r + 10 * s * j + 1 ≤ 17 * r := by
    unfold ExactStoppedG2.axial at hax
    omega
  have hlo : ((5 * r + 10 * s * j : Nat) : Int) + 1 ≤ 17 * (r : Int) := by
    exact_mod_cast hloNat
  intro x hx
  have hcube : ∀ k, |x k - MacroExp.ctr d r y k| ≤ 3 * (r : Int) :=
    CorrMove.mem_cube.1 (by simpa only [CoreRes.target] using hx)
  have hi := hcube i
  rw [hcy] at hi
  simp only [Pi.add_apply, Pi.single_eq_same] at hi
  have heq : sigma * (x i - MacroExp.ctr d r z i) - 20 * (r : Int)
      = sigma * (x i - (MacroExp.ctr d r z i + sigma * (20 * (r : Int)))) := by
    linear_combination (20 * (r : Int)) * hsigma2
  have habs : |sigma * (x i - MacroExp.ctr d r z i) - 20 * (r : Int)| ≤ 3 * (r : Int) := by
    rw [heq, CorrMove.abs_signed hsigma]
    exact hi
  rw [abs_le] at habs
  rw [ExactStoppedG2.mem_Dbox hsigma]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Stopped.lam]
    linarith [habs.1]
  · simp only [Stopped.lam]
    push_cast
    linarith [habs.2]
  · intro k hk
    have hk2 := hcube k
    rw [hcy] at hk2
    simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero] at hk2
    refine hk2.trans ?_
    push_cast
    linarith

omit [NeZero d] in
/-- The `Int`-aspect long-target relation of `ExactStoppedG2` is the `Nat`-aspect relation the
rank-one constructor consumes. -/
theorem rankOne_longTargetAspect {K R : Nat} {i : Fin d} {sigma : Int}
    {active source target : Finset (Site d)}
    (h : ExactStoppedG2.LongTargetAspect (2 * (K : Int)) (R : Int) i sigma
      active source target) :
    ExactLongBoxHitBridge.RankOne.LongTargetAspect (2 * K) R i sigma
      active source target := by
  have hcast : ((2 * K : Nat) : Int) = 2 * (K : Int) := by push_cast; ring
  intro v hv
  obtain ⟨l, hl, hbox, hface⟩ := h v hv
  refine ⟨l, hl, ?_, ?_⟩
  · simpa only [hcast] using hbox
  · simpa only [hcast] using hface

/-! ## §3.  The translated instantiation -/

/-- **The literal (G2) placement of the aspect-`2K` long move.**  The source box is the corrected
isotropic stub face `F^{j+1}_{z,y}`, the active box is `D_j`, and the target is the radius-`3r`
recursive core `CoreRes.target r y`.  The long-target field is exactly
`ExactStoppedG2.longTargetAspect_stubFace_core`. -/
def instantiation {p0 : unitInterval} {alpha : Real} {K r s : Nat}
    (In : Inputs d p0 alpha K) (z y : Site 2) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s)
    (hR : 2 * In.radius ≤ s)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (j : Nat) (hj : j < K) :
    ExactLongBoxHitBridge.RankOne.Instantiation In.family In.numbers In.radius i sigma where
  sourceBox :=
    ExactStoppedG2.faceIntBox (MacroExp.ctr d r z) i sigma r (10 * s * (j + 1))
  activeBox := ExactStoppedG2.DIntBox (MacroExp.ctr d r z) i sigma r s j
  target := CoreRes.target (d := d) r y
  source_ordered := ExactStoppedG2.faceIntBox_ordered _ _ _ _ _
  active_ordered := ExactStoppedG2.DIntBox_ordered _ _ hsigma hK hs hr hj
  target_nonempty := by
    simp only [CoreRes.target]
    exact CorrMove.cube_nonempty _ (by positivity)
  target_subset_active := by
    rw [ExactStoppedG2.DIntBox_sites_eq _ _ hsigma]
    exact coreTarget_subset_Dbox hs hr hj hsigma hemb
  longTarget := by
    rw [ExactStoppedG2.DIntBox_sites_eq _ _ hsigma,
      ExactStoppedG2.faceIntBox_sites_eq _ i hsigma r 0 (10 * s * (j + 1))]
    exact rankOne_longTargetAspect
      (ExactStoppedG2.longTargetAspect_stubFace_core (t := 0) hsigma hK hs hr hj hR hemb)

/-! ## §4.  The translated plan -/

/-- **The exact target plan of one stopped child.**  It is the transparent rank-one plan of
`ExactLongBoxHitBridge` at the (G2) placement; the translation of the centered aspect-`2K`
cylinder to each source-plus site is carried out inside that constructor. -/
def plan {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) {K r s : Nat}
    (In : Inputs d p0 alpha K) (z y : Site 2) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s)
    (hR : 2 * In.radius ≤ s)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (j : Nat) (hj : j < K) : ExactTargetPlan.Plan d :=
  ExactLongBoxHitBridge.RankOne.buildPlan hp0 hp1 ha0 ha1 (show 1 ≤ 2 * K by omega)
    In.family In.numbers i sigma hsigma In.radius_large
    (instantiation In z y i hsigma hK hs hr hR hemb j hj)

section PlanFacts

variable {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
  {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) {K r s : Nat}
  (In : Inputs d p0 alpha K) (z y : Site 2) (i : Fin d) {sigma : Int}
  (hsigma : sigma = 1 ∨ sigma = -1) (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s)
  (hR : 2 * In.radius ≤ s)
  (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
  (j : Nat) (hj : j < K)

theorem plan_wellFormed :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).WellFormed :=
  ExactLongBoxHitBridge.RankOne.buildPlan_wellFormed hp0 hp1 ha0 ha1 _ _ _ i sigma hsigma
    In.radius_ge In.radius_large _

theorem plan_validAt :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).ValidAt p0 :=
  ExactLongBoxHitBridge.RankOne.buildPlan_validAt hp0 hp1 ha0 ha1 _ _ _ i sigma hsigma
    In.radius_ge In.radius_large _

/-- The plan's source is literally the corrected isotropic stub face `F^{j+1}_{z,y}`. -/
theorem plan_source (t : Nat) :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)) :=
  ExactStoppedG2.faceIntBox_sites_eq _ i hsigma r t _

/-- The plan's active box is literally `D_j`. -/
theorem plan_active :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s j :=
  ExactStoppedG2.DIntBox_sites_eq _ i hsigma r s j

/-- The plan's target is the radius-`3r` recursive core. -/
theorem plan_target :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).target =
      CoreRes.target (d := d) r y := rfl

theorem plan_p0 :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).p0 = p0 := rfl

theorem plan_radius :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).radius = In.radius := rfl

theorem plan_epsilon :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).epsilon = alpha := rfl

theorem plan_delta :
    (plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb j hj).delta =
      ExactTargetArithmetic.deltaOf alpha := rfl

end PlanFacts

/-! ## §5.  The `K` stopped children -/

section Children

variable {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
  {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) {K r s : Nat}
  (In : Inputs d p0 alpha K) (z y : Site 2) (i : Fin d) {sigma : Int}
  (hsigma : sigma = 1 ∨ sigma = -1) (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s)
  (hR : 2 * In.radius ≤ s)
  (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)

/-- The `K` literal stopped plans, one per level. -/
def planFamily : Fin K → ExactTargetPlan.Plan d := fun a =>
  plan hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt

theorem planFamily_wellFormed (a : Fin K) :
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a).WellFormed :=
  plan_wellFormed hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt

theorem planFamily_validAt (a : Fin K) :
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a).ValidAt p0 :=
  plan_validAt hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt

theorem planFamily_active (a : Fin K) :
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val :=
  plan_active hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt

theorem planFamily_source (t : Nat) (a : Fin K) :
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)) :=
  plan_source hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt t

theorem planFamily_target (a : Fin K) :
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a).target =
      CoreRes.target (d := d) r y :=
  plan_target hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt

theorem planFamily_epsilon (a : Fin K) :
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a).epsilon = alpha :=
  plan_epsilon hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt

theorem planFamily_radius (a : Fin K) :
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a).radius = In.radius :=
  plan_radius hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt

theorem planFamily_delta (a : Fin K) :
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a).delta =
      ExactTargetArithmetic.deltaOf alpha :=
  plan_delta hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a.val a.isLt

/-- **The stopped-child family.**  Every argument is either a deterministic (G2) shape equality
supplied by §4 or one of the two recorded tolerance comparisons; this is exactly the argument
list of `ExactStoppedChildrenExtraction.assemble`. -/
def stoppedChildren {t : Nat} (ht : 5 * r ≤ t)
    {deltaC delta2 : Real}
    (hdelta : delta2 ≤ ExactTargetArithmetic.deltaOf alpha) (heps : alpha ≤ deltaC) :
    ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma deltaC delta2 :=
  ExactStoppedG2.stoppedChildren hsigma
    (by rw [hr]; exact Nat.mul_pos (by omega) hs) ht hemb
    (planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb)
    (planFamily_wellFormed hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb)
    (planFamily_active hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb)
    (planFamily_source hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb t)
    (fun a => by
      rw [planFamily_target hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a])
    (fun a => by
      rw [planFamily_delta hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a]
      exact hdelta)
    (fun a => by
      rw [planFamily_epsilon hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a]
      exact heps)

theorem stoppedChildren_plan {t : Nat} (ht : 5 * r ≤ t)
    {deltaC delta2 : Real}
    (hdelta : delta2 ≤ ExactTargetArithmetic.deltaOf alpha) (heps : alpha ≤ deltaC)
    (a : Fin K) :
    (stoppedChildren hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb
        ht hdelta heps).plan a =
      planFamily hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a := rfl

theorem stoppedChildren_validAt {t : Nat} (ht : 5 * r ≤ t)
    {deltaC delta2 : Real}
    (hdelta : delta2 ≤ ExactTargetArithmetic.deltaOf alpha) (heps : alpha ≤ deltaC)
    (a : Fin K) :
    ((stoppedChildren hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb
        ht hdelta heps).plan a).ValidAt p0 :=
  planFamily_validAt hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a

end Children

/-! ## §6.  The closing form -/

/-- **The stopped children exist at every admissible macro scale.**  One extraction radius `R` is
fixed first; every macro scale with `2 R ≤ s` and `r = K s` then carries the whole aspect-`2K`
stopped family, with source `F^{j+1}`, active box `D_j` and target the radius-`3r` core. -/
theorem exists_stoppedChildren_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {K : Nat} (hK : 20 ≤ K)
    {deltaC delta2 : Real}
    (hdelta : delta2 ≤ ExactTargetArithmetic.deltaOf alpha) (heps : alpha ≤ deltaC) :
    ∃ R : Nat, 0 < R ∧
      ∀ (r t s : Nat) (z y : Site 2) (i : Fin d) (sigma : Int),
        0 < s → r = K * s → 2 * R ≤ s → 5 * r ≤ t →
        (sigma = 1 ∨ sigma = -1) →
        (MacroExp.emb (y - z) : Site d) = Pi.single i sigma →
        ∃ G : ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma deltaC delta2,
          (∀ a, (G.plan a).ValidAt p0) ∧
          (∀ a, (G.plan a).radius = R) ∧
          (∀ a, (G.plan a).epsilon = alpha) ∧
          (∀ a, (G.plan a).active =
            ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
          (∀ a, (G.plan a).source =
            Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
          (∀ a, (G.plan a).target = CoreRes.target (d := d) r y) := by
  obtain ⟨In⟩ := exists_inputs_of_thetaSite_pos (d := d) p0 hp0 hp1 htheta ha0 ha1
    (K := K) (by omega)
  refine ⟨In.radius, In.radius_pos, ?_⟩
  intro r t s z y i sigma hs hr hR ht hsigma hemb
  refine ⟨stoppedChildren hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb ht hdelta heps,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stoppedChildren_validAt hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb
      ht hdelta heps
  · intro a
    exact planFamily_radius hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a
  · intro a
    exact planFamily_epsilon hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a
  · intro a
    exact planFamily_active hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a
  · intro a
    exact planFamily_source hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb t a
  · intro a
    exact planFamily_target hp0 hp1 ha0 ha1 In z y i hsigma hK hs hr hR hemb a

#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.exists_inputs_of_thetaSite_pos
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.coreTarget_subset_Dbox
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.rankOne_longTargetAspect
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.instantiation
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.plan_wellFormed
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.plan_validAt
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.plan_source
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.plan_active
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.plan_target
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.stoppedChildren
#print axioms KNAll.Site.ExactLongBoxTranslatedPlan.exists_stoppedChildren_of_thetaSite_pos

end KNAll.Site.ExactLongBoxTranslatedPlan

end
