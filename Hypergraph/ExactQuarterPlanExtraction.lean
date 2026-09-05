import Hypergraph.ExactTargetSchemeExtraction
import Hypergraph.CoreFaceTargetPackaging
import Hypergraph.ExactCorridorPlanStability

/-!
# Exact quarter-stage extraction

This module constructs the first `d` nodes of an exact corridor plan.  The nodes use the literal
cross-section boxes from `CorrMove.faceTarget_step`; every translated target orthant is selected
from that concrete `FaceTarget` witness.  In particular, the finite active and target
containments are fields of an actual `ExactTargetScheme.OrthantInstantiation`, not assumptions
attached afterwards to an abstract plan.
-/

noncomputable section

namespace KNAll.Site.ExactQuarterPlanExtraction

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open ExactTargetArithmetic TargetAwareLattice
open scoped Classical

variable {d : Nat} [NeZero d]
variable {q : unitInterval} {chi : Real}

abbrev IntBox := ExactTargetPlan.IntBox
abbrev OrthantScheme := ExactTargetScheme.OrthantScheme

/-! ## Literal cross-section boxes -/

/-- The coordinate half-width of the `j`th cross-section box. -/
def crossRadius (r R j : Nat) (a : Fin d) : Int :=
  (if a.val < j then (CorrMove.hw r : Int) else 3 * (r : Int)) +
    (j : Int) * (R : Int)

/-- `CorrMove.Bx`, represented in the `IntBox` format used by exact target plans. -/
def crossIntBox (c : Site d) (r R j : Nat) : IntBox d where
  lower a := c a - crossRadius r R j a
  upper a := c a + crossRadius r R j a

/-- The common active cube of all `d` cross-section reductions. -/
def activeIntBox (c : Site d) (r : Nat) : IntBox d where
  lower a := c a - 5 * (r : Int)
  upper a := c a + 5 * (r : Int)

/-- The literal finite box used at stage `j`. -/
def crossBox (c : Site d) (r R j : Nat) : Finset (Site d) :=
  CorrMove.Bx c (CorrMove.hw r : Int) (r : Int) ((j : Int) * (R : Int)) j

@[simp] theorem crossIntBox_sites (c : Site d) (r R j : Nat) :
    (crossIntBox c r R j).sites = crossBox c r R j := by
  rfl

@[simp] theorem activeIntBox_sites (c : Site d) (r : Nat) :
    (activeIntBox c r).sites = CorrMove.cube c (5 * (r : Int)) := by
  rfl

theorem crossIntBox_ordered (c : Site d) (r R j : Nat) :
    (crossIntBox c r R j).Ordered := by
  intro a
  have hrho : 0 ≤ crossRadius r R j a := by
    unfold crossRadius
    split_ifs <;> positivity
  dsimp [crossIntBox]
  omega

theorem activeIntBox_ordered (c : Site d) (r : Nat) :
    (activeIntBox c r).Ordered := by
  intro a
  dsimp [activeIntBox]
  omega

theorem crossBox_nonempty (c : Site d) (r R j : Nat) :
    (crossBox c r R j).Nonempty := by
  unfold crossBox
  exact CorrMove.Bx_nonempty c j (by positivity) (by positivity)

/-- Every point of the coordinate inflation of an ordered integer box is within the inflation
radius of an actual point of the original box. -/
theorem exists_near_of_mem_inflate (B : IntBox d) (hB : B.Ordered) (R : Nat)
    (v : (B.inflate R).sites) :
    ∃ b ∈ B.sites, ∀ a, |v.1 a - b a| ≤ (R : Int) := by
  let b : Site d := fun a =>
    if v.1 a < B.lower a then B.lower a
    else if B.upper a < v.1 a then B.upper a
    else v.1 a
  have hb : b ∈ B.sites := by
    rw [ExactTargetPlan.IntBox.mem_sites]
    intro a
    have hba := hB a
    dsimp only [b]
    split_ifs <;> omega
  refine ⟨b, hb, ?_⟩
  intro a
  have hv := (ExactTargetPlan.IntBox.mem_sites.1 v.2) a
  dsimp [ExactTargetPlan.IntBox.inflate] at hv
  rw [abs_le]
  dsimp only [b]
  split_ifs <;> omega

/-! ## A radius-preserving refinement of the genuine face choice -/

/-- The `CoreFaceTarget.ChosenTarget` together with the lower bound on its chosen radius which
is needed by `OrthantInstantiation.radius_le`. -/
structure SizedChosenTarget
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (R : Nat) (Fresh Bset Tset : Finset (Site d)) (v : Site d)
    extends CoreFaceTarget.ChosenTarget S R Fresh Bset Tset v where
  radius_ge : R ≤ radius

theorem exists_sizedChosenTarget
    (S : TargetAwareLattice.BaseScales (d := d) q chi) (R : Nat)
    (hscale : S.localRadius < R) {Fresh Bset Tset : Finset (Site d)}
    (hface : CorrMove.FaceTarget (R : Int) Fresh Bset Tset) (v : Site d)
    (hnear : ∃ b ∈ Bset, ∀ a, |v a - b a| ≤ (R : Int)) :
    Nonempty (SizedChosenTarget S R Fresh Bset Tset v) := by
  obtain ⟨ell, a, sigma, tau, hRell, hsigma, hcube, hqface⟩ := hface v hnear
  have hell0 : 0 ≤ ell := le_trans (Int.natCast_nonneg R) hRell
  let n : Nat := ell.toNat
  have hncast : (n : Int) = ell := Int.toNat_of_nonneg hell0
  have hRnZ : (R : Int) ≤ (n : Int) := by simpa only [hncast] using hRell
  have hRn : R ≤ n := by exact_mod_cast hRnZ
  refine ⟨{
    radius := n
    axis := a
    sigma := sigma
    tau := tau
    sigma_eq := hsigma
    local_lt_radius := hscale.trans_le hRn
    owner_subset_fresh := ?_
    target_subset := ?_
    radius_ge := hRn }⟩
  · rw [shiftedOwner, shiftFinset_box_eq_cube, hncast]
    exact hcube
  · exact (shiftedTarget_subset_qface n v a sigma tau hsigma).trans
      (by simpa only [hncast] using hqface)

def chooseSizedTarget
    (S : TargetAwareLattice.BaseScales (d := d) q chi) (R : Nat)
    (hscale : S.localRadius < R) {Fresh Bset Tset : Finset (Site d)}
    (hface : CorrMove.FaceTarget (R : Int) Fresh Bset Tset) (v : Site d)
    (hnear : ∃ b ∈ Bset, ∀ a, |v a - b a| ≤ (R : Int)) :
    SizedChosenTarget S R Fresh Bset Tset v :=
  Classical.choice (exists_sizedChosenTarget S R hscale hface v hnear)

/-! ## Common finite scales and the cross-section target relation -/

/-- One common face radius dominates the finitely many local and arithmetic scheme radii. -/
def commonRadius {p0 : unitInterval} {epsilon : Fin d → Real}
    (S : ∀ i, OrthantScheme d p0 (epsilon i)) : Nat :=
  (Finset.univ.sup fun i : Fin d => max (S i).scales.localRadius (S i).numbers.R0) + 1

theorem localRadius_lt_commonRadius {p0 : unitInterval} {epsilon : Fin d → Real}
    (S : ∀ i, OrthantScheme d p0 (epsilon i)) (i : Fin d) :
    (S i).scales.localRadius < commonRadius S := by
  have hi := Finset.le_sup (s := (Finset.univ : Finset (Fin d)))
    (f := fun j => max (S j).scales.localRadius (S j).numbers.R0)
    (Finset.mem_univ i)
  exact lt_of_le_of_lt (le_trans (le_max_left _ _) hi) (Nat.lt_succ_self _)

theorem arithmeticRadius_le_commonRadius {p0 : unitInterval} {epsilon : Fin d → Real}
    (S : ∀ i, OrthantScheme d p0 (epsilon i)) (i : Fin d) :
    (S i).numbers.R0 ≤ commonRadius S := by
  have hi := Finset.le_sup (s := (Finset.univ : Finset (Fin d)))
    (f := fun j => max (S j).scales.localRadius (S j).numbers.R0)
    (Finset.mem_univ i)
  exact (le_trans (le_max_right _ _) hi).trans (Nat.le_succ _)

/-- A corridor scale above a requested floor and above the deterministic separation bound. -/
def commonScale (rmin R d : Nat) : Nat :=
  max (max rmin 44) (100 * (d + 1) * (R + 1) + 1)

theorem minScale_le_commonScale (rmin R d : Nat) :
    rmin ≤ commonScale rmin R d :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem fortyFour_le_commonScale (rmin R d : Nat) :
    44 ≤ commonScale rmin R d :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem separation_commonScale (rmin R d : Nat) :
    100 * (d + 1) * (R + 1) < commonScale rmin R d := by
  unfold commonScale
  exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)

/-- Every cross-section box up to level `d` lies in the common active cube. -/
theorem crossBox_subset_active (c : Site d) {r R j : Nat}
    (hj : j ≤ d)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    crossBox c r R j ⊆ CorrMove.cube c (5 * (r : Int)) := by
  have hPnat : 100 * ((d + 1) * R) < r := CorrMove.scale_mul d R r hscale
  have hjPnat : j * R ≤ (d + 1) * R :=
    Nat.mul_le_mul_right R (hj.trans (Nat.le_succ d))
  have hP0 : 0 ≤ ((d + 1) * R : Nat) := Nat.zero_le _
  have hPrNat : (d + 1) * R < r := by omega
  have hArNat : j * R < r := lt_of_le_of_lt hjPnat hPrNat
  have hAr : (j : Int) * (R : Int) < (r : Int) := by
    exact_mod_cast hArNat
  have hhw : 2 * (CorrMove.hw r : Int) ≤ 3 * (r : Int) + 1 := by
    exact_mod_cast CorrMove.two_mul_hw_le r
  unfold crossBox
  apply CorrMove.Bx_subset_cube
  · omega
  · omega

/-- The `i`th source and `(i+1)`st target boxes satisfy the literal quarter-face relation at
the common radius. -/
theorem crossFaceTarget (c : Site d) {r R : Nat} (i : Fin d)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    CorrMove.FaceTarget (R : Int) (CorrMove.cube c (5 * (r : Int)))
      (crossBox c r R i.val) (crossBox c r R (i.val + 1)) := by
  have hPnat : 100 * ((d + 1) * R) < r := CorrMove.scale_mul d R r hscale
  have hiPnat : (i.val + 2) * R ≤ (d + 1) * R :=
    Nat.mul_le_mul_right R (by omega)
  have hPrNat : (d + 1) * R < r := by omega
  have hi100Nat : 100 * ((i.val + 2) * R) < r :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 100 hiPnat) hPnat
  have hiR : ((i.val : Int) * (R : Int) + 2 * (R : Int)) < (r : Int) := by
    have : (i.val + 2) * R < r := lt_of_le_of_lt hiPnat hPrNat
    calc
      (i.val : Int) * (R : Int) + 2 * (R : Int) =
          (((i.val + 2) * R : Nat) : Int) := by push_cast; ring
      _ < (r : Int) := by exact_mod_cast this
  have hi100 : 100 * ((i.val : Int) * (R : Int) + 2 * (R : Int)) <
      (r : Int) := by
    calc
      100 * ((i.val : Int) * (R : Int) + 2 * (R : Int)) =
          ((100 * ((i.val + 2) * R) : Nat) : Int) := by push_cast; ring
      _ < (r : Int) := by exact_mod_cast hi100Nat
  have hhw1 : 3 * (r : Int) ≤ 2 * (CorrMove.hw r : Int) := by
    exact_mod_cast CorrMove.three_mul_le_two_mul_hw r
  have hhw2 : 2 * (CorrMove.hw r : Int) ≤ 3 * (r : Int) + 1 := by
    exact_mod_cast CorrMove.two_mul_hw_le r
  have hrpos : (0 : Int) < (r : Int) := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hA : (i.val : Int) * (R : Int) + 2 * (R : Int) ≤
      (CorrMove.hw r : Int) - (r : Int) := by
    omega
  have hwr : (CorrMove.hw r : Int) + (R : Int) ≤ 3 * (r : Int) := by
    have hRrNat : R < r := by
      have hRle : R ≤ (d + 1) * R := Nat.le_mul_of_pos_left R (by omega)
      exact lt_of_le_of_lt hRle hPrNat
    have hRr : (R : Int) < (r : Int) := by exact_mod_cast hRrNat
    omega
  have htarget := CorrMove.faceTarget_step c (CorrMove.hw r : Int) (r : Int)
    (R : Int) ((i.val : Int) * (R : Int)) i.val i rfl
    (Int.natCast_nonneg R) (by positivity) hA hhw1 hwr
  have hcast : ((i.val + 1 : Nat) : Int) * (R : Int) =
      (i.val : Int) * (R : Int) + (R : Int) := by
    push_cast
    ring
  simpa only [crossBox, hcast] using htarget

/-! ## The actual orthant instantiation at one stage -/

/-- The literal `i`th cross-section call as an `OrthantInstantiation`.  Its total target maps are
chosen from `crossFaceTarget` at every point of the inflated source box. -/
def crossInstantiation {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    ExactTargetScheme.OrthantInstantiation S := by
  let B : IntBox d := crossIntBox c r R i.val
  let A : IntBox d := activeIntBox c r
  let T : Finset (Site d) := crossBox c r R (i.val + 1)
  have hB : B.Ordered := crossIntBox_ordered c r R i.val
  have hA : A.Ordered := activeIntBox_ordered c r
  have hface : CorrMove.FaceTarget (R : Int) A.sites B.sites T := by
    simpa only [A, B, T, activeIntBox_sites, crossIntBox_sites] using
      crossFaceTarget c i hscale
  let C : ∀ v : (B.inflate R).sites, SizedChosenTarget S.scales R A.sites B.sites T v.1 :=
    fun v => chooseSizedTarget S.scales R hlocal hface v.1 (by
      obtain ⟨b, hb, hnear⟩ := exists_near_of_mem_inflate B hB R v
      exact ⟨b, hb, hnear⟩)
  exact {
    sourceBox := B
    activeBox := A
    target := T
    radius := R
    source_ordered := hB
    active_ordered := hA
    target_nonempty := crossBox_nonempty c r R (i.val + 1)
    radius_ge := hR0
    sourcePlus_subset_active := by
      intro v hv
      let v' : (B.inflate R).sites := ⟨v, hv⟩
      have hvOwner : v ∈ shiftedOwner (C v').radius v := by
        rw [shiftedOwner, shiftFinset_box_eq_cube]
        exact CorrMove.centre_mem_cube (c := v) (Int.natCast_nonneg (C v').radius)
      exact (C v').owner_subset_fresh hvOwner
    target_subset_active := by
      simpa only [A, T, activeIntBox_sites] using
        crossBox_subset_active c (j := i.val + 1) (by omega) hscale
    targetRadius := fun v => (C v).radius
    targetFace := fun v =>
      ((C v).axis, qfaceUnits (C v).axis (C v).sigma (C v).tau)
    radius_le := fun v => (C v).radius_ge
    localRadius_le := fun v => (C v).local_lt_radius.le
    owner_subset_active := fun v => (C v).owner_subset_fresh
    face_subset_target := fun v => (C v).target_subset }

@[simp] theorem crossInstantiation_sourceBox {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossInstantiation S c r R i hR0 hlocal hscale).sourceBox =
      crossIntBox c r R i.val := rfl

@[simp] theorem crossInstantiation_activeBox {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossInstantiation S c r R i hR0 hlocal hscale).activeBox =
      activeIntBox c r := rfl

@[simp] theorem crossInstantiation_target {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossInstantiation S c r R i hR0 hlocal hscale).target =
      crossBox c r R (i.val + 1) := rfl

@[simp] theorem crossInstantiation_radius {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossInstantiation S c r R i hR0 hlocal hscale).radius = R := rfl

/-! ## A fully realized exact plan -/

/-- The exact plan underlying `OrthantScheme.exists_plan`, kept transparent so its radius and
epsilon equations remain available to the corridor assembler. -/
def crossPlan {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) : ExactTargetPlan.Plan d :=
  let I := crossInstantiation S c r R i hR0 hlocal hscale
  ExactTargetPlan.buildPlan (S.params I) (S.concreteTarget I) (S.concreteHits I)

theorem crossPlan_wellFormed
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossPlan S c r R i hR0 hlocal hscale).WellFormed := by
  let I := crossInstantiation S c r R i hR0 hlocal hscale
  exact ExactTargetPlan.buildPlan_wellFormed _
    (S.params_admissible hp0 hp1 he0 he1 I) _ _

theorem crossPlan_validAt
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossPlan S c r R i hR0 hlocal hscale).ValidAt p0 := by
  let I := crossInstantiation S c r R i hR0 hlocal hscale
  exact ExactTargetPlan.buildPlan_validAt _
    (S.params_admissible hp0 hp1 he0 he1 I) _ _

@[simp] theorem crossPlan_source
    {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossPlan S c r R i hR0 hlocal hscale).source = crossBox c r R i.val := by
  rfl

@[simp] theorem crossPlan_active
    {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossPlan S c r R i hR0 hlocal hscale).active =
      CorrMove.cube c (5 * (r : Int)) := by
  rfl

@[simp] theorem crossPlan_target
    {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossPlan S c r R i hR0 hlocal hscale).target =
      crossBox c r R (i.val + 1) := by
  rfl

@[simp] theorem crossPlan_radius
    {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossPlan S c r R i hR0 hlocal hscale).radius = R := rfl

@[simp] theorem crossPlan_epsilon
    {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (crossPlan S c r R i hR0 hlocal hscale).epsilon = epsilon := rfl

theorem crossPlan_faceTarget
    {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    CorrMove.FaceTarget ((crossPlan S c r R i hR0 hlocal hscale).radius : Int)
      (crossPlan S c r R i hR0 hlocal hscale).active
      (crossPlan S c r R i hR0 hlocal hscale).source
      (crossPlan S c r R i hR0 hlocal hscale).target := by
  simpa using crossFaceTarget c i hscale

/-! ## The finite family consumed by the corridor assembler -/

/-- The first `d` stages of `ExactCorridorPlan.ofStageFamily`, including the actual target-scheme
instantiations from which their exact plans were built. -/
structure QuarterStageFamily
    (p0 : unitInterval) (epsilon : Fin d → Real) (c : Site d) (rmin : Nat) where
  radius : Nat
  scale : Nat
  scheme : ∀ i, OrthantScheme d p0 (epsilon i)
  instantiation : ∀ i, ExactTargetScheme.OrthantInstantiation (scheme i)
  quarter : Fin d → ExactTargetPlan.Plan d
  radius_pos : 0 < radius
  scale_pos : 0 < scale
  scale_floor : rmin ≤ scale
  separation : 100 * (d + 1) * (radius + 1) < scale
  instantiation_source : ∀ i,
    (instantiation i).sourceBox = crossIntBox c scale radius i.val
  instantiation_active : ∀ i,
    (instantiation i).activeBox = activeIntBox c scale
  instantiation_target : ∀ i,
    (instantiation i).target = crossBox c scale radius (i.val + 1)
  instantiation_radius : ∀ i, (instantiation i).radius = radius
  quarter_wellFormed : ∀ i, (quarter i).WellFormed
  quarter_validAt : ∀ i, (quarter i).ValidAt p0
  quarter_source : ∀ i, (quarter i).source = crossBox c scale radius i.val
  quarter_active : ∀ i,
    (quarter i).active = CorrMove.cube c (5 * (scale : Int))
  quarter_target : ∀ i,
    (quarter i).target = crossBox c scale radius (i.val + 1)
  quarter_radius : ∀ i, (quarter i).radius = radius
  quarter_epsilon : ∀ i, (quarter i).epsilon = epsilon i
  quarter_geometry : ∀ i,
    CorrMove.FaceTarget ((quarter i).radius : Int) (quarter i).active
      (quarter i).source (quarter i).target

namespace QuarterStageFamily

/-- The `d+1` cross-section boxes to pass to `ExactCorridorPlan.ofStageFamily`. -/
def boxes {p0 : unitInterval} {epsilon : Fin d → Real} {c : Site d} {rmin : Nat}
    (Q : QuarterStageFamily p0 epsilon c rmin) :
    Fin (d + 1) → Finset (Site d) :=
  fun j => crossBox c Q.scale Q.radius j.val

@[simp] theorem boxes_zero {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin) :
    Q.boxes 0 = CorrMove.cube c (3 * (Q.scale : Int)) := by
  simp [boxes, crossBox]

@[simp] theorem quarter_source_box {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin)
    (i : Fin d) :
    (Q.quarter i).source = Q.boxes i.castSucc := by
  simpa [boxes] using Q.quarter_source i

@[simp] theorem quarter_target_box {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin)
    (i : Fin d) :
    (Q.quarter i).target = Q.boxes i.succ := by
  simpa [boxes] using Q.quarter_target i

/-- Add any eventual aspect-88 plan as the last member of the family passed to
`ExactCorridorPlan.ofStageFamily`. -/
def stagesWith {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin)
    (aspect88 : ExactTargetPlan.Plan d) : Fin (d + 1) → ExactTargetPlan.Plan d :=
  Fin.lastCases aspect88 Q.quarter

@[simp] theorem stagesWith_castSucc {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin)
    (aspect88 : ExactTargetPlan.Plan d) (i : Fin d) :
    Q.stagesWith aspect88 i.castSucc = Q.quarter i := by
  simp [stagesWith]

@[simp] theorem stagesWith_last {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin)
    (aspect88 : ExactTargetPlan.Plan d) :
    Q.stagesWith aspect88 (Fin.last d) = aspect88 := by
  simp [stagesWith]

/-- Direct application of `ExactCorridorPlan.ofStageFamily`; the supplied final node occupies
the last index and this object's concrete quarter plans occupy all cast-successor indices. -/
def toCorridorPlan {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin)
    (endCentre : Site d) (aspect88 : ExactTargetPlan.Plan d)
    (longAxis : Fin d) (longSign : Int)
    (past : Fin (d + 1) → Finset (Site d))
    (eta : Fin (d + 1) → Real) (alpha : Real) : ExactCorridorPlan.Plan d :=
  ExactCorridorPlan.Plan.ofStageFamily Q.scale c endCentre Q.boxes
    (Q.stagesWith aspect88) longAxis longSign past eta alpha

@[simp] theorem toCorridorPlan_quarter {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin)
    (endCentre : Site d) (aspect88 : ExactTargetPlan.Plan d)
    (longAxis : Fin d) (longSign : Int)
    (past : Fin (d + 1) → Finset (Site d))
    (eta : Fin (d + 1) → Real) (alpha : Real) (i : Fin d) :
    (Q.toCorridorPlan endCentre aspect88 longAxis longSign past eta alpha).quarter i =
      Q.quarter i := by
  simp [toCorridorPlan, ExactCorridorPlan.Plan.ofStageFamily]

/-- The exact delta of each quarter stage, in the form used by the backwards error cascade. -/
theorem quarter_delta {p0 : unitInterval} {epsilon : Fin d → Real}
    {c : Site d} {rmin : Nat} (Q : QuarterStageFamily p0 epsilon c rmin)
    (i : Fin d) :
    (Q.quarter i).delta = deltaOf (epsilon i) := by
  rw [ExactTargetPlan.Plan.delta, Q.quarter_epsilon i]
  rfl

end QuarterStageFamily

/-! ## Extraction from positive percolation -/

/-- Positive percolation at the single extraction parameter supplies the complete finite family
of concrete quarter-face plans, simultaneously at a common face radius and at an arbitrarily
large corridor scale. -/
theorem exists_quarterStageFamily_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (epsilon : Fin d → Real) (he0 : ∀ i, 0 < epsilon i)
    (he1 : ∀ i, epsilon i ≤ 1) (c : Site d) (rmin : Nat) :
    Nonempty (QuarterStageFamily p0 epsilon c rmin) := by
  let schemes : ∀ i, OrthantScheme d p0 (epsilon i) := fun i =>
    Classical.choice
      (ExactTargetScheme.exists_orthantScheme_of_thetaSite_pos p0 hp0 hp1 htheta
        (epsilon i) (he0 i) (he1 i))
  let R : Nat := commonRadius schemes
  let r : Nat := commonScale rmin R d
  have hlocal : ∀ i, (schemes i).scales.localRadius < R :=
    fun i => localRadius_lt_commonRadius schemes i
  have hR0 : ∀ i, (schemes i).numbers.R0 ≤ R :=
    fun i => arithmeticRadius_le_commonRadius schemes i
  have hsep : 100 * (d + 1) * (R + 1) < r := separation_commonScale rmin R d
  let instantiation : ∀ i, ExactTargetScheme.OrthantInstantiation (schemes i) :=
    fun i => crossInstantiation (schemes i) c r R i (hR0 i) (hlocal i) hsep
  let quarter : Fin d → ExactTargetPlan.Plan d := fun i =>
    crossPlan (schemes i) c r R i (hR0 i) (hlocal i) hsep
  refine ⟨{
    radius := R
    scale := r
    scheme := schemes
    instantiation := instantiation
    quarter := quarter
    radius_pos := by
      unfold R commonRadius
      omega
    scale_pos := by
      exact lt_of_lt_of_le (by norm_num : 0 < 44) (fortyFour_le_commonScale rmin R d)
    scale_floor := minScale_le_commonScale rmin R d
    separation := hsep
    instantiation_source := ?_
    instantiation_active := ?_
    instantiation_target := ?_
    instantiation_radius := ?_
    quarter_wellFormed := ?_
    quarter_validAt := ?_
    quarter_source := ?_
    quarter_active := ?_
    quarter_target := ?_
    quarter_radius := ?_
    quarter_epsilon := ?_
    quarter_geometry := ?_ }⟩
  · intro i
    exact crossInstantiation_sourceBox (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossInstantiation_activeBox (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossInstantiation_target (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossInstantiation_radius (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossPlan_wellFormed hp0 hp1 (he0 i) (he1 i) (schemes i) c r R i
      (hR0 i) (hlocal i) hsep
  · intro i
    exact crossPlan_validAt hp0 hp1 (he0 i) (he1 i) (schemes i) c r R i
      (hR0 i) (hlocal i) hsep
  · intro i
    exact crossPlan_source (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossPlan_active (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossPlan_target (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossPlan_radius (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossPlan_epsilon (schemes i) c r R i (hR0 i) (hlocal i) hsep
  · intro i
    exact crossPlan_faceTarget (schemes i) c r R i (hR0 i) (hlocal i) hsep

/-- Cascade-indexed spelling of the extraction theorem.  The `i`th quarter plan has output
tolerance `eta i.succ`, exactly as required by `wellFormed_ofStageFamily`. -/
theorem exists_quarterStageFamily_for_eta
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (eta : Fin (d + 1) → Real) (he0 : ∀ i : Fin d, 0 < eta i.succ)
    (he1 : ∀ i : Fin d, eta i.succ ≤ 1) (c : Site d) (rmin : Nat) :
    Nonempty (QuarterStageFamily p0 (fun i => eta i.succ) c rmin) :=
  exists_quarterStageFamily_of_thetaSite_pos p0 hp0 hp1 htheta
    (fun i => eta i.succ) he0 he1 c rmin

#print axioms KNAll.Site.ExactQuarterPlanExtraction.crossInstantiation
#print axioms KNAll.Site.ExactQuarterPlanExtraction.exists_quarterStageFamily_of_thetaSite_pos
#print axioms KNAll.Site.ExactQuarterPlanExtraction.exists_quarterStageFamily_for_eta

end KNAll.Site.ExactQuarterPlanExtraction

end
