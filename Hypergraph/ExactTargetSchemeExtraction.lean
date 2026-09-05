import Hypergraph.ExactTargetPlanConstructor
import Hypergraph.ExactTargetHits
import Hypergraph.ExactTargetSchemeNumbers

/-!
# Extraction of exact orthant target schemes

This is the first construction theorem connecting `thetaSite d p > 0` to the exact target-plan
interpreter.  The qualitative hypothesis is used only to obtain the finite orthant-hit family.
All remaining scale choices are finite and numerical.  A concrete instantiation supplies the
finite map saying which translated orthant lies in its target.
-/

noncomputable section

namespace KNAll.Site.ExactTargetScheme

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.MoveWindowInput
open ExactTargetArithmetic ExactTargetSchemeNumbers
open TargetAwareLattice ExactTargetHits

variable {d : Nat} [NeZero d]

/-- A reusable target scheme: the finite qualitative hit scales and all numerical choices. -/
structure OrthantScheme (d : Nat) (p0 : unitInterval) (epsilon : Real) where
  scales : BaseScales (d := d) p0 (etaOf epsilon)
  numbers : Numbers d p0 epsilon (scales.source + 1)

/-- Supercriticality supplies a target scheme at every positive output tolerance at most one. -/
theorem exists_orthantScheme_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (epsilon : Real) (he0 : 0 < epsilon) (he1 : epsilon ≤ 1) :
    Nonempty (OrthantScheme d p0 epsilon) := by
  have heta : 0 < etaOf epsilon := by
    unfold etaOf deltaOf deltaCOf
    positivity
  obtain ⟨S⟩ := exists_baseScales_of_thetaSite_pos (d := d) p0 htheta heta
  obtain ⟨N⟩ := ExactTargetSchemeNumbers.exists_numbers (d := d) p0 hp0 hp1
    epsilon he0 he1 (S.source + 1) (by omega)
  exact ⟨{ scales := S, numbers := N }⟩

/-- One fully finite placement of an orthant scheme.  In particular, `targetRadius` and
`targetFace` are total finite maps, not choices made while interpreting the plan. -/
structure OrthantInstantiation {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) where
  sourceBox : ExactTargetPlan.IntBox d
  activeBox : ExactTargetPlan.IntBox d
  target : Finset (Site d)
  radius : Nat
  source_ordered : sourceBox.Ordered
  active_ordered : activeBox.Ordered
  target_nonempty : target.Nonempty
  radius_ge : S.numbers.R0 ≤ radius
  sourcePlus_subset_active : (sourceBox.inflate radius).sites ⊆ activeBox.sites
  target_subset_active : target ⊆ activeBox.sites
  targetRadius : (sourceBox.inflate radius).sites → Nat
  targetFace : (sourceBox.inflate radius).sites → FaceIndex d
  radius_le : ∀ v, radius ≤ targetRadius v
  localRadius_le : ∀ v, S.scales.localRadius ≤ targetRadius v
  owner_subset_active : ∀ v,
    shiftedOwner (targetRadius v) v.1 ⊆ activeBox.sites
  face_subset_target : ∀ v,
    shiftedTarget (targetRadius v) v.1 (targetFace v) ⊆ target

namespace OrthantScheme

def params {p0 : unitInterval} {epsilon : Real} (S : OrthantScheme d p0 epsilon)
    (I : OrthantInstantiation S) : ExactTargetPlan.ConstructorParams d where
  p0 := p0
  epsilon := epsilon
  m := S.scales.source + 1
  k := S.numbers.k
  N := S.numbers.N
  L := S.numbers.L
  radius := I.radius
  barrierLower := S.numbers.barrierLower

theorem params_admissible {p0 : unitInterval} {epsilon : Real}
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : OrthantScheme d p0 epsilon) (I : OrthantInstantiation S) :
    (S.params I).Admissible := by
  let P := S.params I
  have hR : 2 * (S.scales.source + 1) + S.numbers.L + 2 ≤ I.radius :=
    S.numbers.radius_budget.trans I.radius_ge
  refine {
    p0_pos := hp0
    p0_lt_one := hp1
    epsilon_pos := he0
    epsilon_le_one := he1
    m_pos := by
      change 0 < S.scales.source + 1
      omega
    k_pos := S.numbers.k_pos
    N_pos := S.numbers.N_pos
    L_pos := S.numbers.L_pos
    radius_large := by
      change 2 * (S.scales.source + 1) + S.numbers.L + 2 ≤ I.radius
      exact hR
    packing := by
      simpa [P, params] using S.numbers.packing
    selected_budget := by
      simpa [P, params, ExactTargetPlan.ConstructorParams.seedCard,
        ExactTargetPlan.ConstructorParams.delta, seedCardOf, deltaOf] using
        S.numbers.seed_budget
    seed_valid := by
      simpa [P, params, ExactTargetPlan.ConstructorParams.seedCard,
        ExactTargetPlan.ConstructorParams.delta, seedCardOf, deltaOf] using
        S.numbers.seed_failure
    barrier_pos := S.numbers.barrier_pos
    barrier_lt_one := S.numbers.barrier_lt_one
    barrier_valid := by simpa [P, params] using S.numbers.barrier_leaf
    barrier_budget := by
      simpa [P, params, ExactTargetPlan.ConstructorParams.delta, deltaOf] using
        S.numbers.level_budget }

def concreteTarget {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (I : OrthantInstantiation S) :
    ExactTargetPlan.ConcreteTarget (S.params I) where
  sourceBox := I.sourceBox
  activeBox := I.activeBox
  target := I.target
  source_ordered := I.source_ordered
  active_ordered := I.active_ordered
  target_nonempty := I.target_nonempty
  sourcePlus_subset_active := I.sourcePlus_subset_active
  target_subset_active := I.target_subset_active

private theorem sourceBoxAt_subset_shiftedOwner
    {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (I : OrthantInstantiation S)
    (v : (I.sourceBox.inflate I.radius).sites) :
    siteBoxAt v.1 (S.scales.source + 1) ⊆
      shiftedOwner (I.targetRadius v) v.1 := by
  rw [shiftedOwner, shiftFinset_box_eq_siteBoxAt]
  exact siteBoxAt_subset v.1 (by
    have hs := S.scales.source_lt_arm
    have hl := S.scales.arm_lt_local
    have hn := I.localRadius_le v
    omega)

def concreteHits {p0 : unitInterval} {epsilon : Real}
    (S : OrthantScheme d p0 epsilon) (I : OrthantInstantiation S) :
    ExactTargetPlan.ConcreteHits (S.params I) (S.concreteTarget I) where
  scale := I.targetRadius
  region := fun v => shiftedOwner (I.targetRadius v) v.1
  face := fun v => shiftedTarget (I.targetRadius v) v.1 (I.targetFace v)
  scale_ge := I.radius_le
  region_subset_active := I.owner_subset_active
  face_subset_target := I.face_subset_target
  source_subset_region := by
    intro v
    simpa only [params, concreteTarget] using
      sourceBoxAt_subset_shiftedOwner S I v
  hit_valid := fun v => by
    have h := one_sub_lt_prob_hitEvent_mono_source S.scales
      (S.scales.source + 1) (I.targetRadius v) (by omega) (I.localRadius_le v)
      v.1 (I.targetFace v)
    simpa [params, ExactTargetPlan.ConstructorParams.eta,
      ExactTargetPlan.ConstructorParams.delta, ExactTargetPlan.ConstructorParams.deltaC,
      etaOf, deltaOf, deltaCOf] using h

/-- Every concrete orthant placement produces a well-formed plan valid at the extraction
parameter.  This is the finite target-scheme extraction conclusion. -/
theorem exists_plan {p0 : unitInterval} {epsilon : Real}
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : OrthantScheme d p0 epsilon) (I : OrthantInstantiation S) :
    ∃ C : ExactTargetPlan.Plan d,
      C.WellFormed ∧ C.ValidAt p0 ∧
      C.sourceBox = I.sourceBox ∧ C.activeBox = I.activeBox ∧ C.target = I.target := by
  let P := S.params I
  let X := S.concreteTarget I
  let H := S.concreteHits I
  obtain ⟨C, hC, hwf, hv⟩ := ExactTargetPlan.exists_plan_of_concrete_hits P
    (S.params_admissible hp0 hp1 he0 he1 I) X H
  refine ⟨C, hwf, hv, ?_, ?_, ?_⟩
  · simpa [hC, P, X, concreteTarget]
  · simpa [hC, P, X, concreteTarget]
  · simpa [hC, P, X, concreteTarget]

end OrthantScheme

end KNAll.Site.ExactTargetScheme

end

#print axioms KNAll.Site.ExactTargetScheme.exists_orthantScheme_of_thetaSite_pos
#print axioms KNAll.Site.ExactTargetScheme.OrthantScheme.exists_plan
