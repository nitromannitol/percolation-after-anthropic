import Hypergraph.ExactQuarterPlanExtraction
import Hypergraph.ExactLongBoxHitBridge
import Hypergraph.ExactOuterStageExtraction
import Hypergraph.ExactMacroStepFromTheta

/-!
# Prototype stability of the frozen quarter and aspect-`88` outer data

Every quarter-face plan and every aspect-`88` outer plan the exact macro step consumes is built
from *one* frozen scheme, extracted once at `p0`.  Its leaf table therefore consists of

* canonical seed and barrier leaves, which do not depend on the position at all, and
* homogeneous hit leaves, each of which is an exact lattice translate of a *centred* cylinder.

Both facts are literal, not approximate.  So the whole infinite family of plans -- one per macro
centre, per finite axis, per sign -- realises only *finitely many distinct probabilities*: those
of the centred prototypes, of which there are finitely many because the local scale chosen at a
relay point is confined to the plan's own bounded active box.

This module makes that precise and uses it to choose one `q < p0` **before** any macro history:

* `exists_left_nhds_of_finite` : finitely many stored estimates have a common left neighbourhood.
* `targetRadius_le` / `choice_l_le` : the chosen local scale of an orthant, resp. rank-one,
  instantiation is bounded by the diameter of its own active box.
* `prob_quarterHit_eq` / `prob_outerHit_eq` : exact homogeneous translation invariance of the two
  hit cylinders.  A transported leaf carries a literal `HoldsAt q` fact; no abstract inverse
  hypothesis is introduced.
* `buildPlan_validAt_of` : the leaf table of `ExactTargetPlan.buildPlan` is exhausted by the hit,
  seed and barrier pointers, so validity at a new parameter follows from those three classes.
* `exists_left_nhds_quarter` / `exists_left_nhds_rankOne` : one radius each, computed from the
  finitely many centred prototypes.
* `exists_outerStage_validAt` : the `ExactMacroGeometry.OuterStage` built from the frozen
  aspect-`88` `OuterData` has a corridor valid at `q`.
* `exists_left_nhds_quarter_outer`, `exists_stable_below` : the joint statement, and its closing
  form at the frozen data of `ExactMacroStepFromTheta`.

Nothing here takes an infimum over infinitely many positions, and no new probability premise is
added: all inputs are the frozen `p0` estimates already extracted from `0 < thetaSite d p0`.
The `2 r` / `3 r` semantic target split is untouched; `corridor_targets` records it.
-/

noncomputable section

namespace KNAll.Site.ExactQuarterOuterPrototypeStability

set_option maxHeartbeats 1000000

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.MoveWindowInput
open ExactTargetArithmetic TargetAwareLattice
open scoped Classical

variable {d : Nat}

/-! ## §1.  Finitely many stored estimates have a common left neighbourhood

This is the finite Lipschitz argument of `RenormData.exists_valid_nhds`, stated for an arbitrary
finite index type so that the same statement serves the quarter prototypes, the outer prototypes,
and the canonical seed/barrier pair. -/

theorem holdsAt_of_prob_eq {B B' : ProbabilityBound d} {q : unitInterval}
    (hlower : B.lower = B'.lower)
    (hprob : B.experiment.prob q = B'.experiment.prob q)
    (h : B'.HoldsAt q) : B.HoldsAt q := by
  unfold ProbabilityBound.HoldsAt at h ⊢
  rw [hlower, hprob]
  exact h

/-- **Finitely many stored estimates are simultaneously stable.**  Each holds at `p` with a
strictly positive margin, and each moves by at most `card support` times the parameter shift, so
the minimum of `margin / (card support + 1)` is a radius on which all of them survive. -/
theorem exists_left_nhds_of_finite {ι : Type} [Fintype ι]
    (B : ι → ProbabilityBound d) {p : unitInterval} (hB : ∀ j, (B j).HoldsAt p) :
    ∃ ε : Real, 0 < ε ∧ ∀ q : unitInterval,
      |(q : Real) - (p : Real)| < ε → ∀ j, (B j).HoldsAt q := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun _ _ j => (hι.false j).elim⟩
  · have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
    let f : ι → Real := fun j =>
      ((B j).experiment.prob p - (B j).lower) / (((B j).experiment.support.card : Real) + 1)
    have hfpos : ∀ j, 0 < f j := by
      intro j
      exact div_pos (sub_pos.2 (hB j)) (by positivity)
    refine ⟨Finset.univ.inf' hne f, (Finset.lt_inf'_iff hne).2 (fun j _ => hfpos j), ?_⟩
    intro q hq j
    have hle : Finset.univ.inf' hne f ≤ f j := Finset.inf'_le f (Finset.mem_univ j)
    have hcard : (0 : Real) < ((B j).experiment.support.card : Real) + 1 := by positivity
    have hlip := (B j).experiment.abs_prob_sub_le p q
    have key : (B j).experiment.prob p - (B j).experiment.prob q
        < f j * (((B j).experiment.support.card : Real) + 1) := by
      calc (B j).experiment.prob p - (B j).experiment.prob q
          ≤ |(B j).experiment.prob p - (B j).experiment.prob q| := le_abs_self _
        _ ≤ ((B j).experiment.support.card : Real) * |(p : Real) - (q : Real)| := hlip
        _ ≤ (((B j).experiment.support.card : Real) + 1) * |(q : Real) - (p : Real)| := by
            rw [abs_sub_comm]
            exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (((B j).experiment.support.card : Real) + 1) * Finset.univ.inf' hne f :=
            mul_lt_mul_of_pos_left hq hcard
        _ ≤ (((B j).experiment.support.card : Real) + 1) * f j :=
            mul_le_mul_of_nonneg_left hle hcard.le
        _ = f j * (((B j).experiment.support.card : Real) + 1) := mul_comm _ _
    have hval : f j * (((B j).experiment.support.card : Real) + 1)
        = (B j).experiment.prob p - (B j).lower := by
      dsimp only [f]
      field_simp
    rw [hval] at key
    unfold ProbabilityBound.HoldsAt
    linarith

/-- A left neighbourhood contains positive parameters strictly below `p`. -/
theorem exists_lt_of_left_nhds {p : unitInterval} (hp : 0 < (p : Real))
    {ε : Real} (hε : 0 < ε) :
    ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p : Real) ∧
      |(q : Real) - (p : Real)| < ε := by
  have hp1 : (p : Real) ≤ 1 := p.2.2
  let t : Real := min (ε / 2) ((p : Real) / 2)
  have ht : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htp : t ≤ (p : Real) / 2 := min_le_right _ _
  refine ⟨⟨(p : Real) - t, Set.mem_Icc.2 ⟨by linarith, by linarith⟩⟩, ?_, ?_, ?_⟩
  · change 0 < (p : Real) - t
    linarith
  · change (p : Real) - t < (p : Real)
    linarith
  · change |(p : Real) - t - (p : Real)| < ε
    rw [show (p : Real) - t - (p : Real) = -t by ring, abs_neg, abs_of_pos ht]
    exact htε

/-! ## §2.  The leaf table of `ExactTargetPlan.buildPlan` is exhausted by its three pointers

`buildPlan` appends the hit table to the canonical seed/barrier pair.  The hit pointer is
`Fin.castAdd 2` composed with `Fintype.equivFin`, so it is onto the first block; the last two
indices are literally the seed and barrier pointers. -/

section BuildPlan

variable [NeZero d]

/-- The same enumeration of relay points that `ExactTargetPlan.buildPlan` uses internally. -/
def hitFin (P : ExactTargetPlan.ConstructorParams d) (X : ExactTargetPlan.ConcreteTarget P) :
    ((X.sourceBox.inflate P.radius).sites) ≃
      Fin (Fintype.card ((X.sourceBox.inflate P.radius).sites)) :=
  Fintype.equivFin _

theorem buildPlan_hitLeaf_eq (P : ExactTargetPlan.ConstructorParams d)
    (X : ExactTargetPlan.ConcreteTarget P) (H : ExactTargetPlan.ConcreteHits P X)
    (v : ((X.sourceBox.inflate P.radius).sites)) :
    (ExactTargetPlan.buildPlan P X H).hitLeaf v = Fin.castAdd 2 (hitFin P X v) := rfl

/-- **Validity of a built exact target plan at a new parameter.**  Only the three leaf classes
occur, so the three literal `HoldsAt q` facts below are the whole of `ValidAt q`. -/
theorem buildPlan_validAt_of (P : ExactTargetPlan.ConstructorParams d)
    (X : ExactTargetPlan.ConcreteTarget P) (H : ExactTargetPlan.ConcreteHits P X)
    {q : unitInterval} (hq0 : 0 < (q : Real)) (hqp : (q : Real) ≤ (P.p0 : Real))
    (hhit : ∀ v : ((X.sourceBox.inflate P.radius).sites),
      (ExactTargetPlan.hitBound P X H v).HoldsAt q)
    (hseed : (ExactTargetPlan.seedBound P).HoldsAt q)
    (hbar : (ExactTargetPlan.barrierBound P).HoldsAt q) :
    (ExactTargetPlan.buildPlan P X H).ValidAt q := by
  refine ⟨hq0, hqp, ?_⟩
  suffices hall : ∀ j : Fin (Fintype.card ((X.sourceBox.inflate P.radius).sites) + 2),
      ((ExactTargetPlan.buildPlan P X H).leaf j).HoldsAt q by
    intro j
    exact hall j
  intro j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) j
  · have heq : Fin.castAdd 2 a =
        (ExactTargetPlan.buildPlan P X H).hitLeaf ((hitFin P X).symm a) := by
      rw [buildPlan_hitLeaf_eq, Equiv.apply_symm_apply]
    rw [heq, ExactTargetPlan.buildPlan_hitLeaf]
    exact hhit _
  · refine Fin.cases ?_ (fun b => ?_) a
    · show ((ExactTargetPlan.buildPlan P X H).leaf
        (ExactTargetPlan.buildPlan P X H).seedLeaf).HoldsAt q
      rw [ExactTargetPlan.buildPlan_seedLeaf]
      exact hseed
    · refine Fin.cases ?_ (fun c => ?_) b
      · show ((ExactTargetPlan.buildPlan P X H).leaf
          (ExactTargetPlan.buildPlan P X H).barrierLeaf).HoldsAt q
        rw [ExactTargetPlan.buildPlan_barrierLeaf]
        exact hbar
      · exact absurd c.isLt (by omega)

/-- The canonical T5 leaf of an admissible parameter record holds at its own extraction
parameter. -/
theorem seedBound_holdsAt (P : ExactTargetPlan.ConstructorParams d)
    (hP : P.Admissible) : (ExactTargetPlan.seedBound P).HoldsAt P.p0 := by
  show 1 - P.delta < (siteBernoulli (fun _ : Site d => P.p0)).real
    (ExactTargetPlan.seedEvent
      (fun i : Fin P.k => ExactTargetPlan.canonicalSeedBlock (d := d) P.seedCard i))
  rw [FreshLeafTransport.real_seedEvent_eq P.p0
    (fun i : Fin P.k => ExactTargetPlan.canonicalSeedBlock (d := d) P.seedCard i) P.seedCard
    (fun i j hij => ExactTargetPlan.disjoint_canonicalSeedBlock (d := d) P.seedCard i j hij)
    (fun i => ExactTargetPlan.card_canonicalSeedBlock (d := d) P.seedCard i)]
  linarith [hP.seed_valid]

/-- The canonical T6 leaf of an admissible parameter record holds at its own extraction
parameter. -/
theorem barrierBound_holdsAt (P : ExactTargetPlan.ConstructorParams d)
    (hP : P.Admissible) : (ExactTargetPlan.barrierBound P).HoldsAt P.p0 := by
  show P.barrierLower < (siteBernoulli (fun _ : Site d => P.p0)).real
    (ExactTargetPlan.barrierEvent (ExactTargetPlan.canonicalSupport (d := d) (2 * d * P.N)))
  rw [FreshLeafTransport.real_barrierEvent_eq_of_card P.p0 _ (2 * d * P.N)
    (ExactTargetPlan.card_canonicalSupport (d := d) (2 * d * P.N))]
  exact hP.barrier_valid

end BuildPlan

/-! ## §3.  Exact homogeneous translation invariance of the two hit cylinders -/

section Translation

variable [NeZero d]

/-- A quarter-face hit cylinder is the exact translate of the one based at the origin, so its
probability does not depend on the relay point. -/
theorem prob_quarterHit_eq (q : unitInterval) (v : Site d) (n m : Nat)
    (aTau : FaceIndex d) :
    (siteBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (shiftedOwner n v) (siteBoxAt v m)
          (shiftedTarget n v aTau)) =
      (siteBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (box d n) (box d m)
          (orthantFace aTau.1 aTau.2 n)) := by
  have hshift := ExactLongBoxHitBridge.VariableBridge.shift_hitEvent v (box d n) (box d m)
    (orthantFace aTau.1 aTau.2 n)
  rw [ExactTargetHits.shiftFinset_box_eq_siteBoxAt v m] at hshift
  have hev : ExactTargetPlan.hitEvent (shiftedOwner n v) (siteBoxAt v m)
      (shiftedTarget n v aTau) =
      siteShift v ⁻¹' ExactTargetPlan.hitEvent (box d n) (box d m)
        (orthantFace aTau.1 aTau.2 n) := hshift
  rw [hev]
  exact TargetAwareLattice.prob_shift_preimage q v
    (ReinforcedHit.measurableSet_hitEvent _ _ _)

/-- Two quarter-face hit cylinders at different relay points have the same probability. -/
theorem prob_quarterHit_eq_zero (q : unitInterval) (v : Site d) (n m : Nat)
    (aTau : FaceIndex d) :
    (siteBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (shiftedOwner n v) (siteBoxAt v m)
          (shiftedTarget n v aTau)) =
      (siteBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (shiftedOwner n (0 : Site d)) (siteBoxAt (0 : Site d) m)
          (shiftedTarget n (0 : Site d) aTau)) := by
  rw [prob_quarterHit_eq q v n m aTau, prob_quarterHit_eq q (0 : Site d) n m aTau]

/-- An aspect-`A` long-box hit cylinder is the exact translate of the one based at the origin. -/
theorem prob_outerHit_eq (q : unitInterval) (v : Site d) {l : Int} (hl : 0 ≤ l)
    (axis : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {A : Nat} (hA : 1 ≤ A) (m : Nat) :
    (siteBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (CorrMove.longBox v l axis sigma (A : Int)) (siteBoxAt v m)
          (CorrMove.longFace v l axis sigma (A : Int))) =
      (siteBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (CorrMove.longBox (0 : Site d) l axis sigma (A : Int))
          (siteBoxAt (0 : Site d) m)
          (CorrMove.longFace (0 : Site d) l axis sigma (A : Int))) := by
  have hshift := ExactLongBoxHitBridge.VariableBridge.shift_hitEvent v
    (CorrMove.longBox (0 : Site d) l axis sigma (A : Int)) (siteBoxAt (0 : Site d) m)
    (CorrMove.longFace (0 : Site d) l axis sigma (A : Int))
  rw [ExactLongBoxHitBridge.VariableBridge.shift_longBox v hl axis hsigma hA,
    ExactLongBoxHitBridge.VariableBridge.shift_siteBoxAt_zero v m,
    ExactLongBoxHitBridge.VariableBridge.shift_longFace v hl axis hsigma hA] at hshift
  rw [hshift]
  exact TargetAwareLattice.prob_shift_preimage q v
    (ReinforcedHit.measurableSet_hitEvent _ _ _)

end Translation

/-! ## §4.  The chosen local scale is confined by the plan's own active box

Neither instantiation records a bound on the scale it selects.  It is, however, forced: the
selected owner cube, resp. long box, is contained in the instantiation's active box, and the
active boxes used by the macro step are integer boxes of explicitly bounded diameter. -/

section ScaleBound

variable [NeZero d]

/-- The first coordinate axis, which exists because `d` is nonzero. -/
def axis0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩

/-- **The orthant scale is at most the diameter of the active cube.**  The selected owner cube of
radius `targetRadius v` about `v` lies in the active box; if the latter lies in a cube of radius
`M`, then `targetRadius v ≤ 2 M`. -/
theorem targetRadius_le {p0 : unitInterval} {epsilon : Real}
    {S : ExactTargetScheme.OrthantScheme d p0 epsilon}
    (I : ExactTargetScheme.OrthantInstantiation S) (c : Site d) (M : Int)
    (hM : I.activeBox.sites ⊆ CorrMove.cube c M)
    (v : ((I.sourceBox.inflate I.radius).sites)) :
    ((I.targetRadius v : Nat) : Int) ≤ 2 * M := by
  have hsub : CorrMove.cube v.1 ((I.targetRadius v : Nat) : Int) ⊆ CorrMove.cube c M := by
    have h := (I.owner_subset_active v).trans hM
    rwa [shiftedOwner, shiftFinset_box_eq_cube] at h
  have hn0 : (0 : Int) ≤ ((I.targetRadius v : Nat) : Int) := Int.natCast_nonneg _
  have hv : v.1 ∈ CorrMove.cube c M := hsub (CorrMove.centre_mem_cube hn0)
  have hxmem : (fun a => v.1 a + ((I.targetRadius v : Nat) : Int)) ∈
      CorrMove.cube v.1 ((I.targetRadius v : Nat) : Int) := by
    rw [CorrMove.mem_cube]
    intro a
    have hval : |v.1 a + ((I.targetRadius v : Nat) : Int) - v.1 a| =
        ((I.targetRadius v : Nat) : Int) := by
      rw [show v.1 a + ((I.targetRadius v : Nat) : Int) - v.1 a =
        ((I.targetRadius v : Nat) : Int) from by ring]
      exact abs_of_nonneg hn0
    show |v.1 a + ((I.targetRadius v : Nat) : Int) - v.1 a| ≤
      ((I.targetRadius v : Nat) : Int)
    exact le_of_eq hval
  have h2 : |v.1 (axis0 (d := d)) + ((I.targetRadius v : Nat) : Int) -
      c (axis0 (d := d))| ≤ M := by
    have h := (CorrMove.mem_cube.1 (hsub hxmem)) (axis0 (d := d))
    simpa using h
  have h1 : |v.1 (axis0 (d := d)) - c (axis0 (d := d))| ≤ M :=
    (CorrMove.mem_cube.1 hv) (axis0 (d := d))
  rw [abs_le] at h1 h2
  omega

/-- **The rank-one aspect-`A` scale is at most the diameter of the active box.**  The selected
long box about `v` lies in the active box, and it reaches signed axial coordinate `l`. -/
theorem choice_l_le {p0 : unitInterval} {alpha : Real} {A R : Nat}
    {F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A}
    {N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F)}
    {axis : Fin d} {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1) (hA : 1 ≤ A)
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (c : Site d) (M : Int) (hM : I.activeBox.sites ⊆ CorrMove.cube c M)
    (v : ((I.sourceBox.inflate R).sites)) :
    (I.choice v).l ≤ 2 * M := by
  have hl0 : (0 : Int) ≤ (I.choice v).l := I.choice_nonneg v
  have hA' : (1 : Int) ≤ (A : Int) := by exact_mod_cast hA
  have hAl : (I.choice v).l ≤ (A : Int) * (I.choice v).l :=
    le_mul_of_one_le_left hl0 hA'
  have hsub : CorrMove.longBox v.1 (I.choice v).l axis sigma A ⊆ CorrMove.cube c M :=
    (I.choice v).region_subset.trans hM
  have hvmem : v.1 ∈ CorrMove.longBox v.1 (I.choice v).l axis sigma A := by
    rw [CorrMove.mem_longBox hsigma hl0 hA']
    have hz : sigma * (v.1 axis - v.1 axis) = 0 := by ring
    refine ⟨⟨by rw [hz]; omega, by rw [hz]; omega⟩, fun j _ => ?_⟩
    have hzj : v.1 j - v.1 j = 0 := by ring
    rw [hzj, abs_zero]
    exact hl0
  set x : Site d := v.1 + Pi.single axis (sigma * (I.choice v).l) with hxdef
  have hxaxis : x axis = v.1 axis + sigma * (I.choice v).l := by
    simp [hxdef]
  have hxoff : ∀ j : Fin d, j ≠ axis → x j = v.1 j := by
    intro j hj
    simp [hxdef, Pi.single_eq_of_ne hj]
  have hxmem : x ∈ CorrMove.longBox v.1 (I.choice v).l axis sigma A := by
    rw [CorrMove.mem_longBox hsigma hl0 hA']
    have hsq : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
    have hax : sigma * (x axis - v.1 axis) = (I.choice v).l := by
      rw [hxaxis,
        show v.1 axis + sigma * (I.choice v).l - v.1 axis = sigma * (I.choice v).l from by ring,
        ← mul_assoc, hsq, one_mul]
    refine ⟨⟨by rw [hax]; omega, by rw [hax]; omega⟩, fun j hj => ?_⟩
    rw [hxoff j hj, show v.1 j - v.1 j = 0 from by ring, abs_zero]
    exact hl0
  have h1 : |v.1 axis - c axis| ≤ M := (CorrMove.mem_cube.1 (hsub hvmem)) axis
  have h2 : |x axis - c axis| ≤ M := (CorrMove.mem_cube.1 (hsub hxmem)) axis
  have hval : x axis - c axis = (v.1 axis - c axis) + sigma * (I.choice v).l := by
    rw [hxaxis]
    ring
  rw [hval, abs_le] at h2
  rw [abs_le] at h1
  rcases hsigma with rfl | rfl
  · omega
  · omega

end ScaleBound

/-! ## §5.  The frozen quarter schemes are stable at every macro centre and axis

The only non-canonical leaves of `ExactQuarterPlanExtraction.crossPlan` are its quarter-face hit
leaves, and each of those is the translate to its relay point of the centred prototype at the
selected local scale.  Because the selected scale is confined to the plan's own active cube, only
`10 r + 1` prototype scales can ever occur, whatever the macro centre. -/

section Quarter

variable [NeZero d]

open ExactQuarterPlanExtraction

/-- The centred quarter-face prototype cylinder: source radius `m`, local scale `n`, oriented
face `aTau`, based at the origin. -/
def quarterProtoExperiment (m n : Nat) (aTau : FaceIndex d) : CylinderExperiment d where
  support := shiftedOwner n (0 : Site d)
  event := ExactTargetPlan.hitEvent (shiftedOwner n (0 : Site d)) (siteBoxAt (0 : Site d) m)
    (shiftedTarget n (0 : Site d) aTau)
  determined := by
    unfold ExactTargetPlan.hitEvent
    exact DeterminedBy.iUnion fun x => DeterminedBy.iUnion fun _ =>
      determinedBy_connWithinSet (zdGraph d)
        (↑(shiftedOwner n (0 : Site d)) : Set (Site d)) x
        (↑(shiftedTarget n (0 : Site d) aTau) : Set (Site d))
  measurable' := ReinforcedHit.measurableSet_hitEvent _ _ _

/-- The centred quarter-face prototype as a stored estimate with the plan's own threshold. -/
def quarterProtoBound {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon) (n : Nat) (aTau : FaceIndex d) : ProbabilityBound d where
  experiment := quarterProtoExperiment (S.scales.source + 1) n aTau
  lower := 1 - etaOf epsilon

/-- Every centred quarter prototype above the frozen local radius holds at `p0`; this is the
frozen scheme's own oriented quarter-face estimate, with no new probability input. -/
theorem quarterProtoBound_holdsAt_p0 {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon) {n : Nat} (hn : S.scales.localRadius ≤ n)
    (aTau : FaceIndex d) : (quarterProtoBound S n aTau).HoldsAt p0 :=
  ExactTargetHits.one_sub_lt_prob_hitEvent_mono_source S.scales (S.scales.source + 1) n
    (by omega) hn (0 : Site d) aTau

/-- The numerical parameter record of every cross-section call of one frozen scheme; it depends
on the macro centre through nothing at all. -/
def quarterParams {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon) (R : Nat) : ExactTargetPlan.ConstructorParams d where
  p0 := p0
  epsilon := epsilon
  m := S.scales.source + 1
  k := S.numbers.k
  N := S.numbers.N
  L := S.numbers.L
  radius := R
  barrierLower := S.numbers.barrierLower

theorem params_crossInstantiation {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    S.params (crossInstantiation S c r R i hR0 hlocal hscale) = quarterParams S R := rfl

theorem quarterParams_admissible {p0 : unitInterval} (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    (quarterParams S R).Admissible :=
  S.params_admissible hp0 hp1 he0 he1
    (crossInstantiation S (0 : Site d) r R i hR0 hlocal hscale)

/-- **One cross-section plan is valid at `q` as soon as the centred prototypes are.**  The macro
centre `c` is arbitrary: it enters only through which prototype scale each relay point selects,
and that scale is confined to `[localRadius, 10 r]`. -/
theorem crossPlan_validAt_of_proto {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon) (c : Site d) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r)
    {q : unitInterval} (hq0 : 0 < (q : Real)) (hqp : (q : Real) ≤ (p0 : Real))
    (hproto : ∀ n (aTau : FaceIndex d), S.scales.localRadius ≤ n → n ≤ 10 * r →
      (quarterProtoBound S n aTau).HoldsAt q)
    (hseed : (ExactTargetPlan.seedBound (quarterParams S R)).HoldsAt q)
    (hbar : (ExactTargetPlan.barrierBound (quarterParams S R)).HoldsAt q) :
    (crossPlan S c r R i hR0 hlocal hscale).ValidAt q := by
  set I := crossInstantiation S c r R i hR0 hlocal hscale with hIdef
  show (ExactTargetPlan.buildPlan (S.params I) (S.concreteTarget I)
    (S.concreteHits I)).ValidAt q
  refine buildPlan_validAt_of _ _ _ hq0 hqp ?_ hseed hbar
  intro v
  let w : ((I.sourceBox.inflate I.radius).sites) := v
  have hM : I.activeBox.sites ⊆ CorrMove.cube c (5 * (r : Int)) := fun x hx => hx
  have hhi : I.targetRadius w ≤ 10 * r := by
    have h := targetRadius_le I c (5 * (r : Int)) hM w
    omega
  have hlo : S.scales.localRadius ≤ I.targetRadius w := I.localRadius_le w
  have hp := hproto (I.targetRadius w) (I.targetFace w) hlo hhi
  show (1 - etaOf epsilon) < (siteBernoulli (fun _ : Site d => q)).real
    (ExactTargetPlan.hitEvent (shiftedOwner (I.targetRadius w) w.1)
      (siteBoxAt w.1 (S.scales.source + 1))
      (shiftedTarget (I.targetRadius w) w.1 (I.targetFace w)))
  rw [prob_quarterHit_eq_zero q w.1 (I.targetRadius w) (S.scales.source + 1) (I.targetFace w)]
  exact hp

/-- The finite prototype family of one frozen quarter scheme at macro scale `r`: the
`10 r + 1` admissible centred quarter cylinders, plus the two canonical leaves. -/
def quarterFamily {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon) (r R : Nat) :
    ((Fin (10 * r + 1) × FaceIndex d) ⊕ Fin 2) → ProbabilityBound d
  | Sum.inl j => quarterProtoBound S (S.scales.localRadius + j.1.val) j.2
  | Sum.inr j =>
      if j = 0 then ExactTargetPlan.seedBound (quarterParams S R)
      else ExactTargetPlan.barrierBound (quarterParams S R)

theorem quarterFamily_holdsAt_p0 {p0 : unitInterval} (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon) (r R : Nat) (i : Fin d)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    ∀ j, (quarterFamily S r R j).HoldsAt p0 := by
  have hadm := quarterParams_admissible hp0 hp1 he0 he1 S r R i hR0 hlocal hscale
  rintro (j | j)
  · exact quarterProtoBound_holdsAt_p0 S (by omega) j.2
  · show (if j = 0 then ExactTargetPlan.seedBound (quarterParams S R)
      else ExactTargetPlan.barrierBound (quarterParams S R)).HoldsAt p0
    split
    · exact seedBound_holdsAt (quarterParams S R) hadm
    · exact barrierBound_holdsAt (quarterParams S R) hadm

/-- **One left neighbourhood of `p0` serves every macro centre and every finite axis.**  The
radius is read off the finitely many centred prototypes of the `d` frozen schemes, so it is fixed
before any macro centre is named. -/
theorem exists_left_nhds_quarter {p0 : unitInterval} (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) {eps : Fin d → Real} (he0 : ∀ i, 0 < eps i) (he1 : ∀ i, eps i ≤ 1)
    (S : ∀ i : Fin d, ExactTargetScheme.OrthantScheme d p0 (eps i)) (r R : Nat)
    (hR0 : ∀ i, (S i).numbers.R0 ≤ R) (hlocal : ∀ i, (S i).scales.localRadius < R)
    (hscale : 100 * (d + 1) * (R + 1) < r) :
    ∃ ε : Real, 0 < ε ∧ ∀ q : unitInterval, 0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
      |(q : Real) - (p0 : Real)| < ε → ∀ (c : Site d) (i : Fin d),
        (crossPlan (S i) c r R i (hR0 i) (hlocal i) hscale).ValidAt q := by
  obtain ⟨ε, hε, hall⟩ := exists_left_nhds_of_finite
    (fun j : Fin d × ((Fin (10 * r + 1) × FaceIndex d) ⊕ Fin 2) =>
      quarterFamily (S j.1) r R j.2)
    (fun j => quarterFamily_holdsAt_p0 hp0 hp1 (he0 j.1) (he1 j.1) (S j.1) r R j.1
      (hR0 j.1) (hlocal j.1) hscale j.2)
  refine ⟨ε, hε, ?_⟩
  intro q hq0 hqp hdist c i
  refine crossPlan_validAt_of_proto (S i) c r R i (hR0 i) (hlocal i) hscale hq0 hqp ?_ ?_ ?_
  · intro n aTau hlo hhi
    have hj : n - (S i).scales.localRadius < 10 * r + 1 := by omega
    have h : (quarterProtoBound (S i)
        ((S i).scales.localRadius + (n - (S i).scales.localRadius)) aTau).HoldsAt q :=
      hall q hdist (i, Sum.inl (⟨n - (S i).scales.localRadius, hj⟩, aTau))
    rwa [show (S i).scales.localRadius + (n - (S i).scales.localRadius) = n by omega] at h
  · have h : (if (0 : Fin 2) = 0 then ExactTargetPlan.seedBound (quarterParams (S i) R)
        else ExactTargetPlan.barrierBound (quarterParams (S i) R)).HoldsAt q :=
      hall q hdist (i, Sum.inr 0)
    rwa [if_pos rfl] at h
  · have h : (if (1 : Fin 2) = 0 then ExactTargetPlan.seedBound (quarterParams (S i) R)
        else ExactTargetPlan.barrierBound (quarterParams (S i) R)).HoldsAt q :=
      hall q hdist (i, Sum.inr 1)
    rwa [if_neg (by decide)] at h

end Quarter

/-! ## §6.  The frozen aspect-`A` rank-one plan is stable at every source box

The rank-one constructor of `ExactLongBoxHitBridge` fills its `T4` table with translates of the
*centred* long-box cylinder of the frozen scheme family.  Once again the selected long scale is
confined by the plan's own active box, so only finitely many centred prototypes occur. -/

section OuterRankOne

variable [NeZero d]

open ExactLongBoxHitBridge ExactLongBoxHitBridge.RankOne

/-- The centred aspect-`A` long-box prototype cylinder at long scale `l`. -/
def outerProtoExperiment (m : Nat) (l : Int) (axis : Fin d) (sigma : Int) (A : Nat) :
    CylinderExperiment d where
  support := CorrMove.longBox (0 : Site d) l axis sigma (A : Int)
  event := ExactTargetPlan.hitEvent (CorrMove.longBox (0 : Site d) l axis sigma (A : Int))
    (siteBoxAt (0 : Site d) m) (CorrMove.longFace (0 : Site d) l axis sigma (A : Int))
  determined := by
    unfold ExactTargetPlan.hitEvent
    exact DeterminedBy.iUnion fun x => DeterminedBy.iUnion fun _ =>
      determinedBy_connWithinSet (zdGraph d)
        (↑(CorrMove.longBox (0 : Site d) l axis sigma (A : Int)) : Set (Site d)) x
        (↑(CorrMove.longFace (0 : Site d) l axis sigma (A : Int)) : Set (Site d))
  measurable' := ReinforcedHit.measurableSet_hitEvent _ _ _

/-- The centred aspect-`A` prototype as a stored estimate with the plan's own threshold. -/
def outerProtoBound (alpha : Real) (m : Nat) (l : Int) (axis : Fin d) (sigma : Int) (A : Nat) :
    ProbabilityBound d where
  experiment := outerProtoExperiment m l axis sigma A
  lower := 1 - etaOf alpha

theorem etaOf_pos {alpha : Real} (ha0 : 0 < alpha) : 0 < etaOf alpha := by
  unfold etaOf deltaOf deltaCOf
  positivity

theorem etaOf_le_one {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) : etaOf alpha ≤ 1 := by
  unfold etaOf deltaOf deltaCOf
  have hd0 : 0 ≤ alpha ^ 2 / 64 := by positivity
  have hd1 : alpha ^ 2 / 64 ≤ 1 := by nlinarith [sq_nonneg alpha]
  have hdc0 : 0 ≤ alpha / 4 := by positivity
  have hdc1 : alpha / 4 ≤ 1 := by linarith
  have hd2 : (alpha ^ 2 / 64) ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1
  nlinarith [mul_le_mul hd2 hdc1 hdc0 (by positivity : (0 : Real) ≤ 1)]

/-- Every centred aspect-`A` prototype above the frozen scale threshold holds at `p0`.  This is
the frozen long-box chain's own centred estimate; no new probability input occurs. -/
theorem outerProtoBound_holdsAt_p0 {p0 : unitInterval} (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (axis : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (L : Nat) (hL : 8 * scaleThreshold F ≤ L) :
    (outerProtoBound alpha (sourceRadius F) (L : Int) axis sigma A).HoldsAt p0 := by
  have hsc : 3 * A + 3 * A * F.radius + sourceRadius F + 8 ≤ L / 8 := by
    unfold scaleThreshold at hL
    omega
  have hc := ExactLongBoxHitBridge.VariableBridge.centered_hit hp0 hp1 F hA
    (etaOf_pos ha0) (etaOf_le_one ha0 ha1) axis sigma hsigma
    (sourceRadius F) (L / 8) (L % 8) (by unfold sourceRadius; omega) (by omega) hsc
  have hnat : LongBoxVariable.longScale (L / 8) (L % 8) = L := by
    unfold LongBoxVariable.longScale
    omega
  rw [hnat] at hc
  show 1 - etaOf alpha < (siteBernoulli (fun _ : Site d => p0)).real
    (ExactTargetPlan.hitEvent (CorrMove.longBox (0 : Site d) (L : Int) axis sigma (A : Int))
      (siteBoxAt (0 : Site d) (sourceRadius F))
      (CorrMove.longFace (0 : Site d) (L : Int) axis sigma (A : Int)))
  simpa only [siteBernoulli] using hc

/-- **One rank-one plan is valid at `q` as soon as the centred prototypes are.**  The source box
of the instantiation is arbitrary: it enters only through which prototype long scale each relay
point selects, and that scale is confined to `[R, 2 M]`. -/
theorem rankOneBuildPlan_validAt_of_proto
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R)
    (I : Instantiation F N R axis sigma) (c : Site d) (M : Nat)
    (hM : I.activeBox.sites ⊆ CorrMove.cube c (M : Int))
    {q : unitInterval} (hq0 : 0 < (q : Real)) (hqp : (q : Real) ≤ (p0 : Real))
    (hproto : ∀ L : Nat, R ≤ L → L ≤ 2 * M →
      (outerProtoBound alpha (sourceRadius F) (L : Int) axis sigma A).HoldsAt q)
    (hseed : (ExactTargetPlan.seedBound (params F N R)).HoldsAt q)
    (hbar : (ExactTargetPlan.barrierBound (params F N R)).HoldsAt q) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).ValidAt q := by
  show (ExactTargetPlan.buildPlan (params F N R) (concreteTarget hA hsigma I)
    (concreteHits hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I)).ValidAt q
  refine buildPlan_validAt_of _ _ _ hq0 hqp ?_ hseed hbar
  intro v
  let w : ((I.sourceBox.inflate R).sites) := v
  have hl0 : (0 : Int) ≤ (I.choice w).l := I.choice_nonneg w
  have hlR : (R : Int) ≤ (I.choice w).l := (I.choice w).radius_le
  have hlM : (I.choice w).l ≤ 2 * (M : Int) := choice_l_le hsigma hA I c (M : Int) hM w
  have hLcast : ((((I.choice w).l).toNat : Nat) : Int) = (I.choice w).l :=
    Int.toNat_of_nonneg hl0
  have hLR : R ≤ ((I.choice w).l).toNat := by omega
  have hLM : ((I.choice w).l).toNat ≤ 2 * M := by omega
  show (1 - etaOf alpha) < (siteBernoulli (fun _ : Site d => q)).real
    (ExactTargetPlan.hitEvent (CorrMove.longBox w.1 (I.choice w).l axis sigma (A : Int))
      (siteBoxAt w.1 (sourceRadius F))
      (CorrMove.longFace w.1 (I.choice w).l axis sigma (A : Int)))
  rw [prob_outerHit_eq q w.1 hl0 axis hsigma hA (sourceRadius F), ← hLcast]
  exact hproto ((I.choice w).l).toNat hLR hLM

/-- The finite prototype family of one frozen aspect-`A` scheme family: the `2 M + 1` admissible
centred long-box cylinders in each of the `2 d` orientations, plus the two canonical leaves. -/
def outerFamily {p0 : unitInterval} {alpha : Real} {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha (sourceRadius F)) (R M : Nat) :
    ((((Fin d × Bool) × Fin (2 * M + 1))) ⊕ Fin 2) → ProbabilityBound d
  | Sum.inl j =>
      outerProtoBound alpha (sourceRadius F) ((R + j.2.val : Nat) : Int) j.1.1
        (if j.1.2 then (1 : Int) else -1) A
  | Sum.inr j =>
      if j = 0 then ExactTargetPlan.seedBound (params F N R)
      else ExactTargetPlan.barrierBound (params F N R)

theorem outerFamily_holdsAt_p0 {p0 : unitInterval} (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha (sourceRadius F)) (R M : Nat)
    (hRN : N.R0 ≤ R) (hlarge : 8 * scaleThreshold F ≤ R) :
    ∀ j, (outerFamily F N R M j).HoldsAt p0 := by
  have hadm := params_admissible hp0 hp1 ha0 ha1 F N R hRN
  rintro (j | j)
  · refine outerProtoBound_holdsAt_p0 hp0 hp1 ha0 ha1 hA F j.1.1 ?_ (R + j.2.val) (by omega)
    by_cases hb : j.1.2
    · left
      simp [hb]
    · right
      simp [hb]
  · show (if j = 0 then ExactTargetPlan.seedBound (params F N R)
      else ExactTargetPlan.barrierBound (params F N R)).HoldsAt p0
    split
    · exact seedBound_holdsAt (params F N R) hadm
    · exact barrierBound_holdsAt (params F N R) hadm

/-- **One left neighbourhood of `p0` serves every aspect-`A` rank-one placement.**  The radius is
read off the finitely many centred prototypes of the frozen family, in the finitely many
orientations, before any source box is named. -/
theorem exists_left_nhds_rankOne {p0 : unitInterval} (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha (sourceRadius F))
    (hRN : N.R0 ≤ R) (hlarge : 8 * scaleThreshold F ≤ R) (M : Nat) :
    ∃ ε : Real, 0 < ε ∧ ∀ q : unitInterval, 0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
      |(q : Real) - (p0 : Real)| < ε →
      ∀ (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
        (I : Instantiation F N R axis sigma) (c : Site d),
        I.activeBox.sites ⊆ CorrMove.cube c (M : Int) →
        (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).ValidAt q := by
  obtain ⟨ε, hε, hall⟩ := exists_left_nhds_of_finite (outerFamily F N R M)
    (outerFamily_holdsAt_p0 hp0 hp1 ha0 ha1 hA F N R M hRN hlarge)
  refine ⟨ε, hε, ?_⟩
  intro q hq0 hqp hdist axis sigma hsigma I c hM
  refine rankOneBuildPlan_validAt_of_proto hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge
    I c M hM hq0 hqp ?_ ?_ ?_
  · intro L hLR hLM
    have hj : L - R < 2 * M + 1 := by omega
    rcases hsigma with rfl | rfl
    · have h : (outerProtoBound alpha (sourceRadius F) ((R + (L - R) : Nat) : Int) axis
          (if (true : Bool) then (1 : Int) else -1) A).HoldsAt q :=
        hall q hdist (Sum.inl ((axis, true), ⟨L - R, hj⟩))
      simp only [if_pos] at h
      rwa [show R + (L - R) = L by omega] at h
    · have h : (outerProtoBound alpha (sourceRadius F) ((R + (L - R) : Nat) : Int) axis
          (if (false : Bool) then (1 : Int) else -1) A).HoldsAt q :=
        hall q hdist (Sum.inl ((axis, false), ⟨L - R, hj⟩))
      simp only [Bool.false_eq_true, if_false] at h
      rwa [show R + (L - R) = L by omega] at h
  · have h : (if (0 : Fin 2) = 0 then ExactTargetPlan.seedBound (params F N R)
        else ExactTargetPlan.barrierBound (params F N R)).HoldsAt q := hall q hdist (Sum.inr 0)
    rwa [if_pos rfl] at h
  · have h : (if (1 : Fin 2) = 0 then ExactTargetPlan.seedBound (params F N R)
        else ExactTargetPlan.barrierBound (params F N R)).HoldsAt q := hall q hdist (Sum.inr 1)
    rwa [if_neg (by decide)] at h

end OuterRankOne

/-! ## §7.  The frozen aspect-`88` outer stage of `ExactMacroGeometry`

The outer stage is now built from *one* frozen aspect-`88` `OuterData`.  Its plan is the
transparent rank-one plan of `ExactLongBoxHitBridge`, so §6 applies verbatim and the resulting
`OuterStage` corridor is valid at the very same `q` as the quarter children. -/

section Outer88

variable [NeZero d]

open ExactLongBoxHitBridge.RankOne ExactOuterStageExtraction

/-- The frozen aspect-`88` outer data: one scheme family at the internal tolerance, its numerical
record, and one extraction radius admissible for both.  This is exactly the data chosen inside
`exists_outerLongPlan_of_thetaSite_pos`, kept transparent so that the plan it builds stays
readable. -/
structure OuterData (d : Nat) [NeZero d] (p0 : unitInterval) (rho : Real) where
  family : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf (rho / 16)) 88
  numbers : ExactTargetSchemeNumbers.Numbers d p0 (rho / 16) (sourceRadius family)
  radius : Nat
  one_le_radius : 1 ≤ radius
  radius_ge : numbers.R0 ≤ radius
  radius_large : 8 * scaleThreshold family ≤ radius

/-- Supercriticality at `p0` supplies the frozen aspect-`88` outer data.  No new probability
premise is used: this is the same extraction the outer-stage module already performs. -/
theorem exists_outerData_of_thetaSite_pos {p0 : unitInterval} (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0) {rho : Real}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 16) : Nonempty (OuterData d p0 rho) := by
  have ha0 : 0 < rho / 16 := by linarith
  have ha1 : rho / 16 ≤ 1 := by linarith
  obtain ⟨F⟩ := ExactLongBoxVariablePlan.exists_schemeFamily_of_thetaSite_pos
    p0 hp0 hp1 htheta (etaOf (rho / 16)) (etaOf_pos ha0) (etaOf_le_one ha0 ha1) 88 (by omega)
  obtain ⟨N⟩ := ExactTargetSchemeNumbers.exists_numbers (d := d) p0 hp0 hp1 (rho / 16) ha0 ha1
    (sourceRadius F) (by unfold sourceRadius; omega)
  exact ⟨{ family := F
           numbers := N
           radius := max 1 (max N.R0 (8 * scaleThreshold F))
           one_le_radius := le_max_left _ _
           radius_ge := le_trans (le_max_left _ _) (le_max_right _ _)
           radius_large := le_trans (le_max_right _ _) (le_max_right _ _) }⟩

omit [NeZero d] in
/-- The long slab `D'` sits in the cube of radius `22 r` about `c_z`; the bound depends on the
macro scale only, never on the macro centre. -/
theorem outerSlab_subset_cube {r : Nat} {z : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) :
    outerSlab (d := d) r z i sigma ⊆
      CorrMove.cube (MacroExp.ctr d r z) ((22 * r : Nat) : Int) := by
  intro x hx
  rw [outerSlab, CorrMove.mem_dbox hsigma] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  rw [CorrMove.mem_cube]
  intro j
  have hr : (0 : Int) ≤ (r : Int) := Int.natCast_nonneg r
  have hcast : ((22 * r : Nat) : Int) = 22 * (r : Int) := by push_cast; ring
  rw [hcast, abs_le]
  by_cases hj : j = i
  · subst hj
    rcases hsigma with rfl | rfl <;> omega
  · have h4 := h3 j hj
    rw [abs_le] at h4
    omega

/-- **The frozen aspect-`88` outer stage is valid at `q`.**  The plan is built from the frozen
`OuterData` alone, so its `T4` leaves are translates of the centred prototypes and §6 delivers
validity at `q`; the remaining `d` corridor stages are the quarter children. -/
theorem exists_outerStage_validAt
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {rho : Real} (ha0 : 0 < rho / 16) (ha1 : rho / 16 ≤ 1)
    (O : OuterData d p0 rho)
    {eta : Fin (d + 1) → Real} {r t : Nat} (h : ExactMacroGeometry.Tr d) (w z y : Site 2)
    (i : Fin d) (sigma : Int)
    (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0 (fun a : Fin d => eta a.succ)
      (MacroExp.ctr d r z) r)
    (hd : 2 ≤ d) (hr : 44 ≤ r) (ht : 5 * r ≤ t) (hwz : w ≠ z)
    (hRsmall : 200 * (O.radius + 1) ≤ r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hscale : Q.scale = r)
    (heta : ∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc)
    (hetaLast : eta (Fin.last d) = deltaOf (rho / 16))
    {q : unitInterval}
    (hquarter : ∀ a : Fin d, (Q.quarter a).ValidAt q)
    (houter : ∀ (axis : Fin d) (sig : Int) (hs : sig = 1 ∨ sig = -1)
        (I : Instantiation O.family O.numbers O.radius axis sig) (c : Site d),
        I.activeBox.sites ⊆ CorrMove.cube c ((22 * r : Nat) : Int) →
        (buildPlan hp0 hp1 ha0 ha1 (by omega : 1 ≤ 88) O.family O.numbers axis sig hs
          O.radius_large I).ValidAt q) :
    ∃ A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho,
      A.corridor.WellFormed ∧ A.corridor.ValidAt q ∧ A.plan.ValidAt q := by
  have hHr : sourceHalfWidth d Q.scale Q.radius = sourceHalfWidth d r Q.radius := by
    rw [hscale]
  have hH0 : 0 ≤ sourceHalfWidth d Q.scale Q.radius := by
    rw [hHr]
    unfold sourceHalfWidth
    positivity
  have hsepQ : 100 * (d + 1) * (Q.radius + 1) < r := by
    have hs := Q.separation
    rwa [hscale] at hs
  obtain ⟨h89, hRr⟩ := numeric_side_conditions (d := d) (R := O.radius) (radius := Q.radius)
    hr hsepQ hRsmall
  have hbox : (outerSlabBox (d := d) r z i sigma).sites = outerSlab (d := d) r z i sigma :=
    outerSlabBox_sites r z i hsigma
  have hTne : (CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int))).Nonempty :=
    CorrMove.cube_nonempty _ (by positivity)
  set I : Instantiation O.family O.numbers O.radius i sigma :=
    outerInstantiation (y := y) O.family O.numbers (outerSlabBox (d := d) r z i sigma)
      (CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)))
      hH0 hr O.one_le_radius hsigma hemb (by rw [hHr]; exact h89) (by rw [hHr]; exact hRr)
      (outerSlabBox_ordered r z i sigma) (by rw [hbox]) hTne
      (by rw [hbox]; exact cube_two_subset_outerSlab hsigma hemb)
      Finset.Subset.rfl with hIdef
  set C : ExactTargetPlan.Plan d :=
    buildPlan hp0 hp1 ha0 ha1 (by omega : 1 ≤ 88) O.family O.numbers i sigma hsigma
      O.radius_large I with hCdef
  have hMcube : I.activeBox.sites ⊆
      CorrMove.cube (MacroExp.ctr d r z) ((22 * r : Nat) : Int) := by
    have hact : I.activeBox.sites = outerSlab (d := d) r z i sigma := hbox
    rw [hact]
    exact outerSlab_subset_cube hsigma
  have hCvalid : C.ValidAt q := houter i sigma hsigma I (MacroExp.ctr d r z) hMcube
  have hspec : OuterLongPlanSpec p0 r O.radius z i sigma
      (sourceHalfWidth d Q.scale Q.radius) rho (outerSlabBox (d := d) r z i sigma)
      (CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int))) C :=
    { wellFormed := buildPlan_wellFormed hp0 hp1 ha0 ha1 (by omega : 1 ≤ 88) O.family O.numbers
        i sigma hsigma O.radius_ge O.radius_large I
      validAt := buildPlan_validAt hp0 hp1 ha0 ha1 (by omega : 1 ≤ 88) O.family O.numbers
        i sigma hsigma O.radius_ge O.radius_large I
      sourceBox_eq := rfl
      activeBox_eq := rfl
      target_eq := rfl
      radius_eq := rfl
      epsilon_eq := rfl }
  obtain ⟨A, hAplan, hwf, -⟩ :=
    exists_outerStage_of_spec (t := t) (h := h) (w := w) (rho := rho)
      (Dbox := outerSlabBox (d := d) r z i sigma) hd hr ht hwz O.one_le_radius hRsmall
      hsigma hemb hscale heta hetaLast (by rw [hbox])
      (by rw [hbox]; exact outerSlab_subset_narrowDom hd (by omega) ht h hwz y hsigma)
      (by rw [hbox]; exact outerSlab_subset_Q_union_E (by omega) ht hsigma hemb) hspec
  have hAvalid : A.plan.ValidAt q := by rw [hAplan]; exact hCvalid
  refine ⟨A, hwf, ?_, hAvalid⟩
  intro u
  refine Fin.lastCases ?_ (fun a => ?_) u
  · rw [A.corridor_stage, ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_last]
    exact hAvalid
  · rw [A.corridor_stage, ExactQuarterPlanExtraction.QuarterStageFamily.stagesWith_castSucc]
    exact hquarter a

/-! ## §8.  One `q < p0`, fixed before any macro history

Both left neighbourhoods are computed from frozen `p0` data alone -- the `d` quarter schemes and
the single aspect-`88` family -- so their minimum is a radius chosen before any macro centre,
head, or orientation is named. -/

/-- **The joint uniformity statement.**  One radius `ε` works simultaneously for
(1) every quarter plan at every macro centre and every finite axis, and
(2) the frozen aspect-`88` outer corridor of every actual oriented outgoing head. -/
theorem exists_left_nhds_quarter_outer
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {rho : Real} (ha0 : 0 < rho / 16) (ha1 : rho / 16 ≤ 1)
    (O : OuterData d p0 rho)
    {eta : Fin (d + 1) → Real} (he0 : ∀ a : Fin d, 0 < eta a.succ)
    (he1 : ∀ a : Fin d, eta a.succ ≤ 1)
    (S : ∀ a : Fin d, ExactTargetScheme.OrthantScheme d p0 (eta a.succ))
    (r t R : Nat) (hR0 : ∀ a, (S a).numbers.R0 ≤ R)
    (hlocal : ∀ a, (S a).scales.localRadius < R)
    (hd : 2 ≤ d) (hr : 44 ≤ r) (ht : 5 * r ≤ t)
    (hsep : 100 * (d + 1) * (R + 1) < r)
    (hRsmall : 200 * (O.radius + 1) ≤ r)
    (heta : ∀ a : Fin d, deltaOf (eta a.succ) = eta a.castSucc)
    (hetaLast : eta (Fin.last d) = deltaOf (rho / 16)) :
    ∃ ε : Real, 0 < ε ∧ ∀ q : unitInterval, 0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
      |(q : Real) - (p0 : Real)| < ε →
      (∀ (c : Site d) (a : Fin d),
        (ExactQuarterPlanExtraction.crossPlan (S a) c r R a (hR0 a) (hlocal a)
          hsep).ValidAt q) ∧
      ∀ (h : ExactMacroGeometry.Tr d) (w z y : Site 2) (i : Fin d) (sigma : Int)
        (Q : ExactQuarterPlanExtraction.QuarterStageFamily p0 (fun a : Fin d => eta a.succ)
          (MacroExp.ctr d r z) r),
        w ≠ z → (sigma = 1 ∨ sigma = -1) →
        ((MacroExp.emb (y - z) : Site d) = Pi.single i sigma) → Q.scale = r →
        (∀ a : Fin d, (Q.quarter a).ValidAt q) →
        ∃ A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho,
          A.corridor.WellFormed ∧ A.corridor.ValidAt q ∧ A.plan.ValidAt q := by
  obtain ⟨ε1, hε1, hqu⟩ := exists_left_nhds_quarter hp0 hp1 he0 he1 S r R hR0 hlocal hsep
  obtain ⟨ε2, hε2, hou⟩ := exists_left_nhds_rankOne hp0 hp1 ha0 ha1 (by omega : 1 ≤ 88)
    O.family O.numbers O.radius_ge O.radius_large (22 * r)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro q hq0 hqp hdist
  refine ⟨hqu q hq0 hqp (lt_of_lt_of_le hdist (min_le_left _ _)), ?_⟩
  intro h w z y i sigma Q hwz hsigma hemb hscale hquarter
  exact exists_outerStage_validAt hp0 hp1 ha0 ha1 O h w z y i sigma Q hd hr ht hwz hRsmall
    hsigma hemb hscale heta hetaLast hquarter
    (hou q hq0 hqp (lt_of_lt_of_le hdist (min_le_right _ _)))

/-- The frozen aspect-`88` outer data at the fixed v15 batch tolerance. -/
def frozenOuterData (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) : OuterData d p0 ExactMacroNumerics.rho :=
  Classical.choice (exists_outerData_of_thetaSite_pos hp0 hp1 htheta
    ExactMacroNumerics.rho_pos (by linarith [ExactMacroNumerics.rho_le_half]))

theorem quarterAt_quarter (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) (r : Nat) (z : Site 2)
    (hsep : 100 * (d + 1) * (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta + 1) < r)
    (a : Fin d) :
    (ExactMacroStepFromTheta.quarterAt p0 hp0 hp1 htheta r z hsep).quarter a =
      ExactQuarterPlanExtraction.crossPlan
        (ExactMacroStepFromTheta.frozenSchemes p0 hp0 hp1 htheta a)
        (MacroExp.ctr d r z) r (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta) a
        (ExactQuarterPlanExtraction.arithmeticRadius_le_commonRadius _ a)
        (ExactQuarterPlanExtraction.localRadius_lt_commonRadius _ a) hsep := rfl

/-- **The closing form.**  Positive percolation at `p0` and the standing v15 macro scales give one
`q < p0`, chosen before any macro history, at which every frozen quarter plan of every macro
centre and every frozen aspect-`88` outer corridor of every actual oriented outgoing head is
valid.  The two families are the ones `ExactMacroStepFromTheta` consumes. -/
theorem exists_stable_below (hd : 2 ≤ d) (p0 : unitInterval) (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0)
    (r t : Nat) (hr : 44 ≤ r) (ht : 5 * r ≤ t)
    (hsep : 100 * (d + 1) * (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta + 1) < r)
    (hRsmall : 200 * ((frozenOuterData p0 hp0 hp1 htheta).radius + 1) ≤ r) :
    ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p0 : Real) ∧
      (∀ (z : Site 2) (a : Fin d),
        ((ExactMacroStepFromTheta.quarterAt p0 hp0 hp1 htheta r z hsep).quarter a).ValidAt q) ∧
      ∀ (h : ExactMacroGeometry.Tr d) (w z y : Site 2) (i : Fin d) (sigma : Int),
        w ≠ z → (sigma = 1 ∨ sigma = -1) →
        ((MacroExp.emb (y - z) : Site d) = Pi.single i sigma) →
        ∃ A : ExactMacroGeometry.OuterStage p0 (ExactMacroNumerics.eta d) r t h w z
            (ExactMacroStepFromTheta.quarterAt p0 hp0 hp1 htheta r z hsep) y i sigma
            ExactMacroNumerics.rho,
          A.corridor.WellFormed ∧ A.corridor.ValidAt q ∧ A.plan.ValidAt q := by
  have hrho0 : 0 < ExactMacroNumerics.rho / 16 := by
    have := ExactMacroNumerics.rho_pos
    linarith
  have hrho1 : ExactMacroNumerics.rho / 16 ≤ 1 := by
    have := ExactMacroNumerics.rho_le_half
    linarith
  obtain ⟨ε, hε, hall⟩ := exists_left_nhds_quarter_outer hp0 hp1 hrho0 hrho1
    (frozenOuterData p0 hp0 hp1 htheta)
    (fun a => ExactMacroNumerics.eta_pos d a.succ)
    (fun a => ExactMacroNumerics.eta_le_one d a.succ)
    (ExactMacroStepFromTheta.frozenSchemes p0 hp0 hp1 htheta) r t
    (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta)
    (fun a => ExactQuarterPlanExtraction.arithmeticRadius_le_commonRadius _ a)
    (fun a => ExactQuarterPlanExtraction.localRadius_lt_commonRadius _ a)
    hd hr ht hsep hRsmall (ExactMacroNumerics.eta_step d) (ExactMacroNumerics.eta_last d)
  obtain ⟨q, hq0, hqlt, hqdist⟩ := exists_lt_of_left_nhds hp0 hε
  obtain ⟨hquarter, houter⟩ := hall q hq0 hqlt.le hqdist
  refine ⟨q, hq0, hqlt, ?_, ?_⟩
  · intro z a
    rw [quarterAt_quarter p0 hp0 hp1 htheta r z hsep a]
    exact hquarter (MacroExp.ctr d r z) a
  · intro h w z y i sigma hwz hsigma hemb
    refine houter h w z y i sigma _ hwz hsigma hemb rfl ?_
    intro a
    rw [quarterAt_quarter p0 hp0 hp1 htheta r z hsep a]
    exact hquarter (MacroExp.ctr d r z) a

/-! ## §9.  Nonvacuity

None of the finite families above is empty, the hit-leaf hypothesis of `buildPlan_validAt_of` is
not a vacuous quantification, the standing scale hypotheses are satisfiable, and the semantic
target split of the corridor is untouched: the outer plan lands in the radius-`2 r` cube, which is
the corridor's `innerTarget`, while the corridor's `outputCore` is the radius-`3 r` cube. -/

omit [NeZero d] in
theorem hitSite_nonempty (P : ExactTargetPlan.ConstructorParams d)
    (X : ExactTargetPlan.ConcreteTarget P) :
    Nonempty ((X.sourceBox.inflate P.radius).sites) := by
  obtain ⟨v, hv⟩ := ExactTargetPlan.IntBox.sites_nonempty
    (ExactTargetPlan.IntBox.inflate_ordered X.source_ordered P.radius)
  exact ⟨⟨v, hv⟩⟩

omit [NeZero d] in
theorem quarterFamily_index_nonempty (r : Nat) :
    Nonempty (((Fin (10 * r + 1) × FaceIndex d) ⊕ Fin 2)) := ⟨Sum.inr 0⟩

omit [NeZero d] in
theorem outerFamily_index_nonempty (M : Nat) :
    Nonempty ((((Fin d × Bool) × Fin (2 * M + 1))) ⊕ Fin 2) := ⟨Sum.inr 0⟩

omit [NeZero d] in
/-- The `2 r` / `3 r` split of `ExactCorridorPlan` is preserved verbatim. -/
theorem corridor_targets {p0 : unitInterval} {eta : Fin (d + 1) → Real} {r t : Nat}
    {h : ExactMacroGeometry.Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    {Q : ExactQuarterPlanExtraction.QuarterStageFamily p0 (fun a : Fin d => eta a.succ)
      (MacroExp.ctr d r z) r}
    (A : ExactMacroGeometry.OuterStage p0 eta r t h w z Q y i sigma rho) :
    A.plan.target = CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ∧
      A.corridor.innerTarget = CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ∧
      A.corridor.outputCore = CorrMove.cube (MacroExp.ctr d r y) (3 * (r : Int)) := by
  refine ⟨A.target_eq, ?_, ?_⟩
  · show CorrMove.cube (MacroExp.ctr d r y) (2 * ((Q.scale : Nat) : Int)) = _
    rw [A.scale_eq]
  · show CorrMove.cube (MacroExp.ctr d r y) (3 * ((Q.scale : Nat) : Int)) = _
    rw [A.scale_eq]

/-- **The standing scale hypotheses of `exists_stable_below` are satisfiable.**  One application
of `ExactMacroNumerics.exists_macro_scales` at the maximum of the two frozen extraction radii
supplies the depth `K ≥ 20`, the stopped scale `s`, the macro scale `r`, and the reveal radius
`t`, together with both frozen radius inequalities. -/
theorem exists_scales_for_stable_below (p0 : unitInterval) (hp0 : 0 < (p0 : Real))
    (hp1 : (p0 : Real) < 1) (htheta : 0 < thetaSite d p0) (L F R' : Nat) :
    ∃ K s r t : Nat, 20 ≤ K ∧ 0 < s ∧ 0 < r ∧ r = K * s ∧ 10 * s * K ≤ 10 * r ∧
      (1 - AtomTower.f (ExactMacroNumerics.deltaC d)) ^ K ≤ ExactMacroNumerics.rho / 16 ∧
      5 * r ≤ t ∧ 44 ≤ r ∧ 2 * R' ≤ s ∧
      100 * (d + 1) * (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta + 1) < r ∧
      200 * ((frozenOuterData p0 hp0 hp1 htheta).radius + 1) ≤ r := by
  classical
  set Rall : Nat :=
    max R' (max (ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta)
      ((frozenOuterData p0 hp0 hp1 htheta).radius)) with hRall
  obtain ⟨K, s, r, t, hK, hpow, hs, hr, hrEq, hsR, hb1, -, -, -, -, -, -, ht, hr44,
    hsep, houter⟩ := ExactMacroNumerics.exists_macro_scales d L F Rall
  have hq : ExactMacroStepFromTheta.quarterRadius p0 hp0 hp1 htheta ≤ Rall := by
    rw [hRall]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hoR : (frozenOuterData p0 hp0 hp1 htheta).radius ≤ Rall := by
    rw [hRall]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hR' : R' ≤ Rall := by
    rw [hRall]
    exact le_max_left _ _
  refine ⟨K, s, r, t, hK, hs, hr, hrEq, hb1, hpow, ht, hr44, ?_, ?_, ?_⟩
  · exact le_trans (Nat.mul_le_mul (le_refl 2) hR') hsR
  · exact lt_of_le_of_lt
      (Nat.mul_le_mul (le_refl (100 * (d + 1))) (by omega)) hsep
  · exact le_trans (Nat.mul_le_mul (le_refl 200) (by omega)) houter

end Outer88

end KNAll.Site.ExactQuarterOuterPrototypeStability

end

#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.exists_left_nhds_of_finite
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.buildPlan_validAt_of
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.prob_quarterHit_eq
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.prob_outerHit_eq
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.targetRadius_le
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.choice_l_le
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.exists_left_nhds_quarter
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.exists_left_nhds_rankOne
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.exists_outerData_of_thetaSite_pos
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.outerSlab_subset_cube
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.exists_outerStage_validAt
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.exists_left_nhds_quarter_outer
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.quarterAt_quarter
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.exists_stable_below
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.hitSite_nonempty
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.corridor_targets
#print axioms KNAll.Site.ExactQuarterOuterPrototypeStability.exists_scales_for_stable_below
