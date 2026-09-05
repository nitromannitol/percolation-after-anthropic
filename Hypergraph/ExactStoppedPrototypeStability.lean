import Hypergraph.ExactLongBoxTranslatedPlan
import Hypergraph.ExactTargetPlanStability
import Hypergraph.ExactMacroNumerics

/-!
# One left parameter for every translate of the stopped prototype

`ExactTargetPlanStability` gives a left stability radius for **one** exact target plan: its
finitely many leaf margins are Lipschitz in the homogeneous parameter, so all of them survive a
small enough shift.  The macro step, however, must fix a single `q < p0` *before* the head
`(z, y)` is known, and there are infinitely many heads.

The resolution is exact translation invariance.  Every stopped child at the head `(z, y)` with
orientation `(i, sigma)` is the literal translate, by `MacroExp.ctr d r z`, of the corresponding
child at the *prototype* head `(0, y - z)`.  Homogeneous product measure is invariant under
lattice translation, so a translated plan has exactly the same finite leaf table of real numbers
as its prototype.  Only the finitely many orientations `Fin d × Bool` and levels `Fin K` remain,
and a finite minimum of positive radii is positive.

## Contents

* `shiftFinset`, `shiftBox`, `shiftExperiment` : translation of the finite objects a plan is
  built from.  `shiftExperiment_prob` is the one probabilistic ingredient and is exactly
  `TargetAwareLattice.prob_shift_preimage`.
* `translate` : translation of an `ExactTargetPlan.Plan`.  `translate_wellFormed` transports
  (T1)--(T6), and `translate_validAt` transports the finite leaf table; the latter is an
  *equivalence*, since no probability changes.
* `protoPlan` : for each orientation `(i, b)` the prototype stopped family at the head
  `(0, protoDir h)`, `protoDir h` the canonical planar direction.
* `headPlan` : its translate by `MacroExp.ctr d r z`, with `headPlan_active`,
  `headPlan_source` and `headPlan_target` recovering the literal (G2) shapes at the actual
  head `(z, y)`, and `headPlan_validAt` inheriting validity from the prototype.
* `exists_uniform_stoppedChildren_of_thetaSite_pos` : the theorem.  One extraction radius `R` is
  frozen, then, at every admissible macro scale, one `q < p0` such that **every** stopped child
  at **every** head and level is `ValidAt q`.

No new probability assumption is made: the only extraction used is
`ExactLongBoxTranslatedPlan.exists_inputs_of_thetaSite_pos`, which is the frozen `F`/`N`/`R` of
`ExactStoppedChildrenExtraction.Concrete.exists_frozenPlanData_of_thetaSite_pos`.
-/

noncomputable section

namespace KNAll.Site.ExactStoppedPrototypeStability

set_option linter.unusedSectionVars false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-! ## §1.  Translation of finite sets, boxes and cylinder experiments -/

/-- Translation of a finite set of sites; the convention of `MoveWindowInput`. -/
abbrev shiftFinset (v : Site d) (S : Finset (Site d)) : Finset (Site d) :=
  MoveWindowInput.shiftFinset v S

theorem mem_shiftFinset {v x : Site d} {S : Finset (Site d)} :
    x ∈ shiftFinset v S ↔ x - v ∈ S := by
  simp only [shiftFinset, MoveWindowInput.shiftFinset, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - v, hx, by ring⟩

theorem shiftFinset_mono {v : Site d} {S T : Finset (Site d)} (h : S ⊆ T) :
    shiftFinset v S ⊆ shiftFinset v T := by
  intro x hx
  rw [mem_shiftFinset] at hx ⊢
  exact h hx

theorem shiftFinset_nonempty {v : Site d} {S : Finset (Site d)} (h : S.Nonempty) :
    (shiftFinset v S).Nonempty := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x + v, mem_shiftFinset.2 (by simpa using hx)⟩

theorem shiftFinset_card (v : Site d) (S : Finset (Site d)) :
    (shiftFinset v S).card = S.card :=
  Finset.card_image_of_injective S (add_left_injective v)

theorem shiftFinset_disjoint {v : Site d} {S T : Finset (Site d)}
    (h : Disjoint S T) : Disjoint (shiftFinset v S) (shiftFinset v T) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hx'
  rw [mem_shiftFinset] at hx hx'
  exact h hx hx'

theorem shiftFinset_biUnion {k : Nat} (v : Site d) (block : Fin k → Finset (Site d)) :
    shiftFinset v (Finset.univ.biUnion block) =
      Finset.univ.biUnion fun b => shiftFinset v (block b) := by
  ext x
  simp only [mem_shiftFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]

theorem shiftFinset_siteBoxAt (v c : Site d) (m : Nat) :
    shiftFinset v (siteBoxAt c m) = siteBoxAt (c + v) m := by
  ext x
  rw [mem_shiftFinset, mem_siteBoxAt, mem_siteBoxAt]
  refine forall_congr' fun j => ?_
  simp only [Pi.sub_apply, Pi.add_apply]
  omega

/-- Translation of an integer box. -/
def shiftBox (v : Site d) (B : ExactTargetPlan.IntBox d) : ExactTargetPlan.IntBox d where
  lower := fun j => B.lower j + v j
  upper := fun j => B.upper j + v j

theorem shiftBox_ordered {v : Site d} {B : ExactTargetPlan.IntBox d}
    (hB : B.Ordered) : (shiftBox v B).Ordered := by
  intro j
  have := hB j
  simp only [shiftBox]
  omega

theorem shiftBox_inflate (v : Site d) (B : ExactTargetPlan.IntBox d) (R : Nat) :
    (shiftBox v B).inflate R = shiftBox v (B.inflate R) := by
  simp only [shiftBox, ExactTargetPlan.IntBox.inflate,
    ExactTargetPlan.IntBox.mk.injEq]
  constructor <;> funext j <;> omega

theorem shiftBox_sites (v : Site d) (B : ExactTargetPlan.IntBox d) :
    (shiftBox v B).sites = shiftFinset v B.sites := by
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, mem_shiftFinset,
    ExactTargetPlan.IntBox.mem_sites]
  refine forall_congr' fun j => ?_
  simp only [shiftBox, Pi.sub_apply]
  omega

theorem shiftBox_inflate_sites (v : Site d) (B : ExactTargetPlan.IntBox d) (R : Nat) :
    ((shiftBox v B).inflate R).sites = shiftFinset v (B.inflate R).sites := by
  rw [shiftBox_inflate, shiftBox_sites]

/-- The inverse translation on the points of a translated inflated box. -/
def unshiftSite (v : Site d) (B : ExactTargetPlan.IntBox d) (R : Nat)
    (w : ((shiftBox v B).inflate R).sites) : (B.inflate R).sites :=
  ⟨w.1 - v, by
    have hw : (w.1 : Site d) ∈ ((shiftBox v B).inflate R).sites := w.2
    rw [ExactTargetPlan.IntBox.mem_sites] at hw
    rw [ExactTargetPlan.IntBox.mem_sites]
    intro j
    have hj := hw j
    simp only [shiftBox, ExactTargetPlan.IntBox.inflate, Pi.sub_apply] at hj ⊢
    omega⟩

@[simp] theorem unshiftSite_add (v : Site d) (B : ExactTargetPlan.IntBox d) (R : Nat)
    (w : ((shiftBox v B).inflate R).sites) : (unshiftSite v B R w).1 + v = w.1 := by
  simp only [unshiftSite]
  ring

/-- Translation of a cylinder experiment: the support moves by `+v`, the event by `siteShift v`.
Its probability at any homogeneous parameter is unchanged. -/
def shiftExperiment (v : Site d) (E : CylinderExperiment d) : CylinderExperiment d where
  support := shiftFinset v E.support
  event := siteShift v ⁻¹' E.event
  determined := by
    have h := LeftImp2.determinedBy_siteShift_preimage (d := d) v E.determined
    exact h
  measurable' := measurable_siteShift v E.measurable'

@[simp] theorem shiftExperiment_support (v : Site d) (E : CylinderExperiment d) :
    (shiftExperiment v E).support = shiftFinset v E.support := rfl

@[simp] theorem shiftExperiment_event (v : Site d) (E : CylinderExperiment d) :
    (shiftExperiment v E).event = siteShift v ⁻¹' E.event := rfl

/-- **Exact translation invariance of a finite cylinder probability.** -/
@[simp] theorem shiftExperiment_prob (v : Site d) (E : CylinderExperiment d)
    (q : unitInterval) : (shiftExperiment v E).prob q = E.prob q :=
  TargetAwareLattice.prob_shift_preimage q v E.measurable'

/-- Translation of a stored estimate: the threshold is untouched. -/
def shiftBound (v : Site d) (B : ProbabilityBound d) : ProbabilityBound d where
  experiment := shiftExperiment v B.experiment
  lower := B.lower

@[simp] theorem shiftBound_lower (v : Site d) (B : ProbabilityBound d) :
    (shiftBound v B).lower = B.lower := rfl

@[simp] theorem shiftBound_experiment (v : Site d) (B : ProbabilityBound d) :
    (shiftBound v B).experiment = shiftExperiment v B.experiment := rfl

theorem shiftBound_holdsAt_iff (v : Site d) (B : ProbabilityBound d) (q : unitInterval) :
    (shiftBound v B).HoldsAt q ↔ B.HoldsAt q := by
  unfold ProbabilityBound.HoldsAt
  rw [shiftBound_lower, shiftBound_experiment, shiftExperiment_prob]

/-- Translation of one entry of a plan's finite geometry table. -/
def shiftGeometry (v : Site d) (G : ExactTargetPlan.Geometry d) :
    ExactTargetPlan.Geometry d where
  centre := G.centre + v
  scale := G.scale
  region := shiftFinset v G.region
  face := shiftFinset v G.face

/-! ### The two canonical events -/

theorem siteShift_preimage_seedEvent {k : Nat} (v : Site d)
    (block : Fin k → Finset (Site d)) :
    siteShift v ⁻¹' ExactTargetPlan.seedEvent block =
      ExactTargetPlan.seedEvent fun b => shiftFinset v (block b) := by
  ext omega
  simp only [Set.mem_preimage, ExactTargetPlan.seedEvent, Set.mem_setOf_eq,
    Set.subset_def, Finset.mem_coe, mem_siteShift]
  refine exists_congr fun b => ?_
  constructor
  · intro h x hx
    rw [mem_shiftFinset] at hx
    have := h _ hx
    simpa using this
  · intro h x hx
    have := h (x + v) (mem_shiftFinset.2 (by simpa using hx))
    exact this

theorem siteShift_preimage_barrierEvent (v : Site d) (S : Finset (Site d)) :
    siteShift v ⁻¹' ExactTargetPlan.barrierEvent S =
      ExactTargetPlan.barrierEvent (shiftFinset v S) := by
  ext omega
  simp only [Set.mem_preimage, ExactTargetPlan.barrierEvent, Set.mem_setOf_eq,
    mem_siteShift]
  constructor
  · intro h x hx
    rw [mem_shiftFinset] at hx
    have := h _ hx
    simpa using this
  · intro h x hx
    exact h (x + v) (mem_shiftFinset.2 (by simpa using hx))

theorem shiftFinset_seedSupport {k : Nat} (v : Site d) (block : Fin k → Finset (Site d)) :
    shiftFinset v (ExactTargetPlan.seedSupport block) =
      ExactTargetPlan.seedSupport fun b => shiftFinset v (block b) := by
  simp only [ExactTargetPlan.seedSupport]
  exact shiftFinset_biUnion v block

/-! ## §2.  Translation of an exact target plan -/

/-- **Translation of a whole exact target plan.**  Every finite object moves by `+v`; every
stored real number — the extraction parameter, the tolerances and all leaf thresholds — is
untouched.  The `T4` pointers are re-indexed by the inverse translation of the source-plus
sites. -/
def translate (C : ExactTargetPlan.Plan d) (v : Site d) : ExactTargetPlan.Plan d where
  p0 := C.p0
  sourceBox := shiftBox v C.sourceBox
  activeBox := shiftBox v C.activeBox
  target := shiftFinset v C.target
  radius := C.radius
  numGeometries := C.numGeometries
  geometry := fun g => shiftGeometry v (C.geometry g)
  epsilon := C.epsilon
  m := C.m
  k := C.k
  N := C.N
  L := C.L
  numLeaves := C.numLeaves
  leaf := fun l => shiftBound v (C.leaf l)
  hitGeometry := fun w => C.hitGeometry (unshiftSite v C.sourceBox C.radius w)
  hitLeaf := fun w => C.hitLeaf (unshiftSite v C.sourceBox C.radius w)
  seedBlock := fun b => shiftFinset v (C.seedBlock b)
  seedLeaf := C.seedLeaf
  barrierSupport := shiftFinset v C.barrierSupport
  barrierLeaf := C.barrierLeaf
  barrierLower := C.barrierLower

section TranslateEq

variable (C : ExactTargetPlan.Plan d) (v : Site d)

@[simp] theorem translate_p0 : (translate C v).p0 = C.p0 := rfl
@[simp] theorem translate_radius : (translate C v).radius = C.radius := rfl
@[simp] theorem translate_epsilon : (translate C v).epsilon = C.epsilon := rfl
@[simp] theorem translate_m : (translate C v).m = C.m := rfl
@[simp] theorem translate_numLeaves : (translate C v).numLeaves = C.numLeaves := rfl
@[simp] theorem translate_target : (translate C v).target = shiftFinset v C.target := rfl
@[simp] theorem translate_delta : (translate C v).delta = C.delta := rfl
@[simp] theorem translate_eta : (translate C v).eta = C.eta := rfl
@[simp] theorem translate_seedCard : (translate C v).seedCard = C.seedCard := rfl
@[simp] theorem translate_barrierLower : (translate C v).barrierLower = C.barrierLower := rfl

@[simp] theorem translate_leaf (l : Fin C.numLeaves) :
    (translate C v).leaf l = shiftBound v (C.leaf l) := rfl

@[simp] theorem translate_geometry (g : Fin C.numGeometries) :
    (translate C v).geometry g = shiftGeometry v (C.geometry g) := rfl

@[simp] theorem translate_seedBlock (b : Fin C.k) :
    (translate C v).seedBlock b = shiftFinset v (C.seedBlock b) := rfl

@[simp] theorem translate_barrierSupport :
    (translate C v).barrierSupport = shiftFinset v C.barrierSupport := rfl

theorem translate_source : (translate C v).source = shiftFinset v C.source :=
  shiftBox_sites v C.sourceBox

theorem translate_active : (translate C v).active = shiftFinset v C.active :=
  shiftBox_sites v C.activeBox

theorem translate_sourcePlus : (translate C v).sourcePlus = shiftFinset v C.sourcePlus :=
  shiftBox_inflate_sites v C.sourceBox C.radius

variable {C v}

@[simp] theorem translate_hitGeometry
    (w : ((shiftBox v C.sourceBox).inflate C.radius).sites) :
    (translate C v).hitGeometry w =
      C.hitGeometry (unshiftSite v C.sourceBox C.radius w) := rfl

@[simp] theorem translate_hitLeaf
    (w : ((shiftBox v C.sourceBox).inflate C.radius).sites) :
    (translate C v).hitLeaf w =
      C.hitLeaf (unshiftSite v C.sourceBox C.radius w) := rfl

theorem translate_selectedRegion
    (w : ((shiftBox v C.sourceBox).inflate C.radius).sites) :
    (translate C v).selectedRegion w =
      shiftFinset v (C.selectedRegion (unshiftSite v C.sourceBox C.radius w)) := rfl

theorem translate_selectedFace
    (w : ((shiftBox v C.sourceBox).inflate C.radius).sites) :
    (translate C v).selectedFace w =
      shiftFinset v (C.selectedFace (unshiftSite v C.sourceBox C.radius w)) := rfl

end TranslateEq

/-- **Translation changes no probability.**  Validity is a finite table of strict inequalities
between real numbers, and every one of them is literally unchanged. -/
theorem translate_validAt_iff (C : ExactTargetPlan.Plan d) (v : Site d) (q : unitInterval) :
    (translate C v).ValidAt q ↔ C.ValidAt q := by
  unfold ExactTargetPlan.Plan.ValidAt
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i => (shiftBound_holdsAt_iff v (C.leaf i) q).1 (h3 i)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun i => (shiftBound_holdsAt_iff v (C.leaf i) q).2 (h3 i)⟩

theorem translate_validAt {C : ExactTargetPlan.Plan d} {q : unitInterval}
    (h : C.ValidAt q) (v : Site d) : (translate C v).ValidAt q :=
  (translate_validAt_iff C v q).2 h

/-- **Translation preserves (T1)--(T6).**  Every clause is either a finite geometric containment,
which translation preserves, a cardinality, which translation preserves, or a stored number,
which translation does not touch. -/
theorem translate_wellFormed {C : ExactTargetPlan.Plan d} (hC : C.WellFormed)
    (v : Site d) : (translate C v).WellFormed := by
  obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6⟩ := hC
  refine ⟨?_, hT2, hT3, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hT1
    refine ⟨h1, h2, shiftBox_ordered h3, shiftBox_ordered h4,
      shiftFinset_nonempty h5, ?_, ?_, h8, h9, h10⟩
    · rw [translate_sourcePlus, translate_active]
      exact shiftFinset_mono h6
    · rw [translate_target, translate_active]
      exact shiftFinset_mono h7
  · intro w
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hT4 (unshiftSite v C.sourceBox C.radius w)
    have hbox : siteBoxAt (w : Site d) C.m =
        shiftFinset v
          (siteBoxAt ((unshiftSite v C.sourceBox C.radius w : Site d)) C.m) := by
      rw [shiftFinset_siteBoxAt, unshiftSite_add]
    refine ⟨?_, h2, ?_, ?_, ?_, ?_, ?_, h8⟩
    · show (C.geometry (C.hitGeometry (unshiftSite v C.sourceBox C.radius w))).centre + v
        = (w : Site d)
      rw [h1, unshiftSite_add]
    · rw [translate_active]
      exact shiftFinset_mono h3
    · exact shiftFinset_mono h4
    · show siteBoxAt (w : Site d) C.m ⊆
        shiftFinset v (C.selectedRegion (unshiftSite v C.sourceBox C.radius w))
      rw [hbox]
      exact shiftFinset_mono h5
    · show shiftFinset v
          ((C.leaf (C.hitLeaf (unshiftSite v C.sourceBox C.radius w))).experiment.support)
        = shiftFinset v (C.selectedRegion (unshiftSite v C.sourceBox C.radius w))
      rw [h6]
    · show siteShift v ⁻¹'
          ((C.leaf (C.hitLeaf (unshiftSite v C.sourceBox C.radius w))).experiment.event)
        = ExactTargetPlan.hitEvent
            (shiftFinset v (C.selectedRegion (unshiftSite v C.sourceBox C.radius w)))
            (siteBoxAt (w : Site d) C.m)
            (shiftFinset v (C.selectedFace (unshiftSite v C.sourceBox C.radius w)))
      rw [h7, hbox]
      exact (ExactLongBoxHitBridge.VariableBridge.shift_hitEvent v
        (C.selectedRegion (unshiftSite v C.sourceBox C.radius w))
        (siteBoxAt ((unshiftSite v C.sourceBox C.radius w : Site d)) C.m)
        (C.selectedFace (unshiftSite v C.sourceBox C.radius w))).symm
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hT5
    refine ⟨?_, ?_, ?_, ?_, h5⟩
    · intro b
      rw [translate_seedBlock, shiftFinset_card, translate_seedCard]
      exact h1 b
    · intro b b' hbb'
      exact shiftFinset_disjoint (h2 b b' hbb')
    · show (shiftBound v (C.leaf C.seedLeaf)).experiment.support = _
      rw [shiftBound_experiment, shiftExperiment_support, h3]
      exact shiftFinset_seedSupport v C.seedBlock
    · show (shiftBound v (C.leaf C.seedLeaf)).experiment.event = _
      rw [shiftBound_experiment, shiftExperiment_event, h4]
      exact siteShift_preimage_seedEvent v C.seedBlock
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hT6
    refine ⟨?_, ?_, ?_, h4, h5, h6, h7⟩
    · rw [translate_barrierSupport, shiftFinset_card]
      exact h1
    · show (shiftBound v (C.leaf C.barrierLeaf)).experiment.support = _
      rw [shiftBound_experiment, shiftExperiment_support, h2, translate_barrierSupport]
    · show (shiftBound v (C.leaf C.barrierLeaf)).experiment.event = _
      rw [shiftBound_experiment, shiftExperiment_event, h3]
      exact siteShift_preimage_barrierEvent v C.barrierSupport

/-! ## §3.  Translation covariance of the literal (G2) shapes -/

theorem shiftFinset_cube (v c : Site d) (l : Int) :
    shiftFinset v (CorrMove.cube c l) = CorrMove.cube (c + v) l := by
  ext x
  have hkey : ∀ j : Fin d, (x - v) j - c j = x j - (c + v) j := by
    intro j
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [mem_shiftFinset, CorrMove.mem_cube, CorrMove.mem_cube]
  simp only [hkey]

theorem shiftFinset_dbox (v c : Site d) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (lo hi wid : Int) :
    shiftFinset v (CorrMove.dbox c i sigma lo hi wid) =
      CorrMove.dbox (c + v) i sigma lo hi wid := by
  ext x
  have hkey : ∀ j : Fin d, (x - v) j - c j = x j - (c + v) j := by
    intro j
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [mem_shiftFinset, CorrMove.mem_dbox hsigma, CorrMove.mem_dbox hsigma]
  simp only [hkey]

theorem shiftFinset_Dbox (v c : Site d) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (r s j : Nat) :
    shiftFinset v (ExactStoppedG2.Dbox c i sigma r s j) =
      ExactStoppedG2.Dbox (c + v) i sigma r s j :=
  shiftFinset_dbox v c i hsigma _ _ _

theorem shiftFinset_stubFace (v c : Site d) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (r t a : Nat) :
    shiftFinset v (Stopped.stubFace c i sigma r t a) =
      Stopped.stubFace (c + v) i sigma r t a := by
  ext x
  have hkey : ∀ j : Fin d, (x - v) j - c j = x j - (c + v) j := by
    intro j
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [mem_shiftFinset, Stopped.mem_stubFace hsigma, Stopped.mem_stubFace hsigma]
  simp only [Stopped.lam, hkey]

/-- The macro centre of the planar origin is the lattice origin. -/
theorem ctr_zero (r : Nat) : (MacroExp.ctr d r (0 : Site 2) : Site d) = 0 := by
  funext j
  simp [MacroExp.ctr]

/-! ## §4.  A common left parameter for a finite family of plans -/

/-- Finitely many exact target plans, all valid at `p`, remain valid together on a common
left neighbourhood of `p`: take the minimum of the individual radii. -/
theorem exists_valid_left_nhds_family {iota : Type} [Fintype iota] [Nonempty iota]
    (C : iota → ExactTargetPlan.Plan d) {p : unitInterval}
    (hvalid : ∀ x, (C x).ValidAt p) :
    ∃ e : Real, 0 < e ∧ ∀ q : unitInterval, 0 < (q : Real) → (q : Real) ≤ (p : Real) →
      |(q : Real) - (p : Real)| < e → ∀ x, (C x).ValidAt q := by
  classical
  have H : ∀ x : iota, ∃ e : Real, 0 < e ∧ ∀ q : unitInterval,
      0 < (q : Real) → (q : Real) ≤ (p : Real) → |(q : Real) - (p : Real)| < e →
      (C x).ValidAt q := by
    intro x
    obtain ⟨e, he, hq⟩ := (C x).exists_valid_left_nhds (hvalid x)
    exact ⟨e, he, hq⟩
  choose eps heps hq using H
  have hne : (Finset.univ : Finset iota).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.univ.inf' hne eps, (Finset.lt_inf'_iff hne).2 fun x _ => heps x, ?_⟩
  intro q hq0 hqp hd x
  exact hq x q hq0 hqp (lt_of_lt_of_le hd (Finset.inf'_le eps (Finset.mem_univ x)))

/-! ## §5.  The prototype head -/

/-- The signed direction attached to a Boolean orientation index. -/
def dirSign (b : Bool) : Int := if b then 1 else -1

theorem dirSign_spec (b : Bool) : dirSign b = 1 ∨ dirSign b = -1 := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- An orientation `(i, b)` is *realized* when some planar direction embeds onto it.  Every
oriented macro head realizes its own orientation, so this is never an extra assumption. -/
def Realized (d : Nat) (i : Fin d) (b : Bool) : Prop :=
  ∃ w : Site 2, (MacroExp.emb w : Site d) = Pi.single i (dirSign b)

/-- The canonical planar direction of a realized orientation.  Being a `Classical.choose` of a
`Prop`, it does not depend on which proof of realizability is supplied. -/
def protoDir {i : Fin d} {b : Bool} (h : Realized d i b) : Site 2 := Classical.choose h

theorem protoDir_emb {i : Fin d} {b : Bool} (h : Realized d i b) :
    (MacroExp.emb (protoDir h - 0) : Site d) = Pi.single i (dirSign b) := by
  rw [sub_zero]
  exact Classical.choose_spec h

section Prototype

variable {p0 : unitInterval} {alpha : Real} {K r s : Nat}

/-- **The prototype stopped child.**  The literal (G2) aspect-`2K` stopped plan of
`ExactLongBoxTranslatedPlan` at the head `(0, protoDir h)`: source `F^{a+1}`, active box `D_a`,
target the radius-`3r` core, all based at the lattice origin. -/
def protoPlan (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (In : ExactLongBoxTranslatedPlan.Inputs d p0 alpha K)
    {i : Fin d} {b : Bool} (h : Realized d i b)
    (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hR : 2 * In.radius ≤ s)
    (a : Fin K) : ExactTargetPlan.Plan d :=
  ExactLongBoxTranslatedPlan.plan hp0 hp1 ha0 ha1 In 0 (protoDir h) i
    (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt

variable (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
  (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
  (In : ExactLongBoxTranslatedPlan.Inputs d p0 alpha K)
  {i : Fin d} {b : Bool} (h : Realized d i b)
  (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hR : 2 * In.radius ≤ s) (a : Fin K)

theorem protoPlan_wellFormed :
    (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).WellFormed :=
  ExactLongBoxTranslatedPlan.plan_wellFormed hp0 hp1 ha0 ha1 In 0 (protoDir h) i
    (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt

theorem protoPlan_validAt :
    (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).ValidAt p0 :=
  ExactLongBoxTranslatedPlan.plan_validAt hp0 hp1 ha0 ha1 In 0 (protoDir h) i
    (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt

theorem protoPlan_active :
    (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).active =
      ExactStoppedG2.Dbox (0 : Site d) i (dirSign b) r s a.val := by
  rw [show (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).active = _ from
    ExactLongBoxTranslatedPlan.plan_active hp0 hp1 ha0 ha1 In 0 (protoDir h) i
      (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt, ctr_zero]

theorem protoPlan_source (t : Nat) :
    (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).source =
      Stopped.stubFace (0 : Site d) i (dirSign b) r t (10 * s * (a.val + 1)) := by
  rw [show (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).source = _ from
    ExactLongBoxTranslatedPlan.plan_source hp0 hp1 ha0 ha1 In 0 (protoDir h) i
      (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt t, ctr_zero]

theorem protoPlan_target :
    (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).target =
      CorrMove.cube (MacroExp.ctr d r (protoDir h)) (3 * (r : Int)) :=
  ExactLongBoxTranslatedPlan.plan_target hp0 hp1 ha0 ha1 In 0 (protoDir h) i
    (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt

theorem protoPlan_epsilon :
    (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).epsilon = alpha :=
  ExactLongBoxTranslatedPlan.plan_epsilon hp0 hp1 ha0 ha1 In 0 (protoDir h) i
    (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt

theorem protoPlan_radius :
    (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).radius = In.radius :=
  ExactLongBoxTranslatedPlan.plan_radius hp0 hp1 ha0 ha1 In 0 (protoDir h) i
    (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt

theorem protoPlan_delta :
    (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).delta =
      ExactTargetArithmetic.deltaOf alpha :=
  ExactLongBoxTranslatedPlan.plan_delta hp0 hp1 ha0 ha1 In 0 (protoDir h) i
    (dirSign_spec b) hK hs hr hR (protoDir_emb h) a.val a.isLt

/-- The macro centre of a realized prototype direction is the literal axial displacement. -/
theorem ctr_protoDir :
    (MacroExp.ctr d r (protoDir h) : Site d) =
      Pi.single i (dirSign b * (20 * (r : Int))) := by
  have := CorrMove.ctr_add_dir (d := d) r (protoDir_emb h)
  rw [this, ctr_zero, zero_add]

end Prototype

/-! ## §6.  The head family as a translate of the prototype -/

theorem subset_of_finset_eq {S T : Finset (Site d)} (hST : S = T) : S ⊆ T := by
  subst hST
  exact Finset.Subset.refl S

section Head

variable {p0 : unitInterval} {alpha : Real} {K r s : Nat}

/-- **The stopped child at an arbitrary head.**  It is the literal translate, by the macro centre
`MacroExp.ctr d r z`, of the prototype child at the origin head.  Nothing but the lattice
position changes: every stored real number, in particular every leaf threshold and every leaf
probability, is the prototype's. -/
def headPlan (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (In : ExactLongBoxTranslatedPlan.Inputs d p0 alpha K)
    {i : Fin d} {b : Bool} (h : Realized d i b)
    (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hR : 2 * In.radius ≤ s)
    (z : Site 2) (a : Fin K) : ExactTargetPlan.Plan d :=
  translate (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a) (MacroExp.ctr d r z)

variable (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
  (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
  (In : ExactLongBoxTranslatedPlan.Inputs d p0 alpha K)
  {i : Fin d} {b : Bool} (h : Realized d i b)
  (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hR : 2 * In.radius ≤ s)
  (z : Site 2) (a : Fin K)

theorem headPlan_wellFormed :
    (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).WellFormed :=
  translate_wellFormed (protoPlan_wellFormed hp0 hp1 ha0 ha1 In h hK hs hr hR a) _

/-- **Validity is inherited from the prototype at the same parameter.** -/
theorem headPlan_validAt {q : unitInterval}
    (hq : (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).ValidAt q) :
    (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).ValidAt q :=
  translate_validAt hq _

theorem headPlan_active :
    (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i (dirSign b) r s a.val := by
  have h1 : (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).active =
      shiftFinset (MacroExp.ctr d r z)
        (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).active :=
    translate_active _ _
  rw [h1, protoPlan_active hp0 hp1 ha0 ha1 In h hK hs hr hR a,
    shiftFinset_Dbox (MacroExp.ctr d r z) 0 i (dirSign_spec b) r s a.val, zero_add]

theorem headPlan_source (t : Nat) :
    (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i (dirSign b) r t (10 * s * (a.val + 1)) := by
  have h1 : (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).source =
      shiftFinset (MacroExp.ctr d r z)
        (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).source :=
    translate_source _ _
  rw [h1, protoPlan_source hp0 hp1 ha0 ha1 In h hK hs hr hR a t,
    shiftFinset_stubFace (MacroExp.ctr d r z) 0 i (dirSign_spec b) r t _, zero_add]

/-- **The translated target is the recursive core of the actual head.**  The prototype's core sits
at the axial displacement `Pi.single i (sigma * 20 r)` from the origin; translating by
`MacroExp.ctr d r z` lands it exactly on `MacroExp.ctr d r y`. -/
theorem headPlan_target {y : Site 2}
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i (dirSign b)) :
    (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).target =
      CoreRes.target (d := d) r y := by
  have h1 : (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).target =
      shiftFinset (MacroExp.ctr d r z)
        (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).target := rfl
  have hy : (MacroExp.ctr d r y : Site d) =
      MacroExp.ctr d r z + Pi.single i (dirSign b * (20 * (r : Int))) :=
    CorrMove.ctr_add_dir r hemb
  rw [h1, protoPlan_target hp0 hp1 ha0 ha1 In h hK hs hr hR a, shiftFinset_cube,
    ctr_protoDir (r := r) h]
  simp only [CoreRes.target]
  rw [hy, add_comm (MacroExp.ctr d r z) (Pi.single i (dirSign b * (20 * (r : Int))))]

theorem headPlan_epsilon :
    (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).epsilon = alpha :=
  protoPlan_epsilon hp0 hp1 ha0 ha1 In h hK hs hr hR a

theorem headPlan_radius :
    (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).radius = In.radius :=
  protoPlan_radius hp0 hp1 ha0 ha1 In h hK hs hr hR a

theorem headPlan_delta :
    (headPlan hp0 hp1 ha0 ha1 In h hK hs hr hR z a).delta =
      ExactTargetArithmetic.deltaOf alpha :=
  protoPlan_delta hp0 hp1 ha0 ha1 In h hK hs hr hR a

end Head

/-! ## §7.  One left parameter for every head -/

/-- **One fixed stopped input is stable uniformly over every head.**

The input `In` (hence its scheme, numerical leaves, and radius) and the macro scales are fixed
before the neighbourhood is chosen.  Only the finite orientation/level family is minimized.
For every parameter in that neighbourhood and every later head, this returns a literal
`StoppedChildren`; it does not choose the parameter internally. -/
theorem exists_left_nhds_stoppedChildren_of_inputs
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {K r s : Nat} (In : ExactLongBoxTranslatedPlan.Inputs d p0 alpha K)
    (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hR : 2 * In.radius ≤ s)
    {deltaC delta2 : Real}
    (hdelta : delta2 ≤ ExactTargetArithmetic.deltaOf alpha) (heps : alpha ≤ deltaC) :
    ∃ e : Real, 0 < e ∧
      ∀ q : unitInterval, 0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
        |(q : Real) - (p0 : Real)| < e →
      ∀ t : Nat, 5 * r ≤ t →
      ∀ (z y : Site 2) (i : Fin d) (sigma : Int),
        (sigma = 1 ∨ sigma = -1) →
        (MacroExp.emb (y - z) : Site d) = Pi.single i sigma →
        ∃ G : ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma deltaC delta2,
          (∀ a, (G.plan a).ValidAt q) ∧
          (∀ a, (G.plan a).radius = In.radius) ∧
          (∀ a, (G.plan a).epsilon = alpha) ∧
          (∀ a, (G.plan a).active =
            ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
          (∀ a, (G.plan a).source =
            Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
          ∀ a, (G.plan a).target = CoreRes.target (d := d) r y := by
  classical
  haveI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have key : ∀ ib : Fin d × Bool, ∃ e : Real, 0 < e ∧
      ∀ (h : Realized d ib.1 ib.2) (q : unitInterval), 0 < (q : Real) →
        (q : Real) ≤ (p0 : Real) → |(q : Real) - (p0 : Real)| < e →
        ∀ a : Fin K, (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).ValidAt q := by
    rintro ⟨i, b⟩
    by_cases hreal : Realized d i b
    · obtain ⟨e, he, hq⟩ := exists_valid_left_nhds_family
        (fun a : Fin K => protoPlan hp0 hp1 ha0 ha1 In hreal hK hs hr hR a)
        (fun a => protoPlan_validAt hp0 hp1 ha0 ha1 In hreal hK hs hr hR a)
      exact ⟨e, he, fun _ q hq0 hqp hdist a => hq q hq0 hqp hdist a⟩
    · exact ⟨1, one_pos, fun hcon => absurd hcon hreal⟩
  choose e he hspec using key
  have hne : (Finset.univ : Finset (Fin d × Bool)).Nonempty := Finset.univ_nonempty
  refine ⟨Finset.univ.inf' hne e, (Finset.lt_inf'_iff hne).2 fun x _ => he x, ?_⟩
  intro q hq0 hqp hdist t ht z y i sigma hsigma hemb
  obtain ⟨b, rfl⟩ : ∃ bb : Bool, dirSign bb = sigma := by
    rcases hsigma with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  have hreal : Realized d i b := ⟨y - z, hemb⟩
  have hvq : ∀ a : Fin K,
      (protoPlan hp0 hp1 ha0 ha1 In hreal hK hs hr hR a).ValidAt q :=
    hspec (i, b) hreal q hq0 hqp
      (lt_of_lt_of_le hdist (Finset.inf'_le e (Finset.mem_univ (i, b))))
  have hrpos : 0 < r := by
    rw [hr]
    exact Nat.mul_pos (by omega) hs
  refine ⟨ExactStoppedG2.stoppedChildren (dirSign_spec b) hrpos ht hemb
      (fun a => headPlan hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a)
      (fun a => headPlan_wellFormed hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a)
      (fun a => headPlan_active hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a)
      (fun a => headPlan_source hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a t)
      (fun a => subset_of_finset_eq
        (headPlan_target hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a hemb))
      (fun a => by
        rw [headPlan_delta hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a]
        exact hdelta)
      (fun a => by
        rw [headPlan_epsilon hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a]
        exact heps),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a => headPlan_validAt hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a (hvq a)
  · exact fun a => headPlan_radius hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a
  · exact fun a => headPlan_epsilon hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a
  · exact fun a => headPlan_active hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a
  · exact fun a => headPlan_source hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a t
  · exact fun a => headPlan_target hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a hemb

/-- Supercriticality freezes the stopped input once; at every admissible macro scale it yields a
single positive left-neighbourhood radius serving all stopped heads. -/
theorem exists_left_nhds_stoppedChildren_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {K : Nat} (hK : 20 ≤ K) {deltaC delta2 : Real}
    (hdelta : delta2 ≤ ExactTargetArithmetic.deltaOf alpha) (heps : alpha ≤ deltaC) :
    ∃ R : Nat, 0 < R ∧
      ∀ r s : Nat, 0 < s → r = K * s → 2 * R ≤ s →
      ∃ e : Real, 0 < e ∧
        ∀ q : unitInterval, 0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
          |(q : Real) - (p0 : Real)| < e →
        ∀ t : Nat, 5 * r ≤ t →
        ∀ (z y : Site 2) (i : Fin d) (sigma : Int),
          (sigma = 1 ∨ sigma = -1) →
          (MacroExp.emb (y - z) : Site d) = Pi.single i sigma →
          ∃ G : ExactMacroGeometry.StoppedChildren (d := d)
              r t s K z y i sigma deltaC delta2,
            (∀ a, (G.plan a).ValidAt q) ∧
            (∀ a, (G.plan a).radius = R) ∧
            (∀ a, (G.plan a).epsilon = alpha) ∧
            (∀ a, (G.plan a).active =
              ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
            (∀ a, (G.plan a).source =
              Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
            ∀ a, (G.plan a).target = CoreRes.target (d := d) r y := by
  obtain ⟨In⟩ := ExactLongBoxTranslatedPlan.exists_inputs_of_thetaSite_pos (d := d)
    p0 hp0 hp1 htheta ha0 ha1 (K := K) (by omega)
  refine ⟨In.radius, In.radius_pos, ?_⟩
  intro r s hs hr hR
  exact exists_left_nhds_stoppedChildren_of_inputs hp0 hp1 ha0 ha1 In hK hs hr hR
    hdelta heps

/-- Numerical specialization used by the v15 macro step. -/
theorem exists_left_nhds_frozen_stoppedChildren_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0) {K : Nat} (hK : 20 ≤ K) :
    ∃ R : Nat, 0 < R ∧
      ∀ r s : Nat, 0 < s → r = K * s → 2 * R ≤ s →
      ∃ e : Real, 0 < e ∧
        ∀ q : unitInterval, 0 < (q : Real) → (q : Real) ≤ (p0 : Real) →
          |(q : Real) - (p0 : Real)| < e →
        ∀ t : Nat, 5 * r ≤ t →
        ∀ (z y : Site 2) (i : Fin d) (sigma : Int),
          (sigma = 1 ∨ sigma = -1) →
          (MacroExp.emb (y - z) : Site d) = Pi.single i sigma →
          ∃ G : ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma
              (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d),
            ∀ a, (G.plan a).ValidAt q := by
  have hdeltaC_le_one : ExactMacroNumerics.deltaC d ≤ 1 := by
    calc
      ExactMacroNumerics.deltaC d ≤ ExactMacroNumerics.rho / 2 :=
        ExactMacroNumerics.deltaC_le_rho_half d
      _ ≤ 1 := by linarith [ExactMacroNumerics.rho_le_half]
  obtain ⟨R, hR, hstable⟩ := exists_left_nhds_stoppedChildren_of_thetaSite_pos
    p0 hp0 hp1 htheta (ExactMacroNumerics.deltaC_pos d) hdeltaC_le_one hK
    (ExactMacroNumerics.delta2_le_targetDelta d) le_rfl
  refine ⟨R, hR, ?_⟩
  intro r s hs hr hscale
  obtain ⟨e, he, hnear⟩ := hstable r s hs hr hscale
  refine ⟨e, he, ?_⟩
  intro q hq0 hqp hdist t ht z y i sigma hsigma hemb
  obtain ⟨G, hvalid, _⟩ := hnear q hq0 hqp hdist t ht z y i sigma hsigma hemb
  exact ⟨G, hvalid⟩

/-- **The stopped prototype is left-stable uniformly in the head.**

One extraction radius `R` is frozen from supercriticality alone.  At every admissible macro scale
`(r, s)` a single parameter `q < p0` is produced, and *then*, for every transverse level `t`,
every macro head `(z, y)` and every orientation `(i, sigma)`, the whole family of `K` stopped
children exists with all of its literal (G2) shapes and is valid at that same `q`.

The finite minimum is taken over `Fin d × Bool × Fin K` only — the orientations and the levels.
The head position `z` contributes nothing, because the child at `z` is the literal translate of
the child at the origin and translation changes no probability. -/
theorem exists_uniform_stoppedChildren_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {K : Nat} (hK : 20 ≤ K)
    {deltaC delta2 : Real}
    (hdelta : delta2 ≤ ExactTargetArithmetic.deltaOf alpha) (heps : alpha ≤ deltaC) :
    ∃ R : Nat, 0 < R ∧
      ∀ r s : Nat, 0 < s → r = K * s → 2 * R ≤ s →
      ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p0 : Real) ∧
        ∀ t : Nat, 5 * r ≤ t →
        ∀ (z y : Site 2) (i : Fin d) (sigma : Int),
          (sigma = 1 ∨ sigma = -1) →
          (MacroExp.emb (y - z) : Site d) = Pi.single i sigma →
          ∃ G : ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma deltaC delta2,
            (∀ a, (G.plan a).ValidAt q) ∧
            (∀ a, (G.plan a).radius = R) ∧
            (∀ a, (G.plan a).epsilon = alpha) ∧
            (∀ a, (G.plan a).active =
              ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
            (∀ a, (G.plan a).source =
              Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
            (∀ a, (G.plan a).target = CoreRes.target (d := d) r y) := by
  classical
  obtain ⟨In⟩ := ExactLongBoxTranslatedPlan.exists_inputs_of_thetaSite_pos (d := d)
    p0 hp0 hp1 htheta ha0 ha1 (K := K) (by omega)
  refine ⟨In.radius, In.radius_pos, ?_⟩
  intro r s hs hr hR
  haveI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  -- One left-stability radius per orientation, uniform in the level and the head.
  have key : ∀ ib : Fin d × Bool, ∃ e : Real, 0 < e ∧
      ∀ (h : Realized d ib.1 ib.2) (q : unitInterval), 0 < (q : Real) →
        (q : Real) ≤ (p0 : Real) → |(q : Real) - (p0 : Real)| < e →
        ∀ a : Fin K, (protoPlan hp0 hp1 ha0 ha1 In h hK hs hr hR a).ValidAt q := by
    rintro ⟨i, b⟩
    by_cases hreal : Realized d i b
    · obtain ⟨e, he, hq⟩ := exists_valid_left_nhds_family
        (fun a : Fin K => protoPlan hp0 hp1 ha0 ha1 In hreal hK hs hr hR a)
        (fun a => protoPlan_validAt hp0 hp1 ha0 ha1 In hreal hK hs hr hR a)
      exact ⟨e, he, fun _ q hq0 hqp hdist a => hq q hq0 hqp hdist a⟩
    · exact ⟨1, one_pos, fun hcon => absurd hcon hreal⟩
  choose e he hspec using key
  have hne : (Finset.univ : Finset (Fin d × Bool)).Nonempty := Finset.univ_nonempty
  have hEpos : 0 < Finset.univ.inf' hne e := (Finset.lt_inf'_iff hne).2 fun x _ => he x
  obtain ⟨q, hq0, hqp, hqdist⟩ : ∃ q : unitInterval, 0 < (q : Real) ∧
      (q : Real) < (p0 : Real) ∧
      |(q : Real) - (p0 : Real)| < Finset.univ.inf' hne e := by
    set tt : Real := min (Finset.univ.inf' hne e / 2) ((p0 : Real) / 2) with httdef
    have htt0 : 0 < tt := lt_min (by linarith) (by linarith)
    have httE : tt < Finset.univ.inf' hne e :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have http : tt ≤ (p0 : Real) / 2 := min_le_right _ _
    refine ⟨⟨(p0 : Real) - tt, Set.mem_Icc.2 ⟨by linarith, by linarith⟩⟩, ?_, ?_, ?_⟩
    · show 0 < (p0 : Real) - tt
      linarith
    · show (p0 : Real) - tt < (p0 : Real)
      linarith
    · show |(p0 : Real) - tt - (p0 : Real)| < Finset.univ.inf' hne e
      rw [show (p0 : Real) - tt - (p0 : Real) = -tt by ring, abs_neg, abs_of_pos htt0]
      exact httE
  refine ⟨q, hq0, hqp, ?_⟩
  intro t ht z y i sigma hsigma hemb
  obtain ⟨b, rfl⟩ : ∃ bb : Bool, dirSign bb = sigma := by
    rcases hsigma with rfl | rfl
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  have hreal : Realized d i b := ⟨y - z, hemb⟩
  have hvq : ∀ a : Fin K,
      (protoPlan hp0 hp1 ha0 ha1 In hreal hK hs hr hR a).ValidAt q :=
    hspec (i, b) hreal q hq0 hqp.le
      (lt_of_lt_of_le hqdist (Finset.inf'_le e (Finset.mem_univ (i, b))))
  have hrpos : 0 < r := by
    rw [hr]
    exact Nat.mul_pos (by omega) hs
  refine ⟨ExactStoppedG2.stoppedChildren hsigma hrpos ht hemb
      (fun a => headPlan hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a)
      (fun a => headPlan_wellFormed hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a)
      (fun a => headPlan_active hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a)
      (fun a => headPlan_source hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a t)
      (fun a => subset_of_finset_eq
        (headPlan_target hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a hemb))
      (fun a => by
        rw [headPlan_delta hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a]
        exact hdelta)
      (fun a => by
        rw [headPlan_epsilon hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a]
        exact heps),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a => headPlan_validAt hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a (hvq a)
  · exact fun a => headPlan_radius hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a
  · exact fun a => headPlan_epsilon hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a
  · exact fun a => headPlan_active hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a
  · exact fun a => headPlan_source hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a t
  · exact fun a => headPlan_target hp0 hp1 ha0 ha1 In hreal hK hs hr hR z a hemb

/-- The same statement at the numerical parameters of the v15 macro step: the output error is
exactly `ExactMacroNumerics.deltaC d` and the input tolerance dominates `ExactMacroNumerics.delta2 d`,
so neither comparison remains as a hypothesis. -/
theorem exists_uniform_frozen_stoppedChildren_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    {K : Nat} (hK : 20 ≤ K) :
    ∃ R : Nat, 0 < R ∧
      ∀ r s : Nat, 0 < s → r = K * s → 2 * R ≤ s →
      ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p0 : Real) ∧
        ∀ t : Nat, 5 * r ≤ t →
        ∀ (z y : Site 2) (i : Fin d) (sigma : Int),
          (sigma = 1 ∨ sigma = -1) →
          (MacroExp.emb (y - z) : Site d) = Pi.single i sigma →
          ∃ G : ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma
              (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d),
            (∀ a, (G.plan a).ValidAt q) ∧
            (∀ a, (G.plan a).radius = R) ∧
            (∀ a, (G.plan a).epsilon = ExactMacroNumerics.deltaC d) ∧
            (∀ a, (G.plan a).active =
              ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
            (∀ a, (G.plan a).source =
              Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
            (∀ a, (G.plan a).target = CoreRes.target (d := d) r y) := by
  have hdeltaC_le_one : ExactMacroNumerics.deltaC d ≤ 1 := by
    calc
      ExactMacroNumerics.deltaC d ≤ ExactMacroNumerics.rho / 2 :=
        ExactMacroNumerics.deltaC_le_rho_half d
      _ ≤ 1 := by linarith [ExactMacroNumerics.rho_le_half]
  exact exists_uniform_stoppedChildren_of_thetaSite_pos p0 hp0 hp1 htheta
    (ExactMacroNumerics.deltaC_pos d) hdeltaC_le_one hK
    (ExactMacroNumerics.delta2_le_targetDelta d) le_rfl

#print axioms KNAll.Site.ExactStoppedPrototypeStability.shiftExperiment_prob
#print axioms KNAll.Site.ExactStoppedPrototypeStability.translate_validAt_iff
#print axioms KNAll.Site.ExactStoppedPrototypeStability.translate_wellFormed
#print axioms KNAll.Site.ExactStoppedPrototypeStability.exists_valid_left_nhds_family
#print axioms KNAll.Site.ExactStoppedPrototypeStability.headPlan_active
#print axioms KNAll.Site.ExactStoppedPrototypeStability.headPlan_source
#print axioms KNAll.Site.ExactStoppedPrototypeStability.headPlan_target
#print axioms KNAll.Site.ExactStoppedPrototypeStability.exists_left_nhds_stoppedChildren_of_inputs
#print axioms KNAll.Site.ExactStoppedPrototypeStability.exists_left_nhds_stoppedChildren_of_thetaSite_pos
#print axioms KNAll.Site.ExactStoppedPrototypeStability.exists_left_nhds_frozen_stoppedChildren_of_thetaSite_pos
#print axioms KNAll.Site.ExactStoppedPrototypeStability.exists_uniform_stoppedChildren_of_thetaSite_pos
#print axioms KNAll.Site.ExactStoppedPrototypeStability.exists_uniform_frozen_stoppedChildren_of_thetaSite_pos

end KNAll.Site.ExactStoppedPrototypeStability

end
