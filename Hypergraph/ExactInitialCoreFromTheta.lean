import Hypergraph.CoreInitialReservation
import Hypergraph.ExactLongBoxHitBridge

/-!
# The four exact initial leaves

The v15 initial step does not run a post-entry window.  It uses one aspect-`6` long-box
cylinder in each of the four planar directions.  The source of each cylinder is a whole finite
cube contained in the already-open root box; the far face lies in the radius-`3r` reservation
core at the neighbouring macro vertex.  Thus opening the root box transports each ordinary
product estimate directly to the pinned start law.

This file records those four cylinders as a literal finite list, proves their source/active/target
geometry, constructs their validity from positive percolation, and gives the resulting
`CoreInitial.InitialCoreBounds` in the exact type consumed by the reachable interpreter.
-/

noncomputable section

namespace KNAll.Site.ExactInitialCoreFromTheta

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

/-! ## Self-contained planar directions -/

namespace Direction

def planeAxis (hd : 2 ≤ d) (i : Fin 2) : Fin d :=
  ⟨i.val, i.isLt.trans_le hd⟩

def axis (hd : 2 ≤ d) (y : Site 2) : Fin d :=
  if y (0 : Fin 2) ≠ 0 then planeAxis hd 0 else planeAxis hd 1

def sign (y : Site 2) : Int :=
  if y (0 : Fin 2) ≠ 0 then y (0 : Fin 2) else y (1 : Fin 2)

theorem emb_plane_single (hd : 2 ≤ d) (i : Fin 2) (sigma : Int) :
    (MacroExp.emb (Pi.single i sigma) : Site d) = Pi.single (planeAxis hd i) sigma := by
  funext j
  by_cases hj : j.val < 2
  · rw [MacroExp.emb_apply_of_lt _ hj]
    by_cases hji : (⟨j.val, hj⟩ : Fin 2) = i
    · have hjaxis : j = planeAxis hd i := by
        apply Fin.ext
        exact congrArg (fun k : Fin 2 => k.val) hji
      subst j
      have hback :
          (⟨(planeAxis hd i).val, by exact i.isLt⟩ :
            Fin 2) = i := by
        apply Fin.ext
        rfl
      simp [Pi.single_apply, hback]
    · have hjaxis : j ≠ planeAxis hd i := by
        intro heq
        apply hji
        apply Fin.ext
        exact congrArg (fun k : Fin d => k.val) heq
      simp [Pi.single_apply, hji, hjaxis]
  · rw [MacroExp.emb_apply_of_not_lt _ hj, Pi.single_apply, if_neg]
    intro heq
    apply hj
    rw [heq]
    exact i.isLt

theorem sign_unit (hd : 2 ≤ d) {y : Site 2}
    (hy : y ∈ MacroExp.nbrs (0 : Site 2)) : sign y = 1 ∨ sign y = -1 := by
  obtain ⟨i, b, rfl⟩ := MacroExp.mem_nbrs_iff.1 hy
  fin_cases i <;> cases b <;>
    simp [sign, MacroExp.mvUnit, Pi.single_apply]

theorem emb_eq_single (hd : 2 ≤ d) {y : Site 2}
    (hy : y ∈ MacroExp.nbrs (0 : Site 2)) :
    (MacroExp.emb y : Site d) = Pi.single (axis hd y) (sign y) := by
  obtain ⟨i, b, rfl⟩ := MacroExp.mem_nbrs_iff.1 hy
  fin_cases i <;> cases b <;>
    simp [axis, sign, planeAxis, MacroExp.mvUnit, Pi.single_apply,
      emb_plane_single hd]

end Direction

/-! ## Self-contained G1 geometry -/

namespace G1

def box (r : Nat) (i : Fin d) (sigma : Int) : Finset (Site d) :=
  CorrMove.longBox (MacroExp.ctr d r 0) (3 * (r : Int)) i sigma 6

def face (r : Nat) (i : Fin d) (sigma : Int) : Finset (Site d) :=
  CorrMove.longFace (MacroExp.ctr d r 0) (3 * (r : Int)) i sigma 6

def source (r : Nat) : Finset (Site d) :=
  CorrMove.cube (MacroExp.ctr d r 0) (3 * (r : Int))

private theorem longBox_subset_Q_union_E {r t : Nat} {y : Site 2} {i : Fin d}
    {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb y : Site d) = Pi.single i sigma)
    {l K : Int} (hl : 0 ≤ l) (hK : 1 ≤ K)
    (hplanar : l ≤ 5 * (r : Int)) (htrans : l ≤ (t : Int))
    (hfwd : K * l ≤ 25 * (r : Int)) :
    CorrMove.longBox (MacroExp.ctr d r 0) l i sigma K ⊆
      MacroExp.Q d r t 0 ∪ MacroExp.E d r t 0 y := by
  classical
  have hemb0 :
      (MacroExp.emb (y - (0 : Site 2)) : Site d) = Pi.single i sigma := by
    simpa using hemb
  have hi := CorrMove.planar_of_emb (y := y) (z := 0) hsigma hemb0
  have hcy := CorrMove.ctr_add_dir (d := d) (y := y) (z := 0) r hemb0
  intro x hx
  rw [CorrMove.mem_longBox hsigma hl hK] at hx
  obtain ⟨⟨hlo, hhi⟩, htr⟩ := hx
  have habsi : |x i - MacroExp.ctr d r 0 i| =
      |sigma * (x i - MacroExp.ctr d r 0 i)| := (CorrMove.abs_signed hsigma).symm
  by_cases hnear : sigma * (x i - MacroExp.ctr d r 0 i) ≤ 5 * (r : Int)
  · refine Finset.mem_union_left _ ?_
    rw [MacroExp.Q, MacroExp.mem_abox]
    intro j
    by_cases hj : j = i
    · have hb : |x i - MacroExp.ctr d r 0 i| ≤ 5 * (r : Int) := by
        rw [habsi, abs_le]
        omega
      rw [abs_le] at hb
      rw [hj, CorrMove.rad_planar hi]
      omega
    · have hjb := htr j hj
      rw [abs_le] at hjb
      unfold MacroExp.rad
      split_ifs <;> omega
  · push Not at hnear
    refine Finset.mem_union_right _ ?_
    rw [MacroExp.E, Finset.mem_sdiff, MacroExp.mem_hbox]
    constructor
    · intro j
      by_cases hj : j = i
      · have hcyj : MacroExp.ctr d r y i =
            MacroExp.ctr d r 0 i + sigma * (20 * (r : Int)) := by
          rw [hcy]
          simp
        rw [hj, hcyj, CorrMove.rad_planar hi]
        rcases hsigma with rfl | rfl
        · simp only [one_mul] at hlo hhi hnear
          rw [min_eq_left (by omega), max_eq_right (by omega)]
          omega
        · have he1 : (-1 : Int) * (x i - MacroExp.ctr d r 0 i) =
              -(x i - MacroExp.ctr d r 0 i) := by ring
          rw [he1] at hlo hhi hnear
          rw [min_eq_right (by omega), max_eq_left (by omega)]
          omega
      · have hcyj : MacroExp.ctr d r y j = MacroExp.ctr d r 0 j := by
          rw [hcy]
          simp [Pi.single_eq_of_ne hj]
        have hjb := htr j hj
        rw [abs_le] at hjb
        rw [hcyj, min_self, max_self]
        unfold MacroExp.rad
        split_ifs <;> omega
    · intro hQ
      rw [MacroExp.Q, MacroExp.mem_abox] at hQ
      have hb := hQ i
      rw [CorrMove.rad_planar hi] at hb
      have habs : |x i - MacroExp.ctr d r 0 i| ≤ 5 * (r : Int) := by
        rw [abs_le]
        omega
      rw [habsi, abs_le] at habs
      omega

private theorem longFace_subset_cube {r : Nat} {y : Site 2} {i : Fin d}
    {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb y : Site d) = Pi.single i sigma)
    {l K m : Int} (hl : 0 ≤ l) (hK : 1 ≤ K)
    (hlong : |K * l - 20 * (r : Int)| ≤ m) (htrans : l ≤ m) :
    CorrMove.longFace (MacroExp.ctr d r 0) l i sigma K ⊆
      CorrMove.cube (MacroExp.ctr d r y) m := by
  have hsigma2 : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
  have hemb0 :
      (MacroExp.emb (y - (0 : Site 2)) : Site d) = Pi.single i sigma := by
    simpa using hemb
  have hcy := CorrMove.ctr_add_dir (d := d) (y := y) (z := 0) r hemb0
  intro x hx
  rw [CorrMove.mem_longFace hsigma hl hK] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [CorrMove.mem_cube]
  intro j
  by_cases hj : j = i
  · have hcyj : MacroExp.ctr d r y i =
        MacroExp.ctr d r 0 i + sigma * (20 * (r : Int)) := by
      rw [hcy]
      simp
    have hxc : x i - MacroExp.ctr d r 0 i = sigma * (K * l) := by
      calc
        x i - MacroExp.ctr d r 0 i =
            (sigma * sigma) * (x i - MacroExp.ctr d r 0 i) := by rw [hsigma2, one_mul]
        _ = sigma * (sigma * (x i - MacroExp.ctr d r 0 i)) := by ring
        _ = sigma * (K * l) := by rw [h1]
    have hdiff : x i - MacroExp.ctr d r y i =
        sigma * (K * l - 20 * (r : Int)) := by
      rw [hcyj, show x i - (MacroExp.ctr d r 0 i + sigma * (20 * (r : Int))) =
        (x i - MacroExp.ctr d r 0 i) - sigma * (20 * (r : Int)) from by ring, hxc]
      ring
    rw [hj, hdiff, CorrMove.abs_signed hsigma]
    exact hlong
  · have hcyj : MacroExp.ctr d r y j = MacroExp.ctr d r 0 j := by
      rw [hcy]
      simp [Pi.single_eq_of_ne hj]
    rw [hcyj]
    exact le_trans (h2 j hj) htrans

theorem box_subset_Q_union_E {r t : Nat} {y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb y : Site d) = Pi.single i sigma)
    (ht : 3 * r ≤ t) :
    box (d := d) r i sigma ⊆ MacroExp.Q d r t 0 ∪ MacroExp.E d r t 0 y := by
  exact longBox_subset_Q_union_E hsigma hemb (by omega) (by norm_num)
    (by omega) (by exact_mod_cast ht) (by omega)

theorem face_subset_target {r : Nat} {y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb y : Site d) = Pi.single i sigma) :
    face (d := d) r i sigma ⊆ CoreRes.target (d := d) r y := by
  unfold face CoreRes.target
  exact longFace_subset_cube hsigma hemb (by omega) (by norm_num)
    (by rw [show (6 : Int) * (3 * (r : Int)) - 20 * (r : Int) =
      -(2 * (r : Int)) by ring, abs_neg, abs_of_nonneg (by omega)]; omega)
    (by omega)

end G1

/-! ## Literal cylinders -/

/-- The direct aspect-`6` hit used at the root in one oriented planar direction. -/
def initialHitEvent (r m : Nat) (i : Fin d) (sigma : Int) :
    Set (SiteConfig (Site d)) :=
  ExactTargetPlan.hitEvent
    (G1.box (d := d) r i sigma)
    (siteBoxAt (MacroExp.ctr d r 0) m)
    (G1.face (d := d) r i sigma)

/-- A finite cylinder presentation of `initialHitEvent`. -/
def initialHitExperiment (r m : Nat) (i : Fin d) (sigma : Int) :
    CylinderExperiment d where
  support := G1.box (d := d) r i sigma
  event := initialHitEvent r m i sigma
  determined := by
    unfold initialHitEvent ExactTargetPlan.hitEvent
    exact DeterminedBy.iUnion fun x => DeterminedBy.iUnion fun _ =>
      determinedBy_connWithinSet (zdGraph d)
        (↑(G1.box (d := d) r i sigma) : Set (Site d)) x
        (↑(G1.face (d := d) r i sigma) : Set (Site d))
  measurable' := ReinforcedHit.measurableSet_hitEvent _ _ _

@[simp] theorem initialHitExperiment_event (r m : Nat) (i : Fin d) (sigma : Int) :
    (initialHitExperiment (d := d) r m i sigma).event = initialHitEvent r m i sigma := rfl

@[simp] theorem initialHitExperiment_prob (r m : Nat) (i : Fin d) (sigma : Int)
    (q : unitInterval) :
    (initialHitExperiment (d := d) r m i sigma).prob q =
      (siteBernoulli (fun _ : Site d => q)).real (initialHitEvent r m i sigma) := rfl

/-- The literal four-leaf table.  `nbrs 0` has four members; each is assigned its explicit
centre-aware axis and sign. -/
def initialHitList (hd : 2 ≤ d) (r m : Nat) (epsilon : Real) :
    List (CylinderExperiment d × Real) :=
  (MacroExp.nbrs (0 : Site 2)).toList.map fun y =>
    (initialHitExperiment r m (Direction.axis hd y)
      (Direction.sign y), 1 - epsilon)

theorem mem_initialHitList (hd : 2 ≤ d) {r m : Nat} {epsilon : Real}
    {y : Site 2} (hy : y ∈ MacroExp.nbrs (0 : Site 2)) :
    (initialHitExperiment (d := d) r m (Direction.axis hd y)
        (Direction.sign y), 1 - epsilon) ∈
      initialHitList (d := d) hd r m epsilon := by
  classical
  simp only [initialHitList, List.mem_map, Finset.mem_toList]
  exact ⟨y, hy, rfl⟩

theorem initialHitList_nonempty (hd : 2 ≤ d) (r m : Nat) (epsilon : Real) :
    initialHitList (d := d) hd r m epsilon ≠ [] := by
  classical
  let y : Site 2 := MacroExp.mvUnit 0 true
  have hy : y ∈ MacroExp.nbrs (0 : Site 2) := by
    rw [MacroExp.mem_nbrs_iff]
    exact ⟨0, true, by simp [y]⟩
  intro hnil
  have hm := mem_initialHitList (d := d) hd
    (r := r) (m := m) (epsilon := epsilon) hy
  rw [hnil] at hm
  simpa using hm

/-! ## The finite initial plan -/

/-- All runtime data of the four direct root leaves.  No theorem-valued probability field is
stored: validity below is exactly membership-wise validity of `bounds`. -/
structure InitialPlan (d : Nat) where
  p0 : unitInterval
  epsilon : Real
  r : Nat
  t : Nat
  sourceRadius : Nat

namespace InitialPlan

def bounds (hd : 2 ≤ d) (P : InitialPlan d) : List (CylinderExperiment d × Real) :=
  initialHitList hd P.r P.sourceRadius P.epsilon

/-- Parameter-free checks needed by the pinned-start interpretation. -/
def WellFormed (P : InitialPlan d) : Prop :=
  0 < (P.p0 : Real) ∧ (P.p0 : Real) < 1 ∧
  0 < P.epsilon ∧ P.epsilon ≤ 1 ∧
  0 < P.r ∧ 3 * P.r ≤ P.t ∧ P.sourceRadius ≤ 3 * P.r

/-- The only probabilistic content is the finite list of four strict cylinder bounds. -/
def ValidAt (hd : 2 ≤ d) (P : InitialPlan d) (q : unitInterval) : Prop :=
  0 < (q : Real) ∧ (q : Real) ≤ (P.p0 : Real) ∧
    ∀ b ∈ P.bounds hd, b.2 < b.1.prob q

theorem bounds_nonempty (hd : 2 ≤ d) (P : InitialPlan d) : P.bounds hd ≠ [] :=
  initialHitList_nonempty hd P.r P.sourceRadius P.epsilon

/-! ## Source and endpoint geometry -/

theorem source_subset_initialSource (P : InitialPlan d) (hP : P.WellFormed) :
    siteBoxAt (MacroExp.ctr d P.r 0) P.sourceRadius ⊆
      G1.source (d := d) P.r := by
  intro x hx
  rw [mem_siteBoxAt] at hx
  rw [G1.source, CorrMove.mem_cube]
  intro j
  have hj := hx j
  have hm : (P.sourceRadius : Int) ≤ 3 * (P.r : Int) := by
    exact_mod_cast hP.2.2.2.2.2.2
  rw [abs_le]
  omega

theorem source_subset_Q (P : InitialPlan d) (hP : P.WellFormed) :
    siteBoxAt (MacroExp.ctr d P.r 0) P.sourceRadius ⊆
      MacroExp.Q d P.r P.t 0 := by
  intro x hx
  have hcube := source_subset_initialSource P hP hx
  rw [G1.source, CorrMove.mem_cube] at hcube
  rw [MacroExp.Q, MacroExp.mem_abox]
  intro j
  have hj := hcube j
  have ht : (3 * P.r : Int) ≤ (P.t : Int) := by
    exact_mod_cast hP.2.2.2.2.2.1
  rw [abs_le] at hj
  unfold MacroExp.rad
  split_ifs <;> omega

theorem active_subset_rootDom (hd : 2 ≤ d) (P : InitialPlan d) (hP : P.WellFormed)
    {y : Site 2} (hy : y ∈ MacroExp.nbrs (0 : Site 2)) :
    G1.box (d := d) P.r
        (Direction.axis hd y) (Direction.sign y) ⊆
      MacroExp.Q d P.r P.t 0 ∪ MacroExp.E d P.r P.t 0 y := by
  exact G1.box_subset_Q_union_E
    (Direction.sign_unit hd hy)
    (Direction.emb_eq_single hd hy)
    hP.2.2.2.2.2.1

theorem face_subset_target (hd : 2 ≤ d) (P : InitialPlan d)
    {y : Site 2} (hy : y ∈ MacroExp.nbrs (0 : Site 2)) :
    G1.face (d := d) P.r
        (Direction.axis hd y) (Direction.sign y) ⊆
      CoreRes.target (d := d) P.r y := by
  exact G1.face_subset_target
    (Direction.sign_unit hd hy)
    (Direction.emb_eq_single hd hy)

/-! ## Transport to the pinned start -/

/-- One ordinary initial hit cylinder is bounded by the corresponding connection under the
pinned start transcript.  All sites of `Q 0` are pinned open.  They connect the origin to the
whole finite source cube, while the hit path stays in `Q 0 ∪ E 0 y` and its far endpoint lies in
the radius-`3r` core at `y`. -/
theorem initialHitExperiment_prob_le_start (hd : 2 ≤ d) (P : InitialPlan d)
    (hP : P.WellFormed) (q : unitInterval) {y : Site 2}
    (hy : y ∈ MacroExp.nbrs (0 : Site 2)) :
    (initialHitExperiment (d := d) P.r P.sourceRadius
      (Direction.axis hd y) (Direction.sign y)).prob q ≤
      (MacroExp.start d P.r P.t).prob (fun _ : Site d => q)
        (CoreRes.event (d := d) P.r P.t (MacroExp.start d P.r P.t) 0 y) := by
  classical
  let h0 := MacroExp.start d P.r P.t
  let i := Direction.axis hd y
  let sigma := Direction.sign y
  let Reg := G1.box (d := d) P.r i sigma
  let S := siteBoxAt (MacroExp.ctr d P.r 0) P.sourceRadius
  let F := G1.face (d := d) P.r i sigma
  let Dom := MacroExp.Q d P.r P.t 0 ∪ MacroExp.E d P.r P.t 0 y
  let T := CoreRes.target (d := d) P.r y
  let A : Set (SiteConfig (Site d)) :=
    connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) (↑T : Set (Site d))
  rw [FRDom.Transcript.prob_eq]
  change (siteBernoulli (fun _ : Site d => q)).real
      (ExactTargetPlan.hitEvent Reg S F) ≤
    (siteBernoulli (fun _ : Site d => q)).real
      (substitute (↑h0.inspected : Set (Site d)) h0.state ⁻¹' A)
  apply measureReal_mono
  · intro omega hhit
    let omega' : SiteConfig (Site d) :=
      substitute (↑h0.inspected : Set (Site d)) h0.state omega
    have hmono : omega ⊆ omega' := by
      intro x hx
      by_cases hxI : x ∈ (↑h0.inspected : Set (Site d))
      · rw [mem_substitute_of_mem h0.state hxI]
        exact Finset.mem_coe.1 hxI
      · rw [mem_substitute_of_notMem h0.state hxI]
        exact hx
    have hhit' : omega' ∈ ExactTargetPlan.hitEvent Reg S F :=
      ReinforcedHit.isUpperSet_hitEvent Reg S F hmono hhit
    obtain ⟨s, hsS, hsF⟩ := Set.mem_iUnion₂.1 hhit'
    obtain ⟨f, hfF, hsf⟩ :=
      (mem_connWithinSet_iff (zdGraph d) (↑Reg : Set (Site d)) s
        (↑F : Set (Site d)) omega').1 hsF
    have hopenQ : (↑(MacroExp.Q d P.r P.t 0) : Set (Site d)) ⊆ omega' := by
      intro x hxQ
      rw [mem_substitute_of_mem h0.state]
      · exact Finset.mem_coe.1 hxQ
      · exact hxQ
    have hzeroQ : MacroExp.emb (0 : Site 2) ∈ MacroExp.Q d P.r P.t 0 :=
      MacroExp.M_subset_Q P.r P.t 0 (MacroExp.emb_zero_mem_M P.r P.t)
    have hsQ : s ∈ MacroExp.Q d P.r P.t 0 :=
      source_subset_Q P hP (Finset.mem_coe.1 hsS)
    have h0s : omega' ∈ connWithin (zdGraph d)
        (↑(MacroExp.Q d P.r P.t 0) : Set (Site d)) (MacroExp.emb 0) s := by
      change omega' ∈ connWithin (zdGraph d)
        (↑(Corridor.rbox (MacroExp.ctr d P.r 0)
          (MacroExp.rad (5 * P.r) P.t)) : Set (Site d)) (MacroExp.emb 0) s
      exact Corridor.connWithin_rbox_of_allOpen hopenQ
        (Corridor.dist1 (MacroExp.emb 0) s) (MacroExp.emb 0) s hzeroQ hsQ le_rfl
    have hRegDom : (↑Reg : Set (Site d)) ⊆ (↑Dom : Set (Site d)) :=
      Finset.coe_subset.2 (active_subset_rootDom hd P hP hy)
    have hQDom : (↑(MacroExp.Q d P.r P.t 0) : Set (Site d)) ⊆
        (↑Dom : Set (Site d)) :=
      Finset.coe_subset.2 Finset.subset_union_left
    have h0sDom := connWithin_mono_set (zdGraph d) hQDom (MacroExp.emb 0) s h0s
    have hsfDom := connWithin_mono_set (zdGraph d) hRegDom s f hsf
    have h0f0 := TargetExt.connWithin_trans (zdGraph d) h0sDom hsfDom
    have h0f : omega' ∈ connWithin (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) f := by
      simpa only [Set.union_self] using h0f0
    have hfT : f ∈ (↑T : Set (Site d)) :=
      Finset.mem_coe.2 (face_subset_target hd P hy (Finset.mem_coe.1 hfF))
    change substitute (↑h0.inspected : Set (Site d)) h0.state omega ∈ A
    exact (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d))
      (MacroExp.emb 0) (↑T : Set (Site d)) omega').2 ⟨f, hfT, h0f⟩
  · exact measure_ne_top _ _

/-- The four finite leaf inequalities give exactly the initial core reservation required by the
reachable interpreter. -/
theorem initialCoreBounds (hd : 3 ≤ d) (P : InitialPlan d) (hP : P.WellFormed)
    {q : unitInterval} (hv : P.ValidAt (by omega : 2 ≤ d) q) :
    CoreInitial.InitialCoreBounds (d := d) P.r P.t q P.epsilon := by
  intro y hy
  have hyn : y ∈ MacroExp.nbrs (0 : Site 2) :=
    ((MacroExp.mem_pending (d := d)).1 hy).1
  have hmem := mem_initialHitList (d := d) (by omega : 2 ≤ d)
    (r := P.r) (m := P.sourceRadius) (epsilon := P.epsilon) hyn
  have hleaf := hv.2.2 _ hmem
  have htrans := initialHitExperiment_prob_le_start (d := d)
    (by omega : 2 ≤ d) P hP q hyn
  unfold CoreRes.Bound
  exact lt_of_lt_of_le hleaf htrans

/-! ## Extraction from positive percolation -/

/-- The source radius used by the variable-aspect chain. -/
def schemeSourceRadius {p0 : unitInterval} {epsilon : Real}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6) : Nat :=
  (F.scheme 0).scales.source

/-- The exact lower bound on the quotient scale required by the aspect-`6` chain.  Keeping this
separate from the macro radius lets the final construction freeze `F` and then choose the same
external radius as all other finite plan families. -/
def requiredMacroScale {p0 : unitInterval} {epsilon : Real}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6) : Nat :=
  3 * 6 + 3 * 6 * F.radius + schemeSourceRadius F + 8

/-- Quotient/remainder decomposition of the literal scale `3r` in the `8s+rem` convention. -/
def macroScale (r : Nat) : Nat := (3 * r) / 8
def scaleRem (r : Nat) : Nat := (3 * r) % 8

theorem longScale_macroScale_scaleRem (r : Nat) :
    LongBoxVariable.longScale (macroScale r) (scaleRem r) = 3 * r := by
  unfold LongBoxVariable.longScale macroScale scaleRem
  omega

theorem scaleRem_le (r : Nat) : scaleRem r ≤ 7 := by
  unfold scaleRem
  have := Nat.mod_lt (3 * r) (by omega : 0 < 8)
  omega

/-- The plan whose four leaves use the common source radius extracted with an aspect-`6` scheme. -/
def ofScheme {p0 : unitInterval} {epsilon : Real}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6) (r t : Nat) : InitialPlan d where
  p0 := p0
  epsilon := epsilon
  r := r
  t := t
  sourceRadius := schemeSourceRadius F

theorem ofScheme_wellFormed
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6)
    {r t : Nat} (hr : 0 < r) (ht : 3 * r ≤ t)
    (hm : schemeSourceRadius F ≤ 3 * r) :
    (ofScheme F r t).WellFormed :=
  ⟨hp0, hp1, he0, he1, hr, ht, hm⟩

/-- At every scale satisfying the explicit finite chain inequality, all four literal G1 leaves
are valid at the extraction parameter. -/
theorem ofScheme_validAt
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6)
    (hd : 2 ≤ d) (r t : Nat)
    (hscale : requiredMacroScale F ≤ macroScale r) :
    (ofScheme F r t).ValidAt hd p0 := by
  refine ⟨hp0, le_rfl, ?_⟩
  intro b hb
  simp only [InitialPlan.bounds, initialHitList, List.mem_map,
    Finset.mem_toList] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  have hsigma := Direction.sign_unit hd hy
  have hhit := ExactLongBoxHitBridge.VariableBridge.translated_hit
    hp0 hp1 F (by omega : 1 ≤ 6) he0 he1
    (MacroExp.ctr d r 0) (Direction.axis hd y)
    (Direction.sign y) hsigma
    (schemeSourceRadius F) (macroScale r) (scaleRem r)
    (by exact le_rfl) (scaleRem_le r) (by simpa [requiredMacroScale] using hscale)
  simpa only [initialHitExperiment_prob, initialHitEvent,
    G1.box, G1.face,
    longScale_macroScale_scaleRem, siteBernoulli, ofScheme,
    schemeSourceRadius, Nat.cast_mul, Nat.cast_ofNat] using hhit

/-- An arbitrary lower bound on `r` can be met while keeping the aspect-`6` chain inequality.
This is the scale-ordering fact used by macro-plan extraction: the scheme is frozen first and the
single common macro radius is chosen afterwards. -/
theorem exists_large_scale_for_scheme
    {p0 : unitInterval} {epsilon : Real}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6) (rmin : Nat) :
    ∃ r : Nat, rmin ≤ r ∧ 0 < r ∧
      requiredMacroScale F ≤ macroScale r := by
  let B := requiredMacroScale F + rmin + 1
  refine ⟨8 * B, ?_, ?_, ?_⟩
  · dsimp [B]
    omega
  · dsimp [B]
    omega
  · unfold macroScale
    have hB : 0 < B := by dsimp [B]; omega
    have heq : (3 * (8 * B)) / 8 = 3 * B := by omega
    rw [heq]
    dsimp [B, requiredMacroScale]
    omega

/-- At any externally chosen macro radius meeting the displayed quotient-scale threshold, the
frozen aspect-`6` scheme supplies the literal four-leaf plan, with no fresh existential scale. -/
theorem ofScheme_at_shared_radius
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6)
    (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r) (ht : 3 * r ≤ t)
    (hscale : requiredMacroScale F ≤ macroScale r) :
    (ofScheme F r t).WellFormed ∧ (ofScheme F r t).ValidAt hd p0 := by
  have hm0 : schemeSourceRadius F ≤ macroScale r := by
    unfold requiredMacroScale at hscale
    omega
  have hmacro : macroScale r ≤ 3 * r := by
    unfold macroScale
    omega
  exact ⟨ofScheme_wellFormed hp0 hp1 he0 he1 F hr ht (hm0.trans hmacro),
    ofScheme_validAt hp0 hp1 he0 he1 F hd r t hscale⟩

/-- Positive percolation produces a genuine nonempty four-leaf initial plan at an arbitrarily
large macro radius.  Every leaf is already valid at `p0`; no root-window proposition is added. -/
theorem exists_initialPlan_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (epsilon : Real) (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hd : 2 ≤ d) (rmin : Nat) :
    ∃ P : InitialPlan d,
      rmin ≤ P.r ∧ P.t = 5 * P.r ∧ P.WellFormed ∧ P.ValidAt hd p0 ∧
        P.bounds hd ≠ [] := by
  let F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6 :=
    Classical.choice
      (ExactLongBoxVariablePlan.exists_schemeFamily_of_thetaSite_pos
        p0 hp0 hp1 htheta epsilon he0 he1 6 (by omega))
  obtain ⟨r, hrmin, hr, hscale⟩ := exists_large_scale_for_scheme F rmin
  let P := ofScheme F r (5 * r)
  have hP := ofScheme_at_shared_radius hp0 hp1 he0 he1 F hd
    (r := r) (t := 5 * r) hr (by omega) hscale
  exact ⟨P, hrmin, rfl, hP.1, hP.2, P.bounds_nonempty hd⟩

/-! ## Finite left stability -/

theorem exists_valid_left_nhds (hd : 2 ≤ d) (P : InitialPlan d)
    {p : unitInterval} (hv : P.ValidAt hd p) :
    ∃ eta > 0, ∀ q : unitInterval, 0 < (q : Real) →
      (q : Real) ≤ (p : Real) → |(q : Real) - (p : Real)| < eta → P.ValidAt hd q := by
  obtain ⟨eta, heta, hnear⟩ := LeftImp.exists_valid_nhds_list (P.bounds hd) hv.2.2
  refine ⟨eta, heta, fun q hq hqp hdist => ⟨hq, hqp.trans hv.2.1, ?_⟩⟩
  exact hnear q hdist

/-- The shared-radius endpoint used by simultaneous descent: after the scheme and common macro
radius have been frozen, one left neighbourhood works for all four G1 leaves and every parameter
in it yields the concrete initial core bounds at that same parameter. -/
theorem exists_initialCoreBounds_left_nhds_ofScheme
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 epsilon 6)
    (hd : 3 ≤ d) {r t : Nat} (hr : 0 < r) (ht : 3 * r ≤ t)
    (hscale : requiredMacroScale F ≤ macroScale r) :
    ∃ eta > 0, ∀ q : unitInterval, 0 < (q : Real) →
      (q : Real) ≤ (p0 : Real) → |(q : Real) - (p0 : Real)| < eta →
      CoreInitial.InitialCoreBounds (d := d) r t q epsilon := by
  let P := ofScheme F r t
  have hP := ofScheme_at_shared_radius hp0 hp1 he0 he1 F
    (by omega : 2 ≤ d) hr ht hscale
  obtain ⟨eta, heta, hvalid⟩ := P.exists_valid_left_nhds (by omega : 2 ≤ d) hP.2
  refine ⟨eta, heta, ?_⟩
  intro q hq hqp hdist
  exact P.initialCoreBounds hd hP.1 (hvalid q hq hqp hdist)

theorem exists_smaller_valid (hd : 2 ≤ d) (P : InitialPlan d)
    {p : unitInterval} (hp : 0 < (p : Real)) (hv : P.ValidAt hd p) :
    ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p : Real) ∧ P.ValidAt hd q := by
  obtain ⟨eta, heta, hleft⟩ := P.exists_valid_left_nhds hd hv
  let a : Real := min (eta / 2) ((p : Real) / 2)
  have ha : 0 < a := lt_min (by linarith) (by linarith)
  have hap : a ≤ (p : Real) / 2 := min_le_right _ _
  let q : unitInterval :=
    ⟨(p : Real) - a, Set.mem_Icc.2 ⟨by linarith, by linarith [p.2.2]⟩⟩
  refine ⟨q, ?_, ?_, ?_⟩
  · change 0 < (p : Real) - a
    linarith
  · change (p : Real) - a < (p : Real)
    linarith
  apply hleft q
  · change 0 < (p : Real) - a
    linarith [min_le_right (eta / 2) ((p : Real) / 2)]
  · change (p : Real) - a ≤ (p : Real)
    linarith
  · change |(p : Real) - a - (p : Real)| < eta
    rw [show (p : Real) - a - (p : Real) = -a by ring, abs_neg, abs_of_pos ha]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

end InitialPlan

#print axioms KNAll.Site.ExactInitialCoreFromTheta.InitialPlan.initialHitExperiment_prob_le_start
#print axioms KNAll.Site.ExactInitialCoreFromTheta.InitialPlan.initialCoreBounds
#print axioms KNAll.Site.ExactInitialCoreFromTheta.InitialPlan.ofScheme_validAt
#print axioms KNAll.Site.ExactInitialCoreFromTheta.InitialPlan.exists_initialPlan_of_thetaSite_pos
#print axioms KNAll.Site.ExactInitialCoreFromTheta.InitialPlan.exists_valid_left_nhds
#print axioms KNAll.Site.ExactInitialCoreFromTheta.InitialPlan.exists_initialCoreBounds_left_nhds_ofScheme

end KNAll.Site.ExactInitialCoreFromTheta

end
