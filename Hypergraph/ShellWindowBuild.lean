import Hypergraph.CorridorEstimates

/-!
# The shell-window candidate supplied by the recorded experiments

The certificate records one face experiment and one coalescence experiment for every ordered
pair in its source box.  This file packages their translates at a contact and records the two
properties that follow directly from those records: locality in the middle box and the precise
union-bound probability.  The final `ShellWindow` constructor is deliberately not stated below:
the recorded data do not imply either its `relay` field or its probability threshold; see the
closing note.
-/

noncomputable section

namespace KNAll.Site.ShellBuild

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor KNAll.Site.MacroExp

variable {d : ℕ} [NeZero d]

/-- Read a configuration after translation by `v`. -/
def shiftCfg (v : Site d) (ω : SiteConfig (Site d)) : SiteConfig (Site d) :=
  restrictSite (fun z => z + v) ω

@[simp] theorem mem_shiftCfg (v : Site d) (ω : SiteConfig (Site d)) (z : Site d) :
    z ∈ shiftCfg v ω ↔ z + v ∈ ω := Iff.rfl

def shiftEvent (v : Site d) (A : Set (SiteConfig (Site d))) : Set (SiteConfig (Site d)) :=
  shiftCfg v ⁻¹' A

theorem measurable_shiftCfg (v : Site d) : Measurable (shiftCfg (d := d) v) :=
  measurable_restrictSite _

theorem measurePreserving_shiftCfg (p : unitInterval) (v : Site d) :
    MeasurePreserving (shiftCfg (d := d) v) (siteBernoulli fun _ : Site d => p)
      (siteBernoulli fun _ : Site d => p) :=
  ⟨measurable_shiftCfg v, siteBernoulli_map_restrictSite (add_left_injective v) p⟩

theorem measurableSet_shiftEvent (v : Site d) {A : Set (SiteConfig (Site d))}
    (hA : MeasurableSet A) : MeasurableSet (shiftEvent v A) :=
  measurable_shiftCfg v hA

theorem prob_shiftEvent (p : unitInterval) (v : Site d) {A : Set (SiteConfig (Site d))}
    (hA : MeasurableSet A) :
    (siteBernoulli fun _ : Site d => p).real (shiftEvent v A) =
      (siteBernoulli fun _ : Site d => p).real A := by
  have h := (measurePreserving_shiftCfg p v).measure_preimage hA.nullMeasurableSet
  rw [measureReal_def, measureReal_def, shiftEvent, h]

theorem determinedBy_shiftEvent (v : Site d) {A : Set (SiteConfig (Site d))}
    {F : Finset (Site d)} (hA : DeterminedBy A (↑F : Set (Site d))) :
    DeterminedBy (shiftEvent v A) (↑(F.image (fun z => z + v)) : Set (Site d)) := by
  classical
  rw [determinedBy_iff] at hA ⊢
  intro ω ω' hω
  refine hA _ _ ?_
  have key : ∀ z : Site d, z ∈ F → (z + v ∈ ω ↔ z + v ∈ ω') := by
    intro z hz
    have hmem : z + v ∈ (↑(F.image (fun y => y + v)) : Set (Site d)) := by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨z, hz, rfl⟩
    constructor
    · intro hzω
      exact ((Set.ext_iff.1 hω (z + v)).1 ⟨hzω, hmem⟩).1
    · intro hzω'
      exact ((Set.ext_iff.1 hω (z + v)).2 ⟨hzω', hmem⟩).1
  ext z
  simp only [Set.mem_inter_iff, mem_shiftCfg, Finset.mem_coe]
  exact ⟨fun h => ⟨(key z h.2).1 h.1, h.2⟩, fun h => ⟨(key z h.2).2 h.1, h.2⟩⟩

/-- Translating the origin-centred box of radius `N` puts it in the corresponding `rbox`. -/
theorem image_add_box_subset_rbox (v : Site d) (N : ℕ) :
    (box d N).image (fun z => z + v) ⊆ rbox v (fun _ => (N : ℤ)) := by
  classical
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [mem_box] at hz
  rw [mem_rbox]
  intro i
  have hi := hz i
  simp only [Pi.add_apply]
  constructor <;> omega

theorem box_eq_rbox_zero (N : ℕ) :
    box d N = rbox (0 : Site d) (fun _ => (N : ℤ)) := by
  ext z
  rw [mem_box, mem_rbox]
  simp only [Pi.zero_apply, zero_sub, zero_add]

theorem connWithin_box_of_allOpen {N : ℕ} {ω : SiteConfig (Site d)}
    (hopen : (↑(box d N) : Set (Site d)) ⊆ ω) {a b : Site d}
    (ha : a ∈ box d N) (hb : b ∈ box d N) :
    ω ∈ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) a b := by
  rw [box_eq_rbox_zero] at hopen ha hb ⊢
  exact connWithin_rbox_of_allOpen hopen (Corridor.dist1 a b) a b ha hb le_rfl

theorem allOpen_box_mem_localFaceEvent (m N : ℕ) (hmN : m ≤ N) :
    (↑(box d m) : SiteConfig (Site d)) ∈ localFaceEvent d m N := by
  rw [mem_localFaceEvent_iff]
  have hzero : (0 : Site d) ∈ box d m := by
    rw [mem_box]
    intro i
    simp
  refine ⟨0, box_mono d hmN hzero, fun i b => ?_⟩
  let z : Site d := Pi.single i (if b then (m : ℤ) else -(m : ℤ))
  have hz : z ∈ boxFace d m i b := by
    constructor
    · intro k
      by_cases hki : k = i
      · subst k
        cases b <;> simp [z]
      · simp [z, Pi.single_eq_of_ne hki]
    · simp [z]
  refine ⟨z, hz, connWithin_mono_set (zdGraph d) (coe_box_mono d hmN) 0 z ?_⟩
  exact connWithin_box_of_allOpen (Set.Subset.rfl) hzero (mem_box.2 hz.1)

theorem shiftCfg_coe_image_add (F : Finset (Site d)) (v : Site d) :
    shiftCfg v (↑(F.image (fun z => z + v)) : SiteConfig (Site d)) =
      (↑F : SiteConfig (Site d)) := by
  classical
  ext z
  simp only [mem_shiftCfg, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, h⟩
    have : y = z := by
      apply add_right_cancel (b := v)
      exact h
    rwa [← this]
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- The untranslated all-pairs coalescence event. -/
def coalescenceBase (C : LeftImp2.Certificate2 d) : Set (SiteConfig (Site d)) :=
  (⋃ p ∈ box d C.source ×ˢ box d C.source,
    localCoalescenceEvent d C.sphere C.coalTarget p.1 p.2)ᶜ

theorem determinedBy_coalescenceBase (C : LeftImp2.Certificate2 d) :
    DeterminedBy (coalescenceBase C) (↑(box d C.coalTarget) : Set (Site d)) := by
  unfold coalescenceBase
  apply DeterminedBy.compl
  apply DeterminedBy.iUnion
  intro p
  apply DeterminedBy.iUnion
  intro _hp
  exact determinedBy_localCoalescenceEvent d C.sphere C.coalTarget p.1 p.2

theorem measurableSet_coalescenceBase (C : LeftImp2.Certificate2 d) :
    MeasurableSet (coalescenceBase C) :=
  (determinedBy_coalescenceBase C).measurableSet_of_finset

theorem allOpen_box_mem_coalescenceBase {C : LeftImp2.Certificate2 d}
    (hwf : C.WellFormed) :
    (↑(box d C.source) : SiteConfig (Site d)) ∈ coalescenceBase C := by
  intro hbad
  obtain ⟨p, hp, hpbad⟩ := Set.mem_iUnion₂.1 hbad
  obtain ⟨t, htSphere, hpt⟩ :=
    (mem_connWithinSet_iff _ _ _ _ _).1 hpbad.1.1
  have htOpen : t ∈ (↑(box d C.source) : SiteConfig (Site d)) :=
    (mem_of_mem_siteCluster (zdGraph d)
      ((↑(box d C.source) : SiteConfig (Site d)) ∩
        (↑(box d C.coalTarget) : Set (Site d))) ⟨hpt.1, hpt.2⟩).1
  have htBox := mem_box.1 (Finset.mem_coe.1 htOpen)
  obtain ⟨i, hi⟩ := htSphere.2
  have hsourceSphere : C.source < C.sphere := by
    change C.source < C.source + C.shell
    have hshell := hwf.base.shell_pos
    omega
  have hsourceSphere' : (C.source : ℤ) < (C.sphere : ℤ) := by exact_mod_cast hsourceSphere
  have hti := htBox i
  rcases hi with hi | hi <;> rw [hi] at hti <;> omega

/-- What validity gives after union-bounding the separately recorded ordered pairs. -/
theorem prob_coalescenceBase_ge {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {q : unitInterval} (hv : C.ValidAt2 q) :
    1 - (C.pairs : ℝ) * C.coalTol ≤
      (siteBernoulli fun _ : Site d => q).real (coalescenceBase C) := by
  classical
  let μ := siteBernoulli fun _ : Site d => q
  have hbad : ∀ p ∈ box d C.source ×ˢ box d C.source,
      μ.real (localCoalescenceEvent d C.sphere C.coalTarget p.1 p.2) ≤ C.coalTol := by
    intro p hp
    rw [Finset.mem_product] at hp
    have h := hv.1 _ (hwf.base.coalescence_mem p.1 hp.1 p.2 hp.2)
    rw [coalescenceExperiment_prob] at h
    linarith
  have hmeas : MeasurableSet
      (⋃ p ∈ box d C.source ×ˢ box d C.source,
        localCoalescenceEvent d C.sphere C.coalTarget p.1 p.2) :=
    Finset.measurableSet_biUnion _ fun p _ =>
      measurableSet_localCoalescenceEvent d C.sphere C.coalTarget p.1 p.2
  have hU : μ.real
      (⋃ p ∈ box d C.source ×ˢ box d C.source,
        localCoalescenceEvent d C.sphere C.coalTarget p.1 p.2)
      ≤ (C.pairs : ℝ) * C.coalTol := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum hbad).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← C.pairs_eq_card]
  rw [coalescenceBase, measureReal_compl hmeas, probReal_univ]
  linarith

/-- No translated bad coalescence event occurs for any ordered pair in the source box. -/
def coalescenceGood (C : LeftImp2.Certificate2 d) (v : Site d) :
    Set (SiteConfig (Site d)) :=
  shiftEvent v (coalescenceBase C)

/-- The direct candidate: the recorded face event together with all recorded coalescence events. -/
def candidate (C : LeftImp2.Certificate2 d) (c : Site d) (j : ℕ) (x : Site d) :
    Set (SiteConfig (Site d)) :=
  let v := cubeCentre (scalesOf C) c j x
  shiftEvent v (localFaceEvent d C.source C.faceTarget) ∩ coalescenceGood C v

theorem determinedBy_coalescenceGood (C : LeftImp2.Certificate2 d) (v : Site d) :
    DeterminedBy (coalescenceGood C v)
      (↑((box d C.coalTarget).image (fun z => z + v)) : Set (Site d)) :=
  determinedBy_shiftEvent v (determinedBy_coalescenceBase C)

theorem measurableSet_coalescenceGood (C : LeftImp2.Certificate2 d) (v : Site d) :
    MeasurableSet (coalescenceGood C v) :=
  measurableSet_shiftEvent v (measurableSet_coalescenceBase C)

theorem prob_coalescenceGood_ge {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {q : unitInterval} (hv : C.ValidAt2 q) (v : Site d) :
    1 - (C.pairs : ℝ) * C.coalTol ≤
      (siteBernoulli fun _ : Site d => q).real (coalescenceGood C v) := by
  rw [coalescenceGood, prob_shiftEvent q v (measurableSet_coalescenceBase C)]
  exact prob_coalescenceBase_ge hwf hv

theorem prob_shiftedFace_ge {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {q : unitInterval} (hv : C.ValidAt2 q) (v : Site d) :
    1 - C.faceTol ≤ (siteBernoulli fun _ : Site d => q).real
      (shiftEvent v (localFaceEvent d C.source C.faceTarget)) := by
  rw [prob_shiftEvent q v (measurableSet_localFaceEvent d C.source C.faceTarget)]
  have h := hv.1 _ hwf.base.face_mem
  rw [faceExperiment_prob] at h
  exact h.le

theorem measurableSet_candidate (C : LeftImp2.Certificate2 d) (c : Site d) (j : ℕ)
    (x : Site d) : MeasurableSet (candidate C c j x) := by
  unfold candidate
  exact (measurableSet_shiftEvent _
    (measurableSet_localFaceEvent d C.source C.faceTarget)).inter
      (measurableSet_coalescenceGood C _)

/-- The exact lower bound furnished by the two recorded kinds of experiment. -/
theorem prob_candidate_ge {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {q : unitInterval} (hv : C.ValidAt2 q) (c : Site d) (j : ℕ) (x : Site d) :
    1 - (C.faceTol + (C.pairs : ℝ) * C.coalTol) ≤
      (siteBernoulli fun _ : Site d => q).real (candidate C c j x) := by
  let v := cubeCentre (scalesOf C) c j x
  let F := shiftEvent v (localFaceEvent d C.source C.faceTarget)
  let K := coalescenceGood C v
  let μ := siteBernoulli fun _ : Site d => q
  have hFm : MeasurableSet F :=
    measurableSet_shiftEvent v (measurableSet_localFaceEvent d C.source C.faceTarget)
  have hKm : MeasurableSet K := measurableSet_coalescenceGood C v
  have hF := prob_shiftedFace_ge hwf hv v
  have hK := prob_coalescenceGood_ge hwf hv v
  have hFc : μ.real Fᶜ ≤ C.faceTol := by
    rw [measureReal_compl hFm, probReal_univ]
    linarith
  have hKc : μ.real Kᶜ ≤ (C.pairs : ℝ) * C.coalTol := by
    rw [measureReal_compl hKm, probReal_univ]
    linarith
  have hU : μ.real ((F ∩ K)ᶜ) ≤ C.faceTol + (C.pairs : ℝ) * C.coalTol := by
    rw [compl_inter]
    exact (measureReal_union_le Fᶜ Kᶜ).trans (add_le_add hFc hKc)
  change 1 - (C.faceTol + (C.pairs : ℝ) * C.coalTol) ≤ μ.real (F ∩ K)
  rw [measureReal_compl (hFm.inter hKm), probReal_univ] at hU
  linarith

theorem determinedBy_candidate {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {c : Site d} {j : ℕ} (hj : j < C.levels) {Dom : Finset (Site d)} {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j)) :
    DeterminedBy (candidate C c j x) (↑(Obox (scalesOf C) c j) : Set (Site d)) := by
  let v := cubeCentre (scalesOf C) c j x
  have hcontact := isContact_of_mem_outerBoundary (scalesOf C) c j Dom hx
  have hcube : cube (scalesOf C) c j x ⊆ Obox (scalesOf C) c j :=
    (cube_subset_shell (hwf.fits hj) hcontact).trans (Finset.sdiff_subset)
  have hfaceSupport : (box d C.faceTarget).image (fun z => z + v) ⊆
      Obox (scalesOf C) c j := by
    refine (image_add_box_subset_rbox v C.faceTarget).trans ?_
    exact hcube
  have hcoalSupport : (box d C.coalTarget).image (fun z => z + v) ⊆
      Obox (scalesOf C) c j := by
    refine (image_add_box_subset_rbox v C.coalTarget).trans ?_
    refine (rbox_mono (c := v) fun _ => ?_).trans hcube
    exact_mod_cast hwf.base.coalTarget_le_faceTarget
  unfold candidate
  dsimp only
  refine DeterminedBy.inter
    ((determinedBy_shiftEvent v (determinedBy_localFaceEvent d C.source C.faceTarget)).mono
      (Finset.coe_subset.2 hfaceSupport))
    ((determinedBy_coalescenceGood C v).mono (Finset.coe_subset.2 hcoalSupport))

/-- The proposed intersection has a configuration with no open site on the corridor face.

Open exactly the translated source box.  It realizes the face experiment because that box is
connected and lies in the face experiment's target box.  It also realizes every coalescence
complement vacuously: the open set does not reach the strictly larger coalescence sphere.  But the
corridor face is at distance `faceTarget`, strictly beyond `source`. -/
theorem candidate_contains_no_open_relay {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {c : Site d} {j : ℕ} (_hj : j < C.levels) {Dom : Finset (Site d)} {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j)) :
    ∃ ω ∈ candidate C c j x, ∀ u ∈ face (scalesOf C) c j x, u ∉ ω := by
  let v := cubeCentre (scalesOf C) c j x
  let ω : SiteConfig (Site d) :=
    (↑((box d C.source).image (fun z => z + v)) : Set (Site d))
  have hshift : shiftCfg v ω = (↑(box d C.source) : SiteConfig (Site d)) :=
    shiftCfg_coe_image_add (box d C.source) v
  have hsourceFace : C.source ≤ C.faceTarget := hwf.base.source_le_faceTarget
  have hωcandidate : ω ∈ candidate C c j x := by
    change shiftCfg v ω ∈ localFaceEvent d C.source C.faceTarget ∧
      shiftCfg v ω ∈ coalescenceBase C
    rw [hshift]
    exact ⟨allOpen_box_mem_localFaceEvent C.source C.faceTarget hsourceFace,
      allOpen_box_mem_coalescenceBase hwf⟩
  refine ⟨ω, hωcandidate, fun u hu huω => ?_⟩
  have hcontact := isContact_of_mem_outerBoundary (scalesOf C) c j Dom hx
  have hsourceSphere : C.source < C.sphere := by
    change C.source < C.source + C.shell
    have hshell := hwf.base.shell_pos
    omega
  have hsourceTarget : C.source < C.faceTarget :=
    lt_of_lt_of_le hsourceSphere
      (le_trans hwf.base.sphere_le_coalTarget hwf.base.coalTarget_le_faceTarget)
  have hsourceTarget' : (C.source : ℤ) < (C.faceTarget : ℤ) := by
    exact_mod_cast hsourceTarget
  rw [face, Finset.mem_filter] at hu
  have hucoord := hu.2
  change u ∈ (↑((box d C.source).image (fun z => z + v)) : Set (Site d)) at huω
  rw [Finset.mem_coe, Finset.mem_image] at huω
  obtain ⟨z, hz, hzu⟩ := huω
  have hzbound := mem_box.1 hz (cI (scalesOf C) c j x)
  have hzucoord := congrFun hzu (cI (scalesOf C) c j x)
  simp only [Pi.add_apply] at hzucoord
  have hvcoord :
      v (cI (scalesOf C) c j x) =
        c (cI (scalesOf C) c j x) +
          cσ (scalesOf C) c j x *
            (ρO (scalesOf C) j (cI (scalesOf C) c j x) - C.faceTarget) := by
    simp [v, cubeCentre, scalesOf]
  have hsign : cσ (scalesOf C) c j x = 1 ∨ cσ (scalesOf C) c j x = -1 :=
    (dir_spec hcontact).1
  rcases hsign with hsign | hsign <;>
    rw [hsign] at hucoord hvcoord <;>
    simp only [one_mul, neg_one_mul] at hucoord hvcoord <;>
    omega

/-!
## Why the requested constructor does not follow

There are two independent obstructions in the stated interfaces.

* `prob_candidate_ge` is the union bound furnished by `ValidAt2`: its loss is
  `faceTol + pairs * coalTol`.  `Certificate2.WellFormed` records only
  `faceTol ≤ eta` and `coalTol ≤ eta`; it does not record
  `faceTol + pairs * coalTol ≤ eta`, which the `ShellWindow.prob` field would require.
* More basically, `candidate_contains_no_open_relay` proves that this proposed intersection does
  not imply even `∃ u ∈ face ..., u ∈ ω`, the first pointwise clause of
  `ShellWindow.relay`.  The recorded `localFaceEvent source faceTarget` reaches every face of the
  radius-`source` box, whereas the corridor's `face` is a face of the radius-`faceTarget` support
  cube.  Well-formedness forces `source < faceTarget`.  Containment assumptions on `T` cannot make
  a closed relay site open.

Consequently the requested `exists_shellWindow` theorem, with `Gx` built from the prescribed
translated face/all-pairs-coalescence intersection, cannot be constructed from `WellFormed`,
`ValidAt2`, and a containment hypothesis on `T`.  Making `T` so large that the relay becomes
trivial would evade, rather than implement, the requested coalescence argument.
-/

end KNAll.Site.ShellBuild

end
