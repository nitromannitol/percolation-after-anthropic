import Hypergraph.SourceEstimate

/-!
# The entrance estimate for a fresh long corridor

This file holds the innermost target box `innerBox`, its containment and translation geometry, the
anchored cylinder experiment for a fresh corridor, and the transfer of such an experiment to the
pinned law of a transcript.  Every vertex of a pending edge region is fresh, so an estimate for the
finite cylinder event obtained by forcing a *recorded-open* source open transfers verbatim
(`entranceExperiment_prob_le_prob`).

**What this file no longer claims.**  Three theorems used to conclude the pending-edge source
estimate at the designated tip `MacroExp.src d r n h`, from the premise
`hopen : src d r n h ∈ h.openSites`.  That premise is refuted at reachable good transcripts by
`math/RECORDED_OPEN_ENTRY.md` §2, whose counterexample is cut out by a positive-probability
cylinder.  All three are retired; the retirement note below names them.

**What is assumed now, and where it must be discharged.**  The estimate is exposed as a name with
the source a parameter, `InnerSourceEstimate`, and with the recorded origin as the intended
instance, `InnerOriginSourceEstimate`.  No theorem here or elsewhere establishes it at a post-step
transcript; that construction, inside the iterated tolerance `CorrMove.beta`, is the remaining H2
obligation.  Its one proved instance is the initial one, `InitBridge.hinitialLongBox_holds`, which
runs through the wide initial face `InitEnt.entryFace` and never mentions a tip.

The certificate records the face experiment and all pairwise coalescence experiments, but not the
anchored long-box experiment; that missing cylinder bound stays visible as the explicit hypothesis
of `sourceEstimate_of_cylinderBound`.  No proposition or structure is introduced as a substitute
for the geometric chaining argument.
-/

noncomputable section

namespace KNAll.Site.LongBox

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor KNAll.Site.MacroExp

variable {d : ℕ} [NeZero d]

/-! ## The finite anchored experiment -/

/-- The innermost level box, centred at the head of a macro corridor. -/
def innerBox (C : LeftImp2.Certificate2 d) (c : Site d) : Finset (Site d) :=
  Ibox (scalesOf C) c (C.levels - 1)

/-- The event that an independently sampled configuration connects through `Reg` after its source
is forced open.  This is the right unconditioned cylinder event for a source which the transcript
has already recorded open. -/
def forcedEntranceEvent (Reg : Finset (Site d)) (o : Site d) (B : Set (Site d)) :
    Set (SiteConfig (Site d)) :=
  openSite o ⁻¹'
    connWithinSet (zdGraph d) (↑(insert o Reg) : Set (Site d)) o B

/-- The forced entrance event is decided by the finite set consisting of the corridor and its
source. -/
theorem determinedBy_forcedEntranceEvent (Reg : Finset (Site d)) (o : Site d)
    (B : Set (Site d)) :
    DeterminedBy (forcedEntranceEvent Reg o B)
      (↑(insert o Reg) : Set (Site d)) := by
  unfold forcedEntranceEvent
  have h := TargetExt.determinedBy_substitute_preimage_of_determinedBy
    (determinedBy_connWithinSet (zdGraph d) (↑(insert o Reg) : Set (Site d)) o B)
    ({o} : Set (Site d)) (fun _ => True)
  rw [funext (substitute_singleton_true (V := Site d) o)] at h
  exact h.mono Set.sdiff_subset

theorem measurableSet_forcedEntranceEvent (Reg : Finset (Site d)) (o : Site d)
    (B : Set (Site d)) : MeasurableSet (forcedEntranceEvent Reg o B) := by
  unfold forcedEntranceEvent
  exact measurable_openSite o
    (measurableSet_connWithinSet (zdGraph d) (insert o Reg) o B)

/-- The anchored long-box event as a `CylinderExperiment`, so its bound can be recorded in the
same finite certificate list as the face and coalescence experiments. -/
def entranceExperiment (Reg : Finset (Site d)) (o : Site d) (B : Set (Site d)) :
    CylinderExperiment d where
  support := insert o Reg
  event := forcedEntranceEvent Reg o B
  determined := determinedBy_forcedEntranceEvent Reg o B
  measurable' := measurableSet_forcedEntranceEvent Reg o B

/-- The concrete experiment in the oriented macro corridor `w → z`, aimed at the innermost box
centred at the head. -/
def corridorExperiment (C : LeftImp2.Certificate2 d) (r t : ℕ) (w z : Site 2) :
    CylinderExperiment d :=
  entranceExperiment (E d r t w z) (tip d r w z)
    (↑(innerBox C (ctr d r z)) : Set (Site d))

/-! ## Translation of the finite experiment

Only the four corridors out of the planar origin need to be stored in a finite certificate.
Translation invariance carries those four bounds to every oriented macro-edge. -/

/-- Translation of a set of lattice sites by `v`. -/
def shiftSet (v : Site d) (S : Set (Site d)) : Set (Site d) :=
  {x | x - v ∈ S}

/-- Translation of a finite set of lattice sites by `v`. -/
def shiftFinset (v : Site d) (F : Finset (Site d)) : Finset (Site d) :=
  F.image fun x => x + v

@[simp] theorem mem_shiftSet (v x : Site d) (S : Set (Site d)) :
    x ∈ shiftSet v S ↔ x - v ∈ S := Iff.rfl

@[simp] theorem add_mem_shiftSet (v x : Site d) (S : Set (Site d)) :
    x + v ∈ shiftSet v S ↔ x ∈ S := by
  simp [shiftSet]

@[simp] theorem mem_shiftFinset (v x : Site d) (F : Finset (Site d)) :
    x ∈ shiftFinset v F ↔ x - v ∈ F := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.2 ⟨x - v, hx, by simp⟩

theorem coe_shiftFinset (v : Site d) (F : Finset (Site d)) :
    (↑(shiftFinset v F) : Set (Site d)) = shiftSet v (↑F : Set (Site d)) := by
  ext x
  simp

@[simp] theorem shiftFinset_insert (v o : Site d) (F : Finset (Site d)) :
    shiftFinset v (insert o F) = insert (o + v) (shiftFinset v F) := by
  classical
  simp [shiftFinset]

theorem shiftFinset_sdiff (v : Site d) (F K : Finset (Site d)) :
    shiftFinset v (F \ K) = shiftFinset v F \ shiftFinset v K := by
  ext x
  simp

theorem shiftFinset_rbox (v c : Site d) (rho : Fin d → ℤ) :
    shiftFinset v (rbox c rho) = rbox (c + v) rho := by
  classical
  ext x
  rw [mem_shiftFinset]
  rw [mem_rbox, mem_rbox]
  constructor <;> intro h j
  · have hj := h j
    simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
    omega
  · have hj := h j
    simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
    omega

theorem shiftFinset_abox (v c : Site d) (R t : ℕ) :
    shiftFinset v (abox c R t) = abox (c + v) R t := by
  rw [abox_eq_rbox, abox_eq_rbox]
  exact shiftFinset_rbox v c (rad R t)

theorem shiftFinset_hbox (v c c' : Site d) (R t : ℕ) :
    shiftFinset v (hbox c c' R t) = hbox (c + v) (c' + v) R t := by
  classical
  ext x
  rw [mem_shiftFinset]
  rw [mem_hbox, mem_hbox]
  constructor <;> intro h j
  · have hj := h j
    simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
    omega
  · have hj := h j
    simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
    omega

@[simp] theorem ctr_zero (r : ℕ) : ctr d r (0 : Site 2) = 0 := by
  funext j
  simp [ctr, emb]

theorem ctr_add (r : ℕ) (x y : Site 2) :
    ctr d r (x + y) = ctr d r x + ctr d r y := by
  funext j
  by_cases hj : j.val < 2
  · simp [ctr, emb, hj, Pi.add_apply]
    ring
  · simp [ctr, emb, hj]

theorem ctr_sub_add (r : ℕ) (w z : Site 2) :
    ctr d r (z - w) + ctr d r w = ctr d r z := by
  rw [← ctr_add]
  congr 1
  abel

theorem tip_sub_add (r : ℕ) (w z : Site 2) :
    tip d r 0 (z - w) + ctr d r w = tip d r w z := by
  funext j
  by_cases hj : j.val < 2
  · simp [tip, ctr, emb, hj, Pi.sub_apply, Pi.add_apply]
    ring
  · simp [tip, ctr, emb, hj, Pi.add_apply]

theorem shiftFinset_E (r t : ℕ) (w z : Site 2) :
    shiftFinset (ctr d r w) (E d r t 0 (z - w)) = E d r t w z := by
  rw [E, E, shiftFinset_sdiff, shiftFinset_hbox, Q, shiftFinset_abox,
    ctr_zero, zero_add, ctr_sub_add]
  rfl

theorem shiftFinset_innerBox (C : LeftImp2.Certificate2 d) (v c : Site d) :
    shiftFinset v (innerBox C c) = innerBox C (c + v) := by
  unfold innerBox Ibox
  exact shiftFinset_rbox v c _

theorem siteShift_inter_shiftSet (v : Site d) (omega : SiteConfig (Site d))
    (S : Set (Site d)) :
    siteShift v (omega ∩ shiftSet v S) = siteShift v omega ∩ S := by
  ext x
  simp [siteShift, shiftSet]

theorem mem_connWithin_shift_iff (v : Site d) (omega : SiteConfig (Site d))
    (S : Set (Site d)) (x y : Site d) :
    siteShift v omega ∈ connWithin (zdGraph d) S x y ↔
      omega ∈ connWithin (zdGraph d) (shiftSet v S) (x + v) (y + v) := by
  rw [mem_connWithin_iff, mem_connWithin_iff]
  have hreach := reachable_siteShift_iff v (omega ∩ shiftSet v S) x y
  rw [siteShift_inter_shiftSet] at hreach
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨⟨?_, ?_⟩, hreach.1 hxy⟩
    · simpa using hx.1
    · simpa [shiftSet] using hx.2
  · rintro ⟨hx, hxy⟩
    refine ⟨⟨?_, ?_⟩, hreach.2 hxy⟩
    · simpa using hx.1
    · simpa [shiftSet] using hx.2

theorem mem_connWithinSet_shift_iff (v : Site d) (omega : SiteConfig (Site d))
    (S : Set (Site d)) (x : Site d) (B : Set (Site d)) :
    siteShift v omega ∈ connWithinSet (zdGraph d) S x B ↔
      omega ∈ connWithinSet (zdGraph d) (shiftSet v S) (x + v) (shiftSet v B) := by
  rw [mem_connWithinSet_iff, mem_connWithinSet_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y + v, by simpa [shiftSet] using hy,
      (mem_connWithin_shift_iff v omega S x y).1 hxy⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y - v, by simpa [shiftSet] using hy, ?_⟩
    have h := (mem_connWithin_shift_iff v omega S x (y - v)).2
    exact h (by simpa using hxy)

theorem siteShift_openSite_add (v o : Site d) (omega : SiteConfig (Site d)) :
    siteShift v (openSite (o + v) omega) = openSite o (siteShift v omega) := by
  ext x
  simp [mem_openSite]

theorem forcedEntranceEvent_shift (v : Site d) (Reg : Finset (Site d))
    (o : Site d) (B : Set (Site d)) :
    forcedEntranceEvent (shiftFinset v Reg) (o + v) (shiftSet v B) =
      siteShift v ⁻¹' forcedEntranceEvent Reg o B := by
  ext omega
  have hsupp :
      shiftSet v (↑(insert o Reg) : Set (Site d)) =
        (↑(insert (o + v) (shiftFinset v Reg)) : Set (Site d)) := by
    rw [← coe_shiftFinset, shiftFinset_insert]
  change openSite (o + v) omega ∈
      connWithinSet (zdGraph d) (↑(insert (o + v) (shiftFinset v Reg)) : Set (Site d))
        (o + v) (shiftSet v B) ↔
    openSite o (siteShift v omega) ∈
      connWithinSet (zdGraph d) (↑(insert o Reg) : Set (Site d)) o B
  rw [← hsupp]
  simpa only [siteShift_openSite_add] using
    (mem_connWithinSet_shift_iff v (openSite (o + v) omega)
      (↑(insert o Reg) : Set (Site d)) o B).symm

theorem corridorExperiment_prob_eq_sub (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (r t : ℕ) (w z : Site 2) :
    (corridorExperiment C r t w z).prob q =
      (corridorExperiment C r t 0 (z - w)).prob q := by
  let v := ctr d r w
  let Reg := E d r t 0 (z - w)
  let o := tip d r 0 (z - w)
  let B := (↑(innerBox C (ctr d r (z - w))) : Set (Site d))
  have hReg : shiftFinset v Reg = E d r t w z := shiftFinset_E r t w z
  have ho : o + v = tip d r w z := tip_sub_add r w z
  have hc : ctr d r (z - w) + v = ctr d r z := ctr_sub_add r w z
  have hB : shiftSet v B =
      (↑(innerBox C (ctr d r z)) : Set (Site d)) := by
    rw [← coe_shiftFinset, shiftFinset_innerBox, hc]
  have hevent :
      forcedEntranceEvent (E d r t w z) (tip d r w z)
          (↑(innerBox C (ctr d r z)) : Set (Site d)) =
        siteShift v ⁻¹' forcedEntranceEvent Reg o B := by
    rw [← hReg, ← ho, ← hB]
    exact forcedEntranceEvent_shift v Reg o B
  change (siteBernoulli (fun _ : Site d => q)).real
      (forcedEntranceEvent (E d r t w z) (tip d r w z)
        (↑(innerBox C (ctr d r z)) : Set (Site d))) =
    (siteBernoulli (fun _ : Site d => q)).real (forcedEntranceEvent Reg o B)
  rw [hevent]
  have hmap := (measurePreserving_siteShift q v).measure_preimage
    (measurableSet_forcedEntranceEvent Reg o B).nullMeasurableSet
  rw [measureReal_def, measureReal_def, hmap]

/-! ## Transfer to a pinned transcript -/

/-- For a fresh finite region, forcing a recorded-open source in an ordinary product sample gives
a subevent of the connection event under the pinned transcript.  This is the measure-theoretic
step needed to use any finite long-box estimate after an arbitrary exploration history. -/
theorem entranceExperiment_prob_le_prob
    (h : Tr d) (Reg : Finset (Site d)) (hfresh : Disjoint Reg h.inspected)
    (o : Site d) (ho : o ∈ h.openSites) (B : Set (Site d)) (q : unitInterval) :
    (entranceExperiment Reg o B).prob q ≤
      h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B) := by
  classical
  rw [FRDom.Transcript.prob_eq]
  unfold pinnedProb CylinderExperiment.prob entranceExperiment
  apply measureReal_mono
  · intro ω hω
    change openSite o ω ∈
      connWithinSet (zdGraph d) (↑(insert o Reg) : Set (Site d)) o B at hω
    change substitute (↑h.inspected : Set (Site d)) h.state ω ∈
      connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B
    rw [mem_connWithinSet_iff] at hω ⊢
    obtain ⟨b, hb, hob⟩ := hω
    refine ⟨b, hb, ?_⟩
    rw [mem_connWithin_iff] at hob ⊢
    refine ⟨?_, hob.2.mono (openSiteGraph_mono (zdGraph d) ?_)⟩
    · constructor
      · rw [mem_substitute_of_mem h.state]
        exact ho
        exact Finset.mem_coe.2 (h.openSites_subset ho)
      · exact Finset.mem_coe.2
          (Finset.mem_union_left Reg (h.openSites_subset ho))
    · intro x hx
      obtain ⟨hxopen, hxsmall⟩ := hx
      have hxsmall' : x = o ∨ x ∈ Reg := Finset.mem_insert.1 (Finset.mem_coe.1 hxsmall)
      constructor
      · rcases hxsmall' with rfl | hxReg
        · rw [mem_substitute_of_mem h.state]
          · exact ho
          · exact Finset.mem_coe.2 (h.openSites_subset ho)
        · have hxnot : x ∉ h.inspected := fun hxins =>
            Finset.disjoint_left.1 hfresh hxReg (Finset.mem_coe.1 hxins)
          rw [mem_substitute_of_notMem h.state hxnot]
          rcases (mem_openSite o ω x).1 hxopen with rfl | hxω
          · exact absurd (h.openSites_subset ho) hxnot
          · exact hxω
      · exact Finset.mem_coe.2 <| hxsmall'.elim
          (fun hxo => hxo ▸ Finset.mem_union_left Reg (h.openSites_subset ho))
          (fun hxReg => Finset.mem_union_right h.inspected hxReg)
  · exact measure_ne_top _ _

/-! ## The actual source and the actual fresh corridor -/

/-- The innermost `Ibox` is contained in every level's `Dbox`, which is the nesting hypothesis
needed when this estimate is passed to `MacroExp.lt_prob_connWithinSet_of_shellWindow`. -/
theorem innerBox_subset_Dbox (C : LeftImp2.Certificate2 d) (c : Site d) {i : ℕ}
    (hi : i < C.levels) : innerBox C c ⊆ Dbox (scalesOf C) c i := by
  unfold innerBox Ibox Dbox
  apply rbox_mono
  intro j
  simp only [ρI, ρO, ρD, scalesOf]
  push_cast
  omega

/-! ### Retirement of the three fixed-source theorems

**Three theorems have been retired from this section:**

```
lt_prob_src_connWithinSet_innerBox_of_cylinderBound
lt_prob_src_connWithinSet_innerBox_of_recordedCylinders
lt_prob_src_connWithinSet_innerBox_of_certificateClause
```

Each concluded the pending-edge source estimate from the designated tip `MacroExp.src d r n h` to
`innerBox`, and each carried the premise `hopen : MacroExp.src d r n h ∈ h.openSites`.  That
premise is false at reachable good transcripts: `math/RECORDED_OPEN_ENTRY.md` §2 exhibits a
positive-probability cylinder whose transcript is good, non-terminal and reachable by
`MacroExp.run`, and at which the designated tip had been inspected closed.  Neither `MacroExp.Good`
nor reachability implies it, and an invariant that does implies the deleted one-site stub
condition, which `Entrance.entranceExperiment_prob_le` caps by the site density.

A repository-wide name search found no reference to any of the three outside this file, so
retiring them severs no proof.  Everything they used is kept: `innerBox` and its containment
geometry, the translation identities, `corridorExperiment`, and the generic transfer
`entranceExperiment_prob_le_prob`, which takes an arbitrary recorded-open source. -/

/-- **The pending-edge source estimate to the innermost box.**  A name for the premise, with the
source `o` a parameter.  Nothing in this file establishes it at any source. -/
def InnerSourceEstimate (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (r t : ℕ) (h : Tr d) (z y : Site 2) (o : Site d) : Prop :=
  RecordedEntry.SourceEstimate C q h (E d r t z y) o
    (↑(innerBox C (ctr d r y)) : Set (Site d))

/-- The origin instance, which is the one the downstream interface uses.  `MacroExp.emb 0` is
recorded open at every good transcript by `RecordedEntry.origin_mem_openSites`, so this estimate
is not the intersection of a crossing with the event that one unread site is open. -/
def InnerOriginSourceEstimate (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (r t : ℕ) (h : Tr d) (z y : Site 2) : Prop :=
  InnerSourceEstimate C q r t h z y (emb 0)

/-- **The generic transfer, with the estimate named.**  For a fresh corridor and a source the
transcript records open, the ordinary anchored cylinder bound is the source estimate under the
pinned law.  The source is a parameter, never `MacroExp.src`. -/
theorem sourceEstimate_of_cylinderBound
    {C : LeftImp2.Certificate2 d} {q : unitInterval} {r t : ℕ} (h : Tr d)
    {z y : Site 2} (hfresh : Disjoint (E d r t z y) h.inspected)
    (o : Site d) (ho : o ∈ h.openSites)
    (hbound : 1 - C.eps / 8 <
      (entranceExperiment (E d r t z y) o
        (↑(innerBox C (ctr d r y)) : Set (Site d))).prob q) :
    InnerSourceEstimate C q r t h z y o :=
  hbound.trans_le
    (entranceExperiment_prob_le_prob h (E d r t z y) hfresh o ho
      (↑(innerBox C (ctr d r y)) : Set (Site d)) q)

/-- **Satisfiability of the innermost-target shape.**  The statement below is definitionally
`InnerSourceEstimate C q r t h z y o`; it is spelled out so that the interface stays visibly an
assumption rather than a proved proposition.

It rules out both the unsatisfiable-hypothesis and the empty-target failure modes for this shape.
The target is nonempty whenever the certificate is well formed, by
`Certificate2.WellFormed.innerBox_nonempty`, and its centre is a member, so the hypothesis `hoB`
below is satisfiable at `o = MacroExp.ctr d r y`.  What the witness does *not* do is cross the
corridor: the estimate the exploration needs has the recorded origin as its source and the
innermost box of a *different* macro vertex as its target, and no theorem here proves that. -/
theorem lt_prob_connWithinSet_innerBox_of_mem_openSites
    {C : LeftImp2.Certificate2 d} (heps : 0 < C.eps) (q : unitInterval) (r t : ℕ)
    (h : Tr d) (z y : Site 2) {o : Site d} (ho : o ∈ h.openSites)
    (hoB : o ∈ innerBox C (ctr d r y)) :
    1 - C.eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ E d r t z y) : Set (Site d)) o
        (↑(innerBox C (ctr d r y)) : Set (Site d))) :=
  RecordedEntry.lt_prob_connWithinSet_of_mem_openSites_of_mem heps q h (E d r t z y) ho
    (Finset.mem_coe.2 hoB)

/-! ## Arithmetic used by the manuscript's fixed-aspect placements -/

/-- Euclidean division by eight in the exact form used to choose the scale of the chain. -/
theorem eight_mul_div_add_mod (r : ℕ) : 8 * (r / 8) + r % 8 = r ∧ r % 8 ≤ 7 := by
  constructor
  · omega
  · exact Nat.le_pred_of_lt (Nat.mod_lt r (by norm_num : 0 < 8))

/-- The aspect-`88` far coordinate chosen by floor division lies between `20r - 88` and `20r`.
The lower bound `r ≥ 44` is the one used later to ensure the chosen scale is nonzero. -/
theorem aspect88_far_mem {r : ℕ} (_h44 : 44 ≤ r) :
    (20 : ℤ) * r - 88 < 88 * ((20 * r : ℤ) / 88) ∧
      88 * ((20 * r : ℤ) / 88) ≤ 20 * r := by
  constructor
  · have h : (20 * r : ℤ) < 88 * ((20 * r : ℤ) / 88) + 88 := by
      exact Int.lt_mul_ediv_self_add (show (0 : ℤ) < 88 by norm_num)
    linarith
  · exact Int.mul_ediv_self_le (by norm_num)

#print axioms KNAll.Site.LongBox.entranceExperiment_prob_le_prob
#print axioms KNAll.Site.LongBox.sourceEstimate_of_cylinderBound
#print axioms KNAll.Site.LongBox.lt_prob_connWithinSet_innerBox_of_mem_openSites
#print axioms KNAll.Site.LongBox.eight_mul_div_add_mod
#print axioms KNAll.Site.LongBox.aspect88_far_mem

end KNAll.Site.LongBox

end
