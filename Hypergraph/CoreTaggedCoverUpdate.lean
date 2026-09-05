import Hypergraph.CoreBatchShadow
import Hypergraph.CoreTaggedCover

/-!
# Updating the tagged cover after a core batch

This module performs the deterministic reclassification required at the final macro commit.
Every old live edge whose head is the examined centre becomes settled; the other old live edges
remain live.  The incoming edge becomes settled.  On success the new outgoing edges become live,
while on failure they become settled.

The update theorems intentionally expose only two mathematical inputs: persistence of the old
live reservations not aimed at the centre, and acquisition of reservations for the new heads on
success.  All macro-verdict and cover bookkeeping is proved here.
-/

noncomputable section

namespace KNAll.Site.CoreCoverUpdate

open Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]
variable {r t : Nat} {q : unitInterval} {eps : Real} {h : MacroExp.Tr d}

abbrev Tr (d : Nat) := BDDom.Transcript (Site d) (Site 2)
abbrev Edge := CoreTaggedCover.Edge

def moved (C : CoreTaggedCover.Tagged r t q eps h) (z : Site 2) : Finset Edge :=
  C.live.filter fun e => e.2 = z

def kept (C : CoreTaggedCover.Tagged r t q eps h) (z : Site 2) : Finset Edge :=
  C.live.filter fun e => e.2 ≠ z

def newEdges (h : MacroExp.Tr d) (z : Site 2) : Finset Edge :=
  (CoreFrontier.newHeads (d := d) h z).image fun y => (z, y)

theorem mem_newEdges_iff {h : MacroExp.Tr d} {z : Site 2} {e : Edge} :
    e ∈ newEdges h z ↔ e.1 = z ∧ e.2 ∈ CoreFrontier.newHeads (d := d) h z := by
  classical
  constructor
  · intro he
    rw [newEdges, Finset.mem_image] at he
    obtain ⟨y, hy, hey⟩ := he
    subst e
    exact ⟨rfl, hy⟩
  · rintro ⟨he, hy⟩
    rw [newEdges, Finset.mem_image]
    refine ⟨e.2, hy, ?_⟩
    exact Prod.ext he.symm rfl

theorem liveRegion_subset_edgeRegion (d r t : Nat) (e : Edge) :
    CoreFresh.liveRegion d r t e.1 e.2 ⊆ MacroExp.E d r t e.1 e.2 :=
  Finset.sdiff_subset

/-! ## Successful commit -/

def successSettled (C : CoreTaggedCover.Tagged r t q eps h) (w z : Site 2) :
    Finset Edge :=
  insert (w, z) (C.settled ∪ moved C z)

def successLive (C : CoreTaggedCover.Tagged r t q eps h) (z : Site 2) :
    Finset Edge :=
  kept C z ∪ newEdges h z

def tagged_success_eq
    {r t : Nat} {q : unitInterval} {eps : Real}
    {base k : Tr d}
    (C : CoreTaggedCover.Tagged r t q eps base.base)
    (hopen : k.base.openV = base.base.openV)
    (hclosed : k.base.closedV = base.base.closedV)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (newEdges base.base z))
    (hpersist : ∀ e ∈ C.live, e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base e.1 e.2)
    (hnew : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base z,
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base z y) :
    CoreTaggedCover.Tagged r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base := by
  classical
  let post := (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base
  have hOldOpen : base.base.openV ⊆ post.openV := by
    intro v hv
    change v ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).openV
    rw [BDDom.Transcript.step_openV]
    simp only [if_true, Finset.mem_insert]
    apply Or.inr
    change v ∈ k.base.openV
    rw [hopen]
    exact hv
  have hOldDet : base.base.openV ∪ base.base.closedV ⊆ post.openV ∪ post.closedV := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact Finset.mem_union_left _ (hOldOpen hv)
    · apply Finset.mem_union_right
      change v ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).closedV
      rw [BDDom.Transcript.step_closedV]
      simp only [if_true]
      change v ∈ k.base.closedV
      rw [hclosed]
      exact hv
  refine
    { settled := successSettled C w z
      live := successLive C z
      settled_ok := ?_
      live_ok := ?_
      cover := ?_ }
  · intro e he
    rw [successSettled, Finset.mem_insert, Finset.mem_union] at he
    rcases he with rfl | he | he
    · refine ⟨MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 hz).1,
        ?_, ?_⟩
      · exact hOldDet (Finset.mem_union_left _ hw)
      · apply Finset.mem_union_left
        change z ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).openV
        simp
    · have heOld := C.settled_ok e he
      exact ⟨heOld.1, hOldDet heOld.2.1, hOldDet heOld.2.2⟩
    · rw [moved, Finset.mem_filter] at he
      have heOld := C.live_ok e he.1
      refine ⟨MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 heOld.2.1).1,
        hOldDet (Finset.mem_union_left _ heOld.1), ?_⟩
      apply Finset.mem_union_left
      change e.2 ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).openV
      simp [he.2]
  · intro e he
    unfold CoreTaggedCover.Live
    change e.1 ∈ post.openV ∧ e.2 ∈ MacroExp.pending d post e.1 ∧
      CoreRes.Bound r t q eps post e.1 e.2
    rw [successLive, Finset.mem_union] at he
    rcases he with he | he
    · rw [kept, Finset.mem_filter] at he
      have heOld := C.live_ok e he.1
      refine ⟨hOldOpen heOld.1, ?_, hpersist e he.1 he.2⟩
      rw [MacroExp.mem_pending]
      refine ⟨((MacroExp.mem_pending (d := d)).1 heOld.2.1).1, ?_⟩
      intro hdet
      have hundet := ((MacroExp.mem_pending (d := d)).1 heOld.2.1).2
      change e.2 ∈
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).openV ∪
          (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).closedV at hdet
      rw [BDDom.Transcript.step_openV, BDDom.Transcript.step_closedV] at hdet
      simp only [if_true, Finset.mem_union, Finset.mem_insert] at hdet
      rcases hdet with (hez | heo) | hec
      · exact he.2 hez
      · change e.2 ∈ k.base.openV at heo
        rw [hopen] at heo
        exact hundet (Finset.mem_union_left _ heo)
      · change e.2 ∈ k.base.closedV at hec
        rw [hclosed] at hec
        exact hundet (Finset.mem_union_right _ hec)
    · have heNew := (mem_newEdges_iff (d := d)).1 he
      have htail : e.1 ∈ post.openV := by
        rw [heNew.1]
        change z ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).openV
        simp
      have hpend : e.2 ∈ MacroExp.pending d post e.1 := by
        rw [heNew.1, MacroExp.mem_pending]
        refine ⟨((MacroExp.mem_pending (d := d)).1
          ((CoreFrontier.mem_newHeads (d := d)).1 heNew.2).1).1, ?_⟩
        have hyUndet := ((MacroExp.mem_pending (d := d)).1
          ((CoreFrontier.mem_newHeads (d := d)).1 heNew.2).1).2
        intro hdet
        change e.2 ∈
          (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).openV ∪
            (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).closedV at hdet
        rw [BDDom.Transcript.step_openV, BDDom.Transcript.step_closedV] at hdet
        simp only [if_true, Finset.mem_union, Finset.mem_insert] at hdet
        rcases hdet with (hyz | hyo) | hyc
        · have hadj := ((MacroExp.mem_pending (d := d)).1
            ((CoreFrontier.mem_newHeads (d := d)).1 heNew.2).1).1
          have hadj' := MacroExp.adj_of_mem_nbrs hadj
          rw [hyz] at hadj
          rw [hyz] at hadj'
          exact (SimpleGraph.irrefl _) hadj'
        · change e.2 ∈ k.base.openV at hyo
          rw [hopen] at hyo
          exact hyUndet (Finset.mem_union_left _ hyo)
        · change e.2 ∈ k.base.closedV at hyc
          rw [hclosed] at hyc
          exact hyUndet (Finset.mem_union_right _ hyc)
      have hbound : CoreRes.Bound r t q eps post e.1 e.2 := by
        rw [heNew.1]
        exact hnew e.2 heNew.2
      exact ⟨htail, hpend, hbound⟩
  · intro x hx
    have hxk : x ∈ k.inspected := by
      simpa only [BDDom.Transcript.step_inspected, Finset.union_empty] using hx
    have hxR := hreads hxk
    simp only [Finset.mem_union] at hxR ⊢
    rcases hxR with (hxOld | hxIn) | hxNew
    · have hxC := C.cover hxOld
      simp only [Finset.mem_union] at hxC
      rcases hxC with (hxQ | hxS) | hxL
      · exact Or.inl (Or.inl hxQ)
      · left; right
        rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion] at hxS ⊢
        obtain ⟨e, he, hxe⟩ := hxS
        exact ⟨e, by simp [successSettled, he], hxe⟩
      · rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion] at hxL
        obtain ⟨e, he, hxe⟩ := hxL
        by_cases hez : e.2 = z
        · left; right
          rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion]
          exact ⟨e, by simp [successSettled, moved, he, hez],
            liveRegion_subset_edgeRegion d r t e hxe⟩
        · right
          rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion]
          exact ⟨e, by simp [successLive, kept, he, hez], hxe⟩
    · left; right
      rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion]
      exact ⟨(w, z), by simp [successSettled], hxIn⟩
    · right
      rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion] at hxNew ⊢
      obtain ⟨e, he, hxe⟩ := hxNew
      exact ⟨e, by simp [successLive, he], hxe⟩

/-- Compatibility wrapper for the original phase interface.  The update itself is proved by
`tagged_success_eq`, which needs only the two macro-verdict equalities and is therefore also
usable by the corrected admissibility-indexed scheduler. -/
def tagged_success
    {r t : Nat} {q : unitInterval} {eps : Real}
    (R : BDAdaptReg.RevealPhase (Site d) (Site 2))
    {base k : Tr d} (hk : R.Phase base k)
    (C : CoreTaggedCover.Tagged r t q eps base.base)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (newEdges base.base z))
    (hpersist : ∀ e ∈ C.live, e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base e.1 e.2)
    (hnew : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base z,
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base z y) :
    CoreTaggedCover.Tagged r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base :=
  tagged_success_eq C
    (by exact R.openV_eq base k hk)
    (by exact R.closedV_eq base k hk)
    hw hz omega hreads hpersist hnew

/-! ## Failed commit -/

def failureSettled (C : CoreTaggedCover.Tagged r t q eps h) (w z : Site 2) :
    Finset Edge :=
  successSettled C w z ∪ newEdges h z

def failureLive (C : CoreTaggedCover.Tagged r t q eps h) (z : Site 2) :
    Finset Edge :=
  kept C z

/-- On failure all new heads are pessimistically closed.  Hence every newly read outgoing edge
may be tagged settled, including heads whose probe was not reached. -/
def tagged_failure_eq
    {r t : Nat} {q : unitInterval} {eps : Real}
    {base k : Tr d}
    (C : CoreTaggedCover.Tagged r t q eps base.base)
    (hopen : k.base.openV = base.base.openV)
    (hclosed : k.base.closedV = base.base.closedV)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (newEdges base.base z))
    (hpersist : ∀ e ∈ C.live, e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base e.1 e.2) :
    CoreTaggedCover.Tagged r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base := by
  classical
  let post := (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base
  have hOldOpen : base.base.openV ⊆ post.openV := by
    intro v hv
    change v ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).openV
    rw [BDDom.Transcript.step_openV]
    simp only [Bool.false_eq_true, if_false]
    change v ∈ k.base.openV
    rw [hopen]
    exact hv
  have hOldDet : base.base.openV ∪ base.base.closedV ⊆ post.openV ∪ post.closedV := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact Finset.mem_union_left _ (hOldOpen hv)
    · apply Finset.mem_union_right
      change v ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).closedV
      rw [BDDom.Transcript.step_closedV]
      simp only [Bool.false_eq_true, if_false, Finset.mem_union, Finset.mem_insert]
      exact Or.inl (Or.inr (by
        change v ∈ k.base.closedV
        rw [hclosed]
        exact hv))
  refine
    { settled := failureSettled C w z
      live := failureLive C z
      settled_ok := ?_
      live_ok := ?_
      cover := ?_ }
  · intro e he
    rw [failureSettled, Finset.mem_union] at he
    rcases he with he | he
    · rw [successSettled, Finset.mem_insert, Finset.mem_union] at he
      rcases he with rfl | he | he
      · refine ⟨MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 hz).1,
          hOldDet (Finset.mem_union_left _ hw), ?_⟩
        apply Finset.mem_union_right
        change z ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).closedV
        simp
      · have heOld := C.settled_ok e he
        exact ⟨heOld.1, hOldDet heOld.2.1, hOldDet heOld.2.2⟩
      · rw [moved, Finset.mem_filter] at he
        have heOld := C.live_ok e he.1
        refine ⟨MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 heOld.2.1).1,
          hOldDet (Finset.mem_union_left _ heOld.1), ?_⟩
        apply Finset.mem_union_right
        change e.2 ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).closedV
        simp [he.2]
    · have heNew := (mem_newEdges_iff (d := d)).1 he
      have hyPending := (CoreFrontier.mem_newHeads (d := d)).1 heNew.2 |>.1
      refine ⟨?_, ?_, ?_⟩
      · rw [heNew.1]
        exact MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 hyPending).1
      · apply Finset.mem_union_right
        change e.1 ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).closedV
        rw [heNew.1]
        simp
      · apply Finset.mem_union_right
        change e.2 ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).closedV
        rw [BDDom.Transcript.step_closedV]
        simp only [Bool.false_eq_true, if_false, Finset.mem_union, Finset.mem_insert]
        exact Or.inr heNew.2
  · intro e he
    unfold CoreTaggedCover.Live
    change e.1 ∈ post.openV ∧ e.2 ∈ MacroExp.pending d post e.1 ∧
      CoreRes.Bound r t q eps post e.1 e.2
    rw [failureLive, kept, Finset.mem_filter] at he
    have heOld := C.live_ok e he.1
    refine ⟨hOldOpen heOld.1, ?_, hpersist e he.1 he.2⟩
    rw [MacroExp.mem_pending]
    refine ⟨((MacroExp.mem_pending (d := d)).1 heOld.2.1).1, ?_⟩
    have hundet := ((MacroExp.mem_pending (d := d)).1 heOld.2.1).2
    have hfront : CoreFrontier.Frontier base.base e.2 := by
      exact ⟨hundet, e.1, heOld.1,
        ((MacroExp.mem_pending (d := d)).1 heOld.2.1).1⟩
    intro hdet
    change e.2 ∈
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).openV ∪
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).closedV at hdet
    rw [BDDom.Transcript.step_openV, BDDom.Transcript.step_closedV] at hdet
    simp only [Bool.false_eq_true, if_false, Finset.mem_union, Finset.mem_insert] at hdet
    rcases hdet with heo | (hez | hec) | hed
    · change e.2 ∈ k.base.openV at heo
      rw [hopen] at heo
      exact hundet (Finset.mem_union_left _ heo)
    · exact he.2 hez
    · change e.2 ∈ k.base.closedV at hec
      rw [hclosed] at hec
      exact hundet (Finset.mem_union_right _ hec)
    · exact ((CoreFrontier.mem_newHeads (d := d)).1 hed).2 hfront
  · intro x hx
    have hxk : x ∈ k.inspected := by
      simpa only [BDDom.Transcript.step_inspected, Finset.union_empty] using hx
    have hxR := hreads hxk
    simp only [Finset.mem_union] at hxR ⊢
    rcases hxR with (hxOld | hxIn) | hxNew
    · have hxC := C.cover hxOld
      simp only [Finset.mem_union] at hxC
      rcases hxC with (hxQ | hxS) | hxL
      · exact Or.inl (Or.inl hxQ)
      · left; right
        rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion] at hxS ⊢
        obtain ⟨e, he, hxe⟩ := hxS
        exact ⟨e, by simp [failureSettled, successSettled, he], hxe⟩
      · rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion] at hxL
        obtain ⟨e, he, hxe⟩ := hxL
        by_cases hez : e.2 = z
        · left; right
          rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion]
          exact ⟨e, by simp [failureSettled, successSettled, moved, he, hez],
            liveRegion_subset_edgeRegion d r t e hxe⟩
        · right
          rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion]
          exact ⟨e, by simp [failureLive, kept, he, hez], hxe⟩
    · left; right
      rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion]
      exact ⟨(w, z), by simp [failureSettled, successSettled], hxIn⟩
    · left; right
      rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion] at hxNew
      obtain ⟨e, he, hxe⟩ := hxNew
      rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion]
      exact ⟨e, by simp [failureSettled, he], liveRegion_subset_edgeRegion d r t e hxe⟩

/-- Compatibility wrapper for the original phase interface. -/
def tagged_failure
    {r t : Nat} {q : unitInterval} {eps : Real}
    (R : BDAdaptReg.RevealPhase (Site d) (Site 2))
    {base k : Tr d} (hk : R.Phase base k)
    (C : CoreTaggedCover.Tagged r t q eps base.base)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (newEdges base.base z))
    (hpersist : ∀ e ∈ C.live, e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base e.1 e.2) :
    CoreTaggedCover.Tagged r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base :=
  tagged_failure_eq C
    (by exact R.openV_eq base k hk)
    (by exact R.closedV_eq base k hk)
    hw hz omega hreads hpersist

/-! ## Proposition-valued update interfaces -/

/-- Verdict-equality form of the successful update, independent of either reveal-phase
interface. -/
theorem holds_success_eq
    {r t : Nat} {q : unitInterval} {eps : Real}
    {base k : Tr d}
    (hopen : k.base.openV = base.base.openV)
    (hclosed : k.base.closedV = base.base.closedV)
    (hC : CoreTaggedCover.Holds r t q eps base.base)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (newEdges base.base z))
    (hpersist : ∀ e, CoreTaggedCover.Live r t q eps base.base e → e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base e.1 e.2)
    (hnew : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base z,
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base z y) :
    CoreTaggedCover.Holds r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base := by
  rcases hC with ⟨settled, live, hs, hl, hcover⟩
  let C : CoreTaggedCover.Tagged r t q eps base.base :=
    { settled := settled
      live := live
      settled_ok := hs
      live_ok := hl
      cover := hcover }
  exact (tagged_success_eq C hopen hclosed hw hz omega hreads
    (fun e he hne => hpersist e (C.live_ok e he) hne) hnew).holds

/-- Verdict-equality form of the failed update, independent of either reveal-phase interface. -/
theorem holds_failure_eq
    {r t : Nat} {q : unitInterval} {eps : Real}
    {base k : Tr d}
    (hopen : k.base.openV = base.base.openV)
    (hclosed : k.base.closedV = base.base.closedV)
    (hC : CoreTaggedCover.Holds r t q eps base.base)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (newEdges base.base z))
    (hpersist : ∀ e, CoreTaggedCover.Live r t q eps base.base e → e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base e.1 e.2) :
    CoreTaggedCover.Holds r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base := by
  rcases hC with ⟨settled, live, hs, hl, hcover⟩
  let C : CoreTaggedCover.Tagged r t q eps base.base :=
    { settled := settled
      live := live
      settled_ok := hs
      live_ok := hl
      cover := hcover }
  exact (tagged_failure_eq C hopen hclosed hw hz omega hreads
    (fun e he hne => hpersist e (C.live_ok e he) hne)).holds

/-- Successful final commit preserves the proposition-valued tagged-cover invariant.  This is
the form consumed by an exploration's `Admissible` predicate: the old edge lists are unpacked
from `Holds`, updated by `tagged_success`, and repackaged without any choice or hidden
inhabitedness assumption. -/
theorem holds_success
    {r t : Nat} {q : unitInterval} {eps : Real}
    (R : BDAdaptReg.RevealPhase (Site d) (Site 2))
    {base k : Tr d} (hk : R.Phase base k)
    (hC : CoreTaggedCover.Holds r t q eps base.base)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (newEdges base.base z))
    (hpersist : ∀ e, CoreTaggedCover.Live r t q eps base.base e → e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base e.1 e.2)
    (hnew : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base z,
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base z y) :
    CoreTaggedCover.Holds r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base := by
  rcases hC with ⟨settled, live, hs, hl, hcover⟩
  let C : CoreTaggedCover.Tagged r t q eps base.base :=
    { settled := settled
      live := live
      settled_ok := hs
      live_ok := hl
      cover := hcover }
  exact (tagged_success R hk C hw hz omega hreads
    (fun e he hne => hpersist e (C.live_ok e he) hne) hnew).holds

/-- Failed final commit preserves the proposition-valued tagged-cover invariant.  New outgoing
regions are reclassified as settled and their heads are included in the pessimistic damage set;
only reservations whose heads were not the failed centre must persist. -/
theorem holds_failure
    {r t : Nat} {q : unitInterval} {eps : Real}
    (R : BDAdaptReg.RevealPhase (Site d) (Site 2))
    {base k : Tr d} (hk : R.Phase base k)
    (hC : CoreTaggedCover.Holds r t q eps base.base)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (newEdges base.base z))
    (hpersist : ∀ e, CoreTaggedCover.Live r t q eps base.base e → e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base e.1 e.2) :
    CoreTaggedCover.Holds r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base := by
  rcases hC with ⟨settled, live, hs, hl, hcover⟩
  let C : CoreTaggedCover.Tagged r t q eps base.base :=
    { settled := settled
      live := live
      settled_ok := hs
      live_ok := hl
      cover := hcover }
  exact (tagged_failure R hk C hw hz omega hreads
    (fun e he hne => hpersist e (C.live_ok e he) hne)).holds

#print axioms KNAll.Site.CoreCoverUpdate.tagged_success
#print axioms KNAll.Site.CoreCoverUpdate.tagged_failure
#print axioms KNAll.Site.CoreCoverUpdate.holds_success_eq
#print axioms KNAll.Site.CoreCoverUpdate.holds_failure_eq
#print axioms KNAll.Site.CoreCoverUpdate.holds_success
#print axioms KNAll.Site.CoreCoverUpdate.holds_failure

end KNAll.Site.CoreCoverUpdate

end
