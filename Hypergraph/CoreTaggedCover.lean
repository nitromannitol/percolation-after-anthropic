import Hypergraph.CoreLiveCover

/-!
# A tagged cover for stopped core probes

The old macro cover required every recorded corridor to have an open tail and a determined head.
That is false during a stopped outgoing probe.  The replacement below separates settled edges
from live reserved edges.  A live edge owns only `E(u,v) \ Q(v)`; its unread head box is reserved
for the later examination of `v`.

The main theorem proves the freshness fact needed to start a new-head probe: if `y` is genuinely
new when `z` is opened, the entire old inspected set is disjoint from `E(z,y)`.  This is a
deterministic consequence of the tagged cover, rather than a new probabilistic assumption.
-/

noncomputable section

namespace KNAll.Site.CoreTaggedCover

open Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

abbrev Edge := Site 2 × Site 2

def settledRegion (d r t : Nat) (edges : Finset Edge) : Finset (Site d) :=
  edges.biUnion fun e => MacroExp.E d r t e.1 e.2

def liveRegions (d r t : Nat) (edges : Finset Edge) : Finset (Site d) :=
  edges.biUnion fun e => CoreFresh.liveRegion d r t e.1 e.2

/-- A settled edge has adjacent, already determined endpoints.  Its tail need not be open. -/
def Settled (h : MacroExp.Tr d) (e : Edge) : Prop :=
  (zdGraph 2).Adj e.1 e.2 ∧ e.1 ∈ h.openV ∪ h.closedV ∧ e.2 ∈ h.openV ∪ h.closedV

/-- A live edge has an open owner, an undetermined adjacent head, and the core reservation which
the owner promises to that head. -/
def Live (r t : Nat) (q : unitInterval) (eps : Real)
    (h : MacroExp.Tr d) (e : Edge) : Prop :=
  e.1 ∈ h.openV ∧ e.2 ∈ MacroExp.pending d h e.1 ∧
    CoreRes.Bound r t q eps h e.1 e.2

/-- Every inspected site is covered by the initial box, a settled full edge region, or the
head-box-free region of a live reserved edge. -/
structure Tagged (r t : Nat) (q : unitInterval) (eps : Real)
    (h : MacroExp.Tr d) where
  settled : Finset Edge
  live : Finset Edge
  settled_ok : ∀ e ∈ settled, Settled h e
  live_ok : ∀ e ∈ live, Live r t q eps h e
  cover : h.inspected ⊆
    MacroExp.Q d r t 0 ∪ settledRegion d r t settled ∪ liveRegions d r t live

/-- Proposition-valued form suitable for an exploration's `Admissible` predicate.  The edge
lists and every validity clause remain explicit witnesses; this is not an opaque `Nonempty`
hypothesis. -/
def Holds (r t : Nat) (q : unitInterval) (eps : Real) (h : MacroExp.Tr d) : Prop :=
  ∃ (settled live : Finset Edge),
    (∀ e ∈ settled, Settled h e) ∧
    (∀ e ∈ live, Live r t q eps h e) ∧
    h.inspected ⊆
      MacroExp.Q d r t 0 ∪ settledRegion d r t settled ∪ liveRegions d r t live

theorem Tagged.holds {r t : Nat} {q : unitInterval} {eps : Real} {h : MacroExp.Tr d}
    (C : Tagged r t q eps h) : Holds r t q eps h :=
  ⟨C.settled, C.live, C.settled_ok, C.live_ok, C.cover⟩

/-- The tagged cover is genuinely inhabited at the standard start transcript; no reservation or
probability hypothesis is needed for this witness. -/
def startTagged (d r t : Nat) [NeZero d] (q : unitInterval) (eps : Real) :
    Tagged r t q eps (MacroExp.start d r t) where
  settled := ∅
  live := ∅
  settled_ok e he := Finset.notMem_empty e he |>.elim
  live_ok e he := Finset.notMem_empty e he |>.elim
  cover := by
    intro x hx
    change x ∈ MacroExp.Q d r t 0 at hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem holds_start (d r t : Nat) [NeZero d] (q : unitInterval) (eps : Real) :
    Holds r t q eps (MacroExp.start d r t) :=
  (startTagged d r t q eps).holds

theorem settled_region_disjoint_newHead (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {h : MacroExp.Tr d} {z y : Site 2} {e : Edge}
    (he : Settled h e) (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    Disjoint (MacroExp.E d r t e.1 e.2) (MacroExp.E d r t z y) := by
  have hyPending := (CoreFrontier.mem_newHeads (d := d)).1 hy |>.1
  have hyUndet := (MacroExp.mem_pending (d := d)).1 hyPending |>.2
  have hadjZY : (zdGraph 2).Adj z y :=
    MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 hyPending).1
  have hhead : e.2 ≠ y := by
    intro hey
    apply hyUndet
    rw [← hey]
    exact he.2.2
  have hrev : ¬ (e.1 = y ∧ e.2 = z) := by
    rintro ⟨hey, -⟩
    apply hyUndet
    rw [← hey]
    exact he.2.1
  exact MacroExp.protectedEdges_disjoint hd r t hr he.1 hadjZY hhead hrev

theorem live_region_disjoint_newHead (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {q : unitInterval} {eps : Real} {h : MacroExp.Tr d} {z y : Site 2} {e : Edge}
    (he : Live r t q eps h e) (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    Disjoint (CoreFresh.liveRegion d r t e.1 e.2) (MacroExp.E d r t z y) := by
  exact (CoreFrontier.oldOwner_region_disjoint_newHead hd hr he.1 he.2.1 hy).mono_left
    Finset.sdiff_subset

theorem initialQ_disjoint_newHead (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {h : MacroExp.Tr d} {z y : Site 2} (hzero : (0 : Site 2) ∈ h.openV)
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    Disjoint (MacroExp.Q d r t 0) (MacroExp.E d r t z y) := by
  have hy0 : (0 : Site 2) ≠ y := by
    intro h0y
    exact CoreFrontier.newHead_not_mem_openV (d := d) hy (h0y ▸ hzero)
  have hadj : (zdGraph 2).Adj z y :=
    MacroExp.adj_of_mem_nbrs
      ((MacroExp.mem_pending (d := d)).1
        ((CoreFrontier.mem_newHeads (d := d)).1 hy).1).1
  exact (MacroExp.protectedEdge_disjoint_Q hd r t hr hadj hy0).symm

/-- A tagged old history is fresh for the full corridor towards every genuinely new head. -/
theorem inspected_disjoint_newHead_edge (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {q : unitInterval} {eps : Real} {h : MacroExp.Tr d} {z y : Site 2}
    (hzero : (0 : Site 2) ∈ h.openV) (C : Tagged r t q eps h)
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    Disjoint h.inspected (MacroExp.E d r t z y) := by
  rw [Finset.disjoint_left]
  intro x hxI hxE
  have hx := C.cover hxI
  simp only [Finset.mem_union] at hx
  rcases hx with (hxQ | hxSettled) | hxLive
  · exact Finset.disjoint_left.1 (initialQ_disjoint_newHead hd hr hzero hy) hxQ hxE
  · rw [settledRegion, Finset.mem_biUnion] at hxSettled
    obtain ⟨e, heC, hxe⟩ := hxSettled
    exact Finset.disjoint_left.1
      (settled_region_disjoint_newHead hd hr (C.settled_ok e heC) hy) hxe hxE
  · rw [liveRegions, Finset.mem_biUnion] at hxLive
    obtain ⟨e, heC, hxe⟩ := hxLive
    exact Finset.disjoint_left.1
      (live_region_disjoint_newHead hd hr (C.live_ok e heC) hy) hxe hxE

theorem inspected_disjoint_newHead_edge_of_holds (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {q : unitInterval} {eps : Real} {h : MacroExp.Tr d} {z y : Site 2}
    (hzero : (0 : Site 2) ∈ h.openV) (hC : Holds r t q eps h)
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    Disjoint h.inspected (MacroExp.E d r t z y) := by
  rcases hC with ⟨settled, live, hs, hl, hc⟩
  exact inspected_disjoint_newHead_edge hd hr hzero
    ⟨settled, live, hs, hl, hc⟩ hy

#print axioms KNAll.Site.CoreTaggedCover.settled_region_disjoint_newHead
#print axioms KNAll.Site.CoreTaggedCover.live_region_disjoint_newHead
#print axioms KNAll.Site.CoreTaggedCover.initialQ_disjoint_newHead
#print axioms KNAll.Site.CoreTaggedCover.inspected_disjoint_newHead_edge
#print axioms KNAll.Site.CoreTaggedCover.holds_start
#print axioms KNAll.Site.CoreTaggedCover.inspected_disjoint_newHead_edge_of_holds

end KNAll.Site.CoreTaggedCover

end
