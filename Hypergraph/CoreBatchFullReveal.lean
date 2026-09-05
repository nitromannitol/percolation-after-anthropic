import Hypergraph.CoreAcceptedSupported
import Hypergraph.CoreFreshness

/-!
# A concrete bounded core-batch reveal

This module constructs the maximal one-round reveal allocated to an accepted batch.  It proves
freshness, exact read containment, and determination of the complete `batchSuccess` verdict by
the resulting transcript.  These facts are useful independently of the eventual stopped-prefix
scheduler and precisely locate why the maximal reveal cannot itself deliver the new reservations:
`CoreStopped.bound_stopLevel` lives at a selected prefix, whereas the maximal reveal also pins the
unused remainder of that same protected edge.
-/

noncomputable section

namespace KNAll.Site.CoreBatchFullReveal

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

abbrev Tr (d : Nat) := BDDom.Transcript (Site d) (Site 2)

/-! ## Proof-independent accepted choices -/

/-- The finite set of reservation-carrying owners of `z`. -/
def owners (r t : Nat) (q : unitInterval) (eps : Real)
    (h : MacroExp.Tr d) (z : Site 2) : Finset (Site 2) := by
  classical
  exact h.openV.filter fun u => z ∈ MacroExp.pending d h u ∧ CoreRes.Bound r t q eps h u z

/-- A proof-independent owner selection.  The fallback is used only outside accepted active
histories; `owner_spec` eliminates it on every state consumed by the exploration. -/
def owner (r t : Nat) (q : unitInterval) (eps : Real)
    (h : MacroExp.Tr d) (z : Site 2) : Site 2 := by
  classical
  exact if hs : (owners r t q eps h z).Nonempty then hs.choose else 0

theorem owner_spec {r t : Nat} {q : unitInterval} {eps : Real}
    {h : MacroExp.Tr d} {z : Site 2}
    (hI : CoreFrontier.Invariant r t q eps h) (hz : CoreFrontier.Frontier h z) :
    owner r t q eps h z ∈ h.openV ∧
      z ∈ MacroExp.pending d h (owner r t q eps h z) ∧
      CoreRes.Bound r t q eps h (owner r t q eps h z) z := by
  obtain ⟨u, hu, huz, hbound⟩ := hI z hz
  have hs : (owners r t q eps h z).Nonempty := by
    refine ⟨u, ?_⟩
    simp only [owners, Finset.mem_filter]
    exact ⟨hu, huz, hbound⟩
  rw [owner, dif_pos hs]
  have hc := hs.choose_spec
  simpa only [owners, Finset.mem_filter] using hc

/-! ## The allocated support -/

/-- The complete allocated support, with the old inspected coordinates included for convenient
determination statements. -/
def observedSupport (d r t : Nat) (h : MacroExp.Tr d) (w z : Site 2) :
    Finset (Site d) :=
  h.inspected ∪ CoreRes.batchReadSupport d r t h w z

theorem incomingRegion_subset_batchReadSupport
    (d r t : Nat) (h : MacroExp.Tr d) (w z : Site 2) :
    AtomTower.incomingRegion d r t h w z ⊆ CoreRes.batchReadSupport d r t h w z := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.sdiff_subset hx)

theorem incomingEdge_subset_observedSupport
    (d r t : Nat) (h : MacroExp.Tr d) (w z : Site 2) :
    MacroExp.E d r t w z ⊆ observedSupport d r t h w z := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)

/-- Every level which can occur in a stopped search is allocated to the live region of its new
head.  The stronger recursive budget `10*s*K ≤ 10*r` is exactly what makes this true. -/
theorem revealSet_subset_batchReadSupport
    {r t s K : Nat} {h : MacroExp.Tr d} {w z y : Site 2}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {q : unitInterval} {eps : Real} (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hwz : w ≠ z)
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z)
    (hsigma : sign y = 1 ∨ sign y = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single (axis y) (sign y))
    (outer : SiteConfig (Site d)) {j : Nat} (hj : j < K) :
    Stopped.revealSet d r t s (AtomTower.incomingTr d r t h w z outer)
        z (axis y) (sign y) j ⊆ CoreRes.batchReadSupport d r t h w z := by
  let hin := AtomTower.incomingTr d r t h w z outer
  have hQ : MacroExp.Q d r t z ⊆ hin.inspected := by
    intro x hx
    change x ∈ (AtomTower.incomingTr d r t h w z outer).inspected
    rw [AtomTower.incomingTr_inspected]
    exact Finset.mem_union_right _ (CorrMove.Q_subset_E hd r t hr hwz hx)
  have hjdepth : 10 * s * j < 10 * r := by
    have hlt : 10 * s * j < 10 * s * K :=
      Nat.mul_lt_mul_of_pos_left hj (by omega)
    omega
  have hLive : Stopped.revealSet d r t s hin z (axis y) (sign y) j ⊆
      CoreFresh.liveRegion d r t z y := by
    unfold Stopped.revealSet
    exact CoreFresh.freshStub_subset_liveRegion hr hrt hjdepth hsigma hemb hQ
  intro x hx
  apply Finset.mem_union_right
  rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion]
  refine ⟨(z, y), ?_, hLive hx⟩
  exact (CoreCoverUpdate.mem_newEdges_iff (d := d)).2 ⟨rfl, hy⟩

/-! ## Determination of the accepted verdict -/

theorem determinedBy_directionFailure
    {r t s K : Nat} {h : MacroExp.Tr d} {w z y : Site 2}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {q : unitInterval} {eps : Real} (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r) (hwz : w ≠ z)
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z)
    (hsigma : sign y = 1 ∨ sign y = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single (axis y) (sign y)) :
    DeterminedBy
      (CoreBatchTransition.directionFailure r t s K h w z y
        (axis y) (sign y) q eps)
      (↑(observedSupport d r t h w z) : Set (Site d)) := by
  rw [determinedBy_iff]
  intro outer outer' hagree
  have hinAgree : outer ∩ (↑(AtomTower.incomingRegion d r t h w z) : Set (Site d)) =
      outer' ∩ ↑(AtomTower.incomingRegion d r t h w z) := by
    apply Set.ext
    intro x
    have hxsub : x ∈ (↑(AtomTower.incomingRegion d r t h w z) : Set (Site d)) →
        x ∈ (↑(observedSupport d r t h w z) : Set (Site d)) := fun hx =>
      Finset.mem_coe.2 (Finset.mem_union_right _
        (incomingRegion_subset_batchReadSupport d r t h w z (Finset.mem_coe.1 hx)))
    by_cases hx : x ∈ (↑(AtomTower.incomingRegion d r t h w z) : Set (Site d))
    · have heq := Set.ext_iff.1 hagree x
      simpa only [Set.mem_inter_iff, hx, hxsub hx, and_true] using heq
    · simp [hx]
  have hin : AtomTower.incomingTr d r t h w z outer =
      AtomTower.incomingTr d r t h w z outer' :=
    h.step_congr (fun x hx =>
      TargetExt.forall_iff_of_inter_eq hinAgree x (Finset.mem_coe.2 hx))
  let k := AtomTower.incomingTr d r t h w z outer
  have hdet : DeterminedBy
      (CoreStopped.noGoodLevel r t s k z y (axis y) (sign y) q eps K)
      (↑(observedSupport d r t h w z) : Set (Site d)) := by
    unfold CoreStopped.noGoodLevel
    apply Stopped.determinedBy_allBad
    intro j hj
    exact (CoreStopped.determinedBy_levelBad r t s k z y (axis y) (sign y) q eps j).mono
      (Finset.coe_subset.2 (by
        simpa only [k, observedSupport] using (revealSet_subset_batchReadSupport
          (q := q) (eps := eps) hd hr hrt hs hbudget hwz hy hsigma hemb outer hj).trans
            (Finset.subset_union_right : CoreRes.batchReadSupport d r t h w z ⊆
              observedSupport d r t h w z)))
  have hbad := (determinedBy_iff _ _).1 hdet outer outer' hagree
  unfold CoreBatchTransition.directionFailure
  simp only [Set.mem_setOf_eq]
  rw [← hin]
  unfold CoreStopped.directionEvent
  simpa only [k, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff] using
    not_congr (or_congr Iff.rfl (not_congr hbad))

theorem determinedBy_incomingFailure
    (r t : Nat) (h : MacroExp.Tr d) (w z : Site 2) :
    DeterminedBy (CoreBatchTransition.incomingFailure r t h w z)
      (↑(observedSupport d r t h w z) : Set (Site d)) := by
  unfold CoreBatchTransition.incomingFailure CoreRes.event
  exact (determinedBy_connWithinSet (zdGraph d)
    (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d))
    (MacroExp.emb 0) (↑(CoreRes.target (d := d) r z) : Set (Site d))).compl.mono
      (Finset.coe_subset.2 (by
        intro x hx
        rw [Finset.mem_union] at hx
        exact hx.elim (Finset.mem_union_left _)
          (fun hxE => Finset.mem_union_right _ (Finset.mem_union_left _ hxE))))

theorem determinedBy_batchSuccess
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {q : unitInterval} {eps : Real} (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r) (hwz : w ≠ z)
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      (MacroExp.emb (y - z) : Site d) = Pi.single (axis y) (sign y)) :
    DeterminedBy
      (CoreBatchTransition.batchSuccess r t s K h w z axis sign q eps)
      (↑(observedSupport d r t h w z) : Set (Site d)) := by
  unfold CoreBatchTransition.batchSuccess CoreBatchTransition.batchFailure
  apply DeterminedBy.compl
  have hIn := determinedBy_incomingFailure (d := d) r t h w z
  have hOut : DeterminedBy
      (⋃ y ∈ CoreFrontier.newHeads (d := d) h z,
        CoreBatchTransition.directionFailure r t s K h w z y
          (axis y) (sign y) q eps)
      (↑(observedSupport d r t h w z) : Set (Site d)) := by
    exact DeterminedBy.iUnion fun y => DeterminedBy.iUnion fun hy =>
      determinedBy_directionFailure hd hr hrt hs hbudget hwz hy (hsigma y hy) (hemb y hy)
  rw [show CoreBatchTransition.incomingFailure r t h w z ∪
      ⋃ y ∈ CoreFrontier.newHeads (d := d) h z,
        CoreBatchTransition.directionFailure r t s K h w z y
          (axis y) (sign y) q eps =
      ⋃ b : Bool, if b then
        CoreBatchTransition.incomingFailure r t h w z else
          ⋃ y ∈ CoreFrontier.newHeads (d := d) h z,
            CoreBatchTransition.directionFailure r t s K h w z y
              (axis y) (sign y) q eps by
    ext omega
    simp [or_comm]]
  exact DeterminedBy.iUnion fun b => by cases b <;> simp only [Bool.false_eq_true, if_false,
    if_true] <;> assumption

/-! ## A maximal one-round reveal phase -/

/-- The maximal allocated reveal phase.  It is fully concrete and genuinely fresh: the queried
set is defined by subtraction from the current inspected set. -/
def phase (A : Finset (Site 2)) (r t n : Nat) (q : unitInterval) (eps : Real) :
    ABDAdaptReg.RevealPhase (Site d) (Site 2)
      (CoreAcceptedTransition.Admissible (d := d) A r t q eps) where
  Phase base k :=
    (0 : Site 2) ∈ base.openV ∧
      k.openV = base.openV ∧ k.closedV = base.closedV ∧ k.failed = base.failed
  rounds _ := 1
  anchor _ _ := 0
  region base k :=
    CoreRes.batchReadSupport d r t base.base
      (owner r t q eps base.base (MacroExp.pendZ d n base.base))
      (MacroExp.pendZ d n base.base) \ k.inspected
  start h hadm := ⟨hadm.preReveal.zero_open, rfl, rfl, rfl⟩
  openV_eq _ _ hk := hk.2.1
  closedV_eq _ _ hk := hk.2.2.1
  failed_eq _ _ hk := hk.2.2.2
  anchor_open _ _ hk := hk.2.1 ▸ hk.1
  region_fresh _ _ _ := Finset.sdiff_disjoint
  step_phase := by
    intro base k hk omega
    refine ⟨hk.1, ?_, ?_, ?_⟩
    · simpa [BDDom.Transcript.step_openV, hk.2.1, hk.1]
    · simp [hk.2.2.1]
    · simp [hk.2.2.2]

@[simp] theorem phase_rounds (A : Finset (Site 2)) (r t n : Nat)
    (q : unitInterval) (eps : Real) (h : Tr d) :
    (phase (d := d) A r t n q eps).rounds h = 1 := rfl

theorem phase_region_subset_batchReadSupport
    (A : Finset (Site 2)) (r t n : Nat) (q : unitInterval) (eps : Real)
    (base k : Tr d) :
    (phase (d := d) A r t n q eps).region base k ⊆
      CoreRes.batchReadSupport d r t base.base
        (owner r t q eps base.base (MacroExp.pendZ d n base.base))
        (MacroExp.pendZ d n base.base) :=
  Finset.sdiff_subset

/-- Exact containment of every physical coordinate recorded by the maximal reveal. -/
theorem phase_run_inspected
    (A : Finset (Site 2)) (r t n : Nat) (q : unitInterval) (eps : Real)
    (base : Tr d) (omega : SiteConfig (Site d)) :
    ((phase (d := d) A r t n q eps).run base
      ((phase (d := d) A r t n q eps).rounds base) base omega).inspected =
      base.inspected ∪
        CoreRes.batchReadSupport d r t base.base
          (owner r t q eps base.base (MacroExp.pendZ d n base.base))
          (MacroExp.pendZ d n base.base) := by
  simp only [phase_rounds, ABDAdaptReg.RevealPhase.run_succ,
    ABDAdaptReg.RevealPhase.run_zero, ABDAdaptReg.RevealPhase.reveal,
    BDDom.Transcript.step_inspected, phase, Finset.union_sdiff_self_eq_union]

#print axioms KNAll.Site.CoreBatchFullReveal.owner_spec
#print axioms KNAll.Site.CoreBatchFullReveal.revealSet_subset_batchReadSupport
#print axioms KNAll.Site.CoreBatchFullReveal.determinedBy_batchSuccess
#print axioms KNAll.Site.CoreBatchFullReveal.phase_run_inspected

end KNAll.Site.CoreBatchFullReveal

end
