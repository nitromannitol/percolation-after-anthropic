import Hypergraph.AdmissibleBoundedDamageAdaptiveRegion
import Hypergraph.CoreBatchBudget
import Hypergraph.CoreDirectionFromPost
import Hypergraph.CoreReservationPersistence
import Hypergraph.CoreTaggedCoverUpdate

/-!
# Analytic and deterministic interfaces for one core batch

The probability estimate in this file stays at the pre-examination transcript.  Its outgoing
events are exactly the atomwise events of `CoreDirectionFromPost`; no estimate is transported
through an overlapping read.  The deterministic commit theorem below is stated using the two
macro-verdict equalities actually supplied by the corrected reveal phase and keeps every
reservation-persistence premise visible.
-/

noncomputable section

namespace KNAll.Site.CoreBatchTransition

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

abbrev Tr (d : Nat) := BDDom.Transcript (Site d) (Site 2)

def incomingFailure (r t : Nat) (h : MacroExp.Tr d) (w z : Site 2) :
    Set (SiteConfig (Site d)) :=
  (CoreRes.event (d := d) r t h w z)ᶜ

def directionFailure (r t s K : Nat) (h : MacroExp.Tr d) (w z y : Site 2)
    (i : Fin d) (sigma : Int) (q : unitInterval) (eps : Real) :
    Set (SiteConfig (Site d)) :=
  {outer | outer ∉ CoreStopped.directionEvent r t s
    (AtomTower.incomingTr d r t h w z outer) z y i sigma q eps K}

def batchFailure (r t s K : Nat) (h : MacroExp.Tr d) (w z : Site 2)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (q : unitInterval) (eps : Real) : Set (SiteConfig (Site d)) :=
  incomingFailure r t h w z ∪
    ⋃ y ∈ CoreFrontier.newHeads (d := d) h z,
      directionFailure r t s K h w z y (axis y) (sign y) q eps

def batchSuccess (r t s K : Nat) (h : MacroExp.Tr d) (w z : Site 2)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (q : unitInterval) (eps : Real) : Set (SiteConfig (Site d)) :=
  (batchFailure r t s K h w z axis sign q eps)ᶜ

private theorem measurableSet_allBad
    (bad : Nat → Set (SiteConfig (Site d)))
    (hbad : ∀ j, MeasurableSet (bad j)) :
    ∀ K, MeasurableSet (Budget.allBad bad K) := by
  intro K
  induction K with
  | zero => exact MeasurableSet.univ
  | succ K ih => exact ih.inter (hbad K)

theorem measurableSet_directionEvent (r t s K : Nat) (h : MacroExp.Tr d)
    (z y : Site 2) (i : Fin d) (sigma : Int) (q : unitInterval) (eps : Real) :
    MeasurableSet (CoreStopped.directionEvent r t s h z y i sigma q eps K) := by
  unfold CoreStopped.directionEvent CoreStopped.noGoodLevel
  apply MeasurableSet.union (MeasurableSet.const _)
  apply MeasurableSet.compl
  exact measurableSet_allBad _ (fun j =>
    CoreStopped.measurableSet_levelBad r t s h z y i sigma q eps j
  ) K

/-- The atomwise outgoing failure is measurable under the original configuration. -/
theorem measurableSet_directionFailure (r t s K : Nat) (h : MacroExp.Tr d)
    (w z y : Site 2) (i : Fin d) (sigma : Int) (q : unitInterval) (eps : Real) :
    MeasurableSet (directionFailure r t s K h w z y i sigma q eps) := by
  classical
  unfold directionFailure AtomTower.incomingTr
  rw [h.setOf_step_eq_biUnion
    (fun k outer => outer ∉ CoreStopped.directionEvent r t s k z y i sigma q eps K)]
  exact Finset.measurableSet_biUnion _ fun tau _ =>
    (measurableSet_localCylinder
      (AtomTower.incomingRegion d r t h w z).finite_toSet.countable _).inter
      (measurableSet_directionEvent r t s K _ z y i sigma q eps).compl

theorem measurableSet_incomingFailure (r t : Nat) (h : MacroExp.Tr d)
    (w z : Site 2) : MeasurableSet (incomingFailure r t h w z) :=
  (measurableSet_connWithinSet _ _ _ _).compl

theorem measurableSet_batchFailure (r t s K : Nat) (h : MacroExp.Tr d)
    (w z : Site 2) (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (q : unitInterval) (eps : Real) :
    MeasurableSet (batchFailure r t s K h w z axis sign q eps) := by
  unfold batchFailure
  exact (measurableSet_incomingFailure r t h w z).union
    (Finset.measurableSet_biUnion _ fun y _ =>
      measurableSet_directionFailure r t s K h w z y (axis y) (sign y) q eps)

/-- Probability-only batch interface.  A concrete scheduler should consume this theorem, while a
separate analytic module may establish each member of `hout` by any sound route. -/
theorem prob_batchFailure_le_of_directionBounds
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {q : unitInterval} {eps rho : Real}
    (hrho0 : 0 < rho) (heps_rho : eps ≤ rho / 32)
    (hincoming : CoreRes.Bound (d := d) r t q eps h w z)
    (hout : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      h.prob (fun _ : Site d => q)
        (directionFailure r t s K h w z y (axis y) (sign y) q eps) ≤ rho / 16) :
    h.prob (fun _ : Site d => q)
      (batchFailure r t s K h w z axis sign q eps) ≤ 9 * rho / 32 := by
  have hin : h.prob (fun _ : Site d => q) (incomingFailure r t h w z) ≤ rho / 32 := by
    have hm := measurableSet_connWithinSet (zdGraph d)
      (h.inspected ∪ MacroExp.E d r t w z)
      (MacroExp.emb 0) (↑(CoreRes.target (d := d) r z) : Set (Site d))
    rw [incomingFailure, CoreRes.event, FRDom.Transcript.prob_eq,
      pinnedProb_compl _ _ _ hm, ← FRDom.Transcript.prob_eq]
    unfold CoreRes.Bound CoreRes.event at hincoming
    linarith
  exact CoreBatch.prob_newHead_batchFailure_le h (fun _ : Site d => q) z
    (incomingFailure r t h w z)
    (fun y => directionFailure r t s K h w z y (axis y) (sign y) q eps)
    (le_of_lt hrho0) hin hout

/-- The full one-owner batch estimate.  `FaceInputs`, `LongInputs`, pinned gluing, and the complete
post-entry window family occur literally in the signature; none is hidden in a scheduler record. -/
theorem prob_batchFailure_le_of_postWindow
    (hgl : PinnedSiteGluing)
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hdelta : C.delta = C.eps ^ 2 / 96)
    (hd : 3 ≤ d) {r t R s K : Nat} {h : MacroExp.Tr d}
    {w z : Site 2} (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    {rho : Real}
    (hr : 0 < r) (ht : 5 * r ≤ t) (h44 : 44 ≤ r) (hR1 : 1 ≤ R)
    (hscale : 100 * (d + 1) * (R + 1) < r)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hwz : w ≠ z) (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
      MacroExp.thin d t)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (heps_rho : C.eps ≤ rho / 32)
    (he_beta : C.eps ≤ AtomTower.beta rho d)
    (hpow : (1 - AtomTower.f C.eps) ^ K ≤ rho / 32)
    (hincoming : CoreRes.Bound (d := d) r t q C.eps h w z)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (htail : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      (MacroExp.emb (y - z) : Site d) = Pi.single (axis y) (sign y))
    (hy0 : ∀ y ∈ CoreFrontier.newHeads (d := d) h z, y ≠ 0)
    (hfresh : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y))
    (hzero : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      (MacroExp.emb 0 : Site d) ∉ MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (hfresh_out : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      Disjoint (h.inspected ∪ MacroExp.E d r t w z) (MacroExp.E d r t z y))
    (hface : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      CoreRes.FaceInputs (d := d) R h q
        (h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) (axis y) (sign y) r t (17 * r)))
    (hlong : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      CoreRes.LongInputs (d := d) R h q
        (h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) (axis y) (sign y) r t (17 * r))
        (axis y) (sign y))
    (hwindow : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
        CorePost.CorePostWindowBound C q (MacroExp.ctr d r z) (axis y) (sign y)
          r t s j
          (CorePost.levelDom r t s (AtomTower.incomingTr d r t h w z outer)
            z y (axis y) (sign y) j xi) y) :
    h.prob (fun _ : Site d => q)
      (batchFailure r t s K h w z axis sign q C.eps) ≤ 9 * rho / 32 := by
  have hout : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      h.prob (fun _ : Site d => q)
        (directionFailure r t s K h w z y (axis y) (sign y) q C.eps) ≤ rho / 16 := by
    intro y hy
    exact CoreDirectionFromPost.prob_directionFailure_le_of_postWindow
      hgl hwf hv hdelta hd hr ht h44 hR1 hscale hs hbudget
      (hsigma y hy) (hemb y hy) (hy0 y hy) hwz horigin
      (hfresh y hy) (hzero y hy) hthin (hfresh_out y hy)
      (hface y hy) (hlong y hy) hrho0 hrho1 he_beta hpow hincoming
      hclear hwidth htail hplanar htrans (hwindow y hy)
  exact prob_batchFailure_le_of_directionBounds hrho0 heps_rho hincoming hout

/-- Complement form required by the corrected adaptive domination theorem. -/
theorem one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess
    {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {q : unitInterval} {eps rho : Real}
    (hfail : h.prob (fun _ : Site d => q)
      (batchFailure r t s K h w z axis sign q eps) ≤ 9 * rho / 32) :
    1 - 9 * rho / 32 ≤ h.prob (fun _ : Site d => q)
      (batchSuccess r t s K h w z axis sign q eps) := by
  exact CoreBatch.one_sub_le_prob_compl h (fun _ : Site d => q)
    (batchFailure r t s K h w z axis sign q eps)
    (measurableSet_batchFailure r t s K h w z axis sign q eps) hfail

/-! ## Deterministic final-commit invariants -/

private theorem frontier_iff_of_verdict_eq
    {h k : MacroExp.Tr d}
    (hopen : k.openV = h.openV) (hclosed : k.closedV = h.closedV) (y : Site 2) :
    CoreFrontier.Frontier k y ↔ CoreFrontier.Frontier h y := by
  unfold CoreFrontier.Frontier
  rw [hopen, hclosed]

private theorem newHeads_eq_of_verdict_eq
    {h k : MacroExp.Tr d}
    (hopen : k.openV = h.openV) (hclosed : k.closedV = h.closedV) (z : Site 2) :
    CoreFrontier.newHeads (d := d) k z = CoreFrontier.newHeads (d := d) h z := by
  classical
  ext y
  rw [CoreFrontier.mem_newHeads, CoreFrontier.mem_newHeads,
    MacroExp.mem_pending, MacroExp.mem_pending, hopen, hclosed,
    frontier_iff_of_verdict_eq hopen hclosed]

/-- Soundness, one-owner frontier, and tagged cover after a successful batch.  The theorem does
not manufacture persistence: old frontier owners, old tagged live reservations, and all new-head
reservations are separate explicit premises. -/
theorem commit_success_invariants
    {Admissible : Tr d → Prop}
    (Rph : ABDAdaptReg.RevealPhase (Site d) (Site 2) Admissible)
    {r t : Nat} {q : unitInterval} {eps : Real}
    {A : Finset (Site 2)} {o : Site 2}
    {base k : Tr d} (hk : Rph.Phase base k)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w) (hzA : z ∈ A)
    (hsound : base.Sound (zdGraph 2) A o)
    (hcover : CoreTaggedCover.Holds r t q eps base.base)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (CoreCoverUpdate.newEdges base.base z))
    (hpersistLive : ∀ e, CoreTaggedCover.Live r t q eps base.base e → e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base e.1 e.2)
    (hpersistFront : ∀ y, CoreFrontier.Frontier base.base y →
      y ≠ z →
      CoreFrontier.HasOwner r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base y)
    (hnew : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base z,
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base z y) :
    (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).Sound
        (zdGraph 2) A o ∧
      CoreFrontier.Invariant r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base ∧
      CoreTaggedCover.Holds r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base := by
  have hopen : k.base.openV = base.base.openV := Rph.openV_eq base k hk
  have hclosed : k.base.closedV = base.base.closedV := Rph.closedV_eq base k hk
  have hfailed : k.failed = base.failed := Rph.failed_eq base k hk
  have hsK : k.Sound (zdGraph 2) A o := by
    unfold BDDom.Transcript.Sound at hsound ⊢
    rw [Rph.openV_eq base k hk, Rph.closedV_eq base k hk,
      Rph.failed_eq base k hk]
    exact hsound
  have hzUndet := ((MacroExp.mem_pending (d := d)).1 hz).2
  have hzNotOpen : z ∉ k.openV := by
    intro hzo
    change z ∈ k.base.openV at hzo
    rw [hopen] at hzo
    exact hzUndet (Finset.mem_union_left _ hzo)
  have hzNotClosed : z ∉ k.closedV := by
    intro hzc
    change z ∈ k.base.closedV at hzc
    rw [hclosed] at hzc
    exact hzUndet (Finset.mem_union_right _ hzc)
  have hsPost := BDAdaptReg.sound_step_of_local k hsK hzA hzNotOpen hzNotClosed
    (CoreBatchShadow.maximalDamage_local base z)
    (by
      change Disjoint (CoreBatchShadow.maximalDamage base z) k.base.openV
      rw [hopen]
      exact CoreBatchShadow.maximalDamage_disjoint_open base z)
    (F := (∅ : Finset (Site d)))
    (damage := CoreBatchShadow.maximalDamage base z) (b := true) (ω := omega)
  have hnewK : ∀ y ∈ CoreFrontier.newHeads (d := d) k.base z,
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base z y := by
    intro y hy
    exact hnew y (by
      rwa [newHeads_eq_of_verdict_eq (d := d) hopen hclosed z] at hy)
  have hinv : CoreFrontier.Invariant r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base := by
    intro y hyPost
    rcases CoreFrontier.frontier_step_true_cases
        (h := k.base) (z := z) (∅ : Finset (Site d)) omega hyPost with hyOld | hyNew
    · have hyz : y ≠ z := by
        intro hyz
        subst y
        apply hyPost.1
        apply Finset.mem_union_left
        change z ∈
          (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base.openV
        simp
      exact hpersistFront y
        ((frontier_iff_of_verdict_eq (d := d) hopen hclosed y).1 hyOld) hyz
    · refine ⟨z, ?_, ?_, hnewK y hyNew⟩
      · change z ∈
          (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base.openV
        simp
      · apply (MacroExp.mem_pending (d := d)).2
        exact ⟨((MacroExp.mem_pending (d := d)).1
          ((CoreFrontier.mem_newHeads (d := d)).1 hyNew).1).1, hyPost.1⟩
  have htag := CoreCoverUpdate.holds_success_eq hopen hclosed hcover hw hz omega hreads
    hpersistLive hnew
  exact ⟨hsPost, hinv, htag⟩

/-- Soundness, one-owner frontier, and tagged cover after a failed batch.  Closing the centre and
all new heads creates no frontier vertex; every surviving frontier was already present and must
have an explicitly persisted owner. -/
theorem commit_failure_invariants
    {Admissible : Tr d → Prop}
    (Rph : ABDAdaptReg.RevealPhase (Site d) (Site 2) Admissible)
    {r t : Nat} {q : unitInterval} {eps : Real}
    {A : Finset (Site 2)} {o : Site 2}
    {base k : Tr d} (hk : Rph.Phase base k)
    {w z : Site 2} (hw : w ∈ base.openV)
    (hz : z ∈ MacroExp.pending d base.base w) (hzA : z ∈ A)
    (hsound : base.Sound (zdGraph 2) A o)
    (hcover : CoreTaggedCover.Holds r t q eps base.base)
    (omega : SiteConfig (Site d))
    (hreads : k.inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (CoreCoverUpdate.newEdges base.base z))
    (hpersistLive : ∀ e, CoreTaggedCover.Live r t q eps base.base e → e.2 ≠ z →
      CoreRes.Bound r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base e.1 e.2)
    (hpersistFront : ∀ y, CoreFrontier.Frontier base.base y →
      y ≠ z → y ∉ CoreBatchShadow.maximalDamage base z →
      CoreFrontier.HasOwner r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base y) :
    (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).Sound
        (zdGraph 2) A o ∧
      CoreFrontier.Invariant r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base ∧
      CoreTaggedCover.Holds r t q eps
        (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base := by
  have hopen : k.base.openV = base.base.openV := Rph.openV_eq base k hk
  have hclosed : k.base.closedV = base.base.closedV := Rph.closedV_eq base k hk
  have hfailed : k.failed = base.failed := Rph.failed_eq base k hk
  have hsK : k.Sound (zdGraph 2) A o := by
    unfold BDDom.Transcript.Sound at hsound ⊢
    rw [Rph.openV_eq base k hk, Rph.closedV_eq base k hk,
      Rph.failed_eq base k hk]
    exact hsound
  have hzUndet := ((MacroExp.mem_pending (d := d)).1 hz).2
  have hzNotOpen : z ∉ k.openV := by
    intro hzo
    change z ∈ k.base.openV at hzo
    rw [hopen] at hzo
    exact hzUndet (Finset.mem_union_left _ hzo)
  have hzNotClosed : z ∉ k.closedV := by
    intro hzc
    change z ∈ k.base.closedV at hzc
    rw [hclosed] at hzc
    exact hzUndet (Finset.mem_union_right _ hzc)
  have hsPost := BDAdaptReg.sound_step_of_local k hsK hzA hzNotOpen hzNotClosed
    (CoreBatchShadow.maximalDamage_local base z)
    (by
      change Disjoint (CoreBatchShadow.maximalDamage base z) k.base.openV
      rw [hopen]
      exact CoreBatchShadow.maximalDamage_disjoint_open base z)
    (F := (∅ : Finset (Site d)))
    (damage := CoreBatchShadow.maximalDamage base z) (b := false) (ω := omega)
  have hinv : CoreFrontier.Invariant r t q eps
      (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base := by
    intro y hyPost
    have hyNotOpenK : y ∉ k.base.openV := by
      intro hyo
      exact hyPost.1 (Finset.mem_union_left _ (by simpa using hyo))
    have hyNotClosedK : y ∉ k.base.closedV := by
      intro hyc
      have hycPost : y ∈
          (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base.closedV := by
        change y ∈ insert z k.base.closedV ∪ CoreBatchShadow.maximalDamage base z
        exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hyc)
      exact hyPost.1 (Finset.mem_union_right _ hycPost)
    obtain ⟨u, huOpenPost, huy⟩ := hyPost.2
    have huOpenK : u ∈ k.base.openV := by
      change u ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) false omega).base.openV at huOpenPost
      simpa [BDDom.Transcript.step_openV] using huOpenPost
    have hyBase : CoreFrontier.Frontier base.base y := by
      refine ⟨?_, u, ?_, huy⟩
      · intro hyDet
        rw [← hopen, ← hclosed] at hyDet
        rcases Finset.mem_union.1 hyDet with hyo | hyc
        · exact hyNotOpenK hyo
        · exact hyNotClosedK hyc
      · rwa [hopen] at huOpenK
    have hyz : y ≠ z := by
      intro hyz
      subst y
      apply hyPost.1
      apply Finset.mem_union_right
      change z ∈ insert z k.base.closedV ∪ CoreBatchShadow.maximalDamage base z
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    have hydamage : y ∉ CoreBatchShadow.maximalDamage base z := by
      intro hyd
      apply hyPost.1
      apply Finset.mem_union_right
      change y ∈ insert z k.base.closedV ∪ CoreBatchShadow.maximalDamage base z
      exact Finset.mem_union_right _ hyd
    exact hpersistFront y hyBase hyz hydamage
  have htag := CoreCoverUpdate.holds_failure_eq hopen hclosed hcover hw hz omega hreads
    hpersistLive
  exact ⟨hsPost, hinv, htag⟩

/-! ## Persistence supplied by a supported reveal run -/

/-- If every reveal round stays in the allocated batch support, an old live reservation whose
head is not the examined centre persists through the whole reveal run and the final empty
physical commit. -/
private theorem live_bound_after_supported_run
    {Admissible : Tr d → Prop}
    (Rph : ABDAdaptReg.RevealPhase (Site d) (Site 2) Admissible)
    {r t : Nat} {q : unitInterval} {eps : Real}
    {base : Tr d} (hadm : Admissible base)
    {w z u y : Site 2} (hd : 2 ≤ d) (hr : 0 < r)
    (hw : w ∈ base.openV) (hz : z ∈ MacroExp.pending d base.base w)
    (hold : CoreTaggedCover.Live r t q eps base.base (u, y)) (hyz : y ≠ z)
    (hregions : ∀ k, Rph.Phase base k →
      Rph.region base k ⊆ CoreRes.batchReadSupport d r t base.base w z)
    (outer commitOmega : SiteConfig (Site d)) (b : Bool) :
    CoreRes.Bound r t q eps
      ((Rph.run base (Rph.rounds base) base outer).step z ∅
        (CoreBatchShadow.maximalDamage base z) b commitOmega).base u y := by
  have hphase : Rph.Phase base base := Rph.start base hadm
  have hdisjoint : ∀ k, Rph.Phase base k →
      Disjoint (Rph.region base k) (MacroExp.E d r t u y) := by
    intro k hk
    exact CoreRes.readSubset_disjoint_oldLive hd hr (hregions k hk) hw hz hold hyz
  have hrun := CoreRes.bound_revealRun_of_disjoint Rph r t q eps hphase u y
    hdisjoint hold.2.2 (Rph.rounds base) outer
  exact CoreRes.bound_emptyCommit r t q eps
    (Rph.run base (Rph.rounds base) base outer) u y z
    (CoreBatchShadow.maximalDamage base z) b commitOmega hrun

/-- The successful commit theorem with all persistence consequences discharged from one concrete
support obligation.  The only reservation still supplied by the scheduler is the genuinely new
one at each stopped outgoing head. -/
theorem commit_success_after_supported_run
    {Admissible : Tr d → Prop}
    (Rph : ABDAdaptReg.RevealPhase (Site d) (Site 2) Admissible)
    {r t : Nat} {q : unitInterval} {eps : Real}
    {A : Finset (Site 2)} {o : Site 2}
    {base : Tr d} (hadm : Admissible base)
    {w z : Site 2} (hd : 2 ≤ d) (hr : 0 < r)
    (hw : w ∈ base.openV) (hz : z ∈ MacroExp.pending d base.base w) (hzA : z ∈ A)
    (hsound : base.Sound (zdGraph 2) A o)
    (hcover : CoreTaggedCover.Holds r t q eps base.base)
    (hinvariant : CoreFrontier.Invariant r t q eps base.base)
    (hregions : ∀ k, Rph.Phase base k →
      Rph.region base k ⊆ CoreRes.batchReadSupport d r t base.base w z)
    (outer commitOmega : SiteConfig (Site d))
    (hreads : (Rph.run base (Rph.rounds base) base outer).inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (CoreCoverUpdate.newEdges base.base z))
    (hnew : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base z,
      CoreRes.Bound r t q eps
        ((Rph.run base (Rph.rounds base) base outer).step z ∅
          (CoreBatchShadow.maximalDamage base z) true commitOmega).base z y) :
    ((Rph.run base (Rph.rounds base) base outer).step z ∅
        (CoreBatchShadow.maximalDamage base z) true commitOmega).Sound
          (zdGraph 2) A o ∧
      CoreFrontier.Invariant r t q eps
        ((Rph.run base (Rph.rounds base) base outer).step z ∅
          (CoreBatchShadow.maximalDamage base z) true commitOmega).base ∧
      CoreTaggedCover.Holds r t q eps
        ((Rph.run base (Rph.rounds base) base outer).step z ∅
          (CoreBatchShadow.maximalDamage base z) true commitOmega).base := by
  let k := Rph.run base (Rph.rounds base) base outer
  have hk : Rph.Phase base k :=
    Rph.phase_run (Rph.start base hadm) (Rph.rounds base) outer
  have hopen : k.base.openV = base.base.openV := Rph.openV_eq base k hk
  have hclosed : k.base.closedV = base.base.closedV := Rph.closedV_eq base k hk
  apply commit_success_invariants Rph hk hw hz hzA hsound hcover commitOmega hreads
  · intro e heLive hez
    exact live_bound_after_supported_run Rph hadm hd hr hw hz heLive hez
      hregions outer commitOmega true
  · intro y hyFront hyz
    obtain ⟨u, hu, huy, hbound⟩ := hinvariant y hyFront
    have heLive : CoreTaggedCover.Live r t q eps base.base (u, y) :=
      ⟨hu, huy, hbound⟩
    have hboundPost := live_bound_after_supported_run Rph hadm hd hr hw hz
      heLive hyz hregions outer commitOmega true
    refine ⟨u, ?_, ?_, hboundPost⟩
    · change u ∈ insert z k.base.openV
      exact Finset.mem_insert_of_mem (by rwa [hopen])
    · rw [MacroExp.mem_pending]
      refine ⟨((MacroExp.mem_pending (d := d)).1 huy).1, ?_⟩
      intro hyDet
      change y ∈ insert z k.base.openV ∪ k.base.closedV at hyDet
      simp only [Finset.mem_union, Finset.mem_insert] at hyDet
      rcases hyDet with (hyz' | hyo) | hyc
      · exact hyz hyz'
      · exact ((MacroExp.mem_pending (d := d)).1 huy).2
          (Finset.mem_union_left _ (by rwa [hopen] at hyo))
      · exact ((MacroExp.mem_pending (d := d)).1 huy).2
          (Finset.mem_union_right _ (by rwa [hclosed] at hyc))
  · exact hnew

/-- Failure analogue of `commit_success_after_supported_run`.  Since the failed centre and every
new head are closed, only surviving old frontier vertices require owners, and all of them persist
from the pre-batch invariant. -/
theorem commit_failure_after_supported_run
    {Admissible : Tr d → Prop}
    (Rph : ABDAdaptReg.RevealPhase (Site d) (Site 2) Admissible)
    {r t : Nat} {q : unitInterval} {eps : Real}
    {A : Finset (Site 2)} {o : Site 2}
    {base : Tr d} (hadm : Admissible base)
    {w z : Site 2} (hd : 2 ≤ d) (hr : 0 < r)
    (hw : w ∈ base.openV) (hz : z ∈ MacroExp.pending d base.base w) (hzA : z ∈ A)
    (hsound : base.Sound (zdGraph 2) A o)
    (hcover : CoreTaggedCover.Holds r t q eps base.base)
    (hinvariant : CoreFrontier.Invariant r t q eps base.base)
    (hregions : ∀ k, Rph.Phase base k →
      Rph.region base k ⊆ CoreRes.batchReadSupport d r t base.base w z)
    (outer commitOmega : SiteConfig (Site d))
    (hreads : (Rph.run base (Rph.rounds base) base outer).inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (CoreCoverUpdate.newEdges base.base z)) :
    ((Rph.run base (Rph.rounds base) base outer).step z ∅
        (CoreBatchShadow.maximalDamage base z) false commitOmega).Sound
          (zdGraph 2) A o ∧
      CoreFrontier.Invariant r t q eps
        ((Rph.run base (Rph.rounds base) base outer).step z ∅
          (CoreBatchShadow.maximalDamage base z) false commitOmega).base ∧
      CoreTaggedCover.Holds r t q eps
        ((Rph.run base (Rph.rounds base) base outer).step z ∅
          (CoreBatchShadow.maximalDamage base z) false commitOmega).base := by
  let k := Rph.run base (Rph.rounds base) base outer
  have hk : Rph.Phase base k :=
    Rph.phase_run (Rph.start base hadm) (Rph.rounds base) outer
  have hopen : k.base.openV = base.base.openV := Rph.openV_eq base k hk
  have hclosed : k.base.closedV = base.base.closedV := Rph.closedV_eq base k hk
  apply commit_failure_invariants Rph hk hw hz hzA hsound hcover commitOmega hreads
  · intro e heLive hez
    exact live_bound_after_supported_run Rph hadm hd hr hw hz heLive hez
      hregions outer commitOmega false
  · intro y hyFront hyz hydamage
    obtain ⟨u, hu, huy, hbound⟩ := hinvariant y hyFront
    have heLive : CoreTaggedCover.Live r t q eps base.base (u, y) :=
      ⟨hu, huy, hbound⟩
    have hboundPost := live_bound_after_supported_run Rph hadm hd hr hw hz
      heLive hyz hregions outer commitOmega false
    refine ⟨u, ?_, ?_, hboundPost⟩
    · change u ∈ k.base.openV
      rwa [hopen]
    · rw [MacroExp.mem_pending]
      refine ⟨((MacroExp.mem_pending (d := d)).1 huy).1, ?_⟩
      intro hyDet
      change y ∈ k.base.openV ∪
        (insert z k.base.closedV ∪ CoreBatchShadow.maximalDamage base z) at hyDet
      simp only [Finset.mem_union, Finset.mem_insert] at hyDet
      rcases hyDet with hyo | (hyz' | hyc) | hyd
      · exact ((MacroExp.mem_pending (d := d)).1 huy).2
          (Finset.mem_union_left _ (by rwa [hopen] at hyo))
      · exact hyz hyz'
      · exact ((MacroExp.mem_pending (d := d)).1 huy).2
          (Finset.mem_union_right _ (by rwa [hclosed] at hyc))
      · exact hydamage hyd

#print axioms KNAll.Site.CoreBatchTransition.prob_batchFailure_le_of_postWindow
#print axioms KNAll.Site.CoreBatchTransition.one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess
#print axioms KNAll.Site.CoreBatchTransition.commit_success_invariants
#print axioms KNAll.Site.CoreBatchTransition.commit_failure_invariants
#print axioms KNAll.Site.CoreBatchTransition.commit_success_after_supported_run
#print axioms KNAll.Site.CoreBatchTransition.commit_failure_after_supported_run

end KNAll.Site.CoreBatchTransition

end
