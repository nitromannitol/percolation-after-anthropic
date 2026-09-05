import Hypergraph.CoreBatchNoGluing
import Hypergraph.CoreInitialReservation

set_option maxHeartbeats 3000000

/-!
# Accepted pre-reveal core transition

This module is the assembly-facing replacement for the false arbitrary-history source estimate.
It never asks for a core bound after the incoming region has been read.  Instead, an admissible
pre-reveal transcript carries `CoreFrontier.Invariant`; the next frontier vertex obtains one open
owner and its `CoreRes.Bound` from that invariant.  `CoreBatchNoGluing` then runs entirely at the
same pre-reveal pinned law.  Supported commits restore the invariant for the next accepted
pre-reveal transcript.

The finite face/long-box and post-window estimates remain explicit analytic inputs.  In
particular, this file does not import or use `SourceEstimate` or `AssemblyCheck`.
-/

noncomputable section

namespace KNAll.Site.CoreAcceptedTransition

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

abbrev Tr (d : Nat) := BDDom.Transcript (Site d) (Site 2)

/-- The data valid at an accepted pre-reveal state.  Bounds are required only through the
one-owner frontier invariant, never for an arbitrary history or arbitrary oriented edge. -/
structure PreReveal (r t : Nat) (q : unitInterval) (eps : Real)
    (h : MacroExp.Tr d) : Prop where
  zero_open : (0 : Site 2) ∈ h.openV
  origin_open : (MacroExp.emb 0 : Site d) ∈ h.openSites
  tagged : CoreTaggedCover.Holds r t q eps h
  frontier : CoreFrontier.Invariant r t q eps h

/-- Bounded-damage soundness together with the accepted pre-reveal reservation state. -/
structure Admissible (A : Finset (Site 2)) (r t : Nat) (q : unitInterval)
    (eps : Real) (h : Tr d) : Prop where
  sound : h.Sound (zdGraph 2) A 0
  preReveal : PreReveal r t q eps h.base

/-- A boundary vertex in a sound rooted transcript is a genuine open-frontier vertex. -/
theorem frontier_of_mem_boundary {A : Finset (Site 2)} {h : Tr d} {z : Site 2}
    (hsound : h.Sound (zdGraph 2) A 0)
    (hz : z ∈ h.boundary (zdGraph 2) A 0) :
    CoreFrontier.Frontier h.base z := by
  rcases hz with ⟨-, hzo, hzc, hz0 | ⟨u, hu, huz⟩⟩
  · subst z
    exact (hzo hsound.1).elim
  · refine ⟨?_, u, ?_, ?_⟩
    · exact fun hzdet => Finset.mem_union.1 hzdet |>.elim hzo hzc
    · exact Finset.mem_coe.1 (mem_of_mem_siteCluster _ _ hu)
    · exact MacroExp.mem_nbrs_of_adj huz

/-- Select the invariant's owner of a frontier head.  The proof arguments merely certify that
the selection is made on an accepted pre-reveal history. -/
def owner {r t : Nat} {q : unitInterval} {eps : Real} {h : MacroExp.Tr d}
    (hI : CoreFrontier.Invariant r t q eps h) (z : Site 2)
    (hz : CoreFrontier.Frontier h z) : Site 2 :=
  Classical.choose (hI z hz)

theorem owner_spec {r t : Nat} {q : unitInterval} {eps : Real} {h : MacroExp.Tr d}
    (hI : CoreFrontier.Invariant r t q eps h) (z : Site 2)
    (hz : CoreFrontier.Frontier h z) :
    owner hI z hz ∈ h.openV ∧
      z ∈ MacroExp.pending d h (owner hI z hz) ∧
      CoreRes.Bound r t q eps h (owner hI z hz) z :=
  Classical.choose_spec (hI z hz)

/-- Every tagged inspected history stays inside the slab. -/
theorem inspected_subset_thin (hd : 2 ≤ d) {r t : Nat} {q : unitInterval}
    {eps : Real} {h : MacroExp.Tr d} (hC : CoreTaggedCover.Holds r t q eps h) :
    (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t := by
  rcases hC with ⟨settled, live, -, -, hcover⟩
  intro x hx
  have hx' := hcover (Finset.mem_coe.1 hx)
  simp only [Finset.mem_union] at hx'
  rcases hx' with (hxQ | hxSettled) | hxLive
  · exact MacroExp.Q_subset_thin hd r t 0 (Finset.mem_coe.2 hxQ)
  · rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion] at hxSettled
    obtain ⟨e, -, hxe⟩ := hxSettled
    exact MacroExp.E_subset_thin hd r t e.1 e.2 (Finset.mem_coe.2 hxe)
  · rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion] at hxLive
    obtain ⟨e, -, hxe⟩ := hxLive
    exact MacroExp.E_subset_thin hd r t e.1 e.2
      (Finset.mem_coe.2 (Finset.sdiff_subset hxe))

/-- A currently undetermined frontier head still has an unread central box. -/
theorem inspected_disjoint_frontier_Q (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {q : unitInterval} {eps : Real} {h : MacroExp.Tr d} {z : Site 2}
    (hzero : (0 : Site 2) ∈ h.openV)
    (hC : CoreTaggedCover.Holds r t q eps h)
    (hz : CoreFrontier.Frontier h z) :
    Disjoint h.inspected (MacroExp.Q d r t z) := by
  rcases hC with ⟨settled, live, hs, hl, hcover⟩
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    exact hz.1 (Finset.mem_union_left _ hzero)
  rw [Finset.disjoint_left]
  intro x hxI hxQ
  have hx := hcover hxI
  simp only [Finset.mem_union] at hx
  rcases hx with (hxQ0 | hxSettled) | hxLive
  · obtain ⟨u, hu, huz⟩ := hz.2
    have hzu : z ≠ u := by
      intro hzu
      subst u
      exact hz.1 (Finset.mem_union_left _ hu)
    have hxEz := CorrMove.Q_subset_E hd r t hr
      (w := u) (z := z) (Ne.symm hzu) hxQ
    exact Finset.disjoint_left.1
      (MacroExp.protectedEdge_disjoint_Q hd r t hr
        (MacroExp.adj_of_mem_nbrs huz) hz0.symm) hxEz hxQ0
  · rw [CoreTaggedCover.settledRegion, Finset.mem_biUnion] at hxSettled
    obtain ⟨e, he, hxe⟩ := hxSettled
    have hez : z ≠ e.2 := by
      intro hez
      subst z
      exact hz.1 (hs e he).2.2
    exact Finset.disjoint_left.1
      (MacroExp.protectedEdge_disjoint_Q hd r t hr (hs e he).1 hez) hxe hxQ
  · rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion] at hxLive
    obtain ⟨e, he, hxe⟩ := hxLive
    by_cases hez : e.2 = z
    · subst z
      exact (Finset.mem_sdiff.1 hxe).2 hxQ
    · exact Finset.disjoint_left.1
        (MacroExp.protectedEdge_disjoint_Q hd r t hr
          (MacroExp.adj_of_mem_nbrs
            ((MacroExp.mem_pending (d := d)).1 (hl e he).2.1).1) (Ne.symm hez))
        (Finset.sdiff_subset hxe) hxQ

/-- All deterministic side conditions needed by an outgoing new-head probe follow from the
accepted tagged cover and the chosen incoming owner. -/
theorem outgoing_geometry_of_preReveal (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {q : unitInterval} {eps : Real} {h : MacroExp.Tr d}
    (hpre : PreReveal r t q eps h) {z : Site 2}
    (hz : CoreFrontier.Frontier h z) :
    let w := owner hpre.frontier z hz
    w ≠ z ∧
      (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
        MacroExp.thin d t ∧
      ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
        y ≠ 0 ∧
        Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y) ∧
        (MacroExp.emb 0 : Site d) ∉
          MacroExp.Q d r t z ∪ MacroExp.E d r t z y ∧
        Disjoint (h.inspected ∪ MacroExp.E d r t w z)
          (MacroExp.E d r t z y) := by
  dsimp only
  let w := owner hpre.frontier z hz
  have hw := owner_spec hpre.frontier z hz
  have hwz : w ≠ z := by
    intro hwz
    have hzopen : w ∈ h.openV := hw.1
    rw [hwz] at hzopen
    exact ((MacroExp.mem_pending (d := d)).1 hw.2.1).2
      (Finset.mem_union_left _ hzopen)
  refine ⟨hwz, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact inspected_subset_thin hd hpre.tagged (Finset.mem_coe.2 hx)
    · exact MacroExp.E_subset_thin hd r t w z (Finset.mem_coe.2 hx)
  · intro y hy
    have hy0 : y ≠ 0 := by
      intro hy0
      subst y
      exact CoreFrontier.newHead_not_mem_openV (d := d) hy hpre.zero_open
    have hIQ := inspected_disjoint_frontier_Q hd hr hpre.zero_open hpre.tagged hz
    have hIE := CoreTaggedCover.inspected_disjoint_newHead_edge_of_holds
      hd hr hpre.zero_open hpre.tagged hy
    have hfresh : Disjoint h.inspected
        (MacroExp.Q d r t z ∪ MacroExp.E d r t z y) :=
      Finset.disjoint_union_right.2 ⟨hIQ, hIE⟩
    have hzero : (MacroExp.emb 0 : Site d) ∉
        MacroExp.Q d r t z ∪ MacroExp.E d r t z y := by
      intro hmem
      exact Finset.disjoint_left.1 hfresh
        (show (MacroExp.emb 0 : Site d) ∈ h.inspected from
          h.openSites_subset hpre.origin_open)
        hmem
    have hownerE := CoreFrontier.oldOwner_region_disjoint_newHead
      hd (r := r) (t := t) hr hw.1 hw.2.1 hy
    exact ⟨hy0, hfresh, hzero,
      Finset.disjoint_union_left.2 ⟨hIE, hownerE⟩⟩

/-! ## The accepted-only analytic transition -/

/-- The gluing-free core batch estimate with no free incoming-source hypothesis.  The owner and
its `CoreRes.Bound` are extracted from the accepted pre-reveal frontier invariant.  Every
freshness and slab-containment premise is discharged from the tagged cover. -/
theorem prob_batchFailure_le_of_preReveal
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hd : 3 ≤ d) {r t R s K : Nat} {h : MacroExp.Tr d}
    {z : Site 2} (hz : CoreFrontier.Frontier h z)
    (hpre : PreReveal r t q C.eps h)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int) {rho : Real}
    (hr : 0 < r) (ht : 5 * r ≤ t) (h44 : 44 ≤ r) (hR1 : 1 ≤ R)
    (hscale : 100 * (d + 1) * (R + 1) < r)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (heps_rho : C.eps ≤ rho / 32)
    (he_beta : C.eps ≤ AtomTower.beta rho d)
    (hpow : (1 - AtomTower.f C.eps) ^ K ≤ rho / 32)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (htail : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      (MacroExp.emb (y - z) : Site d) = Pi.single (axis y) (sign y))
    (hface : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      CoreRes.FaceInputs (d := d) R h q
        (h.inspected ∪
          MacroExp.E d r t (owner hpre.frontier z hz) z ∪
          Stopped.stub (MacroExp.ctr d r z) (axis y) (sign y) r t (17 * r)))
    (hlong : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      CoreRes.LongInputs (d := d) R h q
        (h.inspected ∪
          MacroExp.E d r t (owner hpre.frontier z hz) z ∪
          Stopped.stub (MacroExp.ctr d r z) (axis y) (sign y) r t (17 * r))
        (axis y) (sign y))
    (hwindow : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
        CorePost.CorePostWindowBound C q (MacroExp.ctr d r z) (axis y) (sign y)
          r t s j
          (CorePost.levelDom r t s
            (AtomTower.incomingTr d r t h (owner hpre.frontier z hz) z outer)
            z y (axis y) (sign y) j xi) y) :
    h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h
        (owner hpre.frontier z hz) z axis sign q C.eps) ≤ 9 * rho / 32 := by
  let w := owner hpre.frontier z hz
  have hw := owner_spec hpre.frontier z hz
  have hgeom := outgoing_geometry_of_preReveal (d := d) (by omega) hr hpre hz
  change w ≠ z ∧
      (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
        MacroExp.thin d t ∧
      ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
        y ≠ 0 ∧
        Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y) ∧
        (MacroExp.emb 0 : Site d) ∉
          MacroExp.Q d r t z ∪ MacroExp.E d r t z y ∧
        Disjoint (h.inspected ∪ MacroExp.E d r t w z)
          (MacroExp.E d r t z y) at hgeom
  change h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h w z axis sign q C.eps) ≤
        9 * rho / 32
  apply CoreBatchNoGluing.prob_batchFailure_le_of_postWindow
    hwf hv hd axis sign hr ht h44 hR1 hscale hs hbudget
    hgeom.1 hpre.origin_open hgeom.2.1 hrho0 hrho1 heps_rho he_beta hpow hw.2.2
    hclear hwidth htail hplanar htrans hsigma hemb
  · intro y hy
    exact (hgeom.2.2 y hy).1
  · intro y hy
    exact (hgeom.2.2 y hy).2.1
  · intro y hy
    exact (hgeom.2.2 y hy).2.2.1
  · intro y hy
    exact (hgeom.2.2 y hy).2.2.2
  · exact hface
  · exact hlong
  · exact hwindow

/-- Complement form of the accepted-only batch estimate. -/
theorem one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess_of_preReveal
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {r t s K : Nat} {h : MacroExp.Tr d} {z : Site 2}
    (hz : CoreFrontier.Frontier h z) (hpre : PreReveal r t q C.eps h)
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {rho : Real}
    (hfail : h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h
        (owner hpre.frontier z hz) z axis sign q C.eps) ≤ 9 * rho / 32) :
    1 - 9 * rho / 32 ≤ h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchSuccess r t s K h
        (owner hpre.frontier z hz) z axis sign q C.eps) :=
  CoreBatchNoGluing.one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess
    (R := 0) hfail

/-! ## Closure under supported accepted commits -/

/-- Reveal-only rounds never forget a site already recorded open. -/
theorem openSites_subset_run
    {P : Tr d → Prop} (Rph : ABDAdaptReg.RevealPhase (Site d) (Site 2) P)
    (base h : Tr d) (n : Nat) (omega : SiteConfig (Site d)) :
    h.openSites ⊆ (Rph.run base n h omega).openSites := by
  classical
  induction n generalizing h with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
      exact Finset.Subset.trans (by
        intro x hx
        change x ∈ h.openSites ∪
          (Rph.region base h).filter (fun x => x ∈ omega)
        exact Finset.mem_union_left _ hx)
        (ih (Rph.reveal base h omega))

/-- A supported successful core batch returns to exactly the reservation-admissible class.  The
only new probabilistic data required here are the core bounds delivered by the actually selected
stopped levels. -/
theorem commit_success_admissible
    {A : Finset (Site 2)} {r t : Nat} {q : unitInterval} {eps : Real}
    (Rph : ABDAdaptReg.RevealPhase (Site d) (Site 2)
      (Admissible (d := d) A r t q eps))
    {base : Tr d} (hadm : Admissible A r t q eps base)
    {w z : Site 2} (hd : 2 ≤ d) (hr : 0 < r)
    (hw : w ∈ base.openV) (hz : z ∈ MacroExp.pending d base.base w)
    (hzA : z ∈ A)
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
    Admissible A r t q eps
      ((Rph.run base (Rph.rounds base) base outer).step z ∅
        (CoreBatchShadow.maximalDamage base z) true commitOmega) := by
  classical
  let k := Rph.run base (Rph.rounds base) base outer
  let post := k.step z ∅ (CoreBatchShadow.maximalDamage base z) true commitOmega
  have hi := CoreBatchTransition.commit_success_after_supported_run
    Rph hadm hd hr hw hz hzA hadm.sound hadm.preReveal.tagged
      hadm.preReveal.frontier hregions outer commitOmega hreads hnew
  have horun : (MacroExp.emb 0 : Site d) ∈ k.openSites :=
    openSites_subset_run Rph base base (Rph.rounds base) outer
      hadm.preReveal.origin_open
  have hopost : (MacroExp.emb 0 : Site d) ∈ post.openSites := by
    change (MacroExp.emb 0 : Site d) ∈ k.openSites ∪
      (∅ : Finset (Site d)).filter (fun x => x ∈ commitOmega)
    exact Finset.mem_union_left _ horun
  exact
    { sound := hi.1
      preReveal :=
        { zero_open := hi.1.1
          origin_open := hopost
          tagged := hi.2.2
          frontier := hi.2.1 } }

/-- Failure closure for the same supported reveal.  The centre and at most four new heads are
closed, while every surviving old owner persists from the pre-reveal invariant. -/
theorem commit_failure_admissible
    {A : Finset (Site 2)} {r t : Nat} {q : unitInterval} {eps : Real}
    (Rph : ABDAdaptReg.RevealPhase (Site d) (Site 2)
      (Admissible (d := d) A r t q eps))
    {base : Tr d} (hadm : Admissible A r t q eps base)
    {w z : Site 2} (hd : 2 ≤ d) (hr : 0 < r)
    (hw : w ∈ base.openV) (hz : z ∈ MacroExp.pending d base.base w)
    (hzA : z ∈ A)
    (hregions : ∀ k, Rph.Phase base k →
      Rph.region base k ⊆ CoreRes.batchReadSupport d r t base.base w z)
    (outer commitOmega : SiteConfig (Site d))
    (hreads : (Rph.run base (Rph.rounds base) base outer).inspected ⊆
      base.inspected ∪ MacroExp.E d r t w z ∪
        CoreTaggedCover.liveRegions d r t (CoreCoverUpdate.newEdges base.base z)) :
    Admissible A r t q eps
      ((Rph.run base (Rph.rounds base) base outer).step z ∅
        (CoreBatchShadow.maximalDamage base z) false commitOmega) := by
  classical
  let k := Rph.run base (Rph.rounds base) base outer
  let post := k.step z ∅ (CoreBatchShadow.maximalDamage base z) false commitOmega
  have hi := CoreBatchTransition.commit_failure_after_supported_run
    Rph hadm hd hr hw hz hzA hadm.sound hadm.preReveal.tagged
      hadm.preReveal.frontier hregions outer commitOmega hreads
  have horun : (MacroExp.emb 0 : Site d) ∈ k.openSites :=
    openSites_subset_run Rph base base (Rph.rounds base) outer
      hadm.preReveal.origin_open
  have hopost : (MacroExp.emb 0 : Site d) ∈ post.openSites := by
    change (MacroExp.emb 0 : Site d) ∈ k.openSites ∪
      (∅ : Finset (Site d)).filter (fun x => x ∈ commitOmega)
    exact Finset.mem_union_left _ horun
  exact
    { sound := hi.1
      preReveal :=
        { zero_open := hi.1.1
          origin_open := hopost
          tagged := hi.2.2
          frontier := hi.2.1 } }

/-! ## Honest initialization -/

/-- The bounded-damage transcript corresponding to the usual macro start. -/
def start (d r t : Nat) [NeZero d] : Tr d :=
  ⟨MacroExp.start d r t, ∅⟩

/-- Genuine initial core bounds initialize the accepted-only admissible class. -/
theorem start_admissible_of_initialCoreBounds
    (A : Finset (Site 2)) (r t : Nat) (q : unitInterval) (eps : Real)
    (hb : CoreInitial.InitialCoreBounds (d := d) r t q eps) :
    Admissible A r t q eps (start d r t) := by
  classical
  have hinit := CoreInitial.initialized_of_initialCoreBounds
    (d := d) r t q eps hb
  have horigin : (MacroExp.emb 0 : Site d) ∈
      (MacroExp.start d r t).openSites := by
    change (MacroExp.emb 0 : Site d) ∈ MacroExp.Q d r t 0
    exact MacroExp.M_subset_Q r t 0 (MacroExp.emb_zero_mem_M r t)
  refine
    { sound := ?_
      preReveal :=
        { zero_open := by simp [start, MacroExp.start]
          origin_open := horigin
          tagged := hinit.1
          frontier := hinit.2 } }
  unfold BDDom.Transcript.Sound
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (0 : Site 2) ∈ ({0} : Finset (Site 2))
    simp
  · change Disjoint ({0} : Finset (Site 2)) ∅
    rw [Finset.disjoint_left]
    simp
  · change (∅ : Finset (Site 2)) ⊆ ∅
    exact Finset.Subset.rfl
  · intro v hv
    change v ∈ (∅ : Finset (Site 2)) at hv
    exact (Finset.notMem_empty v hv).elim

#print axioms KNAll.Site.CoreAcceptedTransition.frontier_of_mem_boundary
#print axioms KNAll.Site.CoreAcceptedTransition.owner_spec
#print axioms KNAll.Site.CoreAcceptedTransition.inspected_subset_thin
#print axioms KNAll.Site.CoreAcceptedTransition.inspected_disjoint_frontier_Q
#print axioms KNAll.Site.CoreAcceptedTransition.outgoing_geometry_of_preReveal
#print axioms KNAll.Site.CoreAcceptedTransition.prob_batchFailure_le_of_preReveal
#print axioms KNAll.Site.CoreAcceptedTransition.commit_success_admissible
#print axioms KNAll.Site.CoreAcceptedTransition.commit_failure_admissible
#print axioms KNAll.Site.CoreAcceptedTransition.start_admissible_of_initialCoreBounds

end KNAll.Site.CoreAcceptedTransition

end
