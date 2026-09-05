import Hypergraph.ExactCorridorPlan
import Hypergraph.CoreAcceptedAssembly
import Hypergraph.CoreReachableSafe

/-!
# Exact finite macro-plan interpreter bridges

This module starts the rank-three exact macro interpreter at its smallest reusable seam.  An exact
corridor plan is interpreted under the current finite pinned transcript and supplies the precise
radius-`2r` core event consumed by the stopped incoming-atom tower.  Exact stopped target plans in
turn supply the one-level contraposition used by that tower.  Extraction of these finite plans is
deliberately separate.
-/

noncomputable section

namespace KNAll.Site.ExactMacroPlan

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

/-! ## Event and pinned-measure monotonicity -/

private theorem connWithinSet_mono
    {D D' A A' : Finset (Site d)} {o : Site d}
    (hD : D ⊆ D') (hA : A ⊆ A') :
    connWithinSet (zdGraph d) (↑D : Set (Site d)) o (↑A : Set (Site d)) ⊆
      connWithinSet (zdGraph d) (↑D' : Set (Site d)) o (↑A' : Set (Site d)) := by
  intro omega homega
  obtain ⟨x, hx, hox⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑D : Set (Site d)) o
      (↑A : Set (Site d)) omega).1 homega
  exact (mem_connWithinSet_iff (zdGraph d) (↑D' : Set (Site d)) o
    (↑A' : Set (Site d)) omega).2
      ⟨x, Finset.mem_coe.2 (hA (Finset.mem_coe.1 hx)),
        connWithin_mono_set (zdGraph d) (Finset.coe_subset.2 hD) o x hox⟩

private theorem transcript_prob_mono {h : MacroExp.Tr d} {q : unitInterval}
    {A B : Set (SiteConfig (Site d))} (hAB : A ⊆ B) :
    h.prob (fun _ : Site d => q) A ≤ h.prob (fun _ : Site d => q) B :=
  ProbInv.prob_mono h (fun _ : Site d => q) hAB

/-! ## The exact corridor conclusion before its final radius enlargement -/

/-- Exact corridor soundness with the terminal target kept at the radius-`2r` inner core.  The
existing `ExactCorridorPlan.Plan.soundPinned` proves a radius-`3r` enlargement; the stopped tower
needs this preceding conclusion of the same finite chain. -/
theorem soundPinnedInner (J : ExactCorridorPlan.Plan d) (hJ : J.WellFormed)
    {q : unitInterval} (hvalid : J.ValidAt q)
    (R : Finset (Site d)) (val : Site d → Prop) (o : Site d)
    (hRactive : ∀ i, Disjoint R (J.stage i).active)
    (hoR : o ∈ R) (hvalo : val o)
    (hbase : 1 - J.beta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑(J.domain 0) : Set (Site d)) o
          (↑J.initialCore : Set (Site d)))) :
    1 - J.alpha <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(J.domain (Fin.last d)) : Set (Site d)) o
          (↑J.innerTarget : Set (Site d))) := by
  have hbase' : 1 - (J.stage 0).delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑(J.domain 0) : Set (Site d)) o
          (↑(J.stage 0).source : Set (Site d))) := by
    rw [hJ.stage_delta 0, hJ.stage_source 0, hJ.initial_box]
    exact hbase
  have hchain := ExactTargetPlan.Plan.soundPinnedChain d J.stage J.domain R val o
    hJ.stage_wf hvalid
    (fun i x hx => Finset.mem_union_right (J.past i) hx)
    hRactive hoR hvalo hbase' hJ.domain_mono
    (fun i => by rw [hJ.quarter_target i, hJ.stage_source i.succ])
    (fun i => by rw [hJ.quarter_epsilon i, hJ.stage_delta i.succ])
  rw [J.stage_last, hJ.aspect_epsilon, hJ.aspect_target] at hchain
  simpa [ExactCorridorPlan.Plan.domain] using hchain

/-- Overlap-compatible exterior form of `soundPinnedInner`, obtained from the exact exterior
stage chain.  This is the form used by the macro interpreter before the incoming region is read. -/
theorem soundPinnedInnerExterior (J : ExactCorridorPlan.Plan d) (hJ : J.WellFormed)
    {q : unitInterval} (hvalid : J.ValidAt q)
    (R : Finset (Site d)) (val : Site d → Prop) (o : Site d)
    (hRext : ∀ u, R ⊆ ExactTargetPlan.exterior (J.past u) (J.stage u).active)
    (hoR : o ∈ R) (hvalo : val o)
    (hbase : 1 - J.beta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑(J.domain 0) : Set (Site d)) o
          (↑J.initialCore : Set (Site d)))) :
    1 - J.alpha <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(J.domain (Fin.last d)) : Set (Site d)) o
          (↑J.innerTarget : Set (Site d))) := by
  have hbase' : 1 - (J.stage 0).delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(J.past 0 ∪ (J.stage 0).active) : Set (Site d)) o
          (↑(J.stage 0).source : Set (Site d))) := by
    rw [hJ.stage_delta 0, hJ.stage_source 0, hJ.initial_box]
    exact hbase
  have hchain := ExactTargetPlan.Plan.soundPinnedExteriorChain d J.stage J.past R val o
    hJ.stage_wf hvalid hRext hoR hvalo hbase' hJ.domain_mono
    (fun u => by rw [hJ.quarter_target u, hJ.stage_source u.succ])
    (fun u => by rw [hJ.quarter_epsilon u, hJ.stage_delta u.succ])
  rw [J.stage_last, hJ.aspect_epsilon, hJ.aspect_target] at hchain
  simpa [ExactCorridorPlan.Plan.domain] using hchain

/-! ## One exact corridor invocation -/

/-- An actual exact corridor plan supplies the pre-examination radius-`2r` corridor estimate.

All matching premises are finite set inclusions or numerical comparisons.  In particular, no
universal face/long-box implication is assumed.  The current incoming reservation is enlarged to
the plan's first domain and source; the plan is interpreted once; its terminal event is then
restricted to the exact narrow corridor domain used by `CoreAtom`. -/
theorem corridor_bound_of_exactPlan
    (J : ExactCorridorPlan.Plan d) (hJ : J.WellFormed)
    {q : unitInterval} (hvalid : J.ValidAt q)
    {r t : Nat} {h : MacroExp.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {e rho : Real}
    (hincoming : CoreRes.Bound (d := d) r t q e h w z)
    (heBeta : e ≤ J.beta) (hAlpha : J.alpha ≤ rho / 32)
    (hRext : ∀ u, h.inspected ⊆
      ExactTargetPlan.exterior (J.past u) (J.stage u).active)
    (horiginInspected : (MacroExp.emb 0 : Site d) ∈ h.inspected)
    (horiginOpen : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfirstDomain : h.inspected ∪ MacroExp.E d r t w z ⊆ J.domain 0)
    (hfirstSource : CoreRes.target (d := d) r z ⊆ J.initialCore)
    (hlastDomain : J.domain (Fin.last d) ⊆
      h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r))
    (hlastTarget : J.innerTarget ⊆ CoreRes.target (d := d) r y) :
    1 - rho / 32 < h.prob (fun _ : Site d => q)
      (CoreAtom.narrowCoreCorridor r t h w z y i sigma) := by
  have hbaseEvent : CoreRes.event (d := d) r t h w z ⊆
      connWithinSet (zdGraph d) (↑(J.domain 0) : Set (Site d))
        (MacroExp.emb 0) (↑J.initialCore : Set (Site d)) := by
    unfold CoreRes.event
    exact connWithinSet_mono hfirstDomain hfirstSource
  have hbaseProb := transcript_prob_mono (h := h) (q := q) hbaseEvent
  have hbase : 1 - J.beta <
      h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑(J.domain 0) : Set (Site d))
          (MacroExp.emb 0) (↑J.initialCore : Set (Site d))) := by
    unfold CoreRes.Bound at hincoming
    exact lt_of_le_of_lt (by linarith : 1 - J.beta ≤ 1 - e)
      (lt_of_lt_of_le hincoming hbaseProb)
  have hinner := soundPinnedInnerExterior J hJ hvalid h.inspected h.state (MacroExp.emb 0)
    hRext horiginInspected horiginOpen hbase
  have hlastEvent :
      connWithinSet (zdGraph d) (↑(J.domain (Fin.last d)) : Set (Site d))
          (MacroExp.emb 0) (↑J.innerTarget : Set (Site d)) ⊆
        CoreAtom.narrowCoreCorridor r t h w z y i sigma := by
    unfold CoreAtom.narrowCoreCorridor
    exact connWithinSet_mono hlastDomain hlastTarget
  have hlastProb := transcript_prob_mono (h := h) (q := q) hlastEvent
  exact lt_of_le_of_lt (by linarith : 1 - rho / 32 ≤ 1 - J.alpha)
    (lt_of_lt_of_le hinner hlastProb)

/-! ## One exact stopped target invocation -/

/-- A finite exact target plan supplies precisely the one-level implication used by the stopped
tower.  This is the manuscript's contraposition: were the narrow face reached with probability
greater than `1 - P.delta`, exact target soundness would make the next core reservation good.

The freshness premise is imposed at the *actual level transcript*.  Thus the active coordinates
cannot include an old-frontier site or a suffix already read for the same head. -/
theorem prob_crossEvent_le_of_exactTarget
    (P : ExactTargetPlan.Plan d) (hP : P.WellFormed)
    {q : unitInterval} (hvalid : P.ValidAt q)
    {r t s j : Nat} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : Int} {deltaC e : Real}
    (omega : SiteConfig (Site d))
    (hactive : P.active ⊆
      (Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
        MacroExp.E d r t z y)
    (hfresh : Disjoint
      (Stopped.levelTr d r t s h z i sigma j omega).inspected P.active)
    (horigin : (MacroExp.emb 0 : Site d) ∈
      (Stopped.levelTr d r t s h z i sigma j omega).inspected)
    (horiginOpen :
      (Stopped.levelTr d r t s h z i sigma j omega).state (MacroExp.emb 0))
    (hstubDomain :
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)) ⊆
        (Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
          MacroExp.E d r t z y)
    (hfaceSource :
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)) ⊆
        P.source)
    (htarget : P.target ⊆ CoreRes.target (d := d) r y)
    (hPdelta : AtomTower.f e ≤ P.delta)
    (hPepsilon : P.epsilon ≤ deltaC)
    (hbad : substitute (↑h.inspected : Set (Site d)) h.state omega ∈
      CoreStopped.levelBad r t s h z y i sigma q deltaC j) :
    (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
      (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - AtomTower.f e := by
  let k := Stopped.levelTr d r t s h z i sigma j omega
  let Dom := k.inspected ∪ MacroExp.E d r t z y
  have hbad' : omega ∈ CoreStopped.levelBad r t s h z y i sigma q deltaC j :=
    (CoreStopped.substitute_mem_levelBad_iff r t s h z y i sigma q deltaC j omega).1 hbad
  have hcore : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
        (↑(CoreRes.target (d := d) r y) : Set (Site d))) ≤ 1 - deltaC := by
    simpa only [CoreStopped.levelBad, CoreRes.event, Set.mem_setOf_eq, k, Dom] using hbad'
  have hplanTarget : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
        (↑P.target : Set (Site d))) ≤ 1 - P.epsilon := by
    have hmono := transcript_prob_mono (h := k) (q := q)
      (connWithinSet_mono (D := Dom) (D' := Dom) (A := P.target)
        (A' := CoreRes.target (d := d) r y) (o := MacroExp.emb 0)
        (fun _ hx => hx) htarget)
    exact (hmono.trans hcore).trans (by linarith)
  have hcrossPlan : Stopped.crossEvent d r t s h z i sigma j ⊆
      connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
        (↑P.source : Set (Site d)) := by
    unfold Stopped.crossEvent
    apply connWithinSet_mono
    · intro x hx
      rw [Finset.mem_union] at hx ⊢
      exact hx.elim
        (fun hxk => Or.inl (by
          change x ∈ (Stopped.levelTr d r t s h z i sigma j omega).inspected
          rw [Stopped.levelTr_inspected]
          exact Finset.mem_union_left _ hxk))
        (fun hxF => by
          have hxDom : x ∈ k.inspected ∪ MacroExp.E d r t z y := by
            simpa only [k] using hstubDomain hxF
          exact Finset.mem_union.1 hxDom)
    · exact hfaceSource
  have hcross : k.prob (fun _ : Site d => q)
      (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - P.delta := by
    by_contra hnot
    have hsrc : 1 - P.delta < k.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑P.source : Set (Site d))) :=
      lt_of_lt_of_le (lt_of_not_ge hnot)
        (transcript_prob_mono (h := k) (q := q) hcrossPlan)
    have hout := P.soundPinned hP hvalid (Dom := Dom) (R := k.inspected)
      hactive hfresh k.state (MacroExp.emb 0)
      (Finset.mem_union_left _ horigin)
      horigin horiginOpen hsrc
    exact (not_lt_of_ge hplanTarget) hout
  exact hcross.trans (by linarith)

/-! ## Finite one-step plan data -/

/-- The outgoing directions which this concrete one-step interpreter must handle. -/
abbrev Head (h : MacroExp.Tr d) (z : Site 2) :=
  {y : Site 2 // y ∈ CoreFrontier.newHeads (d := d) h z}

/-- The smallest finite exact-plan datum for one interior macro examination.  There is one exact
corridor plan per actual new head and one stopped target plan per head and tested level.  The
structure contains data only: validity, geometry, freshness, and soundness are separate
predicates/theorem premises. -/
structure Plan (h : MacroExp.Tr d) (z : Site 2) (K : Nat) where
  corridor : Head h z → ExactCorridorPlan.Plan d
  stopped : Head h z → Fin K → ExactTargetPlan.Plan d

namespace Plan

/-- Purely deterministic local well-formedness of every finite child. -/
def WellFormed {h : MacroExp.Tr d} {z : Site 2} {K : Nat}
    (M : Plan h z K) : Prop :=
  (∀ y, (M.corridor y).WellFormed) ∧
    ∀ y j, (M.stopped y j).WellFormed

/-- Finite validity of every child at the same product parameter. -/
def ValidAt {h : MacroExp.Tr d} {z : Site 2} {K : Nat}
    (M : Plan h z K) (q : unitInterval) : Prop :=
  (∀ y, (M.corridor y).ValidAt q) ∧
    ∀ y j, (M.stopped y j).ValidAt q

end Plan

/-- Deterministic interpretation data matching one finite pair of children to one actual outgoing
head.  It contains no probability bound or soundness implication.  The two transcript-quantified
freshness clauses state the no-stale-reservation fact at the exact level where pinning occurs. -/
structure DirectionCompatible
    {h : MacroExp.Tr d} {z : Site 2} {K r t s : Nat} {w : Site 2}
    {e deltaC rho : Real} (axis : Site 2 → Site 2 → Fin d)
    (sign : Site 2 → Site 2 → Int)
    (M : Plan h z K) (Y : Head h z) : Prop where
  sign_unit : sign z Y.1 = 1 ∨ sign z Y.1 = -1
  emb_direction : (MacroExp.emb (Y.1 - z) : Site d) =
    Pi.single (axis z Y.1) (sign z Y.1)
  head_ne_zero : Y.1 ≠ 0
  outgoing_fresh : Disjoint (h.inspected ∪ MacroExp.E d r t w z)
    (MacroExp.E d r t z Y.1)
  corridor_beta : e ≤ (M.corridor Y).beta
  corridor_alpha : (M.corridor Y).alpha ≤ rho / 16
  corridor_exterior : ∀ u, h.inspected ⊆ ExactTargetPlan.exterior
    ((M.corridor Y).past u) ((M.corridor Y).stage u).active
  corridor_first_domain : h.inspected ∪ MacroExp.E d r t w z ⊆
    (M.corridor Y).domain 0
  corridor_first_source : CoreRes.target (d := d) r z ⊆
    (M.corridor Y).initialCore
  corridor_last_domain : (M.corridor Y).domain (Fin.last d) ⊆
    h.inspected ∪ MacroExp.E d r t w z ∪
      Stopped.stub (MacroExp.ctr d r z) (axis z Y.1) (sign z Y.1) r t (17 * r)
  corridor_last_target : (M.corridor Y).innerTarget ⊆
    CoreRes.target (d := d) r Y.1
  stopped_active : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
    ∀ xi : SiteConfig (Site d), (M.stopped Y a).active ⊆
      (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
        z (axis z Y.1) (sign z Y.1) a.val xi).inspected ∪ MacroExp.E d r t z Y.1
  stopped_fresh : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
    ∀ xi : SiteConfig (Site d), Disjoint
      (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
        z (axis z Y.1) (sign z Y.1) a.val xi).inspected (M.stopped Y a).active
  stopped_stub_domain : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
    ∀ xi : SiteConfig (Site d),
    Stopped.stub (MacroExp.ctr d r z) (axis z Y.1) (sign z Y.1) r t
      (10 * s * (a.val + 1)) ⊆
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
          z (axis z Y.1) (sign z Y.1) a.val xi).inspected ∪ MacroExp.E d r t z Y.1
  stopped_source : ∀ a : Fin K,
    Stopped.stubFace (MacroExp.ctr d r z) (axis z Y.1) (sign z Y.1) r t
      (10 * s * (a.val + 1)) ⊆ (M.stopped Y a).source
  stopped_target : ∀ a : Fin K,
    (M.stopped Y a).target ⊆ CoreRes.target (d := d) r Y.1
  stopped_delta : ∀ a : Fin K, AtomTower.f e ≤ (M.stopped Y a).delta
  stopped_epsilon : ∀ a : Fin K, (M.stopped Y a).epsilon ≤ deltaC

/-! ## Finite stopped-family interpretation -/

/-- Interpret the `K` explicitly stored stopped-target children into the exact `hone` premise of
the incoming-atom tower.  All variable facts concern only inclusion/freshness at the actual level
transcript; no probability implication is assumed. -/
theorem hone_of_exactTargets
    {q : unitInterval} {r t s K : Nat} {g : MacroExp.Tr d} {w z y : Site 2}
    {i : Fin d} {sigma : Int} {deltaC e : Real}
    (T : Fin K → ExactTargetPlan.Plan d)
    (hTwf : ∀ a, (T a).WellFormed) (hTvalid : ∀ a, (T a).ValidAt q)
    (hactive : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d), (T a).active ⊆
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t g w z outer)
          z i sigma a.val xi).inspected ∪ MacroExp.E d r t z y)
    (hfresh : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d), Disjoint
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t g w z outer)
          z i sigma a.val xi).inspected (T a).active)
    (horigin : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d), (MacroExp.emb 0 : Site d) ∈
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t g w z outer)
          z i sigma a.val xi).inspected)
    (horiginOpen : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d),
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t g w z outer)
          z i sigma a.val xi).state (MacroExp.emb 0))
    (hstubDomain : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d),
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)) ⊆
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t g w z outer)
          z i sigma a.val xi).inspected ∪ MacroExp.E d r t z y)
    (hsource : ∀ a : Fin K,
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)) ⊆
        (T a).source)
    (htarget : ∀ a : Fin K,
      (T a).target ⊆ CoreRes.target (d := d) r y)
    (hdelta : ∀ a : Fin K, AtomTower.f e ≤ (T a).delta)
    (hepsilon : ∀ a : Fin K, (T a).epsilon ≤ deltaC) :
    ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
      substitute
          (↑(AtomTower.incomingTr d r t g w z outer).inspected : Set (Site d))
          (AtomTower.incomingTr d r t g w z outer).state xi ∈
        CoreStopped.levelBad r t s (AtomTower.incomingTr d r t g w z outer)
          z y i sigma q deltaC j →
      (Stopped.levelTr d r t s (AtomTower.incomingTr d r t g w z outer)
          z i sigma j xi).prob (fun _ : Site d => q)
        (Stopped.crossEvent d r t s (AtomTower.incomingTr d r t g w z outer)
          z i sigma j) ≤ 1 - AtomTower.f e := by
  intro outer j hj xi hbad
  let a : Fin K := ⟨j, hj⟩
  exact prob_crossEvent_le_of_exactTarget (T a) (hTwf a)
    (hTvalid a) xi (hactive outer a xi) (hfresh outer a xi)
    (horigin outer a xi) (horiginOpen outer a xi) (hstubDomain outer a xi)
    (hsource a) (htarget a) (hdelta a) (hepsilon a) hbad

/-! ## One exact outgoing direction -/

/-- One exact corridor child and its `K` exact stopped-target children imply the v15 directional
failure bound `rho/8`.  Internally the existing atom tower is instantiated at error parameter
`2*rho`; hence its two `rho/32` terms become `rho/16`, exactly the manuscript budget. -/
theorem prob_directionFailure_le_of_exactChildren
    (hd : 3 ≤ d) {q : unitInterval} {r t s K : Nat}
    {h : MacroExp.Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int}
    {deltaC e rho : Real}
    (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hy : y ≠ 0)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
      MacroExp.thin d t)
    (hfreshOut : Disjoint (h.inspected ∪ MacroExp.E d r t w z)
      (MacroExp.E d r t z y))
    (hrho0 : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (he0 : 0 < e) (heBeta : e ≤ AtomTower.beta (2 * rho) d)
    (hpow : (1 - AtomTower.f e) ^ K ≤ rho / 16)
    (hincoming : CoreRes.Bound (d := d) r t q e h w z)
    (J : ExactCorridorPlan.Plan d) (hJ : J.WellFormed)
    (hJvalid : J.ValidAt q) (heJBeta : e ≤ J.beta)
    (hJalpha : J.alpha ≤ rho / 16)
    (hJext : ∀ u, h.inspected ⊆
      ExactTargetPlan.exterior (J.past u) (J.stage u).active)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.inspected)
    (horiginOpen : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hJfirstDomain : h.inspected ∪ MacroExp.E d r t w z ⊆ J.domain 0)
    (hJfirstSource : CoreRes.target (d := d) r z ⊆ J.initialCore)
    (hJlastDomain : J.domain (Fin.last d) ⊆
      h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r))
    (hJlastTarget : J.innerTarget ⊆ CoreRes.target (d := d) r y)
    (T : Fin K → ExactTargetPlan.Plan d)
    (hTwf : ∀ a, (T a).WellFormed) (hTvalid : ∀ a, (T a).ValidAt q)
    (hTactive : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d), (T a).active ⊆
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma a.val xi).inspected ∪ MacroExp.E d r t z y)
    (hTfresh : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d), Disjoint
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma a.val xi).inspected (T a).active)
    (hTorigin : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d), (MacroExp.emb 0 : Site d) ∈
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma a.val xi).inspected)
    (hToriginOpen : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d),
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma a.val xi).state (MacroExp.emb 0))
    (hTstubDomain : ∀ (outer : SiteConfig (Site d)) (a : Fin K),
      ∀ xi : SiteConfig (Site d),
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)) ⊆
        (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma a.val xi).inspected ∪ MacroExp.E d r t z y)
    (hTsource : ∀ a : Fin K,
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)) ⊆
        (T a).source)
    (hTtarget : ∀ a : Fin K,
      (T a).target ⊆ CoreRes.target (d := d) r y)
    (hTdelta : ∀ a : Fin K, AtomTower.f e ≤ (T a).delta)
    (hTepsilon : ∀ a : Fin K, (T a).epsilon ≤ deltaC) :
    h.prob (fun _ : Site d => q)
      (CoreBatchTransition.directionFailure r t s K h w z y i sigma q deltaC) ≤
        rho / 8 := by
  have hrho2_0 : 0 < 2 * rho := by positivity
  have hrho2_1 : 2 * rho ≤ 1 := by linarith
  have hcorr : 1 - (2 * rho) / 32 < h.prob (fun _ : Site d => q)
      (CoreAtom.narrowCoreCorridor r t h w z y i sigma) :=
    corridor_bound_of_exactPlan J hJ hJvalid hincoming heJBeta
      (by linarith) hJext horigin horiginOpen hJfirstDomain hJfirstSource
      hJlastDomain hJlastTarget
  have hone := hone_of_exactTargets T hTwf hTvalid hTactive hTfresh hTorigin
    hToriginOpen hTstubDomain hTsource hTtarget hTdelta hTepsilon
  have hpow' : (1 - AtomTower.f e) ^ K ≤ (2 * rho) / 32 := by
    convert hpow using 1 <;> ring
  have houter := CoreAtom.prob_outerNoGoodLevel_le hd hr ht hs hbudget hsigma hemb hy
    hthin hfreshOut hrho2_0 hrho2_1 he0 heBeta hpow' hcorr hone
  have hdir := CoreAtom.prob_outerDirectionFailure_le houter
  change h.prob (fun _ : Site d => q)
    {outer | outer ∉ CoreStopped.directionEvent r t s
      (AtomTower.incomingTr d r t h w z outer) z y i sigma q deltaC K} ≤ rho / 8
  convert hdir using 1 <;> ring

/-- Interpret one head of the finite `Plan`.  This is the direct bridge from the concrete child
tables and their deterministic compatibility proof to the runtime direction event. -/
theorem Plan.prob_directionFailure_le
    {q : unitInterval} {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {deltaC rho : Real} (axis : Site 2 → Site 2 → Fin d)
    (sign : Site 2 → Site 2 → Int)
    (M : Plan h z K) (hM : M.WellFormed) (hvalid : M.ValidAt q)
    (Y : Head h z)
    (hcompat : DirectionCompatible (r := r) (t := t) (s := s) (w := w)
      (e := deltaC) (deltaC := deltaC) (rho := rho) axis sign M Y)
    (hd : 3 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
      MacroExp.thin d t)
    (hrho0 : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (he0 : 0 < deltaC) (heBeta : deltaC ≤ AtomTower.beta (2 * rho) d)
    (hpow : (1 - AtomTower.f deltaC) ^ K ≤ rho / 16)
    (hincoming : CoreRes.Bound (d := d) r t q deltaC h w z)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.inspected)
    (horiginOpen : (MacroExp.emb 0 : Site d) ∈ h.openSites) :
    h.prob (fun _ : Site d => q)
      (CoreBatchTransition.directionFailure r t s K h w z Y.1
        (axis z Y.1) (sign z Y.1) q deltaC) ≤ rho / 8 := by
  exact prob_directionFailure_le_of_exactChildren hd hr ht hs hbudget
    hcompat.sign_unit hcompat.emb_direction hcompat.head_ne_zero hthin
    hcompat.outgoing_fresh hrho0 hrhoHalf he0 heBeta hpow hincoming
    (M.corridor Y) (hM.1 Y) (hvalid.1 Y) hcompat.corridor_beta
    hcompat.corridor_alpha hcompat.corridor_exterior horigin horiginOpen
    hcompat.corridor_first_domain hcompat.corridor_first_source
    hcompat.corridor_last_domain hcompat.corridor_last_target
    (M.stopped Y) (hM.2 Y) (hvalid.2 Y) hcompat.stopped_active
    hcompat.stopped_fresh
    (fun outer a xi => by
      rw [Stopped.levelTr_inspected, AtomTower.incomingTr_inspected]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ horigin))
    (fun outer a xi => by
      rw [Stopped.levelTr, FRDom.Transcript.step_state,
        AtomTower.incomingTr, FRDom.Transcript.step_state]
      exact Or.inl (Or.inl horiginOpen))
    hcompat.stopped_stub_domain hcompat.stopped_source hcompat.stopped_target
    hcompat.stopped_delta hcompat.stopped_epsilon

/-! ## The v15 one-owner batch budget -/

/-- The manuscript's exact batch union bound.  The one incoming failure costs at most `deltaC`,
and the at-most-four exact outgoing children cost `rho/8` each.  No independence is used. -/
theorem prob_batchFailure_le_v15
    {q : unitInterval} {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {deltaC rho : Real}
    (hrho0 : 0 < rho) (hdeltaC : deltaC ≤ rho / 2)
    (hincoming : CoreRes.Bound (d := d) r t q deltaC h w z)
    (hout : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      h.prob (fun _ : Site d => q)
        (CoreBatchTransition.directionFailure r t s K h w z y
          (axis z y) (sign z y) q deltaC) ≤ rho / 8) :
    h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h w z (axis z) (sign z) q deltaC) ≤ rho := by
  have hin : h.prob (fun _ : Site d => q)
      (CoreBatchTransition.incomingFailure r t h w z) ≤ deltaC := by
    have hm := measurableSet_connWithinSet (zdGraph d)
      (h.inspected ∪ MacroExp.E d r t w z)
      (MacroExp.emb 0) (↑(CoreRes.target (d := d) r z) : Set (Site d))
    rw [CoreBatchTransition.incomingFailure, CoreRes.event,
      FRDom.Transcript.prob_eq, pinnedProb_compl _ _ _ hm,
      ← FRDom.Transcript.prob_eq]
    unfold CoreRes.Bound CoreRes.event at hincoming
    linarith
  have hdirs : h.prob (fun _ : Site d => q)
      (⋃ y ∈ CoreFrontier.newHeads (d := d) h z,
        CoreBatchTransition.directionFailure r t s K h w z y
          (axis z y) (sign z y) q deltaC) ≤
      (CoreFrontier.newHeads (d := d) h z).card * (rho / 8) :=
    CoreBatch.prob_biUnion_finset_le_card_mul h (fun _ : Site d => q)
      (CoreFrontier.newHeads (d := d) h z)
      (fun y => CoreBatchTransition.directionFailure r t s K h w z y
        (axis z y) (sign z y) q deltaC) hout
  have hcard : ((CoreFrontier.newHeads (d := d) h z).card : Real) ≤ 4 := by
    exact_mod_cast CoreFrontier.card_newHeads_le_four (d := d) h z
  have hmul : ((CoreFrontier.newHeads (d := d) h z).card : Real) * (rho / 8) ≤
      4 * (rho / 8) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  unfold CoreBatchTransition.batchFailure
  calc
    h.prob (fun _ : Site d => q)
        (CoreBatchTransition.incomingFailure r t h w z ∪
          ⋃ y ∈ CoreFrontier.newHeads (d := d) h z,
            CoreBatchTransition.directionFailure r t s K h w z y
              (axis z y) (sign z y) q deltaC)
      ≤ h.prob (fun _ : Site d => q) (CoreBatchTransition.incomingFailure r t h w z) +
          h.prob (fun _ : Site d => q)
            (⋃ y ∈ CoreFrontier.newHeads (d := d) h z,
              CoreBatchTransition.directionFailure r t s K h w z y
                (axis z y) (sign z y) q deltaC) := AtomTower.prob_union_le h _ _ _
    _ ≤ deltaC + (CoreFrontier.newHeads (d := d) h z).card * (rho / 8) :=
      add_le_add hin hdirs
    _ ≤ rho / 2 + 4 * (rho / 8) := add_le_add hdeltaC hmul
    _ = rho := by ring

/-- The complete probability interpretation of one finite exact `Plan`: each finite head is
interpreted by its exact corridor/stopped children and the results are combined by the v15
one-owner budget. -/
theorem Plan.prob_batchFailure_le
    {q : unitInterval} {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {deltaC rho : Real} (axis : Site 2 → Site 2 → Fin d)
    (sign : Site 2 → Site 2 → Int)
    (M : Plan h z K) (hM : M.WellFormed) (hvalid : M.ValidAt q)
    (hcompat : ∀ Y : Head h z,
      DirectionCompatible (r := r) (t := t) (s := s) (w := w)
        (e := deltaC) (deltaC := deltaC) (rho := rho) axis sign M Y)
    (hd : 3 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
      MacroExp.thin d t)
    (hrho0 : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (hdeltaC0 : 0 < deltaC) (hdeltaC : deltaC ≤ rho / 2)
    (heBeta : deltaC ≤ AtomTower.beta (2 * rho) d)
    (hpow : (1 - AtomTower.f deltaC) ^ K ≤ rho / 16)
    (hincoming : CoreRes.Bound (d := d) r t q deltaC h w z)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.inspected)
    (horiginOpen : (MacroExp.emb 0 : Site d) ∈ h.openSites) :
    h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h w z (axis z) (sign z) q deltaC) ≤ rho := by
  apply prob_batchFailure_le_v15 hrho0 hdeltaC hincoming
  intro y hy
  let Y : Head h z := ⟨y, hy⟩
  exact M.prob_directionFailure_le axis sign hM hvalid Y (hcompat Y)
    hd hr ht hs hbudget hthin hrho0 hrhoHalf hdeltaC0 heBeta hpow hincoming
    horigin horiginOpen

/-- Complement form of the exact v15 batch estimate, directly consumed by the accepted stopped
scheduler's probability equality. -/
theorem one_sub_rho_le_prob_batchSuccess_v15
    {q : unitInterval} {r t s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Site 2 → Fin d} {sign : Site 2 → Site 2 → Int}
    {deltaC rho : Real}
    (hfail : h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h w z (axis z) (sign z) q deltaC) ≤ rho) :
    1 - rho ≤ h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchSuccess r t s K h w z (axis z) (sign z) q deltaC) := by
  exact CoreBatch.one_sub_le_prob_compl h (fun _ : Site d => q)
    (CoreBatchTransition.batchFailure r t s K h w z (axis z) (sign z) q deltaC)
    (CoreBatchTransition.measurableSet_batchFailure r t s K h w z
      (axis z) (sign z) q deltaC)
    hfail

/-! ## Accepted stopped-scheduler bridge -/

/-- A v15 batch estimate is transferred, without loss, through the concrete accepted-only
stopped scheduler.  This is the one-step probability clause required by adaptive soundness. -/
theorem acceptedExploration_success_of_batchFailure_v15
    (r t s K n : Nat) (q : unitInterval) (deltaC rho : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q deltaC base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q deltaC base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y))
    (base : BDDom.Transcript (Site d) (Site 2))
    (hparam : (CoreSafe.successParam : Real) ≤ 1 - rho)
    (hfail : base.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K base.base
        (CoreStoppedReveal.owner r t q deltaC n base)
        (CoreStoppedReveal.centre n base)
        (axis (CoreStoppedReveal.centre n base))
        (sign (CoreStoppedReveal.centre n base)) q deltaC) ≤ rho) :
    (CoreSafe.successParam : Real) ≤
      base.prob (fun _ : Site d => q)
        ((CoreAcceptedAssembly.exploration r t s K n q deltaC axis sign
          hd hr hrt hs hbudget hsigma hemb).success base) := by
  have hbatch := one_sub_rho_le_prob_batchSuccess_v15 hfail
  have heq := CoreAcceptedAssembly.exploration_prob_success_eq_prob_batchSuccess
    r t s K n q deltaC axis sign hd hr hrt hs hbudget hsigma hemb base
  rw [heq]
  exact hparam.trans hbatch

/-- The same scheduler bridge with the v15 incoming and outgoing estimates as premises. -/
theorem acceptedExploration_success_of_directionBounds_v15
    (r t s K n : Nat) (q : unitInterval) (deltaC rho : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q deltaC base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q deltaC base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y))
    (base : BDDom.Transcript (Site d) (Site 2))
    (hrho0 : 0 < rho) (hdeltaC : deltaC ≤ rho / 2)
    (hparam : (CoreSafe.successParam : Real) ≤ 1 - rho)
    (hincoming : CoreRes.Bound (d := d) r t q deltaC base.base
      (CoreStoppedReveal.owner r t q deltaC n base)
      (CoreStoppedReveal.centre n base))
    (hout : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
      (CoreStoppedReveal.centre n base),
      base.prob (fun _ : Site d => q)
        (CoreBatchTransition.directionFailure r t s K base.base
          (CoreStoppedReveal.owner r t q deltaC n base)
          (CoreStoppedReveal.centre n base) y
          (axis (CoreStoppedReveal.centre n base) y)
          (sign (CoreStoppedReveal.centre n base) y) q deltaC) ≤ rho / 8) :
    (CoreSafe.successParam : Real) ≤
      base.prob (fun _ : Site d => q)
        ((CoreAcceptedAssembly.exploration r t s K n q deltaC axis sign
          hd hr hrt hs hbudget hsigma hemb).success base) := by
  apply acceptedExploration_success_of_batchFailure_v15 r t s K n q deltaC rho axis sign
    hd hr hrt hs hbudget hsigma hemb base hparam
  exact prob_batchFailure_le_v15 hrho0 hdeltaC hincoming hout

/-- **Concrete one-step exact macro soundness.**  A finite exact `Plan` matched to the current
accepted state gives the success lower bound of the actual stopped scheduler.  This is the seam
needed by the reachable adaptive assembly; construction/transport of the finite children remains
a separate extraction task. -/
theorem Plan.acceptedExploration_success_v15
    (r t s K n : Nat) (q : unitInterval) (deltaC rho : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 3 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q deltaC base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q deltaC base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y))
    (base : BDDom.Transcript (Site d) (Site 2))
    (M : Plan base.base (CoreStoppedReveal.centre n base) K)
    (hM : M.WellFormed) (hvalid : M.ValidAt q)
    (hcompat : ∀ Y : Head base.base (CoreStoppedReveal.centre n base),
      DirectionCompatible (r := r) (t := t) (s := s)
        (w := CoreStoppedReveal.owner r t q deltaC n base)
        (e := deltaC) (deltaC := deltaC) (rho := rho) axis sign M Y)
    (hthin : (↑(base.inspected ∪ MacroExp.E d r t
      (CoreStoppedReveal.owner r t q deltaC n base)
      (CoreStoppedReveal.centre n base)) : Set (Site d)) ⊆ MacroExp.thin d t)
    (hrho0 : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (hdeltaC0 : 0 < deltaC) (hdeltaC : deltaC ≤ rho / 2)
    (heBeta : deltaC ≤ AtomTower.beta (2 * rho) d)
    (hpow : (1 - AtomTower.f deltaC) ^ K ≤ rho / 16)
    (hincoming : CoreRes.Bound (d := d) r t q deltaC base.base
      (CoreStoppedReveal.owner r t q deltaC n base)
      (CoreStoppedReveal.centre n base))
    (horigin : (MacroExp.emb 0 : Site d) ∈ base.inspected)
    (horiginOpen : (MacroExp.emb 0 : Site d) ∈ base.openSites)
    (hparam : (CoreSafe.successParam : Real) ≤ 1 - rho) :
    (CoreSafe.successParam : Real) ≤
      base.prob (fun _ : Site d => q)
        ((CoreAcceptedAssembly.exploration r t s K n q deltaC axis sign
          (by omega : 2 ≤ d) hr (by omega : 2 * r ≤ t)
          hs hbudget hsigma hemb).success base) := by
  have hfail := M.prob_batchFailure_le axis sign hM hvalid hcompat hd hr ht hs hbudget
    hthin hrho0 hrhoHalf hdeltaC0 hdeltaC heBeta hpow hincoming horigin horiginOpen
  exact acceptedExploration_success_of_batchFailure_v15 r t s K n q deltaC rho
    axis sign (by omega) hr (by omega : 2 * r ≤ t)
    hs hbudget hsigma hemb base hparam hfail

#print axioms KNAll.Site.ExactMacroPlan.soundPinnedInner
#print axioms KNAll.Site.ExactMacroPlan.soundPinnedInnerExterior
#print axioms KNAll.Site.ExactMacroPlan.corridor_bound_of_exactPlan
#print axioms KNAll.Site.ExactMacroPlan.prob_crossEvent_le_of_exactTarget
#print axioms KNAll.Site.ExactMacroPlan.hone_of_exactTargets
#print axioms KNAll.Site.ExactMacroPlan.prob_directionFailure_le_of_exactChildren
#print axioms KNAll.Site.ExactMacroPlan.prob_batchFailure_le_v15
#print axioms KNAll.Site.ExactMacroPlan.acceptedExploration_success_of_directionBounds_v15
#print axioms KNAll.Site.ExactMacroPlan.Plan.prob_batchFailure_le
#print axioms KNAll.Site.ExactMacroPlan.Plan.acceptedExploration_success_v15

end KNAll.Site.ExactMacroPlan

end
