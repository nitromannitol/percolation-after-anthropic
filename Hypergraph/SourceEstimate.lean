import Hypergraph.CorridorEstimates

/-!
# The recorded-entry source estimate

## What this file is

This file names, once, the probabilistic input that the corridor machinery consumes at the
entrance of a fresh macro corridor, and it names it with an **origin** source.  It proves no
probability bound.  It is an interface, and the statement it names is an open obligation.

```
SourceEstimate C q h Reg o B  :=
  1 - C.eps / 8 < h.prob (fun _ => q)
    (connWithinSet (zdGraph d) ↑(h.inspected ∪ Reg) o B)
```

`OriginSourceEstimate` is the instance `o = MacroExp.emb 0`, and
`PendingOriginSourceEstimates` is the family of those instances over the still-pending
directions of one macro vertex, evaluated at one transcript.

## What is assumed, and where it has to be discharged

**Assumed.**  `PendingOriginSourceEstimates C q r t h⁺ z B` at the *accepted* transcript `h⁺` of
every accepting macro step.  Nothing in this repository proves it.  It is the H2 obligation: a
proof must construct, at each newly accepted macro vertex and inside the iterated tolerance
`β = (ρ/32)^(2^(d+1)) / 96^(2^(d+1)-1)` recorded by `CorrMove.beta` and `Certificate2.betaOf`,
a crossing of the fresh corridor `E z y` from the recorded origin to an inner target `B y`.

**Not assumed, and already proved.**  The initial instance at the start transcript.
`InitBridge.hinitialLongBox_holds` is exactly `PendingOriginSourceEstimates` at
`MacroExp.start d C.corridor C.halfWidth`, with `z = 0` and `B y = LongBox.innerBox`, from
`C.WellFormed` and `C.ValidAt2 q` alone.  It goes through the wide initial entrance experiment
`InitEnt.wideLongBoxExperiment`, whose source is the whole face `InitEnt.entryFace`, and it never
mentions `MacroExp.src`.

## Why the source is the origin and not a tip

A designated single fresh site as source caps the probability of the event by the site density:
`Entrance.entranceExperiment_prob_le` and `PinEnt.forcedCorridorExperiment_prob_le` prove exactly
that, and `PinEnt.not_pinnedEntranceBound_of_q_le` turns the cap into an impossibility at every
`q ≤ 1 - C.eps / 8`.  The origin escapes the cap because it is *recorded* open, which is
`origin_mem_openSites` below: a consequence of `MacroExp.Good.cert` at the macro vertex `0`, not
an extra assumption and not an observation of an unread coordinate.

For the same reason no theorem here, and none downstream, may replace the existential source of a
wide entrance event by the equation `g = MacroExp.src ...`.  That is the deleted one-site stub
condition under another name, and `math/RECORDED_OPEN_ENTRY.md` §2 exhibits a reachable,
positive-probability good transcript at which `MacroExp.src d r n h ∉ h.openSites`.

## Satisfiability

`lt_prob_connWithinSet_of_mem_openSites_of_mem` below is a machine-checked witness that the shape
of `SourceEstimate` is inhabited: at a recorded-open source whose target contains it, the pinned
probability is one.  This rules out the vacuous-hypothesis failure mode; it is deliberately a
degenerate target and is *not* evidence for the corridor-crossing instances, whose only proved
instance is the initial one named above.
-/

noncomputable section

namespace KNAll.Site.RecordedEntry

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor KNAll.Site.MacroExp

variable {d : ℕ}

/-! ## The named estimate -/

/-- **The source estimate.**  A name for the premise that the corridor machinery consumes; it
asserts no new probability bound.  `Reg` is the fresh region that the estimate is allowed to use,
`o` is the source, and `B` is the inner target. -/
def SourceEstimate (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (h : MacroExp.Tr d) (Reg : Finset (Site d)) (o : Site d) (B : Set (Site d)) : Prop :=
  1 - C.eps / 8 <
    h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B)

theorem sourceEstimate_iff (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (h : MacroExp.Tr d) (Reg : Finset (Site d)) (o : Site d) (B : Set (Site d)) :
    SourceEstimate C q h Reg o B ↔
      1 - C.eps / 8 <
        h.prob (fun _ : Site d => q)
          (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B) :=
  Iff.rfl

/-- **The origin-based source estimate.**  This is the only source the downstream interface uses.
Its source is the embedded lattice origin, which every good transcript records open. -/
def OriginSourceEstimate (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (h : MacroExp.Tr d) (Reg : Finset (Site d)) (B : Set (Site d)) : Prop :=
  SourceEstimate C q h Reg (MacroExp.emb 0) B

theorem originSourceEstimate_iff (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (h : MacroExp.Tr d) (Reg : Finset (Site d)) (B : Set (Site d)) :
    OriginSourceEstimate C q h Reg B ↔
      1 - C.eps / 8 <
        h.prob (fun _ : Site d => q)
          (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d))
            (MacroExp.emb 0) B) :=
  Iff.rfl

/-- **The family consumed at a macro transition.**  One origin-based estimate for each direction
still pending at `h`, each confined to that direction's own protected corridor.  The transcript is
a parameter, so an instance of this family is a statement about one specific history and cannot be
transported across a later read without a disjointness argument. -/
def PendingOriginSourceEstimates (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (r t : ℕ) (h : MacroExp.Tr d) (z : Site 2) (B : Site 2 → Set (Site d)) : Prop :=
  ∀ y ∈ MacroExp.pending d h z,
    OriginSourceEstimate C q h (MacroExp.E d r t z y) (B y)

theorem pendingOriginSourceEstimates_iff (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (r t : ℕ) (h : MacroExp.Tr d) (z : Site 2) (B : Site 2 → Set (Site d)) :
    PendingOriginSourceEstimates C q r t h z B ↔
      ∀ y ∈ MacroExp.pending d h z,
        1 - C.eps / 8 <
          h.prob (fun _ : Site d => q)
            (connWithinSet (zdGraph d)
              (↑(h.inspected ∪ MacroExp.E d r t z y) : Set (Site d))
              (MacroExp.emb 0) (B y)) :=
  Iff.rfl

/-! ## The origin is recorded open

This is the structural reason the interface is stated at the origin.  A source that the transcript
records open is open with probability one under the pinned law, so the estimate is a statement
about crossing the corridor and not about one unread coordinate being open. -/

/-- **The origin is recorded open at every good transcript.**  It is read off the certificate
clause of `MacroExp.Good` at the macro vertex `0`. -/
theorem origin_mem_openSites [NeZero d] {r t : ℕ} {q : unitInterval} {δ : ℝ}
    {h : MacroExp.Tr d} (hg : MacroExp.Good d r t (q := q) (δ := δ) h) :
    (MacroExp.emb 0 : Site d) ∈ h.openSites := by
  obtain ⟨a, -, hconn⟩ := hg.cert 0 hg.zero_mem
  exact Finset.mem_coe.1 hconn.1.1

/-! ## Satisfiability of the shape

The statement below is definitionally `SourceEstimate C q h Reg o B`; it is spelled out so that
`SourceEstimate` itself stays visibly an assumption of the tree rather than a proved proposition.
Its target is degenerate on purpose: it witnesses that the shape has models, and nothing more. -/

/-- **The shape is satisfiable.**  At a recorded-open source contained in the target, the pinned
probability of the confined connection event is one, so the estimate holds for every positive
tolerance. -/
theorem lt_prob_connWithinSet_of_mem_openSites_of_mem
    {C : LeftImp2.Certificate2 d} (heps : 0 < C.eps) (q : unitInterval)
    (h : MacroExp.Tr d) (Reg : Finset (Site d)) {o : Site d} (ho : o ∈ h.openSites)
    {B : Set (Site d)} (hoB : o ∈ B) :
    1 - C.eps / 8 <
      h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B) := by
  classical
  have hoI : o ∈ h.inspected := h.openSites_subset ho
  have hset : substitute (↑h.inspected : Set (Site d)) h.state ⁻¹'
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B) =
      (Set.univ : Set (SiteConfig (Site d))) := by
    refine Set.eq_univ_of_forall fun ω => ?_
    have hosub : o ∈ substitute (↑h.inspected : Set (Site d)) h.state ω := by
      rw [mem_substitute_of_mem h.state (Finset.mem_coe.2 hoI)]
      exact ho
    refine Set.mem_preimage.2 ((mem_connWithinSet_iff _ _ _ _ _).2 ⟨o, hoB, ?_⟩)
    exact ⟨⟨hosub, Finset.mem_coe.2 (Finset.mem_union_left Reg hoI)⟩,
      SimpleGraph.Reachable.refl o⟩
  have hone : h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B) = 1 := by
    rw [FRDom.Transcript.prob_eq]
    have hEq : pinnedProb (fun _ : Site d => q) (↑h.inspected : Set (Site d)) h.state
        (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B) =
        pinnedProb (fun _ : Site d => q) (↑h.inspected : Set (Site d)) h.state
          (Set.univ : Set (SiteConfig (Site d))) := by
      unfold pinnedProb
      rw [hset, Set.preimage_univ]
    rw [hEq, pinnedProb_univ]
  rw [hone]
  linarith

/-! ## The two honest consumers

Both theorems below are the existing consumers with their decisive premise replaced by its name.
Neither manufactures the premise.  The second is stated in `KN/AcquireClause.lean`, where the
accepted transcript is in scope. -/

/-- **The target extension, with its source premise named.**  Exactly
`MacroExp.lt_prob_connWithinSet_of_shellWindow`: from a source estimate at threshold
`1 - C.eps / 8` it produces the corridor estimate at threshold `1 - C.eps`.  The source `o` is
arbitrary; the interface instantiates it at `MacroExp.emb 0`. -/
theorem lt_prob_connWithinSet_of_sourceEstimate
    [NeZero d] {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q)
    (hpack : C.seedCount * (8 * C.faceTarget + 5) ^ d ≤ C.contacts)
    (h : MacroExp.Tr d) (Reg : Finset (Site d)) (hfresh : Disjoint Reg h.inspected)
    (c : Site d) (hplace : ∀ j, Dbox (scalesOf C) c j ⊆ Reg)
    (o : Site d) (ho : o ∉ Dbox (scalesOf C) c 0)
    (T B : Set (Site d)) (hBsub : ∀ i < C.levels, B ⊆ ↑(Dbox (scalesOf C) c i))
    (W : MacroExp.ShellWindow C q c (h.inspected ∪ Reg) T)
    (hsrc : SourceEstimate C q h Reg o B) :
    1 - C.eps < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o T) :=
  MacroExp.lt_prob_connWithinSet_of_shellWindow hwf hv hpack h Reg hfresh c hplace o ho T B
    hBsub W hsrc

/-- The same statement with the source fixed at the recorded origin. -/
theorem lt_prob_connWithinSet_of_originSourceEstimate
    [NeZero d] {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q)
    (hpack : C.seedCount * (8 * C.faceTarget + 5) ^ d ≤ C.contacts)
    (h : MacroExp.Tr d) (Reg : Finset (Site d)) (hfresh : Disjoint Reg h.inspected)
    (c : Site d) (hplace : ∀ j, Dbox (scalesOf C) c j ⊆ Reg)
    (ho : (MacroExp.emb 0 : Site d) ∉ Dbox (scalesOf C) c 0)
    (T B : Set (Site d)) (hBsub : ∀ i < C.levels, B ⊆ ↑(Dbox (scalesOf C) c i))
    (W : MacroExp.ShellWindow C q c (h.inspected ∪ Reg) T)
    (hsrc : OriginSourceEstimate C q h Reg B) :
    1 - C.eps < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d))
        (MacroExp.emb 0) T) :=
  lt_prob_connWithinSet_of_sourceEstimate hwf hv hpack h Reg hfresh c hplace
    (MacroExp.emb 0) ho T B hBsub W hsrc

#print axioms KNAll.Site.RecordedEntry.origin_mem_openSites
#print axioms KNAll.Site.RecordedEntry.lt_prob_connWithinSet_of_mem_openSites_of_mem
#print axioms KNAll.Site.RecordedEntry.lt_prob_connWithinSet_of_sourceEstimate
#print axioms KNAll.Site.RecordedEntry.lt_prob_connWithinSet_of_originSourceEstimate

end KNAll.Site.RecordedEntry

end
