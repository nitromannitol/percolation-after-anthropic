import Hypergraph.CoreStoppedReveal
import Hypergraph.CoreAdaptiveSoundness

set_option maxHeartbeats 3000000

/-!
# Accepted-only bounded-damage core assembly

This module instantiates the admissibility-indexed bounded-damage exploration with the concrete
stopped scheduler.  Its interpreter proof supplies both scheduler-correctness facts: a positive
terminal verdict extends every selected stopped prefix without later reads in that head's
protected edge, and the composite success probability is the pre-reveal `batchSuccess`
probability.

Everything else -- boundary selection, one-owner selection, bounded read support, persistence of
old owners, bounded collateral damage, and post-commit new-head reservations -- is discharged
here.  The analytic theorem below keeps every scale, face, long-box, and post-window input visible.
-/

noncomputable section

namespace KNAll.Site.CoreAcceptedAssembly

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

abbrev Tr (d : Nat) := BDDom.Transcript (Site d) (Site 2)

/-- The remaining deterministic scheduler contract.  It is separated from the analytic inputs
and states exactly that later heads do not invalidate an earlier stopped reservation. -/
def StopsExtend (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int) : Prop :=
  ∀ (base k : Tr d),
    CoreStoppedReveal.PhaseRel (box 2 n) r t s K n q eps
      (axis (CoreStoppedReveal.centre n base))
      (sign (CoreStoppedReveal.centre n base)) base k →
    ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
    CoreStoppedReveal.verdict r t s K n q eps
      (axis (CoreStoppedReveal.centre n base))
      (sign (CoreStoppedReveal.centre n base)) base k →
    ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (CoreStoppedReveal.centre n base),
      CoreStoppedReveal.StopExtension r t s K n q eps
        (axis (CoreStoppedReveal.centre n base))
        (sign (CoreStoppedReveal.centre n base)) base k y

theorem stopsExtend
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base, CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base, CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y)) :
    StopsExtend (d := d) r t s K n q eps axis sign := by
  intro base k hk hactive hverdict y hy
  have hadm := CoreStoppedReveal.PhaseRel.admissible_base hk
  exact CoreStoppedReveal.stopExtension_of_phase_verdict hd hr hrt hs hbudget hk hactive
    (hsigma base hadm hactive) (hemb base hadm hactive) hverdict hy

/-- The stopped reveal phase with directions selected from the current base centre.  During one
phase the base is fixed, so this is definitionally the already proved unary stopped scheduler at
`axis (centre base)` and `sign (centre base)`. -/
def centredRevealPhase
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int) :
    ABDAdaptReg.RevealPhase (Site d) (Site 2)
      (CoreAcceptedTransition.Admissible (d := d) A r t q eps) where
  Phase := fun base k => CoreStoppedReveal.PhaseRel A r t s K n q eps
    (axis (CoreStoppedReveal.centre n base))
    (sign (CoreStoppedReveal.centre n base)) base k
  rounds _ := K + 1
  anchor _ _ := 0
  region := fun base k => CoreStoppedReveal.region r t s K n q eps
    (axis (CoreStoppedReveal.centre n base))
    (sign (CoreStoppedReveal.centre n base)) base k
  start _ hadm := CoreStoppedReveal.PhaseRel.start hadm
  openV_eq _ _ hk := CoreStoppedReveal.PhaseRel.openV_eq hk
  closedV_eq _ _ hk := CoreStoppedReveal.PhaseRel.closedV_eq hk
  failed_eq _ _ hk := CoreStoppedReveal.PhaseRel.failed_eq hk
  anchor_open _ _ hk := CoreStoppedReveal.PhaseRel.zero_open hk
  region_fresh := by
    intro base k hk
    exact CoreStoppedReveal.region_fresh r t s K n q eps
      (axis (CoreStoppedReveal.centre n base))
      (sign (CoreStoppedReveal.centre n base)) base k
  step_phase := fun _ _ hk omega => CoreStoppedReveal.PhaseRel.step hk omega

theorem centredRevealPhase_run_eq
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (base h : Tr d) (m : Nat) (omega : SiteConfig (Site d)) :
    (centredRevealPhase (d := d) A r t s K n q eps axis sign).run base m h omega =
      (CoreStoppedReveal.phase (d := d) A r t s K n q eps
        (axis (CoreStoppedReveal.centre n base))
        (sign (CoreStoppedReveal.centre n base))).run base m h omega := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih =>
      change (centredRevealPhase (d := d) A r t s K n q eps axis sign).run base m
          (h.step 0 (CoreStoppedReveal.region r t s K n q eps
            (axis (CoreStoppedReveal.centre n base))
            (sign (CoreStoppedReveal.centre n base)) base h) ∅ true omega) omega =
        (CoreStoppedReveal.phase (d := d) A r t s K n q eps
          (axis (CoreStoppedReveal.centre n base))
          (sign (CoreStoppedReveal.centre n base))).run base m
            (h.step 0 (CoreStoppedReveal.region r t s K n q eps
              (axis (CoreStoppedReveal.centre n base))
              (sign (CoreStoppedReveal.centre n base)) base h) ∅ true omega) omega
      exact ih _

/-- Concrete accepted-only exploration.  No analytic estimate is stored in this object. -/
def exploration
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base, CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base, CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y)) :
    ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) where
  density := fun _ => q
  Admissible := CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps
  revealPhase := centredRevealPhase (d := d) (box 2 n) r t s K n q eps axis sign
  next := CoreStoppedReveal.centre n
  damage := fun base _ =>
    CoreBatchShadow.maximalDamage base (CoreStoppedReveal.centre n base)
  succ := fun base => CoreStoppedReveal.succ r t s K n q eps
    (axis (CoreStoppedReveal.centre n base))
    (sign (CoreStoppedReveal.centre n base)) base
  succ_measurable := fun base => CoreStoppedReveal.succ_measurable r t s K n q eps
    (axis (CoreStoppedReveal.centre n base))
    (sign (CoreStoppedReveal.centre n base)) base
  next_mem_boundary := by
    intro base hadm hactive
    exact MacroExp.pendZ_mem d n (MacroExp.boundary_nonempty_of_not_terminal d n hactive)
  succ_determinedBy := by
    intro base hadm hactive k hk
    exact CoreStoppedReveal.succ_determinedBy r t s K n q eps
      (axis (CoreStoppedReveal.centre n base))
      (sign (CoreStoppedReveal.centre n base)) base k
  commit_admissible := by
    classical
    intro base hadm hactive k hk b omega hb
    let z := CoreStoppedReveal.centre n base
    let w := CoreStoppedReveal.owner r t q eps n base
    have hzbd : z ∈ base.boundary (zdGraph 2) (box 2 n) 0 :=
      MacroExp.pendZ_mem d n (MacroExp.boundary_nonempty_of_not_terminal d n hactive)
    have hzfront : CoreFrontier.Frontier base.base z :=
      CoreAcceptedTransition.frontier_of_mem_boundary hadm.sound hzbd
    have hw := CoreStoppedReveal.owner_spec hadm.preReveal.frontier hzfront
    have hreads : k.inspected ⊆
        base.inspected ∪ MacroExp.E d r t w z ∪
          CoreTaggedCover.liveRegions d r t (CoreCoverUpdate.newEdges base.base z) := by
      simpa only [z, w, CoreRes.batchReadSupport, Finset.union_assoc] using
        CoreStoppedReveal.inspected_subset_of_phase hd hr hrt hs hbudget hk hactive
          (hsigma base hadm hactive) (hemb base hadm hactive)
    have hpersist : ∀ (bb : Bool) (u y : Site 2),
        CoreTaggedCover.Live r t q eps base.base (u, y) → y ≠ z →
        CoreRes.Bound r t q eps
          (k.step z ∅ (CoreBatchShadow.maximalDamage base z) bb omega).base u y := by
      intro bb u y hold hyz
      have hb0 := CoreStoppedReveal.oldLive_bound_of_phase hd hr hrt hs hbudget hk hactive
        (hsigma base hadm hactive) (hemb base hadm hactive) hold hyz
      exact CoreRes.bound_emptyCommit r t q eps k u y z
        (CoreBatchShadow.maximalDamage base z) bb omega hb0
    have hopen : k.base.openV = base.base.openV :=
      (centredRevealPhase (d := d) (box 2 n) r t s K n q eps axis sign).openV_eq
        base k hk
    have hclosed : k.base.closedV = base.base.closedV :=
      (centredRevealPhase (d := d) (box 2 n) r t s K n q eps axis sign).closedV_eq
        base k hk
    have hpersistFront : ∀ (bb : Bool) (y : Site 2),
        CoreFrontier.Frontier base.base y → y ≠ z →
        (bb = false → y ∉ CoreBatchShadow.maximalDamage base z) →
        CoreFrontier.HasOwner r t q eps
          (k.step z ∅ (CoreBatchShadow.maximalDamage base z) bb omega).base y := by
      intro bb y hyFront hyz hsafe
      obtain ⟨u, hu, huy, hbound⟩ := hadm.preReveal.frontier y hyFront
      have hold : CoreTaggedCover.Live r t q eps base.base (u, y) := ⟨hu, huy, hbound⟩
      refine ⟨u, ?_, ?_, hpersist bb u y hold hyz⟩
      · change u ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) bb omega).openV
        rw [BDDom.Transcript.step_openV]
        cases bb <;> simp only [Bool.false_eq_true, if_false, if_true, Finset.mem_insert]
        · change u ∈ k.openV
          rwa [CoreStoppedReveal.PhaseRel.openV_eq hk]
        · exact Or.inr (by
            change u ∈ k.openV
            rwa [CoreStoppedReveal.PhaseRel.openV_eq hk])
      · rw [MacroExp.mem_pending]
        refine ⟨((MacroExp.mem_pending (d := d)).1 huy).1, ?_⟩
        intro hydet
        change y ∈ (k.step z ∅ (CoreBatchShadow.maximalDamage base z) bb omega).openV ∪
          (k.step z ∅ (CoreBatchShadow.maximalDamage base z) bb omega).closedV at hydet
        have hyold := ((MacroExp.mem_pending (d := d)).1 huy).2
        cases bb with
        | false =>
            change y ∈ k.base.openV ∪
              (insert z k.base.closedV ∪ CoreBatchShadow.maximalDamage base z) at hydet
            simp only [Finset.mem_union, Finset.mem_insert] at hydet
            rcases hydet with hyo | (hyz' | hyc) | hyd
            · exact hyold (Finset.mem_union_left _ (by
                rw [hopen] at hyo
                exact hyo))
            · exact hyz hyz'
            · exact hyold (Finset.mem_union_right _ (by
                rw [hclosed] at hyc
                exact hyc))
            · exact (hsafe rfl) hyd
        | true =>
            change y ∈ insert z k.base.openV ∪ k.base.closedV at hydet
            simp only [Finset.mem_union, Finset.mem_insert] at hydet
            rcases hydet with (hyz' | hyo) | hyc
            · exact hyz hyz'
            · exact hyold (Finset.mem_union_left _ (by
                rw [hopen] at hyo
                exact hyo))
            · exact hyold (Finset.mem_union_right _ (by
                rw [hclosed] at hyc
                exact hyc))
    cases b with
    | false =>
        have hi := CoreBatchTransition.commit_failure_invariants
          (centredRevealPhase (d := d) (box 2 n) r t s K n q eps axis sign)
          hk hw.1 hw.2.1 hzbd.1 hadm.sound hadm.preReveal.tagged omega hreads
          (fun e he hez => hpersist false e.1 e.2 he hez)
          (fun y hy hyz hyd => hpersistFront false y hy hyz (fun _ => hyd))
        exact
          { sound := hi.1
            preReveal :=
              { zero_open := hi.1.1
                origin_open := by
                  have ho : (MacroExp.emb 0 : Site d) ∈ k.openSites :=
                    CoreStoppedReveal.PhaseRel.openSites_subset hk
                      hadm.preReveal.origin_open
                  change (MacroExp.emb 0 : Site d) ∈ k.openSites ∪
                    (∅ : Finset (Site d)).filter (fun x => x ∈ omega)
                  exact Finset.mem_union_left _ ho
                tagged := hi.2.2
                frontier := hi.2.1 } }
    | true =>
        have hmem : omega ∈ CoreStoppedReveal.succ r t s K n q eps
            (axis z) (sign z) base k := hb.mp rfl
        have hverdict := (CoreStoppedReveal.mem_succ_iff_verdict
          r t s K n q eps (axis z) (sign z) base k omega).1 hmem
        have hnew : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base z,
            CoreRes.Bound r t q eps
              (k.step z ∅ (CoreBatchShadow.maximalDamage base z) true omega).base z y := by
          intro y hy
          exact CoreStoppedReveal.bound_after_commit_of_stopExtension
            (hverdict.2.2 y hy)
              (CoreStoppedReveal.stopExtension_of_phase_verdict hd hr hrt hs hbudget hk hactive
                (hsigma base hadm hactive) (hemb base hadm hactive) hverdict hy)
              (CoreBatchShadow.maximalDamage base z) true omega
        have hi := CoreBatchTransition.commit_success_invariants
          (centredRevealPhase (d := d) (box 2 n) r t s K n q eps axis sign)
          hk hw.1 hw.2.1 hzbd.1 hadm.sound hadm.preReveal.tagged omega hreads
          (fun e he hez => hpersist true e.1 e.2 he hez)
          (fun y hy hyz => hpersistFront true y hy hyz (fun hfalse => by simp at hfalse))
          hnew
        exact
          { sound := hi.1
            preReveal :=
              { zero_open := hi.1.1
                origin_open := by
                  have ho : (MacroExp.emb 0 : Site d) ∈ k.openSites :=
                    CoreStoppedReveal.PhaseRel.openSites_subset hk
                      hadm.preReveal.origin_open
                  change (MacroExp.emb 0 : Site d) ∈ k.openSites ∪
                    (∅ : Finset (Site d)).filter (fun x => x ∈ omega)
                  exact Finset.mem_union_left _ ho
                tagged := hi.2.2
                frontier := hi.2.1 } }
  admissible_sound := fun _ hadm => hadm.sound

/-- The concrete exploration's success event is exactly the base-pinned pullback of the analytic
`batchSuccess` event. -/
theorem exploration_success_eq_substitute_preimage_batchSuccess
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base, CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base, CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y))
    (base : Tr d) :
    (exploration r t s K n q eps axis sign hd hr hrt hs hbudget hsigma hemb).success base =
      substitute (↑base.inspected : Set (Site d)) base.state ⁻¹'
        CoreBatchTransition.batchSuccess r t s K base.base
          (CoreStoppedReveal.owner r t q eps n base)
          (CoreStoppedReveal.centre n base)
          (axis (CoreStoppedReveal.centre n base))
          (sign (CoreStoppedReveal.centre n base)) q eps := by
  change {omega : SiteConfig (Site d) |
      omega ∈ CoreStoppedReveal.succ r t s K n q eps
        (axis (CoreStoppedReveal.centre n base))
        (sign (CoreStoppedReveal.centre n base)) base
        ((centredRevealPhase (d := d) (box 2 n) r t s K n q eps axis sign).run
          base (K + 1) base omega)} = _
  simp_rw [centredRevealPhase_run_eq]
  exact CoreStoppedReveal.compositeSuccess_eq_substitute_preimage_batchSuccess
    (box 2 n) r t s K n q eps
      (axis (CoreStoppedReveal.centre n base))
      (sign (CoreStoppedReveal.centre n base)) base

theorem exploration_prob_success_eq_prob_batchSuccess
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base, CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base, CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y))
    (base : Tr d) :
    base.prob (fun _ : Site d => q)
        ((exploration r t s K n q eps axis sign hd hr hrt hs hbudget hsigma hemb).success base) =
      base.prob (fun _ : Site d => q)
        (CoreBatchTransition.batchSuccess r t s K base.base
          (CoreStoppedReveal.owner r t q eps n base)
          (CoreStoppedReveal.centre n base)
          (axis (CoreStoppedReveal.centre n base))
          (sign (CoreStoppedReveal.centre n base)) q eps) := by
  rw [exploration_success_eq_substitute_preimage_batchSuccess]
  change pinnedProb (fun _ : Site d => q) (↑base.inspected : Set (Site d)) base.state
      (substitute (↑base.inspected : Set (Site d)) base.state ⁻¹'
        CoreBatchTransition.batchSuccess r t s K base.base
          (CoreStoppedReveal.owner r t q eps n base)
          (CoreStoppedReveal.centre n base)
          (axis (CoreStoppedReveal.centre n base))
          (sign (CoreStoppedReveal.centre n base)) q eps) = _
  unfold pinnedProb
  congr 1
  ext omega
  simp only [Set.mem_preimage]
  have hidem : substitute (↑base.inspected : Set (Site d)) base.state
      (substitute (↑base.inspected : Set (Site d)) base.state omega) =
      substitute (↑base.inspected : Set (Site d)) base.state omega := by
    ext x
    by_cases hx : x ∈ (↑base.inspected : Set (Site d))
    · rw [mem_substitute_of_mem base.state hx, mem_substitute_of_mem base.state hx]
    · rw [mem_substitute_of_notMem base.state hx, mem_substitute_of_notMem base.state hx]
  rw [hidem]

/-! ## Explicit analytic step -/

/-- All analytic inputs for one accepted examination remain visible.  The displayed probability
equality is discharged by `exploration_prob_success_eq_prob_batchSuccess` for the concrete
exploration; no source estimate or pinned-site gluing premise occurs. -/
theorem success_lower_bound_of_windows
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hd : 3 ≤ d)
    {r t R s K n : Nat} {base : Tr d}
    (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q C.eps base)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int) {rho : Real}
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
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
      (CoreStoppedReveal.centre n base),
      sign (CoreStoppedReveal.centre n base) y = 1 ∨
        sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
      (CoreStoppedReveal.centre n base),
      (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
        Pi.single (axis (CoreStoppedReveal.centre n base) y)
          (sign (CoreStoppedReveal.centre n base) y))
    (hface : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
      (CoreStoppedReveal.centre n base),
      CoreRes.FaceInputs (d := d) R base.base q
        (base.inspected ∪ MacroExp.E d r t
          (CoreStoppedReveal.owner r t q C.eps n base)
          (CoreStoppedReveal.centre n base) ∪
          Stopped.stub (MacroExp.ctr d r (CoreStoppedReveal.centre n base))
            (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y) r t (17 * r)))
    (hlong : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
      (CoreStoppedReveal.centre n base),
      CoreRes.LongInputs (d := d) R base.base q
        (base.inspected ∪ MacroExp.E d r t
          (CoreStoppedReveal.owner r t q C.eps n base)
          (CoreStoppedReveal.centre n base) ∪
          Stopped.stub (MacroExp.ctr d r (CoreStoppedReveal.centre n base))
            (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y) r t (17 * r))
        (axis (CoreStoppedReveal.centre n base) y)
        (sign (CoreStoppedReveal.centre n base) y))
    (hwindow : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
      (CoreStoppedReveal.centre n base),
      ∀ outer : SiteConfig (Site d), ∀ j, j < K → ∀ xi : SiteConfig (Site d),
      CorePostSupport.CorePostWindowBound C q
        (MacroExp.ctr d r (CoreStoppedReveal.centre n base))
        (axis (CoreStoppedReveal.centre n base) y)
        (sign (CoreStoppedReveal.centre n base) y)
        r t s j
        (CorePost.levelDom r t s
          (AtomTower.incomingTr d r t base.base
            (CoreStoppedReveal.owner r t q C.eps n base)
            (CoreStoppedReveal.centre n base) outer)
          (CoreStoppedReveal.centre n base) y
          (axis (CoreStoppedReveal.centre n base) y)
          (sign (CoreStoppedReveal.centre n base) y) j xi)
        (↑(CoreRes.target (d := d) r y) : Set (Site d)))
    (E : ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hmatch : base.prob E.density (E.success base) =
      base.prob (fun _ : Site d => q)
        (CoreBatchTransition.batchSuccess r t s K base.base
          (CoreStoppedReveal.owner r t q C.eps n base)
          (CoreStoppedReveal.centre n base)
          (axis (CoreStoppedReveal.centre n base))
          (sign (CoreStoppedReveal.centre n base)) q C.eps)) :
    1 - 9 * rho / 32 ≤ base.prob E.density (E.success base) := by
  have hzbd : CoreStoppedReveal.centre n base ∈
      base.boundary (zdGraph 2) (box 2 n) 0 :=
    MacroExp.pendZ_mem d n (MacroExp.boundary_nonempty_of_not_terminal d n hactive)
  have hzfront := CoreAcceptedTransition.frontier_of_mem_boundary hadm.sound hzbd
  have howner := CoreStoppedReveal.owner_eq_of_invariant hadm.preReveal.frontier hzfront
  rw [howner] at hface hlong hwindow hmatch
  have hfail := CoreAcceptedSupport.prob_batchFailure_le_of_preReveal
    hwf hv hd hzfront hadm.preReveal
      (axis (CoreStoppedReveal.centre n base))
      (sign (CoreStoppedReveal.centre n base)) hr ht h44 hR1 hscale hs hbudget
    hrho0 hrho1 heps_rho he_beta hpow hclear hwidth htail hplanar htrans
    hsigma hemb hface hlong hwindow
  have hsucc := CoreAcceptedSupport.one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess_of_preReveal
    hzfront hadm.preReveal hfail
  change base.base.prob E.density (E.success base) =
    base.base.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchSuccess r t s K base.base
        (CoreAcceptedTransition.owner hadm.preReveal.frontier
          (CoreStoppedReveal.centre n base) hzfront)
        (CoreStoppedReveal.centre n base)
        (axis (CoreStoppedReveal.centre n base))
        (sign (CoreStoppedReveal.centre n base)) q C.eps) at hmatch
  change 1 - 9 * rho / 32 ≤ base.base.prob E.density (E.success base)
  rw [hmatch]
  exact hsucc

/-- Honest initialization feed for the accepted-only assembly. -/
abbrev start_admissible_of_initialCoreBounds :=
  @CoreAcceptedTransition.start_admissible_of_initialCoreBounds

/-- Slab/certificate consumer for the exact admissibility-indexed bounded-damage exploration type
constructed above. -/
abbrev certificateSound2_of_acceptedAssembly :=
  @CoreAdaptSound.certificateSound2_of_adaptive

#print axioms KNAll.Site.CoreAcceptedAssembly.exploration
#print axioms KNAll.Site.CoreAcceptedAssembly.stopsExtend
#print axioms KNAll.Site.CoreAcceptedAssembly.exploration_success_eq_substitute_preimage_batchSuccess
#print axioms KNAll.Site.CoreAcceptedAssembly.exploration_prob_success_eq_prob_batchSuccess
#print axioms KNAll.Site.CoreAcceptedAssembly.success_lower_bound_of_windows
#print axioms KNAll.Site.CoreAcceptedAssembly.certificateSound2_of_acceptedAssembly

end KNAll.Site.CoreAcceptedAssembly

end
