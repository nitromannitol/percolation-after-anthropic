import Hypergraph.AdaptiveRegion
import Hypergraph.BoundedDamageDomination

/-!
# Adaptive reveal phases with bounded local damage

This module combines the two independent extensions of finite-radius domination already proved in
`AdaptiveRegion` and `BoundedDamageDomination`.  Before each macro verdict, a bounded reveal tree
may inspect a configuration-dependent finite region.  Reveal-only transitions leave the macro
state and the failed-centre ledger unchanged.  There is then exactly one commit: success opens one
centre, while failure records that one centre and may close a local finite damage set.

The comparison law therefore pays for exactly one Bernoulli failure coordinate per unsuccessful
macro examination, irrespective of the size of its collateral damage.
-/

noncomputable section

namespace KNAll.Site.BDAdaptReg

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

abbrev Tr (κ V : Type*) := BDDom.Transcript κ V

/-! ## Reveal-only phases -/

/-- A bounded reveal phase on bounded-damage transcripts.  Intermediate reveal states need not
satisfy the macro admissibility invariant, but they preserve all macro verdicts and the failed
centre ledger. -/
structure RevealPhase (κ V : Type*) [DecidableEq κ] [DecidableEq V] where
  Phase : Tr κ V → Tr κ V → Prop
  rounds : Tr κ V → ℕ
  anchor : Tr κ V → Tr κ V → V
  region : Tr κ V → Tr κ V → Finset κ
  start : ∀ h, Phase h h
  openV_eq : ∀ h k, Phase h k → k.openV = h.openV
  closedV_eq : ∀ h k, Phase h k → k.closedV = h.closedV
  failed_eq : ∀ h k, Phase h k → k.failed = h.failed
  anchor_open : ∀ h k, Phase h k → anchor h k ∈ k.openV
  region_fresh : ∀ h k, Phase h k → Disjoint (region h k) k.inspected
  step_phase : ∀ h k, Phase h k → ∀ ω : Set κ,
    Phase h (k.step (anchor h k) (region h k) ∅ true ω)

namespace RevealPhase

variable {κ V : Type*} [DecidableEq κ] [DecidableEq V] (R : RevealPhase κ V)

/-! ### Lifting an ordinary reveal phase

The physical part of a bounded-damage transcript is its `base` field.  During a reveal-only
step the collateral set is empty and the verdict is `true` at an already-open anchor, so this
physical part evolves by exactly the ordinary `FRDom.Transcript.step`.  The construction below
lets a stopped scheduler be implemented and verified once using `AdaptReg.RevealPhase`, then
lifts it to the bounded-damage state while keeping the failed-centre ledger fixed.
-/

/-- A reveal-only bounded-damage step projects definitionally to the corresponding ordinary
transcript step. -/
@[simp] theorem base_step_empty_true (h : Tr κ V) (z : V) (F : Finset κ) (ω : Set κ) :
    (h.step z F ∅ true ω).base = h.base.step z F true ω := rfl

/-- Lift an ordinary adaptive reveal phase through the physical `base` projection. -/
def ofBase (S : AdaptReg.RevealPhase κ V) : RevealPhase κ V where
  Phase base k := S.Phase base.base k.base ∧ k.failed = base.failed
  rounds base := S.rounds base.base
  anchor base k := S.anchor base.base k.base
  region base k := S.region base.base k.base
  start base := ⟨S.start base.base, rfl⟩
  openV_eq base k hk := S.openV_eq base.base k.base hk.1
  closedV_eq base k hk := S.closedV_eq base.base k.base hk.1
  failed_eq base k hk := hk.2
  anchor_open base k hk := S.anchor_open base.base k.base hk.1
  region_fresh base k hk := S.region_fresh base.base k.base hk.1
  step_phase base k hk ω := by
    refine ⟨?_, ?_⟩
    · simpa using S.step_phase base.base k.base hk.1 ω
    · simpa using hk.2

@[simp] theorem ofBase_rounds (S : AdaptReg.RevealPhase κ V) (h : Tr κ V) :
    (ofBase S).rounds h = S.rounds h.base := rfl

@[simp] theorem ofBase_anchor (S : AdaptReg.RevealPhase κ V) (base k : Tr κ V) :
    (ofBase S).anchor base k = S.anchor base.base k.base := rfl

@[simp] theorem ofBase_region (S : AdaptReg.RevealPhase κ V) (base k : Tr κ V) :
    (ofBase S).region base k = S.region base.base k.base := rfl

theorem ofBase_phase_iff (S : AdaptReg.RevealPhase κ V) (base k : Tr κ V) :
    (ofBase S).Phase base k ↔ S.Phase base.base k.base ∧ k.failed = base.failed := Iff.rfl

/-- One reveal-only transition.  Its damage argument is empty and its already-open anchor makes it
a pure physical-coordinate reveal. -/
def reveal (base h : Tr κ V) (ω : Set κ) : Tr κ V :=
  h.step (R.anchor base h) (R.region base h) ∅ true ω

/-- Run exactly `n` reveal rounds.  A stopped implementation uses the empty region in its
remaining rounds. -/
def run (base : Tr κ V) : ℕ → Tr κ V → Set κ → Tr κ V
  | 0, h, _ => h
  | n + 1, h, ω => run base n (R.reveal base h ω) ω

@[simp] theorem run_zero (base h : Tr κ V) (ω : Set κ) :
    R.run base 0 h ω = h := rfl

@[simp] theorem run_succ (base h : Tr κ V) (n : ℕ) (ω : Set κ) :
    R.run base (n + 1) h ω = R.run base n (R.reveal base h ω) ω := rfl

@[simp] theorem ofBase_reveal_base (S : AdaptReg.RevealPhase κ V)
    (base h : Tr κ V) (ω : Set κ) :
    ((ofBase S).reveal base h ω).base = S.reveal base.base h.base ω := rfl

/-- The whole lifted reveal tree has exactly the same physical shadow as the ordinary tree. -/
theorem ofBase_run_base (S : AdaptReg.RevealPhase κ V) (base h : Tr κ V) :
    ∀ n ω, ((ofBase S).run base n h ω).base = S.run base.base n h.base ω := by
  intro n
  induction n generalizing h with
  | zero => intro ω; rfl
  | succ n ih =>
      intro ω
      exact ih ((ofBase S).reveal base h ω) ω

theorem phase_run {base h : Tr κ V} (hh : R.Phase base h) :
    ∀ n ω, R.Phase base (R.run base n h ω) := by
  revert h
  intro h hh n
  induction n generalizing h with
  | zero => intro ω; simpa using hh
  | succ n ih =>
      intro ω
      exact ih (R.step_phase base h hh ω) ω

theorem reveal_openV {base h : Tr κ V} (hh : R.Phase base h) (ω : Set κ) :
    (R.reveal base h ω).openV = h.openV := by
  simp [reveal, Finset.insert_eq_of_mem (R.anchor_open base h hh)]

theorem reveal_closedV (base h : Tr κ V) (ω : Set κ) :
    (R.reveal base h ω).closedV = h.closedV := by
  simp [reveal]

theorem reveal_failed (base h : Tr κ V) (ω : Set κ) :
    (R.reveal base h ω).failed = h.failed := by
  simp [reveal]

theorem run_openV {base h : Tr κ V} (hh : R.Phase base h) :
    ∀ n ω, (R.run base n h ω).openV = h.openV := by
  revert h
  intro h hh n
  induction n generalizing h with
  | zero => intro ω; rfl
  | succ n ih =>
      intro ω
      calc
        (R.run base (n + 1) h ω).openV = (R.reveal base h ω).openV :=
          ih (R.step_phase base h hh ω) ω
        _ = h.openV := R.reveal_openV hh ω

theorem run_closedV {base h : Tr κ V} (hh : R.Phase base h) :
    ∀ n ω, (R.run base n h ω).closedV = h.closedV := by
  revert h
  intro h hh n
  induction n generalizing h with
  | zero => intro ω; rfl
  | succ n ih =>
      intro ω
      calc
        (R.run base (n + 1) h ω).closedV = (R.reveal base h ω).closedV :=
          ih (R.step_phase base h hh ω) ω
        _ = h.closedV := R.reveal_closedV base h ω

theorem run_failed {base h : Tr κ V} (hh : R.Phase base h) :
    ∀ n ω, (R.run base n h ω).failed = h.failed := by
  revert h
  intro h hh n
  induction n generalizing h with
  | zero => intro ω; rfl
  | succ n ih =>
      intro ω
      calc
        (R.run base (n + 1) h ω).failed = (R.reveal base h ω).failed :=
          ih (R.step_phase base h hh ω) ω
        _ = h.failed := R.reveal_failed base h ω

/-- The configuration-dependent region actually read by the phase. -/
def recordedRegion (base : Tr κ V) (ω : Set κ) : Finset κ :=
  (R.run base (R.rounds base) base ω).inspected \ base.inspected

theorem recordedRegion_fresh (base : Tr κ V) (ω : Set κ) :
    Disjoint (R.recordedRegion base ω) base.inspected := Finset.sdiff_disjoint

theorem inspected_mono {base h : Tr κ V} :
    ∀ n ω, h.inspected ⊆ (R.run base n h ω).inspected := by
  revert h
  intro h n
  induction n generalizing h with
  | zero => intro ω; exact Finset.Subset.rfl
  | succ n ih =>
      intro ω
      exact Finset.Subset.trans (by simp [reveal])
        (ih (h := R.reveal base h ω) ω)

theorem inspected_final (base : Tr κ V) (ω : Set κ) :
    (R.run base (R.rounds base) base ω).inspected =
      base.inspected ∪ R.recordedRegion base ω := by
  symm
  exact Finset.union_sdiff_of_subset
    (R.inspected_mono (base := base) (h := base) (R.rounds base) ω)

/-! ### Measurability and tower calculation -/

/-- A predicate evaluated after a bounded adaptive reveal is measurable whenever it is measurable
at every fixed terminal transcript. -/
theorem measurableSet_setOf_run
    (P : Tr κ V → Set κ → Prop)
    (hP : ∀ h, MeasurableSet {ω : Set κ | P h ω}) :
    ∀ n base h, MeasurableSet {ω : Set κ | P (R.run base n h ω) ω} := by
  intro n
  induction n with
  | zero => intro base h; simpa using hP h
  | succ n ih =>
      intro base h
      rw [show {ω : Set κ | P (R.run base (n + 1) h ω) ω} =
          {ω : Set κ | P (R.run base n
            (h.step (R.anchor base h) (R.region base h) ∅ true ω) ω) ω} by rfl]
      rw [h.setOf_step_eq_biUnion (fun _ => (∅ : Finset V))
        (fun _ _ _ => rfl)
        (fun h' ω => P (R.run base n h' ω) ω)]
      exact Finset.measurableSet_biUnion _ fun σ _ =>
        (measurableSet_localCylinder (R.region base h).finite_toSet.countable _).inter
          (ih base _)

/-- One reveal preserves a linear probability inequality. -/
theorem linear_tower_step
    (p : κ → unitInterval) (h : Tr κ V) (z : V) (F : Finset κ)
    (hfresh : Disjoint F h.inspected) (c : ℝ)
    (B D : Tr κ V → Set (Set κ))
    (hBm : ∀ k, MeasurableSet (B k)) (hDm : ∀ k, MeasurableSet (D k))
    (hlin : ∀ ω : Set κ,
      c * (h.step z F ∅ true ω).prob p (B (h.step z F ∅ true ω)) ≤
        (h.step z F ∅ true ω).prob p (D (h.step z F ∅ true ω))) :
    c * h.prob p {ω | ω ∈ B (h.step z F ∅ true ω)} ≤
      h.prob p {ω | ω ∈ D (h.step z F ∅ true ω)} := by
  let lift : FRDom.Transcript κ V → Tr κ V := fun k =>
    { base := k, failed := h.failed }
  have hlift : ∀ ω : Set κ,
      lift (h.base.step z F true ω) = h.step z F ∅ true ω := by
    intro ω
    apply BDDom.Transcript.ext
    · apply FRDom.Transcript.ext <;>
        simp [lift, BDDom.Transcript.step, FRDom.Transcript.step]
    · simp [lift, BDDom.Transcript.step]
  have hlin' : ∀ ω : Set κ,
      c * (h.base.step z F true ω).prob p (B (lift (h.base.step z F true ω))) ≤
        (h.base.step z F true ω).prob p (D (lift (h.base.step z F true ω))) := by
    intro ω
    rw [hlift]
    exact hlin ω
  have ht := AdaptReg.RevealPhase.linear_tower_step p h.base z F hfresh c
    (fun k => B (lift k)) (fun k => D (lift k))
    (fun k => hBm (lift k)) (fun k => hDm (lift k)) hlin'
  change c * h.base.prob p {ω | ω ∈ B (h.step z F ∅ true ω)} ≤
    h.base.prob p {ω | ω ∈ D (h.step z F ∅ true ω)}
  simpa only [hlift] using ht

/-- Iterate the preceding one-reveal identity through the complete reveal tree. -/
theorem linear_tower_run
    (p : κ → unitInterval) (base h : Tr κ V) (hh : R.Phase base h) (c : ℝ)
    (B D : Tr κ V → Set (Set κ))
    (hBm : ∀ k, MeasurableSet (B k)) (hDm : ∀ k, MeasurableSet (D k))
    (hlin : ∀ k, R.Phase base k → c * k.prob p (B k) ≤ k.prob p (D k)) :
    ∀ n,
      c * h.prob p {ω | ω ∈ B (R.run base n h ω)} ≤
        h.prob p {ω | ω ∈ D (R.run base n h ω)} := by
  intro n
  induction n generalizing h with
  | zero => simpa using hlin h hh
  | succ n ih =>
      apply linear_tower_step p h (R.anchor base h) (R.region base h)
        (R.region_fresh base h hh) c
        (fun k => {ω | ω ∈ B (R.run base n k ω)})
        (fun k => {ω | ω ∈ D (R.run base n k ω)})
      · intro k
        exact measurableSet_setOf_run R (fun k ω => ω ∈ B k) hBm n base k
      · intro k
        exact measurableSet_setOf_run R (fun k ω => ω ∈ D k) hDm n base k
      · intro ω
        exact ih (R.reveal base h ω) (R.step_phase base h hh ω)

end RevealPhase

/-! ## The exact local soundness lemma -/

/-- `BDDom.Transcript.sound_step` asks additionally that every collateral vertex belong to the
finite arena.  That condition is not used by the invariant: the failed *centre* must be in the
arena, while a collateral neighbour may lie just outside it.  This exact variant records the
minimal hypotheses and is useful at the boundary of a finite exploration box. -/
theorem sound_step_of_local {κ V : Type*} [DecidableEq κ] [DecidableEq V]
    (h : Tr κ V) {G : SimpleGraph V} {A : Finset V} {o z : V}
    {F : Finset κ} {damage : Finset V} {b : Bool} {ω : Set κ}
    (hs : h.Sound G A o) (hzA : z ∈ A) (hzo : z ∉ h.openV)
    (hzc : z ∉ h.closedV)
    (hdlocal : ∀ v ∈ damage, z = v ∨ G.Adj z v)
    (hdopen : Disjoint damage h.openV) :
    (h.step z F damage b ω).Sound G A o := by
  cases b with
  | false =>
      refine ⟨hs.1, ?_, ?_, ?_⟩
      · rw [BDDom.Transcript.step_openV, BDDom.Transcript.step_closedV]
        simp only [Bool.false_eq_true, if_false]
        rw [Finset.disjoint_union_right]
        constructor
        · rw [Finset.disjoint_insert_right]
          exact ⟨hzo, hs.2.1⟩
        · exact hdopen.symm
      · intro x hx
        change x ∈ insert z h.failed at hx
        change x ∈ insert z h.closedV ∪ damage
        apply Finset.mem_union_left
        rw [Finset.mem_insert] at hx ⊢
        exact hx.imp_right (hs.2.2.1 ·)
      · intro v hv
        rw [BDDom.Transcript.step_closedV] at hv
        simp only [Bool.false_eq_true, if_false] at hv
        rcases Finset.mem_union.1 hv with hv | hv
        · rw [Finset.mem_insert] at hv
          rcases hv with hv | hv
          · exact ⟨v, by simp [hv], by simpa [hv] using hzA, Or.inl rfl⟩
          · obtain ⟨x, hxf, hxA, hxv⟩ := hs.2.2.2 v hv
            exact ⟨x, by simp [hxf], hxA, hxv⟩
        · exact ⟨z, by simp, hzA, hdlocal v hv⟩
  | true =>
      refine ⟨Finset.mem_insert_of_mem hs.1, ?_, ?_, ?_⟩
      · rw [BDDom.Transcript.step_openV, BDDom.Transcript.step_closedV]
        simp only [if_true]
        rw [Finset.disjoint_insert_left]
        exact ⟨hzc, hs.2.1⟩
      · change h.failed ⊆ h.closedV
        exact hs.2.2.1
      · simpa [BDDom.Transcript.step_failed, BDDom.Transcript.step_closedV] using hs.2.2.2

/-! ## Adaptive bounded-damage explorations -/

/-- An exploration with a finite reveal-only phase before every bounded-damage verdict.

The centre is selected from the pre-reveal transcript.  The final damage set may depend on the
complete reveal transcript, but no additional physical coordinate is read by the commit.  The
single Boolean verdict is therefore the only Bernoulli comparison coordinate consumed by this
macro transition. -/
structure Exploration (κ : Type*) [DecidableEq κ] {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) where
  density : κ → unitInterval
  Admissible : Tr κ V → Prop
  revealPhase : RevealPhase κ V
  next : Tr κ V → V
  damage : Tr κ V → Tr κ V → Finset V
  succ : Tr κ V → Tr κ V → Set (Set κ)
  succ_measurable : ∀ h k, MeasurableSet (succ h k)
  next_mem_boundary : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    next h ∈ h.boundary G A o
  succ_determinedBy : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    ∀ k, revealPhase.Phase h k →
    DeterminedBy (succ h k) (↑k.inspected : Set κ)
  commit_admissible : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    ∀ k, revealPhase.Phase h k → ∀ (b : Bool) (ω : Set κ),
      (b = true ↔ ω ∈ succ h k) →
        Admissible (k.step (next h) ∅ (damage h k) b ω)
  admissible_sound : ∀ h, Admissible h → h.Sound G A o

namespace Exploration

variable {κ V : Type*} [DecidableEq κ] [DecidableEq V]
  {G : SimpleGraph V} {A : Finset V} {o : V} {T : Set V}
  (E : Exploration κ G A o T)

/-- Transcript after the bounded reveal-only phase. -/
def revealed (h : Tr κ V) (ω : Set κ) : Tr κ V :=
  E.revealPhase.run h (E.revealPhase.rounds h) h ω

/-- The finite region actually read during the reveal phase. -/
def recordedRegion (h : Tr κ V) (ω : Set κ) : Finset κ :=
  E.revealPhase.recordedRegion h ω

theorem revealed_inspected (h : Tr κ V) (ω : Set κ) :
    (E.revealed h ω).inspected = h.inspected ∪ E.recordedRegion h ω :=
  E.revealPhase.inspected_final h ω

theorem recordedRegion_fresh (h : Tr κ V) (ω : Set κ) :
    Disjoint (E.recordedRegion h ω) h.inspected :=
  E.revealPhase.recordedRegion_fresh h ω

theorem revealed_phase (h : Tr κ V) (ω : Set κ) :
    E.revealPhase.Phase h (E.revealed h ω) :=
  E.revealPhase.phase_run (E.revealPhase.start h) _ _

theorem revealed_openV (h : Tr κ V) (ω : Set κ) :
    (E.revealed h ω).openV = h.openV :=
  E.revealPhase.openV_eq h _ (E.revealed_phase h ω)

theorem revealed_closedV (h : Tr κ V) (ω : Set κ) :
    (E.revealed h ω).closedV = h.closedV :=
  E.revealPhase.closedV_eq h _ (E.revealed_phase h ω)

theorem revealed_failed (h : Tr κ V) (ω : Set κ) :
    (E.revealed h ω).failed = h.failed :=
  E.revealPhase.failed_eq h _ (E.revealed_phase h ω)

/-- Reveal-only rounds preserve the bounded-damage soundness invariant. -/
theorem revealed_sound (h : Tr κ V) (ω : Set κ) (hs : h.Sound G A o) :
    (E.revealed h ω).Sound G A o := by
  unfold BDDom.Transcript.Sound at hs ⊢
  rw [E.revealed_openV h ω, E.revealed_closedV h ω, E.revealed_failed h ω]
  exact hs

/-- The stopped success event of one composite macro examination. -/
def success (h : Tr κ V) : Set (Set κ) :=
  {ω | ω ∈ E.succ h (E.revealed h ω)}

theorem success_measurable (h : Tr κ V) : MeasurableSet (E.success h) :=
  E.revealPhase.measurableSet_setOf_run
    (fun k ω => ω ∈ E.succ h k) (E.succ_measurable h)
    (E.revealPhase.rounds h) h h

open Classical in
/-- Verdict after the reveal phase. -/
def bit (h : Tr κ V) (ω : Set κ) : Bool := decide (ω ∈ E.success h)

theorem bit_eq_true_iff (h : Tr κ V) (ω : Set κ) :
    E.bit h ω = true ↔ ω ∈ E.success h := by simp [bit]

theorem bit_of_mem {h : Tr κ V} {ω : Set κ} (hω : ω ∈ E.success h) :
    E.bit h ω = true := (E.bit_eq_true_iff h ω).2 hω

theorem bit_of_notMem {h : Tr κ V} {ω : Set κ} (hω : ω ∉ E.success h) :
    E.bit h ω = false := by
  have := (E.bit_eq_true_iff h ω).not.2 hω
  simpa using this

/-- The unique macro commit.  Only its false branch uses `damage`; `Transcript.step` ignores that
argument on the true branch. -/
def commit (base k : Tr κ V) (b : Bool) : Tr κ V :=
  k.step (E.next base) ∅ (E.damage base k) b ∅

/-- Reveal, then commit one verdict. -/
def advance (h : Tr κ V) (ω : Set κ) : Tr κ V :=
  E.commit h (E.revealed h ω) (E.bit h ω)

theorem commit_eq_step (base k : Tr κ V) (b : Bool) (ω : Set κ) :
    E.commit base k b = k.step (E.next base) ∅ (E.damage base k) b ω := by
  unfold commit
  exact k.step_congr rfl fun x hx => absurd hx (Finset.notMem_empty x)

theorem commit_inspected (base k : Tr κ V) (b : Bool) :
    (E.commit base k b).inspected = k.inspected := by simp [commit]

theorem commit_state (base k : Tr κ V) (b : Bool) (x : κ) :
    (E.commit base k b).state x ↔ k.state x := by
  simp [commit, BDDom.Transcript.step_state]

/-- A commit consumes one comparison coordinate: independently of collateral damage, the set of
centres with determined trial verdict becomes the old set plus the selected centre. -/
theorem commit_trial_determined {base k : Tr κ V}
    (hk : E.revealPhase.Phase base k) (b : Bool) :
    (E.commit base k b).openV ∪ (E.commit base k b).failed =
      insert (E.next base) (base.openV ∪ base.failed) := by
  rw [commit, BDDom.Transcript.step_trial_determined,
    E.revealPhase.openV_eq base k hk, E.revealPhase.failed_eq base k hk]

/-- Exact local hypotheses under which the bounded-damage commit preserves `Sound`.  This lemma
is the reusable witness for `Exploration.commit_admissible` when admissibility consists of the
soundness invariant together with separate geometric data. -/
theorem commit_sound_of_local {base k : Tr κ V}
    (hk : E.revealPhase.Phase base k) (hs : base.Sound G A o)
    (hzA : E.next base ∈ A) (hzo : E.next base ∉ base.openV)
    (hzc : E.next base ∉ base.closedV)
    (hdlocal : ∀ v ∈ E.damage base k, E.next base = v ∨ G.Adj (E.next base) v)
    (hdopen : Disjoint (E.damage base k) base.openV) (b : Bool) :
    (E.commit base k b).Sound G A o := by
  have hs' : k.Sound G A o := by
    unfold BDDom.Transcript.Sound at hs ⊢
    rw [E.revealPhase.openV_eq base k hk,
      E.revealPhase.closedV_eq base k hk,
      E.revealPhase.failed_eq base k hk]
    exact hs
  apply sound_step_of_local k hs' hzA
    (by simpa [E.revealPhase.openV_eq base k hk] using hzo)
    (by simpa [E.revealPhase.closedV_eq base k hk] using hzc)
    hdlocal
  simpa [E.revealPhase.openV_eq base k hk] using hdopen

theorem advance_admissible {h : Tr κ V} (hadm : E.Admissible h)
    (hT : ¬ h.Terminal G A o T) (ω : Set κ) : E.Admissible (E.advance h ω) := by
  rw [advance, E.commit_eq_step _ _ _ ω]
  exact E.commit_admissible h hadm hT _ (E.revealed_phase h ω) _ ω
    (E.bit_eq_true_iff h ω)

/-- Every macro transition determines at least its centre.  Collateral closure can only decrease
the number of undetermined arena vertices further. -/
theorem undetermined_advance_lt {h : Tr κ V} (hadm : E.Admissible h)
    (hT : ¬ h.Terminal G A o T) (ω : Set κ) :
    (E.advance h ω).undetermined A < h.undetermined A := by
  obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
  rw [advance]
  have hu := (E.revealed h ω).undetermined_step_lt A hzA
    (by simpa [E.revealed_openV h ω] using hzo)
    (by simpa [E.revealed_closedV h ω] using hzc)
    (F := (∅ : Finset κ)) (damage := E.damage h (E.revealed h ω))
    (b := E.bit h ω) (ω := (∅ : Set κ))
  have hopen : (E.revealed h ω).base.openV = h.base.openV :=
    E.revealed_openV h ω
  have hclosed : (E.revealed h ω).base.closedV = h.base.closedV :=
    E.revealed_closedV h ω
  have hku : (E.revealed h ω).undetermined A = h.undetermined A := by
    unfold BDDom.Transcript.undetermined FRDom.Transcript.undetermined
    rw [hopen, hclosed]
  change (E.commit h (E.revealed h ω) (E.bit h ω)).undetermined A <
    (E.revealed h ω).undetermined A at hu
  rw [hku] at hu
  exact hu

open Classical in
/-- A terminally complete finite run. -/
def run : ℕ → Tr κ V → Set κ → Tr κ V
  | 0, h, _ => h
  | n + 1, h, ω =>
      if h.Terminal G A o T then h else run n (E.advance h ω) ω

@[simp] theorem run_zero (h : Tr κ V) (ω : Set κ) : E.run 0 h ω = h := rfl

theorem run_succ_of_terminal {h : Tr κ V} (hT : h.Terminal G A o T)
    (n : ℕ) (ω : Set κ) : E.run (n + 1) h ω = h := by simp [run, hT]

theorem run_succ_of_not_terminal {h : Tr κ V} (hT : ¬ h.Terminal G A o T)
    (n : ℕ) (ω : Set κ) : E.run (n + 1) h ω = E.run n (E.advance h ω) ω := by
  simp [run, hT]

theorem terminal_run :
    ∀ (n : ℕ) (h : Tr κ V), E.Admissible h → h.undetermined A ≤ n →
      ∀ ω : Set κ, (E.run n h ω).Terminal G A o T := by
  intro n
  induction n with
  | zero =>
      intro h _ hn ω
      rw [run_zero]
      exact h.base.terminal_of_undetermined_eq_zero G A o T (Nat.le_zero.1 hn)
  | succ n ih =>
      intro h hadm hn ω
      by_cases hT : h.Terminal G A o T
      · rw [E.run_succ_of_terminal hT]
        exact hT
      · rw [E.run_succ_of_not_terminal hT]
        refine ih _ (E.advance_admissible hadm hT ω) ?_ ω
        have hlt := E.undetermined_advance_lt hadm hT ω
        omega

/-! ### Measurability of the complete run -/

theorem setOf_run_succ_eq {h : Tr κ V} (hT : ¬ h.Terminal G A o T)
    (P : Tr κ V → Prop) (n : ℕ) :
    {ω : Set κ | P (E.run (n + 1) h ω)} =
      (E.success h ∩ {ω | P (E.run n (E.commit h (E.revealed h ω) true) ω)}) ∪
      ((E.success h)ᶜ ∩ {ω | P (E.run n (E.commit h (E.revealed h ω) false) ω)}) := by
  ext ω
  by_cases hω : ω ∈ E.success h
  · rw [Set.mem_setOf_eq, E.run_succ_of_not_terminal hT, advance, E.bit_of_mem hω]
    simp [hω]
  · rw [Set.mem_setOf_eq, E.run_succ_of_not_terminal hT, advance, E.bit_of_notMem hω]
    simp [hω]

theorem measurableSet_setOf_run (P : Tr κ V → Prop) :
    ∀ n h, MeasurableSet {ω : Set κ | P (E.run n h ω)} := by
  intro n
  induction n with
  | zero =>
      intro h
      simpa only [run_zero] using (MeasurableSet.const (α := Set κ) (P h))
  | succ n ih =>
      intro h
      by_cases hT : h.Terminal G A o T
      · have heq : {ω : Set κ | P (E.run (n + 1) h ω)} = {_ω : Set κ | P h} := by
          ext ω
          rw [Set.mem_setOf_eq, E.run_succ_of_terminal hT]
          rfl
        rw [heq]
        exact MeasurableSet.const _
      · have hbranch : ∀ b : Bool,
            MeasurableSet {ω : Set κ |
              P (E.run n (E.commit h (E.revealed h ω) b) ω)} := by
          intro b
          exact E.revealPhase.measurableSet_setOf_run
            (fun k ω => P (E.run n (E.commit h k b) ω))
            (fun k => ih (E.commit h k b)) (E.revealPhase.rounds h) h h
        rw [E.setOf_run_succ_eq hT P n]
        exact ((E.success_measurable h).inter (hbranch true)).union
          ((E.success_measurable h).compl.inter (hbranch false))

/-! ### Bounded-damage domination through the reveal tower -/

/-- The benchmark Bernoulli value of a commit is independent of all preceding reveal-only reads
and of the collateral damage set. -/
theorem commit_bern_eq {a : unitInterval} {base k : Tr κ V}
    (hk : E.revealPhase.Phase base k) (b : Bool) :
    (E.commit base k b).bern a G A o T =
      (base.step (E.next base) ∅ ∅ b ∅).bern a G A o T := by
  unfold commit BDDom.Transcript.bern
  rw [BDDom.Transcript.coe_step_trial_determined,
    BDDom.Transcript.coe_step_trial_determined,
    E.revealPhase.openV_eq base k hk,
    E.revealPhase.failed_eq base k hk]
  refine pinnedProb_congr_val _ _ (fun v _ => ?_) _
  have hopen : k.base.openV = base.base.openV :=
    E.revealPhase.openV_eq base k hk
  cases b <;> simp [BDDom.Transcript.step_openV, hopen]

/-- A commit reads no new physical coordinate. -/
theorem commit_prob (p : κ → unitInterval) (base k : Tr κ V) (b : Bool)
    (Y : Set (Set κ)) : (E.commit base k b).prob p Y = k.prob p Y := by
  rw [BDDom.Transcript.prob_eq, BDDom.Transcript.prob_eq, E.commit_inspected]
  exact pinnedProb_congr_val p _ (fun x hx => E.commit_state base k b x) _

/-- **Finite adaptive-reveal bounded-damage domination.**  One failed macro examination records
one failed centre in the comparison law, even when its final commit closes several neighboring
arena vertices. -/
theorem bern_le_prob_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : ℝ) ≤ h.prob E.density (E.success h)) :
    ∀ (n : ℕ) (h : Tr κ V), E.Admissible h → h.undetermined A ≤ n →
      h.bern a G A o T ≤
        h.prob E.density {ω | (E.run n h ω).Reaches G o T} := by
  intro n
  induction n with
  | zero =>
      intro h hadm hn
      have hT : h.Terminal G A o T :=
        h.base.terminal_of_undetermined_eq_zero G A o T (Nat.le_zero.1 hn)
      simpa only [run_zero] using
        h.bern_le_prob_of_terminal a E.density (E.admissible_sound h hadm) hT
  | succ n ih =>
      intro h hadm hn
      by_cases hT : h.Terminal G A o T
      · have heq : {ω : Set κ | (E.run (n + 1) h ω).Reaches G o T} =
            {_ω : Set κ | h.Reaches G o T} := by
          ext ω
          rw [Set.mem_setOf_eq, E.run_succ_of_terminal hT]
          rfl
        rw [heq]
        exact h.bern_le_prob_of_terminal a E.density (E.admissible_sound h hadm) hT
      · obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
        have hs := E.admissible_sound h hadm
        have hzf : E.next h ∉ h.failed := fun hzf => hzc (hs.2.2.1 hzf)
        have hund : ∀ k, E.revealPhase.Phase h k → ∀ b : Bool,
            (E.commit h k b).undetermined A ≤ n := by
          intro k hk b
          have hlt := k.undetermined_step_lt A hzA
            (by simpa [E.revealPhase.openV_eq h k hk] using hzo)
            (by simpa [E.revealPhase.closedV_eq h k hk] using hzc)
            (F := (∅ : Finset κ)) (damage := E.damage h k) (b := b) (ω := (∅ : Set κ))
          change (E.commit h k b).undetermined A < k.undetermined A at hlt
          have hku : k.undetermined A = h.undetermined A := by
            have hopen : k.base.openV = h.base.openV :=
              E.revealPhase.openV_eq h k hk
            have hclosed : k.base.closedV = h.base.closedV :=
              E.revealPhase.closedV_eq h k hk
            unfold BDDom.Transcript.undetermined FRDom.Transcript.undetermined
            rw [hopen, hclosed]
          rw [hku] at hlt
          omega
        let cT := (h.step (E.next h) ∅ ∅ true ∅).bern a G A o T
        let cF := (h.step (E.next h) ∅ ∅ false ∅).bern a G A o T
        let BT : Tr κ V → Set (Set κ) := fun k => E.succ h k
        let BF : Tr κ V → Set (Set κ) := fun k => (E.succ h k)ᶜ
        let DT : Tr κ V → Set (Set κ) := fun k =>
          BT k ∩ {ω | (E.run n (E.commit h k true) ω).Reaches G o T}
        let DF : Tr κ V → Set (Set κ) := fun k =>
          BF k ∩ {ω | (E.run n (E.commit h k false) ω).Reaches G o T}
        have hBTm : ∀ k, MeasurableSet (BT k) := fun k => E.succ_measurable h k
        have hBFm : ∀ k, MeasurableSet (BF k) := fun k => (E.succ_measurable h k).compl
        have hDTm : ∀ k, MeasurableSet (DT k) := fun k =>
          (hBTm k).inter (E.measurableSet_setOf_run (fun r => r.Reaches G o T) n _)
        have hDFm : ∀ k, MeasurableSet (DF k) := fun k =>
          (hBFm k).inter (E.measurableSet_setOf_run (fun r => r.Reaches G o T) n _)
        have hlinT : ∀ k, E.revealPhase.Phase h k →
            cT * k.prob E.density (BT k) ≤ k.prob E.density (DT k) := by
          intro k hk
          apply BDDom.Exploration.branch_linear E.density k cT
            (E.succ_determinedBy h hadm hT k hk)
            (E.measurableSet_setOf_run (fun r => r.Reaches G o T) n _)
          intro hmem
          let ω₀ : Set κ := substitute (↑k.inspected : Set κ) k.state ∅
          have hadm' : E.Admissible (E.commit h k true) := by
            rw [E.commit_eq_step h k true ω₀]
            exact E.commit_admissible h hadm hT k hk true ω₀ (by
              simpa [ω₀] using hmem)
          have hih := ih (E.commit h k true) hadm' (hund k hk true)
          rw [E.commit_bern_eq hk true, E.commit_prob E.density h k true] at hih
          exact hih
        have hlinF : ∀ k, E.revealPhase.Phase h k →
            cF * k.prob E.density (BF k) ≤ k.prob E.density (DF k) := by
          intro k hk
          apply BDDom.Exploration.branch_linear E.density k cF
            (determinedBy_compl (E.succ_determinedBy h hadm hT k hk))
            (E.measurableSet_setOf_run (fun r => r.Reaches G o T) n _)
          intro hmem
          let ω₀ : Set κ := substitute (↑k.inspected : Set κ) k.state ∅
          have hadm' : E.Admissible (E.commit h k false) := by
            rw [E.commit_eq_step h k false ω₀]
            exact E.commit_admissible h hadm hT k hk false ω₀ (by
              simp only [Bool.false_eq_true, false_iff]
              simpa [ω₀] using hmem)
          have hih := ih (E.commit h k false) hadm' (hund k hk false)
          rw [E.commit_bern_eq hk false, E.commit_prob E.density h k false] at hih
          exact hih
        have hkeyT := E.revealPhase.linear_tower_run E.density h h
          (E.revealPhase.start h) cT BT DT hBTm hDTm hlinT (E.revealPhase.rounds h)
        have hkeyF := E.revealPhase.linear_tower_run E.density h h
          (E.revealPhase.start h) cF BF DF hBFm hDFm hlinF (E.revealPhase.rounds h)
        have hq : (a : ℝ) ≤ h.prob E.density (E.success h) := hstep h hadm hT
        have hq1 : h.prob E.density (E.success h) ≤ 1 := h.prob_le_one _ _
        have hqc : h.prob E.density (E.success h)ᶜ =
            1 - h.prob E.density (E.success h) := by
          rw [BDDom.Transcript.prob_eq, BDDom.Transcript.prob_eq]
          exact pinnedProb_compl _ _ _ (E.success_measurable h)
        have hbern := h.bern_split a G A o T (F := (∅ : Finset κ)) hzo hzf
          (∅ : Finset V) (∅ : Finset V) (∅ : Set κ) (∅ : Set κ)
        have hmono := h.bern_step_false_le_true a G A o T (z := E.next h)
          (F := (∅ : Finset κ)) (∅ : Finset V) (∅ : Finset V)
          (∅ : Set κ) (∅ : Set κ)
        have hsplit : h.prob E.density {ω | (E.run (n + 1) h ω).Reaches G o T} =
            h.prob E.density
              (E.success h ∩ {ω |
                (E.run n (E.commit h (E.revealed h ω) true) ω).Reaches G o T}) +
            h.prob E.density
              ((E.success h)ᶜ ∩ {ω |
                (E.run n (E.commit h (E.revealed h ω) false) ω).Reaches G o T}) := by
          rw [BDDom.Transcript.prob_eq, BDDom.Transcript.prob_eq,
            BDDom.Transcript.prob_eq,
            E.setOf_run_succ_eq hT (fun r => r.Reaches G o T) n]
          refine pinnedProb_union _ _ _
            (Set.disjoint_left.2 fun ω hω hω' => hω'.1 hω.1) ?_
          exact (E.success_measurable h).compl.inter
            (E.revealPhase.measurableSet_setOf_run
              (fun k ω => (E.run n (E.commit h k false) ω).Reaches G o T)
              (fun k => E.measurableSet_setOf_run (fun r => r.Reaches G o T) n _)
              (E.revealPhase.rounds h) h h)
        change cT * h.prob E.density (E.success h) ≤ _ at hkeyT
        change cF * h.prob E.density (E.success h)ᶜ ≤ _ at hkeyF
        change _ ≤ h.prob E.density
          (E.success h ∩ {ω |
            (E.run n (E.commit h (E.revealed h ω) true) ω).Reaches G o T}) at hkeyT
        change _ ≤ h.prob E.density
          ((E.success h)ᶜ ∩ {ω |
            (E.run n (E.commit h (E.revealed h ω) false) ω).Reaches G o T}) at hkeyF
        rw [hqc] at hkeyF
        have hprod : (0 : ℝ) ≤
            (h.prob E.density (E.success h) - a) * (cT - cF) := by
          apply mul_nonneg
          · linarith
          · exact sub_nonneg.2 hmono
        rw [hbern, hsplit]
        dsimp only [cT, cF] at hkeyT hkeyF hprod ⊢
        nlinarith [hkeyT, hkeyF, hprod]

/-- Start-state form.  The root centre is accepted, no failed centre has been recorded, and no
physical coordinate has yet been read. -/
theorem pinnedProb_safeTargetConn_le_real_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : ℝ) ≤ h.prob E.density (E.success h))
    (h₀ : Tr κ V) (hadm : E.Admissible h₀) (hins : h₀.inspected = ∅)
    (hopen : h₀.openV = {o}) (hfailed : h₀.failed = ∅)
    (n : ℕ) (hn : h₀.undetermined A ≤ n) :
    pinnedProb (fun _ : V => a) {o} (fun _ => True) (BDDom.Safe.targetConn G A o T) ≤
      (prodBernoulli E.density).real {ω | (E.run n h₀ ω).Reaches G o T} := by
  have hmain := E.bern_le_prob_run hstep n h₀ hadm hn
  rw [BDDom.Transcript.prob_eq, hins, Finset.coe_empty, pinnedProb_empty] at hmain
  refine le_trans (le_of_eq ?_) hmain
  unfold BDDom.Transcript.bern
  have hopen' : h₀.base.openV = {o} := hopen
  rw [hopen', hfailed, Finset.union_empty, Finset.coe_singleton]
  refine pinnedProb_congr_val _ _ (fun v hv => ?_) _
  rw [Set.mem_singleton_iff] at hv
  simp [hv]

end Exploration

#print axioms KNAll.Site.BDAdaptReg.RevealPhase.linear_tower_step
#print axioms KNAll.Site.BDAdaptReg.RevealPhase.linear_tower_run
#print axioms KNAll.Site.BDAdaptReg.sound_step_of_local
#print axioms KNAll.Site.BDAdaptReg.Exploration.commit_trial_determined
#print axioms KNAll.Site.BDAdaptReg.Exploration.commit_sound_of_local
#print axioms KNAll.Site.BDAdaptReg.Exploration.terminal_run
#print axioms KNAll.Site.BDAdaptReg.Exploration.bern_le_prob_run
#print axioms KNAll.Site.BDAdaptReg.Exploration.pinnedProb_safeTargetConn_le_real_run

end KNAll.Site.BDAdaptReg

end
