import Hypergraph.StoppedLevel

/-!
# Finite adaptive reveal phases

`FRDom.Exploration.region h` is fixed before the next verdict is read.  This file gives the
minimal extension needed by a stopped, layer-by-layer examination: before each macro verdict we
run a *bounded* sequence of reveal-only transitions.  The set read by one transition is fixed by
the current transcript, but later sets may therefore depend on the states found earlier.  After
the bounded reveal phase there is exactly one commit, so terminal completeness is unchanged.

The point at which the old interface used configuration-independence is the averaging of the two
recursive branches in `FRDom.Exploration.bern_le_prob_run` (and the companion measurability
induction).  On an atom of the fixed set `region h`, `Transcript.step_congr` freezes the successor
transcript.  Here the same argument is iterated through a finite reveal tree.  The one-reveal
calculation is `Stopped.step_prob_eq_pinnedProb`; no conditional-probability denominator and no
stopping shortcut are introduced.
-/

noncomputable section

namespace KNAll.Site.AdaptReg

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

abbrev Tr (κ V : Type*) := FRDom.Transcript κ V

/-! ## Reveal-only phases -/

/-- A bounded reveal phase attached to a macro exploration.

`Phase base current` is deliberately separate from macro admissibility: the intermediate
reveal-only transcripts need not already satisfy the invariant required after the final commit.
The anchor is occupied, so `step anchor F true` changes only the inspected-site part of the
transcript. -/
structure RevealPhase (κ V : Type*) [DecidableEq κ] [DecidableEq V] where
  Phase : Tr κ V → Tr κ V → Prop
  rounds : Tr κ V → ℕ
  anchor : Tr κ V → Tr κ V → V
  region : Tr κ V → Tr κ V → Finset κ
  start : ∀ h, Phase h h
  openV_eq : ∀ h k, Phase h k → k.openV = h.openV
  closedV_eq : ∀ h k, Phase h k → k.closedV = h.closedV
  anchor_open : ∀ h k, Phase h k → anchor h k ∈ k.openV
  region_fresh : ∀ h k, Phase h k → Disjoint (region h k) k.inspected
  step_phase : ∀ h k, Phase h k → ∀ ω : Set κ,
    Phase h (k.step (anchor h k) (region h k) true ω)

namespace RevealPhase

variable {κ V : Type*} [DecidableEq κ] [DecidableEq V] (R : RevealPhase κ V)

/-- One reveal-only transition. -/
def reveal (R : RevealPhase κ V) (base h : Tr κ V) (ω : Set κ) : Tr κ V :=
  h.step (R.anchor base h) (R.region base h) true ω

/-- A bounded reveal phase.  It always performs the prescribed number of substeps; an
implementation which has stopped chooses the empty region on its remaining substeps. -/
def run (R : RevealPhase κ V) (base : Tr κ V) : ℕ → Tr κ V → Set κ → Tr κ V
  | 0, h, _ => h
  | n + 1, h, ω => run R base n (R.reveal base h ω) ω

@[simp] theorem run_zero (base h : Tr κ V) (ω : Set κ) : run R base 0 h ω = h := rfl

@[simp] theorem run_succ (base h : Tr κ V) (n : ℕ) (ω : Set κ) :
    run R base (n + 1) h ω = run R base n (R.reveal base h ω) ω := rfl

theorem phase_run {base h : Tr κ V} (hh : R.Phase base h) :
    ∀ n ω, R.Phase base (run R base n h ω) := by
  revert h
  intro h hh n
  induction n generalizing h with
  | zero => intro ω; simpa using hh
  | succ n ih =>
      intro ω
      exact ih (R.step_phase base h hh ω) ω

/-- A reveal does not commit a macro vertex. -/
theorem reveal_openV {base h : Tr κ V} (hh : R.Phase base h) (ω : Set κ) :
    (R.reveal base h ω).openV = h.openV := by
  simp [reveal, Finset.insert_eq_of_mem (R.anchor_open base h hh)]

theorem reveal_closedV (base h : Tr κ V) (ω : Set κ) :
    (R.reveal base h ω).closedV = h.closedV := by
  simp [reveal]

theorem run_openV {base h : Tr κ V} (hh : R.Phase base h) :
    ∀ n ω, (run R base n h ω).openV = h.openV := by
  revert h
  intro h hh n
  induction n generalizing h with
  | zero => intro ω; rfl
  | succ n ih =>
      intro ω
      calc
        (run R base (n + 1) h ω).openV
            = (R.reveal base h ω).openV := ih (R.step_phase base h hh ω) ω
        _ = h.openV := R.reveal_openV hh ω

theorem run_closedV {base h : Tr κ V} (hh : R.Phase base h) :
    ∀ n ω, (run R base n h ω).closedV = h.closedV := by
  revert h
  intro h hh n
  induction n generalizing h with
  | zero => intro ω; rfl
  | succ n ih =>
      intro ω
      calc
        (run R base (n + 1) h ω).closedV
            = (R.reveal base h ω).closedV := ih (R.step_phase base h hh ω) ω
        _ = h.closedV := R.reveal_closedV base h ω

/-- The actually recorded region.  Unlike `FRDom.Exploration.region`, this may depend on `ω`. -/
def recordedRegion (R : RevealPhase κ V) (base : Tr κ V) (ω : Set κ) : Finset κ :=
  (run R base (R.rounds base) base ω).inspected \ base.inspected

theorem recordedRegion_fresh (base : Tr κ V) (ω : Set κ) :
    Disjoint (recordedRegion R base ω) base.inspected := Finset.sdiff_disjoint

theorem inspected_mono {base h : Tr κ V} :
    ∀ n ω, h.inspected ⊆ (run R base n h ω).inspected := by
  revert h
  intro h n
  induction n generalizing h with
  | zero => intro ω; exact Finset.Subset.rfl
  | succ n ih =>
      intro ω
      exact Finset.Subset.trans (by simp [reveal]) (ih (h := R.reveal base h ω) ω)

theorem inspected_final (base : Tr κ V) (ω : Set κ) :
    (run R base (R.rounds base) base ω).inspected
      = base.inspected ∪ recordedRegion R base ω := by
  symm
  exact Finset.union_sdiff_of_subset
    (inspected_mono R (base := base) (h := base) (R.rounds base) ω)

/-! ### Measurability and the one-reveal linear tower calculation -/

/-- A predicate read after a bounded adaptive reveal remains measurable. -/
theorem measurableSet_setOf_run
    (P : Tr κ V → Set κ → Prop)
    (hP : ∀ h, MeasurableSet {ω : Set κ | P h ω}) :
    ∀ n base h, MeasurableSet {ω : Set κ | P (run R base n h ω) ω} := by
  intro n
  induction n with
  | zero => intro base h; simpa using hP h
  | succ n ih =>
      intro base h
      rw [show {ω : Set κ | P (run R base (n + 1) h ω) ω} =
          {ω : Set κ | P (run R base n
            (h.step (R.anchor base h) (R.region base h) true ω) ω) ω} by rfl]
      rw [h.setOf_step_eq_biUnion
        (fun h' ω => P (run R base n h' ω) ω)]
      exact Finset.measurableSet_biUnion _ fun σ _ =>
        (measurableSet_localCylinder (R.region base h).finite_toSet.countable _).inter
          (ih base _)

/-- One reveal preserves a linear probability inequality.  This is the atom-by-atom tower
calculation needed to iterate reveal-only substeps. -/
theorem linear_tower_step
    (p : κ → unitInterval) (h : Tr κ V) (z : V) (F : Finset κ)
    (hfresh : Disjoint F h.inspected) (c : ℝ)
    (B D : Tr κ V → Set (Set κ))
    (hBm : ∀ k, MeasurableSet (B k)) (hDm : ∀ k, MeasurableSet (D k))
    (hlin : ∀ ω : Set κ,
      c * (h.step z F true ω).prob p (B (h.step z F true ω)) ≤
        (h.step z F true ω).prob p (D (h.step z F true ω))) :
    c * h.prob p {ω | ω ∈ B (h.step z F true ω)} ≤
      h.prob p {ω | ω ∈ D (h.step z F true ω)} := by
  classical
  let X : Set (Set κ) := {ω | ω ∈ B (h.step z F true ω)}
  let Y : Set (Set κ) := {ω | ω ∈ D (h.step z F true ω)}
  have hXm : MeasurableSet X := by
    unfold X
    rw [h.setOf_step_eq_biUnion (fun k ω => ω ∈ B k)]
    exact Finset.measurableSet_biUnion _ fun σ _ =>
      (measurableSet_localCylinder F.finite_toSet.countable _).inter (hBm _)
  have hYm : MeasurableSet Y := by
    unfold Y
    rw [h.setOf_step_eq_biUnion (fun k ω => ω ∈ D k)]
    exact Finset.measurableSet_biUnion _ fun σ _ =>
      (measurableSet_localCylinder F.finite_toSet.countable _).inter (hDm _)
  rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq, pinnedProb, pinnedProb,
    TargetExt.real_eq_sum_inter_localCylinder p F
      ((measurable_substitute _ _) hXm),
    TargetExt.real_eq_sum_inter_localCylinder p F
      ((measurable_substitute _ _) hYm), Finset.mul_sum]
  refine Finset.sum_le_sum fun S hSF => ?_
  have hSF' : S ⊆ F := Finset.mem_powerset.1 hSF
  let ωS : Set κ := (↑S : Set κ)
  let k := h.step z F true ωS
  have hfreeze : ∀ ξ ∈ localCylinder (↑F : Set κ) ωS,
      h.step z F true (substitute (↑h.inspected : Set κ) h.state ξ) = k := by
    intro ξ hξ
    apply h.step_congr
    intro x hx
    have hxI : x ∉ (↑h.inspected : Set κ) := fun hxI =>
      Finset.disjoint_left.1 hfresh hx (Finset.mem_coe.1 hxI)
    rw [mem_substitute_of_notMem _ hxI]
    exact hξ x (Finset.mem_coe.2 hx)
  have hXeq :
      (substitute (↑h.inspected : Set κ) h.state ⁻¹' X) ∩
          localCylinder (↑F : Set κ) ωS =
        (substitute (↑h.inspected : Set κ) h.state ⁻¹' B k) ∩
          localCylinder (↑F : Set κ) ωS := by
    ext ξ
    simp only [Set.mem_inter_iff, Set.mem_preimage, X, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hξ, hcyl⟩
      exact ⟨hfreeze ξ hcyl ▸ hξ, hcyl⟩
    · rintro ⟨hξ, hcyl⟩
      exact ⟨hfreeze ξ hcyl ▸ hξ, hcyl⟩
  have hYeq :
      (substitute (↑h.inspected : Set κ) h.state ⁻¹' Y) ∩
          localCylinder (↑F : Set κ) ωS =
        (substitute (↑h.inspected : Set κ) h.state ⁻¹' D k) ∩
          localCylinder (↑F : Set κ) ωS := by
    ext ξ
    simp only [Set.mem_inter_iff, Set.mem_preimage, Y, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hξ, hcyl⟩
      exact ⟨hfreeze ξ hcyl ▸ hξ, hcyl⟩
    · rintro ⟨hξ, hcyl⟩
      exact ⟨hfreeze ξ hcyl ▸ hξ, hcyl⟩
  rw [hXeq, hYeq,
    TargetExt.real_inter_localCylinder_eq_mul_pinnedProb p F ωS
      ((measurable_substitute _ _) (hBm k)),
    TargetExt.real_inter_localCylinder_eq_mul_pinnedProb p F ωS
      ((measurable_substitute _ _) (hDm k)),
    ← Stopped.step_prob_eq_pinnedProb h p z F true ωS (B k) hfresh,
    ← Stopped.step_prob_eq_pinnedProb h p z F true ωS (D k) hfresh]
  have h0 : 0 ≤ (prodBernoulli p).real (localCylinder (↑F : Set κ) ωS) :=
    measureReal_nonneg
  have hk := hlin ωS
  dsimp only [k] at hk ⊢
  nlinarith

/-- Iteration of `linear_tower_step` through the whole finite reveal tree. -/
theorem linear_tower_run
    (p : κ → unitInterval) (base h : Tr κ V) (hh : R.Phase base h) (c : ℝ)
    (B D : Tr κ V → Set (Set κ))
    (hBm : ∀ k, MeasurableSet (B k)) (hDm : ∀ k, MeasurableSet (D k))
    (hlin : ∀ k, R.Phase base k →
      c * k.prob p (B k) ≤ k.prob p (D k)) :
    ∀ n,
      c * h.prob p {ω | ω ∈ B (run R base n h ω)} ≤
        h.prob p {ω | ω ∈ D (run R base n h ω)} := by
  intro n
  induction n generalizing h with
  | zero => simpa using hlin h hh
  | succ n ih =>
      apply linear_tower_step p h (R.anchor base h) (R.region base h)
        (R.region_fresh base h hh) c
        (fun k => {ω | ω ∈ B (run R base n k ω)})
        (fun k => {ω | ω ∈ D (run R base n k ω)})
      · intro k
        exact measurableSet_setOf_run R (fun k ω => ω ∈ B k) hBm n base k
      · intro k
        exact measurableSet_setOf_run R (fun k ω => ω ∈ D k) hDm n base k
      · intro ω
        exact ih (R.reveal base h ω) (R.step_phase base h hh ω)

end RevealPhase

/-! ## Adaptive-region explorations -/

/-- An exploration with a finite reveal-only phase before every macro verdict.

The macro vertex `next h` is chosen before the reveal phase.  Each substep reads the region chosen
from the current reveal transcript, and the final success event is determined by the sites then
recorded.  Only the final `commit` changes `openV` or `closedV`. -/
structure Exploration (κ : Type*) [DecidableEq κ] {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) where
  density : κ → unitInterval
  Admissible : Tr κ V → Prop
  revealPhase : RevealPhase κ V
  next : Tr κ V → V
  succ : Tr κ V → Tr κ V → Set (Set κ)
  succ_measurable : ∀ h k, MeasurableSet (succ h k)
  next_mem_boundary : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    next h ∈ h.boundary G A o
  succ_determinedBy : ∀ h k, revealPhase.Phase h k →
    DeterminedBy (succ h k) (↑k.inspected : Set κ)
  commit_admissible : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    ∀ k, revealPhase.Phase h k → ∀ (b : Bool) (ω : Set κ),
      (b = true ↔ ω ∈ succ h k) →
        Admissible (k.step (next h) ∅ b ω)

namespace Exploration

variable {κ V : Type*} [DecidableEq κ] [DecidableEq V]
  {G : SimpleGraph V} {A : Finset V} {o : V} {T : Set V}
  (E : Exploration κ G A o T)

/-- The transcript at the end of the bounded reveal-only phase. -/
def revealed (h : Tr κ V) (ω : Set κ) : Tr κ V :=
  E.revealPhase.run h (E.revealPhase.rounds h) h ω

/-- The configuration-dependent finite region actually recorded by the reveal phase. -/
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

/-- The success event of the composite macro examination. -/
def success (h : Tr κ V) : Set (Set κ) :=
  {ω | ω ∈ E.succ h (E.revealed h ω)}

theorem success_measurable (h : Tr κ V) : MeasurableSet (E.success h) :=
  E.revealPhase.measurableSet_setOf_run
    (fun k ω => ω ∈ E.succ h k) (E.succ_measurable h)
    (E.revealPhase.rounds h) h h

open Classical in
/-- The verdict read after all reveal-only substeps. -/
def bit (h : Tr κ V) (ω : Set κ) : Bool := decide (ω ∈ E.success h)

theorem bit_eq_true_iff (h : Tr κ V) (ω : Set κ) :
    E.bit h ω = true ↔ ω ∈ E.success h := by
  simp [bit]

theorem bit_of_mem {h : Tr κ V} {ω : Set κ} (hω : ω ∈ E.success h) :
    E.bit h ω = true := (E.bit_eq_true_iff h ω).2 hω

theorem bit_of_notMem {h : Tr κ V} {ω : Set κ} (hω : ω ∉ E.success h) :
    E.bit h ω = false := by
  have := (E.bit_eq_true_iff h ω).not.2 hω
  simpa using this

/-- The unique commit following the reveal phase. -/
def commit (base k : Tr κ V) (b : Bool) : Tr κ V :=
  k.step (E.next base) ∅ b ∅

/-- One complete macro transition: bounded reveals, then exactly one commit. -/
def advance (h : Tr κ V) (ω : Set κ) : Tr κ V :=
  E.commit h (E.revealed h ω) (E.bit h ω)

theorem commit_eq_step (base k : Tr κ V) (b : Bool) (ω : Set κ) :
    E.commit base k b = k.step (E.next base) ∅ b ω := by
  unfold commit
  exact k.step_congr fun x hx => absurd hx (Finset.notMem_empty x)

theorem commit_inspected (base k : Tr κ V) (b : Bool) :
    (E.commit base k b).inspected = k.inspected := by simp [commit]

theorem commit_state (base k : Tr κ V) (b : Bool) (x : κ) :
    (E.commit base k b).state x ↔ k.state x := by
  simp [commit, FRDom.Transcript.step_state]

theorem advance_admissible {h : Tr κ V} (hadm : E.Admissible h)
    (hT : ¬ h.Terminal G A o T) (ω : Set κ) : E.Admissible (E.advance h ω) := by
  rw [advance, E.commit_eq_step _ _ _ ω]
  exact E.commit_admissible h hadm hT _ (E.revealed_phase h ω) _ ω
    (E.bit_eq_true_iff h ω)

/-- A macro transition determines one new arena vertex.  Reveal-only substeps do not contribute
to the count. -/
theorem undetermined_advance {h : Tr κ V} (hadm : E.Admissible h)
    (hT : ¬ h.Terminal G A o T) (ω : Set κ) :
    (E.advance h ω).undetermined A + 1 = h.undetermined A := by
  obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
  rw [advance]
  have hu := (E.revealed h ω).undetermined_step
    (F := (∅ : Finset κ)) (b := E.bit h ω) (ω := (∅ : Set κ)) hzA
    (by simpa [E.revealed_openV h ω] using hzo)
    (by simpa [E.revealed_closedV h ω] using hzc)
  simpa [commit, FRDom.Transcript.undetermined,
    E.revealed_openV h ω, E.revealed_closedV h ω] using hu

open Classical in
/-- Terminal completeness is still controlled solely by `Transcript.Terminal`; neither the
reveal phase nor the exploration may stop the macro run early. -/
def run (E : Exploration κ G A o T) : ℕ → Tr κ V → Set κ → Tr κ V
  | 0, h, _ => h
  | n + 1, h, ω =>
      if h.Terminal G A o T then h else run E n (E.advance h ω) ω

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
      exact h.terminal_of_undetermined_eq_zero G A o T (Nat.le_zero.1 hn)
  | succ n ih =>
      intro h hadm hn ω
      by_cases hT : h.Terminal G A o T
      · rw [E.run_succ_of_terminal hT]
        exact hT
      · rw [E.run_succ_of_not_terminal hT]
        refine ih _ (E.advance_admissible hadm hT ω) ?_ ω
        have := E.undetermined_advance hadm hT ω
        omega

/-! ### Measurability of the complete macro run -/

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

/-! ### Domination -/

theorem commit_bern_eq {a : unitInterval} {base k : Tr κ V}
    (hk : E.revealPhase.Phase base k) (b : Bool) :
    (E.commit base k b).bern a G A o T =
      (base.step (E.next base) ∅ b ∅).bern a G A o T := by
  unfold commit FRDom.Transcript.bern
  simp only [FRDom.Transcript.step_openV, FRDom.Transcript.step_closedV]
  rw [E.revealPhase.openV_eq base k hk, E.revealPhase.closedV_eq base k hk]

/-- Committing a verdict without reading another site does not change the pinned law. -/
theorem commit_prob (p : κ → unitInterval) (base k : Tr κ V) (b : Bool)
    (Y : Set (Set κ)) : (E.commit base k b).prob p Y = k.prob p Y := by
  rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq, E.commit_inspected]
  exact pinnedProb_congr_val p _ (fun x hx => E.commit_state base k b x) _

/-- If `B` is already decided by a transcript, a continuation bound needed only when `B` holds
multiplies by the probability of `B`.  This is the empty-reveal case of the same atomwise tower
calculus used above. -/
theorem branch_linear (p : κ → unitInterval) (k : Tr κ V) (c : ℝ)
    {B Y : Set (Set κ)} (hBdet : DeterminedBy B (↑k.inspected : Set κ))
    (hYm : MeasurableSet Y)
    (hc : substitute (↑k.inspected : Set κ) k.state ∅ ∈ B → c ≤ k.prob p Y) :
    c * k.prob p B ≤ k.prob p (B ∩ Y) := by
  have hBm : MeasurableSet B := hBdet.measurableSet_of_finset
  rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq]
  refine FRDom.le_pinnedProb_inter_of_forall_extend_of_mem p hBm hYm
    (∅ : Finset κ) (↑k.inspected : Set κ) (by simp) k.state (by simpa using hBdet) ?_
  intro val' hval' hmem
  let ω₀ : Set κ := substitute (↑k.inspected : Set κ) val' ∅
  have hω₀B : ω₀ ∈ B := by simpa [ω₀] using hmem
  have hcan : substitute (↑k.inspected : Set κ) k.state ∅ ∈ B := by
    refine ((determinedBy_iff B (↑k.inspected : Set κ)).1 hBdet ω₀
      (substitute (↑k.inspected : Set κ) k.state ∅) ?_).1 hω₀B
    ext x
    simp only [Set.mem_inter_iff]
    by_cases hx : x ∈ (↑k.inspected : Set κ)
    · rw [mem_substitute_of_mem _ hx, mem_substitute_of_mem _ hx]
      exact and_congr (hval' x hx) Iff.rfl
    · simp [hx]
  refine (hc hcan).trans_eq ?_
  rw [FRDom.Transcript.prob_eq, Finset.coe_empty, Set.union_empty]
  exact pinnedProb_congr_val p _ (fun x hx => (hval' x hx).symm) _

/-- **Finite adaptive-region domination.**  A bounded adaptive reveal phase followed by one
commit satisfies the same Bernoulli domination theorem as `FRDom.Exploration`. -/
theorem bern_le_prob_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : ℝ) ≤ h.prob E.density (E.success h)) :
    ∀ (n : ℕ) (h : Tr κ V), E.Admissible h → h.undetermined A ≤ n →
      h.bern a G A o T ≤ h.prob E.density {ω | (E.run n h ω).Reaches G o T} := by
  intro n
  induction n with
  | zero =>
      intro h _ hn
      have hT : h.Terminal G A o T :=
        h.terminal_of_undetermined_eq_zero G A o T (Nat.le_zero.1 hn)
      simpa only [run_zero] using h.bern_le_prob_of_terminal a G A o T E.density hT
  | succ n ih =>
      intro h hadm hn
      by_cases hT : h.Terminal G A o T
      · have heq : {ω : Set κ | (E.run (n + 1) h ω).Reaches G o T} =
            {_ω : Set κ | h.Reaches G o T} := by
          ext ω
          rw [Set.mem_setOf_eq, E.run_succ_of_terminal hT]
          rfl
        rw [heq]
        exact h.bern_le_prob_of_terminal a G A o T E.density hT
      · obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
        have hund : ∀ k, E.revealPhase.Phase h k → ∀ b : Bool,
            (E.commit h k b).undetermined A ≤ n := by
          intro k hk b
          have hu := k.undetermined_step (F := (∅ : Finset κ)) (b := b)
            (ω := (∅ : Set κ)) hzA
            (by simpa [E.revealPhase.openV_eq h k hk] using hzo)
            (by simpa [E.revealPhase.closedV_eq h k hk] using hzc)
          have hku : k.undetermined A = h.undetermined A := by
            unfold FRDom.Transcript.undetermined
            rw [E.revealPhase.openV_eq h k hk, E.revealPhase.closedV_eq h k hk]
          have hu' : (E.commit h k b).undetermined A + 1 = k.undetermined A := by
            change (k.step (E.next h) ∅ b ∅).undetermined A + 1 = k.undetermined A
            exact hu
          rw [hku] at hu'
          omega
        let cT := (h.step (E.next h) ∅ true ∅).bern a G A o T
        let cF := (h.step (E.next h) ∅ false ∅).bern a G A o T
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
          apply branch_linear E.density k cT (E.succ_determinedBy h k hk)
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
          apply branch_linear E.density k cF
            (determinedBy_compl (E.succ_determinedBy h k hk))
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
          rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq]
          exact pinnedProb_compl _ _ _ (E.success_measurable h)
        have hbern := h.bern_split a G A o T (F := (∅ : Finset κ)) hzo hzc
          (∅ : Set κ) (∅ : Set κ)
        have hmono := h.bern_step_false_le_true a G A o T (z := E.next h)
          (F := (∅ : Finset κ)) (∅ : Set κ) (∅ : Set κ)
        have hsplit : h.prob E.density {ω | (E.run (n + 1) h ω).Reaches G o T} =
            h.prob E.density
              (E.success h ∩ {ω | (E.run n (E.commit h (E.revealed h ω) true) ω).Reaches G o T}) +
            h.prob E.density
              ((E.success h)ᶜ ∩ {ω | (E.run n (E.commit h (E.revealed h ω) false) ω).Reaches G o T}) := by
          rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq,
            FRDom.Transcript.prob_eq,
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
          (E.success h ∩ {ω | (E.run n (E.commit h (E.revealed h ω) true) ω).Reaches G o T})
          at hkeyT
        change _ ≤ h.prob E.density
          ((E.success h)ᶜ ∩ {ω | (E.run n (E.commit h (E.revealed h ω) false) ω).Reaches G o T})
          at hkeyF
        rw [hqc] at hkeyF
        have hprod : (0 : ℝ) ≤ (h.prob E.density (E.success h) - a) * (cT - cF) := by
          apply mul_nonneg
          · linarith
          · exact sub_nonneg.2 hmono
        rw [hbern, hsplit]
        dsimp only [cT, cF] at hkeyT hkeyF hprod ⊢
        nlinarith [hkeyT, hkeyF, hprod]

end Exploration

/-! ## The contract consumed by `MacroExp.StepBound` -/

/-- A configuration-dependent stopped success event implies the existing `MacroExp.StepBound`
contract as soon as it is contained in `MacroExp.succ`.  Thus downstream code need not change its
interface: the adaptive exploration supplies the probability estimate, and monotonicity forgets
how much of the finite reveal tree was actually recorded. -/
theorem macroStepBound_of_adaptive_success {d r t : ℕ} [NeZero d]
    (q a : unitInterval) (δ : ℝ) (hδ0 : 0 < δ)
    (hδa : δ ≤ (1 - (a : ℝ)) / 4) (hδhalf : δ ≤ 1 / 2)
    (hstart : MacroExp.Good d r t (MacroExp.start d r t) q δ)
    (S : ℕ → MacroExp.Tr d → Set (Set (Site d)))
    (hprob : ∀ n h, MacroExp.Good d r t h q δ →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      (a : ℝ) ≤ h.prob (fun _ : Site d => q) (S n h))
    (hsub : ∀ n h, MacroExp.Good d r t h q δ →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      S n h ⊆ MacroExp.succ d r t n q δ h) :
    MacroExp.StepBound d r t q a := by
  refine ⟨δ, hδ0, hδa, hδhalf, hstart, ?_⟩
  intro n h hg hT
  exact (hprob n h hg hT).trans
    (ProbInv.prob_mono h (fun _ : Site d => q) (hsub n h hg hT))

/-- The preceding adapter specialized to success events produced by adaptive-region
explorations.  This is the literal interface handoff to `MacroExp.StepBound`. -/
theorem macroStepBound_of_explorations {d r t : ℕ} [NeZero d]
    (q a : unitInterval) (δ : ℝ) (hδ0 : 0 < δ)
    (hδa : δ ≤ (1 - (a : ℝ)) / 4) (hδhalf : δ ≤ 1 / 2)
    (hstart : MacroExp.Good d r t (MacroExp.start d r t) q δ)
    (E : ∀ n, Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hprob : ∀ n h, MacroExp.Good d r t h q δ →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      (a : ℝ) ≤ h.prob (fun _ : Site d => q) ((E n).success h))
    (hsub : ∀ n h, MacroExp.Good d r t h q δ →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      (E n).success h ⊆ MacroExp.succ d r t n q δ h) :
    MacroExp.StepBound d r t q a :=
  macroStepBound_of_adaptive_success q a δ hδ0 hδa hδhalf hstart
    (fun n h => (E n).success h) hprob hsub

#print axioms KNAll.Site.AdaptReg.RevealPhase.linear_tower_step
#print axioms KNAll.Site.AdaptReg.RevealPhase.linear_tower_run
#print axioms KNAll.Site.AdaptReg.Exploration.bern_le_prob_run
#print axioms KNAll.Site.AdaptReg.macroStepBound_of_adaptive_success
#print axioms KNAll.Site.AdaptReg.macroStepBound_of_explorations

end KNAll.Site.AdaptReg

end
