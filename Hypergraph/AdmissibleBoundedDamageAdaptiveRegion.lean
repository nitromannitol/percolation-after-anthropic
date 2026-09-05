import Hypergraph.BoundedDamageAdaptiveRegion

/-!
# Admissibility-indexed adaptive reveals with bounded damage

`AdaptReg.RevealPhase` and `BDAdaptReg.RevealPhase` require an open reveal anchor at every
transcript, including the empty-open transcript, and are therefore uninhabited.  This module gives
the corrected interface.  A reveal phase starts only from an admissible transcript.  All later
phase states are descendants of that genuine start, so the anchor obligation remains exactly what
the finite tower needs.

The domination proof is repeated from the finite definitions.  It does not transport the theorem
for the inconsistent global interface.
-/

noncomputable section

namespace KNAll.Site.ABDAdaptReg

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

abbrev Tr (kappa V : Type*) := BDDom.Transcript kappa V

/-! ## Corrected reveal-only phases -/

/-- A reveal phase whose initial state is required only for an explicitly admissible transcript. -/
structure RevealPhase (kappa V : Type*) [DecidableEq kappa] [DecidableEq V]
    (Admissible : Tr kappa V → Prop) where
  Phase : Tr kappa V → Tr kappa V → Prop
  rounds : Tr kappa V → Nat
  anchor : Tr kappa V → Tr kappa V → V
  region : Tr kappa V → Tr kappa V → Finset kappa
  start : ∀ h, Admissible h → Phase h h
  openV_eq : ∀ h k, Phase h k → k.openV = h.openV
  closedV_eq : ∀ h k, Phase h k → k.closedV = h.closedV
  failed_eq : ∀ h k, Phase h k → k.failed = h.failed
  anchor_open : ∀ h k, Phase h k → anchor h k ∈ k.openV
  region_fresh : ∀ h k, Phase h k → Disjoint (region h k) k.inspected
  step_phase : ∀ h k, Phase h k → ∀ omega : Set kappa,
    Phase h (k.step (anchor h k) (region h k) ∅ true omega)

namespace RevealPhase

variable {kappa V : Type*} [DecidableEq kappa] [DecidableEq V]
  {Admissible : Tr kappa V → Prop} (R : RevealPhase kappa V Admissible)

def reveal (base h : Tr kappa V) (omega : Set kappa) : Tr kappa V :=
  h.step (R.anchor base h) (R.region base h) ∅ true omega

def run (base : Tr kappa V) : Nat → Tr kappa V → Set kappa → Tr kappa V
  | 0, h, _ => h
  | n + 1, h, omega => run base n (R.reveal base h omega) omega

@[simp] theorem run_zero (base h : Tr kappa V) (omega : Set kappa) :
    R.run base 0 h omega = h := rfl

@[simp] theorem run_succ (base h : Tr kappa V) (n : Nat) (omega : Set kappa) :
    R.run base (n + 1) h omega = R.run base n (R.reveal base h omega) omega := rfl

theorem phase_run {base h : Tr kappa V} (hh : R.Phase base h) :
    ∀ n omega, R.Phase base (R.run base n h omega) := by
  intro n
  induction n generalizing h with
  | zero => intro omega; simpa using hh
  | succ n ih =>
      intro omega
      exact ih (R.step_phase base h hh omega) omega

theorem reveal_openV {base h : Tr kappa V} (hh : R.Phase base h) (omega : Set kappa) :
    (R.reveal base h omega).openV = h.openV := by
  simp [reveal, Finset.insert_eq_of_mem (R.anchor_open base h hh)]

theorem reveal_closedV (base h : Tr kappa V) (omega : Set kappa) :
    (R.reveal base h omega).closedV = h.closedV := by simp [reveal]

theorem reveal_failed (base h : Tr kappa V) (omega : Set kappa) :
    (R.reveal base h omega).failed = h.failed := by simp [reveal]

theorem run_openV {base h : Tr kappa V} (hh : R.Phase base h) :
    ∀ n omega, (R.run base n h omega).openV = h.openV := by
  intro n
  induction n generalizing h with
  | zero => intro omega; rfl
  | succ n ih =>
      intro omega
      exact (ih (R.step_phase base h hh omega) omega).trans (R.reveal_openV hh omega)

theorem run_closedV {base h : Tr kappa V} (hh : R.Phase base h) :
    ∀ n omega, (R.run base n h omega).closedV = h.closedV := by
  intro n
  induction n generalizing h with
  | zero => intro omega; rfl
  | succ n ih =>
      intro omega
      exact (ih (R.step_phase base h hh omega) omega).trans (R.reveal_closedV base h omega)

theorem run_failed {base h : Tr kappa V} (hh : R.Phase base h) :
    ∀ n omega, (R.run base n h omega).failed = h.failed := by
  intro n
  induction n generalizing h with
  | zero => intro omega; rfl
  | succ n ih =>
      intro omega
      exact (ih (R.step_phase base h hh omega) omega).trans (R.reveal_failed base h omega)

def recordedRegion (base : Tr kappa V) (omega : Set kappa) : Finset kappa :=
  (R.run base (R.rounds base) base omega).inspected \ base.inspected

theorem recordedRegion_fresh (base : Tr kappa V) (omega : Set kappa) :
    Disjoint (R.recordedRegion base omega) base.inspected := Finset.sdiff_disjoint

theorem inspected_mono {base h : Tr kappa V} :
    ∀ n omega, h.inspected ⊆ (R.run base n h omega).inspected := by
  intro n
  induction n generalizing h with
  | zero => intro omega; exact Finset.Subset.rfl
  | succ n ih =>
      intro omega
      exact Finset.Subset.trans (by simp [reveal]) (ih (h := R.reveal base h omega) omega)

theorem inspected_final (base : Tr kappa V) (omega : Set kappa) :
    (R.run base (R.rounds base) base omega).inspected =
      base.inspected ∪ R.recordedRegion base omega := by
  symm
  exact Finset.union_sdiff_of_subset
    (R.inspected_mono (base := base) (h := base) (R.rounds base) omega)

theorem measurableSet_setOf_run
    (P : Tr kappa V → Set kappa → Prop)
    (hP : ∀ h, MeasurableSet {omega : Set kappa | P h omega}) :
    ∀ n base h, MeasurableSet {omega : Set kappa | P (R.run base n h omega) omega} := by
  intro n
  induction n with
  | zero => intro base h; simpa using hP h
  | succ n ih =>
      intro base h
      rw [show {omega : Set kappa | P (R.run base (n + 1) h omega) omega} =
          {omega : Set kappa | P (R.run base n
            (h.step (R.anchor base h) (R.region base h) ∅ true omega) omega) omega} by rfl]
      rw [h.setOf_step_eq_biUnion (fun _ => (∅ : Finset V))
        (fun _ _ _ => rfl)
        (fun h' omega => P (R.run base n h' omega) omega)]
      exact Finset.measurableSet_biUnion _ fun sigma _ =>
        (measurableSet_localCylinder (R.region base h).finite_toSet.countable _).inter
          (ih base _)

theorem linear_tower_step
    (p : kappa → unitInterval) (h : Tr kappa V) (z : V) (F : Finset kappa)
    (hfresh : Disjoint F h.inspected) (c : Real)
    (B D : Tr kappa V → Set (Set kappa))
    (hBm : ∀ k, MeasurableSet (B k)) (hDm : ∀ k, MeasurableSet (D k))
    (hlin : ∀ omega : Set kappa,
      c * (h.step z F ∅ true omega).prob p (B (h.step z F ∅ true omega)) ≤
        (h.step z F ∅ true omega).prob p (D (h.step z F ∅ true omega))) :
    c * h.prob p {omega | omega ∈ B (h.step z F ∅ true omega)} ≤
      h.prob p {omega | omega ∈ D (h.step z F ∅ true omega)} :=
  BDAdaptReg.RevealPhase.linear_tower_step p h z F hfresh c B D hBm hDm hlin

/-- The finite reveal tower, proved using only reachable phase descendants. -/
theorem linear_tower_run
    (p : kappa → unitInterval) (base h : Tr kappa V) (hh : R.Phase base h) (c : Real)
    (B D : Tr kappa V → Set (Set kappa))
    (hBm : ∀ k, MeasurableSet (B k)) (hDm : ∀ k, MeasurableSet (D k))
    (hlin : ∀ k, R.Phase base k → c * k.prob p (B k) ≤ k.prob p (D k)) :
    ∀ n, c * h.prob p {omega | omega ∈ B (R.run base n h omega)} ≤
      h.prob p {omega | omega ∈ D (R.run base n h omega)} := by
  intro n
  induction n generalizing h with
  | zero => simpa using hlin h hh
  | succ n ih =>
      apply linear_tower_step p h (R.anchor base h) (R.region base h)
        (R.region_fresh base h hh) c
        (fun k => {omega | omega ∈ B (R.run base n k omega)})
        (fun k => {omega | omega ∈ D (R.run base n k omega)})
      · intro k
        exact measurableSet_setOf_run R (fun k omega => omega ∈ B k) hBm n base k
      · intro k
        exact measurableSet_setOf_run R (fun k omega => omega ∈ D k) hDm n base k
      · intro omega
        exact ih (R.reveal base h omega) (R.step_phase base h hh omega)

end RevealPhase

/-! ## Corrected explorations -/

structure Exploration (kappa : Type*) [DecidableEq kappa]
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) where
  density : kappa → unitInterval
  Admissible : Tr kappa V → Prop
  revealPhase : RevealPhase kappa V Admissible
  next : Tr kappa V → V
  damage : Tr kappa V → Tr kappa V → Finset V
  succ : Tr kappa V → Tr kappa V → Set (Set kappa)
  succ_measurable : ∀ h k, MeasurableSet (succ h k)
  next_mem_boundary : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    next h ∈ h.boundary G A o
  succ_determinedBy : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    ∀ k, revealPhase.Phase h k →
    DeterminedBy (succ h k) (↑k.inspected : Set kappa)
  commit_admissible : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    ∀ k, revealPhase.Phase h k → ∀ (b : Bool) (omega : Set kappa),
      (b = true ↔ omega ∈ succ h k) →
        Admissible (k.step (next h) ∅ (damage h k) b omega)
  admissible_sound : ∀ h, Admissible h → h.Sound G A o

namespace Exploration

variable {kappa V : Type*} [DecidableEq kappa] [DecidableEq V]
  {G : SimpleGraph V} {A : Finset V} {o : V} {T : Set V}
  (E : Exploration kappa G A o T)

def revealed (h : Tr kappa V) (omega : Set kappa) : Tr kappa V :=
  E.revealPhase.run h (E.revealPhase.rounds h) h omega

def recordedRegion (h : Tr kappa V) (omega : Set kappa) : Finset kappa :=
  E.revealPhase.recordedRegion h omega

theorem revealed_phase {h : Tr kappa V} (hadm : E.Admissible h) (omega : Set kappa) :
    E.revealPhase.Phase h (E.revealed h omega) :=
  E.revealPhase.phase_run (E.revealPhase.start h hadm) _ _

theorem revealed_openV {h : Tr kappa V} (hadm : E.Admissible h) (omega : Set kappa) :
    (E.revealed h omega).openV = h.openV :=
  E.revealPhase.openV_eq h _ (E.revealed_phase hadm omega)

theorem revealed_closedV {h : Tr kappa V} (hadm : E.Admissible h) (omega : Set kappa) :
    (E.revealed h omega).closedV = h.closedV :=
  E.revealPhase.closedV_eq h _ (E.revealed_phase hadm omega)

theorem revealed_failed {h : Tr kappa V} (hadm : E.Admissible h) (omega : Set kappa) :
    (E.revealed h omega).failed = h.failed :=
  E.revealPhase.failed_eq h _ (E.revealed_phase hadm omega)

theorem revealed_sound {h : Tr kappa V} (hadm : E.Admissible h) (omega : Set kappa)
    (hs : h.Sound G A o) : (E.revealed h omega).Sound G A o := by
  unfold BDDom.Transcript.Sound at hs ⊢
  rw [E.revealed_openV hadm omega, E.revealed_closedV hadm omega,
    E.revealed_failed hadm omega]
  exact hs

def success (h : Tr kappa V) : Set (Set kappa) :=
  {omega | omega ∈ E.succ h (E.revealed h omega)}

theorem success_measurable (h : Tr kappa V) : MeasurableSet (E.success h) :=
  E.revealPhase.measurableSet_setOf_run
    (fun k omega => omega ∈ E.succ h k) (E.succ_measurable h)
    (E.revealPhase.rounds h) h h

open Classical in
def bit (h : Tr kappa V) (omega : Set kappa) : Bool := decide (omega ∈ E.success h)

theorem bit_eq_true_iff (h : Tr kappa V) (omega : Set kappa) :
    E.bit h omega = true ↔ omega ∈ E.success h := by simp [bit]

theorem bit_of_mem {h : Tr kappa V} {omega : Set kappa} (homega : omega ∈ E.success h) :
    E.bit h omega = true := (E.bit_eq_true_iff h omega).2 homega

theorem bit_of_notMem {h : Tr kappa V} {omega : Set kappa} (homega : omega ∉ E.success h) :
    E.bit h omega = false := by
  have := (E.bit_eq_true_iff h omega).not.2 homega
  simpa using this

def commit (base k : Tr kappa V) (b : Bool) : Tr kappa V :=
  k.step (E.next base) ∅ (E.damage base k) b ∅

def advance (h : Tr kappa V) (omega : Set kappa) : Tr kappa V :=
  E.commit h (E.revealed h omega) (E.bit h omega)

theorem commit_eq_step (base k : Tr kappa V) (b : Bool) (omega : Set kappa) :
    E.commit base k b = k.step (E.next base) ∅ (E.damage base k) b omega := by
  unfold commit
  exact k.step_congr rfl fun x hx => absurd hx (Finset.notMem_empty x)

theorem commit_inspected (base k : Tr kappa V) (b : Bool) :
    (E.commit base k b).inspected = k.inspected := by simp [commit]

theorem commit_state (base k : Tr kappa V) (b : Bool) (x : kappa) :
    (E.commit base k b).state x ↔ k.state x := by
  simp [commit, BDDom.Transcript.step_state]

theorem advance_admissible {h : Tr kappa V} (hadm : E.Admissible h)
    (hT : ¬ h.Terminal G A o T) (omega : Set kappa) : E.Admissible (E.advance h omega) := by
  rw [advance, E.commit_eq_step _ _ _ omega]
  exact E.commit_admissible h hadm hT _ (E.revealed_phase hadm omega) _ omega
    (E.bit_eq_true_iff h omega)

theorem undetermined_advance_lt {h : Tr kappa V} (hadm : E.Admissible h)
    (hT : ¬ h.Terminal G A o T) (omega : Set kappa) :
    (E.advance h omega).undetermined A < h.undetermined A := by
  obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
  rw [advance]
  have hu := (E.revealed h omega).undetermined_step_lt A hzA
    (by simpa [E.revealed_openV hadm omega] using hzo)
    (by simpa [E.revealed_closedV hadm omega] using hzc)
    (F := (∅ : Finset kappa)) (damage := E.damage h (E.revealed h omega))
    (b := E.bit h omega) (ω := (∅ : Set kappa))
  have hku : (E.revealed h omega).undetermined A = h.undetermined A := by
    have hopen : (E.revealed h omega).base.openV = h.base.openV :=
      E.revealed_openV hadm omega
    have hclosed : (E.revealed h omega).base.closedV = h.base.closedV :=
      E.revealed_closedV hadm omega
    unfold BDDom.Transcript.undetermined FRDom.Transcript.undetermined
    rw [hopen, hclosed]
  change (E.commit h (E.revealed h omega) (E.bit h omega)).undetermined A <
    (E.revealed h omega).undetermined A at hu
  rwa [hku] at hu

open Classical in
def run : Nat → Tr kappa V → Set kappa → Tr kappa V
  | 0, h, _ => h
  | n + 1, h, omega =>
      if h.Terminal G A o T then h else run n (E.advance h omega) omega

@[simp] theorem run_zero (h : Tr kappa V) (omega : Set kappa) : E.run 0 h omega = h := rfl

theorem run_succ_of_terminal {h : Tr kappa V} (hT : h.Terminal G A o T)
    (n : Nat) (omega : Set kappa) : E.run (n + 1) h omega = h := by simp [run, hT]

theorem run_succ_of_not_terminal {h : Tr kappa V} (hT : ¬ h.Terminal G A o T)
    (n : Nat) (omega : Set kappa) :
    E.run (n + 1) h omega = E.run n (E.advance h omega) omega := by simp [run, hT]

theorem terminal_run :
    ∀ (n : Nat) (h : Tr kappa V), E.Admissible h → h.undetermined A ≤ n →
      ∀ omega : Set kappa, (E.run n h omega).Terminal G A o T := by
  intro n
  induction n with
  | zero =>
      intro h _ hn omega
      rw [run_zero]
      exact h.base.terminal_of_undetermined_eq_zero G A o T (Nat.le_zero.1 hn)
  | succ n ih =>
      intro h hadm hn omega
      by_cases hT : h.Terminal G A o T
      · rw [E.run_succ_of_terminal hT]
        exact hT
      · rw [E.run_succ_of_not_terminal hT]
        refine ih _ (E.advance_admissible hadm hT omega) ?_ omega
        have hlt := E.undetermined_advance_lt hadm hT omega
        omega

/-! ### Measurability of the terminally complete run -/

theorem setOf_run_succ_eq {h : Tr kappa V} (hT : ¬ h.Terminal G A o T)
    (P : Tr kappa V → Prop) (n : Nat) :
    {omega : Set kappa | P (E.run (n + 1) h omega)} =
      (E.success h ∩ {omega | P (E.run n (E.commit h (E.revealed h omega) true) omega)}) ∪
      ((E.success h)ᶜ ∩
        {omega | P (E.run n (E.commit h (E.revealed h omega) false) omega)}) := by
  ext omega
  by_cases homega : omega ∈ E.success h
  · rw [Set.mem_setOf_eq, E.run_succ_of_not_terminal hT, advance, E.bit_of_mem homega]
    simp [homega]
  · rw [Set.mem_setOf_eq, E.run_succ_of_not_terminal hT, advance, E.bit_of_notMem homega]
    simp [homega]

theorem measurableSet_setOf_run (P : Tr kappa V → Prop) :
    ∀ n h, MeasurableSet {omega : Set kappa | P (E.run n h omega)} := by
  intro n
  induction n with
  | zero =>
      intro h
      simpa only [run_zero] using (MeasurableSet.const (α := Set kappa) (P h))
  | succ n ih =>
      intro h
      by_cases hT : h.Terminal G A o T
      · have heq : {omega : Set kappa | P (E.run (n + 1) h omega)} =
            {_omega : Set kappa | P h} := by
          ext omega
          rw [Set.mem_setOf_eq, E.run_succ_of_terminal hT]
          rfl
        rw [heq]
        exact MeasurableSet.const _
      · have hbranch : ∀ b : Bool,
            MeasurableSet {omega : Set kappa |
              P (E.run n (E.commit h (E.revealed h omega) b) omega)} := by
          intro b
          exact E.revealPhase.measurableSet_setOf_run
            (fun k omega => P (E.run n (E.commit h k b) omega))
            (fun k => ih (E.commit h k b)) (E.revealPhase.rounds h) h h
        rw [E.setOf_run_succ_eq hT P n]
        exact ((E.success_measurable h).inter (hbranch true)).union
          ((E.success_measurable h).compl.inter (hbranch false))

/-! ### Bounded-damage domination through the corrected reveal tower -/

theorem commit_bern_eq {a : unitInterval} {base k : Tr kappa V}
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

theorem commit_prob (p : kappa → unitInterval) (base k : Tr kappa V) (b : Bool)
    (Y : Set (Set kappa)) : (E.commit base k b).prob p Y = k.prob p Y := by
  rw [BDDom.Transcript.prob_eq, BDDom.Transcript.prob_eq, E.commit_inspected]
  exact pinnedProb_congr_val p _ (fun x hx => E.commit_state base k b x) _

/-- Finite adaptive-reveal bounded-damage domination, with the reveal phase entered only from the
admissible history supplied to this induction. -/
theorem bern_le_prob_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : Real) ≤ h.prob E.density (E.success h)) :
    ∀ (n : Nat) (h : Tr kappa V), E.Admissible h → h.undetermined A ≤ n →
      h.bern a G A o T ≤
        h.prob E.density {omega | (E.run n h omega).Reaches G o T} := by
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
      · have heq : {omega : Set kappa | (E.run (n + 1) h omega).Reaches G o T} =
            {_omega : Set kappa | h.Reaches G o T} := by
          ext omega
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
            (F := (∅ : Finset kappa)) (damage := E.damage h k) (b := b)
            (ω := (∅ : Set kappa))
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
        let BT : Tr kappa V → Set (Set kappa) := fun k => E.succ h k
        let BF : Tr kappa V → Set (Set kappa) := fun k => (E.succ h k)ᶜ
        let DT : Tr kappa V → Set (Set kappa) := fun k =>
          BT k ∩ {omega | (E.run n (E.commit h k true) omega).Reaches G o T}
        let DF : Tr kappa V → Set (Set kappa) := fun k =>
          BF k ∩ {omega | (E.run n (E.commit h k false) omega).Reaches G o T}
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
          let omega0 : Set kappa := substitute (↑k.inspected : Set kappa) k.state ∅
          have hadm' : E.Admissible (E.commit h k true) := by
            rw [E.commit_eq_step h k true omega0]
            exact E.commit_admissible h hadm hT k hk true omega0 (by
              simpa [omega0] using hmem)
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
          let omega0 : Set kappa := substitute (↑k.inspected : Set kappa) k.state ∅
          have hadm' : E.Admissible (E.commit h k false) := by
            rw [E.commit_eq_step h k false omega0]
            exact E.commit_admissible h hadm hT k hk false omega0 (by
              simp only [Bool.false_eq_true, false_iff]
              simpa [omega0] using hmem)
          have hih := ih (E.commit h k false) hadm' (hund k hk false)
          rw [E.commit_bern_eq hk false, E.commit_prob E.density h k false] at hih
          exact hih
        have hkeyT := E.revealPhase.linear_tower_run E.density h h
          (E.revealPhase.start h hadm) cT BT DT hBTm hDTm hlinT
          (E.revealPhase.rounds h)
        have hkeyF := E.revealPhase.linear_tower_run E.density h h
          (E.revealPhase.start h hadm) cF BF DF hBFm hDFm hlinF
          (E.revealPhase.rounds h)
        have hq : (a : Real) ≤ h.prob E.density (E.success h) := hstep h hadm hT
        have hq1 : h.prob E.density (E.success h) ≤ 1 := h.prob_le_one _ _
        have hqc : h.prob E.density (E.success h)ᶜ =
            1 - h.prob E.density (E.success h) := by
          rw [BDDom.Transcript.prob_eq, BDDom.Transcript.prob_eq]
          exact pinnedProb_compl _ _ _ (E.success_measurable h)
        have hbern := h.bern_split a G A o T (F := (∅ : Finset kappa)) hzo hzf
          (∅ : Finset V) (∅ : Finset V) (∅ : Set kappa) (∅ : Set kappa)
        have hmono := h.bern_step_false_le_true a G A o T (z := E.next h)
          (F := (∅ : Finset kappa)) (∅ : Finset V) (∅ : Finset V)
          (∅ : Set kappa) (∅ : Set kappa)
        have hsplit : h.prob E.density
            {omega | (E.run (n + 1) h omega).Reaches G o T} =
            h.prob E.density
              (E.success h ∩ {omega |
                (E.run n (E.commit h (E.revealed h omega) true) omega).Reaches G o T}) +
            h.prob E.density
              ((E.success h)ᶜ ∩ {omega |
                (E.run n (E.commit h (E.revealed h omega) false) omega).Reaches G o T}) := by
          rw [BDDom.Transcript.prob_eq, BDDom.Transcript.prob_eq,
            BDDom.Transcript.prob_eq,
            E.setOf_run_succ_eq hT (fun r => r.Reaches G o T) n]
          refine pinnedProb_union _ _ _
            (Set.disjoint_left.2 fun omega homega homega' => homega'.1 homega.1) ?_
          exact (E.success_measurable h).compl.inter
            (E.revealPhase.measurableSet_setOf_run
              (fun k omega => (E.run n (E.commit h k false) omega).Reaches G o T)
              (fun k => E.measurableSet_setOf_run (fun r => r.Reaches G o T) n _)
              (E.revealPhase.rounds h) h h)
        change cT * h.prob E.density (E.success h) ≤ _ at hkeyT
        change cF * h.prob E.density (E.success h)ᶜ ≤ _ at hkeyF
        change _ ≤ h.prob E.density
          (E.success h ∩ {omega |
            (E.run n (E.commit h (E.revealed h omega) true) omega).Reaches G o T}) at hkeyT
        change _ ≤ h.prob E.density
          ((E.success h)ᶜ ∩ {omega |
            (E.run n (E.commit h (E.revealed h omega) false) omega).Reaches G o T}) at hkeyF
        rw [hqc] at hkeyF
        have hprod : (0 : Real) ≤
            (h.prob E.density (E.success h) - a) * (cT - cF) := by
          apply mul_nonneg
          · linarith
          · exact sub_nonneg.2 hmono
        rw [hbern, hsplit]
        dsimp only [cT, cF] at hkeyT hkeyF hprod ⊢
        nlinarith [hkeyT, hkeyF, hprod]

/-- Start-state form.  The admissibility witness is explicit and is used to enter the corrected
reveal phase; no global start field is available. -/
theorem pinnedProb_safeTargetConn_le_real_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : Real) ≤ h.prob E.density (E.success h))
    (h0 : Tr kappa V) (hadm : E.Admissible h0) (hins : h0.inspected = ∅)
    (hopen : h0.openV = {o}) (hfailed : h0.failed = ∅)
    (n : Nat) (hn : h0.undetermined A ≤ n) :
    pinnedProb (fun _ : V => a) {o} (fun _ => True) (BDDom.Safe.targetConn G A o T) ≤
      (prodBernoulli E.density).real {omega | (E.run n h0 omega).Reaches G o T} := by
  have hmain := E.bern_le_prob_run hstep n h0 hadm hn
  rw [BDDom.Transcript.prob_eq, hins, Finset.coe_empty, pinnedProb_empty] at hmain
  refine le_trans (le_of_eq ?_) hmain
  unfold BDDom.Transcript.bern
  have hopen' : h0.base.openV = {o} := hopen
  rw [hopen', hfailed, Finset.union_empty, Finset.coe_singleton]
  refine pinnedProb_congr_val _ _ (fun v hv => ?_) _
  rw [Set.mem_singleton_iff] at hv
  simp [hv]

#print axioms KNAll.Site.ABDAdaptReg.Exploration.bern_le_prob_run
#print axioms KNAll.Site.ABDAdaptReg.Exploration.pinnedProb_safeTargetConn_le_real_run

end Exploration

end KNAll.Site.ABDAdaptReg

end
