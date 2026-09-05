import Hypergraph.CoreBatchFullReveal
import Hypergraph.CoreReservationExtension

set_option maxHeartbeats 3000000

/-!
# Bounded stopped reveals for an accepted core batch

The maximal reveal in `CoreBatchFullReveal` is useful for support and determination, but reads
past the first good level.  This file gives the actual bounded scheduler.  It first exposes the
fresh incoming corridor.  Thereafter every new head advances by one nested level per round, and
becomes inactive as soon as a completely exposed level is good.  Thus no unused suffix of that
head's protected corridor is read.

The scheduler is defined from the transcript alone.  In particular it never looks at an
uninspected bit of the ambient configuration.
-/

noncomputable section

namespace KNAll.Site.CoreStoppedReveal

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

abbrev Tr (d : Nat) := BDDom.Transcript (Site d) (Site 2)

def centre (n : Nat) (base : Tr d) : Site 2 := MacroExp.pendZ d n base.base

def owner (r t : Nat) (q : unitInterval) (eps : Real) (n : Nat)
    (base : Tr d) : Site 2 := by
  classical
  exact if H : CoreFrontier.Invariant r t q eps base.base ∧
      CoreFrontier.Frontier base.base (centre n base) then
    CoreAcceptedTransition.owner H.1 (centre n base) H.2
  else 0

/-- On an accepted active state the proof-independent choice is definitionally the accepted
transition's owner, up to proof irrelevance.  This lets the concrete scheduler consume the
existing analytic batch theorem without equating two unrelated `Finset.choose` operations. -/
theorem owner_eq_of_invariant
    {r t n : Nat} {q : unitInterval} {eps : Real} {base : Tr d}
    (hI : CoreFrontier.Invariant r t q eps base.base)
    (hz : CoreFrontier.Frontier base.base (centre n base)) :
    owner r t q eps n base = CoreAcceptedTransition.owner hI (centre n base) hz := by
  classical
  unfold owner
  rw [dif_pos ⟨hI, hz⟩]

theorem owner_spec
    {r t n : Nat} {q : unitInterval} {eps : Real} {base : Tr d}
    (hI : CoreFrontier.Invariant r t q eps base.base)
    (hz : CoreFrontier.Frontier base.base (centre n base)) :
    owner r t q eps n base ∈ base.openV ∧
      centre n base ∈ MacroExp.pending d base.base (owner r t q eps n base) ∧
      CoreRes.Bound r t q eps base.base (owner r t q eps n base) (centre n base) := by
  rw [owner_eq_of_invariant hI hz]
  exact CoreAcceptedTransition.owner_spec hI (centre n base) hz

def incomingRegion (r t n : Nat) (q : unitInterval) (eps : Real)
    (base : Tr d) : Finset (Site d) :=
  AtomTower.incomingRegion d r t base.base (owner r t q eps n base) (centre n base)

/-- The incoming transcript reconstructed from the bits already recorded in `k`.  Extra outgoing
bits in `k.openSites` are harmless because `incomingTr` filters them through `incomingRegion`. -/
def incomingTr (r t n : Nat) (q : unitInterval) (eps : Real)
    (base k : Tr d) : MacroExp.Tr d :=
  AtomTower.incomingTr d r t base.base (owner r t q eps n base) (centre n base)
    (↑k.openSites : Set (Site d))

/-- Level `j` may be queried exactly when every preceding level is already completely exposed and
is bad.  This is decidable noncomputably; all its inputs are fields of the current transcript. -/
def ready (r t s n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) (y : Site 2) (j : Nat) : Prop :=
  ∀ m ∈ Finset.range j,
    Stopped.revealSet d r t s (incomingTr r t n q eps base k)
        (centre n base) (axis y) (sign y) m ⊆ k.inspected ∧
      (↑k.openSites : Set (Site d)) ∈
        CoreStopped.levelBad r t s (incomingTr r t n q eps base k)
          (centre n base) y (axis y) (sign y) q eps m

/-- The next fresh layer of one head.  At most the first not-yet-complete level contributes:
later levels require that one to be complete, and after a good level none contributes. -/
def headRegion (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) (y : Site 2) : Finset (Site d) := by
  classical
  exact (Finset.range K).biUnion fun j =>
    if ready r t s n q eps axis sign base k y j then
      Stopped.revealSet d r t s (incomingTr r t n q eps base k)
          (centre n base) (axis y) (sign y) j \ k.inspected
    else ∅

def outgoingRegion (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) : Finset (Site d) := by
  classical
  exact (CoreFrontier.newHeads (d := d) base.base (centre n base)).biUnion
    (headRegion r t s K n q eps axis sign base k)

/-- One scheduler round.  The incoming read has priority.  Once it is complete, all still-active
heads advance in parallel by one level.  Every displayed set is subtracted from `k.inspected`. -/
def region (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) : Finset (Site d) := by
  classical
  exact if incomingRegion r t n q eps base ⊆ k.inspected then
    outgoingRegion r t s K n q eps axis sign base k
  else incomingRegion r t n q eps base \ k.inspected

theorem region_fresh (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int) (base k : Tr d) :
    Disjoint (region r t s K n q eps axis sign base k) k.inspected := by
  classical
  unfold region outgoingRegion headRegion
  split_ifs
  · rw [Finset.disjoint_left]
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨y, -, hxy⟩ := hx
    rw [Finset.mem_biUnion] at hxy
    obtain ⟨j, -, hxj⟩ := hxy
    split at hxj
    · exact (Finset.mem_sdiff.1 hxj).2
    · exact (Finset.notMem_empty x hxj).elim
  · exact Finset.sdiff_disjoint

/-- The defining inequalities show monotonicity in the height even before the sign is known to be
one of the two geometric directions. -/
theorem stub_mono_any {c : Site d} {i : Fin d} {sigma : Int} {r t a a' : Nat}
    (haa' : a ≤ a') :
    Stopped.stub c i sigma r t a ⊆ Stopped.stub c i sigma r t a' := by
  intro x hx
  rw [Stopped.stub, Finset.mem_filter] at hx ⊢
  refine ⟨?_, hx.2.1, ?_, hx.2.2.2⟩
  · rw [MacroExp.mem_abox] at hx ⊢
    intro j
    have hj := hx.1 j
    unfold MacroExp.rad at hj ⊢
    split_ifs <;> push_cast at hj ⊢ <;> omega
  · push_cast at hx ⊢
    omega

theorem revealSet_mono_any
    {r t s : Nat} {h : MacroExp.Tr d} {z : Site 2} {i : Fin d} {sigma : Int}
    {j j' : Nat} (hjj' : j ≤ j') :
    Stopped.revealSet d r t s h z i sigma j ⊆
      Stopped.revealSet d r t s h z i sigma j' := by
  exact Finset.sdiff_subset_sdiff
    (stub_mono_any (Nat.mul_le_mul_left (10 * s) hjj')) (Finset.Subset.refl _)

/-- A compact transcript-extension relation used by the stopped-history induction. -/
def RecordExtends (later earlier : Tr d) : Prop :=
  earlier.inspected ⊆ later.inspected ∧
    ∀ x ∈ earlier.inspected, (later.state x ↔ earlier.state x)

theorem recordExtends_refl (h : Tr d) : RecordExtends h h :=
  ⟨Finset.Subset.rfl, fun _ _ => Iff.rfl⟩

theorem recordExtends_trans {h k l : Tr d}
    (hlk : RecordExtends l k) (hkh : RecordExtends k h) : RecordExtends l h :=
  ⟨hkh.1.trans hlk.1, fun x hx => (hlk.2 x (hkh.1 hx)).trans (hkh.2 x hx)⟩

theorem recordExtends_step (h : Tr d) (z : Site 2) (F : Finset (Site d))
    (damage : Finset (Site 2)) (b : Bool) (omega : SiteConfig (Site d))
    (hfresh : Disjoint F h.inspected) :
    RecordExtends (h.step z F damage b omega) h := by
  constructor
  · exact Finset.subset_union_left
  · intro x hx
    rw [BDDom.Transcript.step_state]
    constructor
    · rintro (hopen | ⟨hxF, -⟩)
      · exact hopen
      · exact (Finset.disjoint_left.1 hfresh hxF hx).elim
    · exact Or.inl

theorem incomingTr_eq_of_recordExtends
    {r t n : Nat} {q : unitInterval} {eps : Real} {base current later : Tr d}
    (hin : incomingRegion r t n q eps base ⊆ current.inspected)
    (hext : RecordExtends later current) :
    incomingTr r t n q eps base current = incomingTr r t n q eps base later := by
  unfold incomingTr
  apply FRDom.Transcript.step_congr
  intro x hx
  change current.state x ↔ later.state x
  exact (hext.2 x (hin hx)).symm

/-- The actual reveal descendants of an admissible base.  Using reachability as the phase
predicate rules out pathological transcripts with the same macro verdicts but unrelated reads;
this is important because `Exploration.commit_admissible` is quantified over every phase state. -/
inductive PhaseRel (A : Finset (Site 2)) (r t s K n : Nat)
    (q : unitInterval) (eps : Real) (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) : Tr d → Prop where
  | start (hadm : CoreAcceptedTransition.Admissible (d := d) A r t q eps base) :
      PhaseRel A r t s K n q eps axis sign base base
  | step {k : Tr d} (hk : PhaseRel A r t s K n q eps axis sign base k)
      (omega : SiteConfig (Site d)) :
      PhaseRel A r t s K n q eps axis sign base
        (k.step 0 (region r t s K n q eps axis sign base k) ∅ true omega)

namespace PhaseRel

theorem admissible_base
    {A : Finset (Site 2)} {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {base k : Tr d}
    (hk : PhaseRel A r t s K n q eps axis sign base k) :
    CoreAcceptedTransition.Admissible (d := d) A r t q eps base := by
  induction hk with
  | start hadm => exact hadm
  | step _ _ ih => exact ih

theorem zero_open
    {A : Finset (Site 2)} {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {base k : Tr d}
    (hk : PhaseRel A r t s K n q eps axis sign base k) : (0 : Site 2) ∈ k.openV := by
  induction hk with
  | start hadm => exact hadm.preReveal.zero_open
  | @step k hk omega ih =>
      change (0 : Site 2) ∈ insert 0 k.openV
      simp

theorem openV_eq
    {A : Finset (Site 2)} {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {base k : Tr d}
    (hk : PhaseRel A r t s K n q eps axis sign base k) : k.openV = base.openV := by
  induction hk with
  | start _ => rfl
  | @step k hk omega ih =>
      simpa [BDDom.Transcript.step_openV, Finset.insert_eq_of_mem (zero_open hk)] using ih

theorem closedV_eq
    {A : Finset (Site 2)} {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {base k : Tr d}
    (hk : PhaseRel A r t s K n q eps axis sign base k) : k.closedV = base.closedV := by
  induction hk with
  | start _ => rfl
  | step hk omega ih => simpa using ih

theorem failed_eq
    {A : Finset (Site 2)} {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {base k : Tr d}
    (hk : PhaseRel A r t s K n q eps axis sign base k) : k.failed = base.failed := by
  induction hk with
  | start _ => rfl
  | step hk omega ih => simpa using ih

theorem openSites_subset
    {A : Finset (Site 2)} {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {base k : Tr d}
    (hk : PhaseRel A r t s K n q eps axis sign base k) :
    base.openSites ⊆ k.openSites := by
  classical
  induction hk with
  | start _ => exact Finset.Subset.rfl
  | @step current hk omega ih =>
      exact ih.trans (by
        intro x hx
        change x ∈ current.openSites ∪
          (region r t s K n q eps axis sign base current).filter (fun a => a ∈ omega)
        exact Finset.mem_union_left _ hx)

/-- Reachable reveal states extend their admitted base without revising an old bit. -/
theorem extends_base
    {A : Finset (Site 2)} {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {base k : Tr d}
    (hk : PhaseRel A r t s K n q eps axis sign base k) :
    base.inspected ⊆ k.inspected ∧
      ∀ x ∈ base.inspected, (k.state x ↔ base.state x) := by
  classical
  induction hk with
  | start _ => exact ⟨Finset.Subset.rfl, fun _ _ => Iff.rfl⟩
  | @step current hk omega ih =>
      constructor
      · exact ih.1.trans Finset.subset_union_left
      · intro x hx
        rw [BDDom.Transcript.step_state]
        constructor
        · rintro (hopen | ⟨hxR, -⟩)
          · exact ih.2 x hx |>.mp hopen
          · exact (Finset.disjoint_left.1
              (region_fresh r t s K n q eps axis sign base current)
              hxR (ih.1 hx)).elim
        · intro hopen
          exact Or.inl (ih.2 x hx |>.mpr hopen)

end PhaseRel

/-- One incoming round and `K` active-level rounds suffice, since every active head completes at
least one further nested level in each outgoing round. -/
def phase (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int) :
    ABDAdaptReg.RevealPhase (Site d) (Site 2)
      (CoreAcceptedTransition.Admissible (d := d) A r t q eps) where
  Phase := PhaseRel A r t s K n q eps axis sign
  rounds _ := K + 1
  anchor _ _ := 0
  region := region r t s K n q eps axis sign
  start _ hadm := PhaseRel.start hadm
  openV_eq _ _ hk := PhaseRel.openV_eq hk
  closedV_eq _ _ hk := PhaseRel.closedV_eq hk
  failed_eq _ _ hk := PhaseRel.failed_eq hk
  anchor_open _ _ hk := PhaseRel.zero_open hk
  region_fresh := by
    intro base k hk
    exact region_fresh r t s K n q eps axis sign base k
  step_phase := fun _ _ hk omega => PhaseRel.step hk omega

@[simp] theorem phase_rounds (A : Finset (Site 2)) (r t s K n : Nat)
    (q : unitInterval) (eps : Real) (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) :
    (phase (d := d) A r t s K n q eps axis sign).rounds base = K + 1 := rfl

/-- The iterative definition can also be read with the last reveal exposed. -/
theorem run_succ_last
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base h : Tr d) (m : Nat) (omega : SiteConfig (Site d)) :
    (phase (d := d) A r t s K n q eps axis sign).run base (m + 1) h omega =
      (phase (d := d) A r t s K n q eps axis sign).reveal base
        ((phase (d := d) A r t s K n q eps axis sign).run base m h omega) omega := by
  let Rph := phase (d := d) A r t s K n q eps axis sign
  induction m generalizing h with
  | zero => rfl
  | succ m ih =>
      change Rph.run base (m + 1) (Rph.reveal base h omega) omega =
        Rph.reveal base (Rph.run base (m + 1) h omega) omega
      rw [ih]
      rfl

def Compatible (base : Tr d) (omega : SiteConfig (Site d)) (k : Tr d) : Prop :=
  RecordExtends k base ∧
    ∀ x ∈ k.inspected, x ∉ base.inspected → (k.state x ↔ x ∈ omega)

theorem compatible_base (base : Tr d) (omega : SiteConfig (Site d)) :
    Compatible base omega base := by
  exact ⟨recordExtends_refl base, fun _ hx hxnot => (hxnot hx).elim⟩

theorem compatible_step
    {base k : Tr d} {omega : SiteConfig (Site d)}
    (hk : Compatible base omega k) (z : Site 2) (F : Finset (Site d))
    (damage : Finset (Site 2)) (b : Bool) (hfresh : Disjoint F k.inspected) :
    Compatible base omega (k.step z F damage b omega) := by
  classical
  constructor
  · exact recordExtends_trans (recordExtends_step k z F damage b omega hfresh) hk.1
  · intro x hx hxbase
    rw [BDDom.Transcript.step_state]
    have hxU : x ∈ k.inspected ∪ F := by simpa using hx
    constructor
    · rintro (hOld | ⟨-, hxomega⟩)
      · exact (hk.2 x (k.base.mem_inspected_of_state hOld) hxbase).mp hOld
      · exact hxomega
    · intro hxomega
      by_cases hxold : x ∈ k.inspected
      · exact Or.inl ((hk.2 x hxold hxbase).mpr hxomega)
      · exact Or.inr ⟨(Finset.mem_union.1 hxU).resolve_left hxold, hxomega⟩

theorem compatible_state_iff_substitute
    {base k : Tr d} {omega : SiteConfig (Site d)}
    (hk : Compatible base omega k) {x : Site d} (hx : x ∈ k.inspected) :
    k.state x ↔ x ∈ substitute (↑base.inspected : Set (Site d)) base.state omega := by
  by_cases hxbase : x ∈ base.inspected
  · rw [mem_substitute_of_mem base.state (Finset.mem_coe.2 hxbase)]
    exact hk.1.2 x hxbase
  · rw [mem_substitute_of_notMem base.state (by simpa only [Finset.mem_coe] using hxbase)]
    exact hk.2 x hx hxbase

theorem compatible_run
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (m : Nat) (omega : SiteConfig (Site d)) :
    Compatible base omega
      ((phase (d := d) A r t s K n q eps axis sign).run base m base omega) := by
  let Rph := phase (d := d) A r t s K n q eps axis sign
  induction m with
  | zero => exact compatible_base base omega
  | succ m ih =>
      rw [run_succ_last]
      exact compatible_step ih 0 _ ∅ true
        (region_fresh r t s K n q eps axis sign base (Rph.run base m base omega))

theorem compatible_run_from
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    {base h : Tr d} {omega : SiteConfig (Site d)}
    (hh : Compatible base omega h) (m : Nat) :
    Compatible base omega
      ((phase (d := d) A r t s K n q eps axis sign).run base m h omega) := by
  let Rph := phase (d := d) A r t s K n q eps axis sign
  induction m with
  | zero => exact hh
  | succ m ih =>
      rw [run_succ_last]
      exact compatible_step ih 0 _ ∅ true
        (region_fresh r t s K n q eps axis sign base (Rph.run base m h omega))

theorem run_inspected_mono_succ
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base h : Tr d) (m : Nat) (omega : SiteConfig (Site d)) :
    ((phase (d := d) A r t s K n q eps axis sign).run base m h omega).inspected ⊆
      ((phase (d := d) A r t s K n q eps axis sign).run base (m + 1) h omega).inspected := by
  rw [run_succ_last, ABDAdaptReg.RevealPhase.reveal, BDDom.Transcript.step_inspected]
  exact Finset.subset_union_left

theorem run_inspected_mono
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base h : Tr d) (omega : SiteConfig (Site d)) {a b : Nat} (hab : a ≤ b) :
    ((phase (d := d) A r t s K n q eps axis sign).run base a h omega).inspected ⊆
      ((phase (d := d) A r t s K n q eps axis sign).run base b h omega).inspected := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ b hab ih =>
      exact ih.trans (run_inspected_mono_succ A r t s K n q eps axis sign base h b omega)

theorem incomingTr_eq_outer_of_compatible
    {r t n : Nat} {q : unitInterval} {eps : Real}
    {base k : Tr d} {omega : SiteConfig (Site d)}
    (hk : Compatible base omega k)
    (hin : incomingRegion r t n q eps base ⊆ k.inspected) :
    incomingTr r t n q eps base k =
      AtomTower.incomingTr d r t base.base (owner r t q eps n base) (centre n base) omega := by
  unfold incomingTr
  apply FRDom.Transcript.step_congr
  intro x hx
  change k.state x ↔ x ∈ omega
  apply hk.2 x (hin hx)
  exact (Finset.mem_sdiff.1 hx).2

theorem run_recordExtends_initial
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base h : Tr d) (m : Nat) (omega : SiteConfig (Site d)) :
    RecordExtends
      ((phase (d := d) A r t s K n q eps axis sign).run base m h omega) h := by
  let Rph := phase (d := d) A r t s K n q eps axis sign
  induction m with
  | zero => exact recordExtends_refl h
  | succ m ih =>
      rw [run_succ_last]
      exact recordExtends_trans
        (recordExtends_step (Rph.run base m h omega) 0 _ ∅ true omega
          (region_fresh r t s K n q eps axis sign base (Rph.run base m h omega))) ih

theorem incoming_complete_after_first
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d)) :
    incomingRegion r t n q eps base ⊆
      ((phase (d := d) A r t s K n q eps axis sign).run base 1 base omega).inspected := by
  classical
  intro x hx
  change x ∈ base.inspected ∪ region r t s K n q eps axis sign base base
  by_cases hin : incomingRegion r t n q eps base ⊆ base.inspected
  · exact Finset.mem_union_left _ (hin hx)
  · by_cases hxbase : x ∈ base.inspected
    · exact Finset.mem_union_left _ hxbase
    · apply Finset.mem_union_right
      rw [region, if_neg hin, Finset.mem_sdiff]
      exact ⟨hx, hxbase⟩

theorem incoming_complete_final
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d)) :
    incomingRegion r t n q eps base ⊆
      ((phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega).inspected := by
  let Rph := phase (d := d) A r t s K n q eps axis sign
  have hfirst := incoming_complete_after_first A r t s K n q eps axis sign base omega
  have hfirst' : incomingRegion r t n q eps base ⊆
      (Rph.reveal base base omega).inspected := by
    simpa only [ABDAdaptReg.RevealPhase.run_succ,
      ABDAdaptReg.RevealPhase.run_zero] using hfirst
  have hext : RecordExtends (Rph.run base K (Rph.reveal base base omega) omega)
      (Rph.reveal base base omega) :=
    run_recordExtends_initial A r t s K n q eps axis sign base
      (Rph.reveal base base omega) K omega
  change incomingRegion r t n q eps base ⊆
    (Rph.run base K (Rph.reveal base base omega) omega).inspected
  exact hfirst'.trans hext.1

theorem mem_levelBad_iff_outer_of_compatible
    {r t s n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {base k : Tr d} {omega : SiteConfig (Site d)} {y : Site 2} {j : Nat}
    (hk : Compatible base omega k)
    (hin : incomingRegion r t n q eps base ⊆ k.inspected)
    (hread : Stopped.revealSet d r t s (incomingTr r t n q eps base k)
      (centre n base) (axis y) (sign y) j ⊆ k.inspected) :
    (↑k.openSites : Set (Site d)) ∈
        CoreStopped.levelBad r t s (incomingTr r t n q eps base k)
          (centre n base) y (axis y) (sign y) q eps j ↔
      omega ∈ CoreStopped.levelBad r t s
        (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
          (centre n base) omega)
        (centre n base) y (axis y) (sign y) q eps j := by
  classical
  have hinEq := incomingTr_eq_outer_of_compatible hk hin
  rw [hinEq] at hread ⊢
  apply (determinedBy_iff _ _).1
    (CoreStopped.determinedBy_levelBad r t s
      (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
        (centre n base) omega)
      (centre n base) y (axis y) (sign y) q eps j)
  ext x
  simp only [Set.mem_inter_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hxopen, hxR⟩
    have hxnot : x ∉ base.inspected := by
      intro hxbase
      exact Finset.disjoint_left.1
        (Stopped.revealSet_fresh d r t s
          (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
            (centre n base) omega)
          (centre n base) (axis y) (sign y) j)
        hxR (by
          rw [AtomTower.incomingTr_inspected]
          exact Finset.mem_union_left _ hxbase)
    exact ⟨(hk.2 x (hread hxR) hxnot).mp hxopen, hxR⟩
  · rintro ⟨hxopen, hxR⟩
    have hxnot : x ∉ base.inspected := by
      intro hxbase
      exact Finset.disjoint_left.1
        (Stopped.revealSet_fresh d r t s
          (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
            (centre n base) omega)
          (centre n base) (axis y) (sign y) j)
        hxR (by
          rw [AtomTower.incomingTr_inspected]
          exact Finset.mem_union_left _ hxbase)
    exact ⟨(hk.2 x (hread hxR) hxnot).mpr hxopen, hxR⟩

theorem revealSet_subset_after_outgoing_rounds
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d))
    {y : Site 2} (hy : y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base))
    (j : Nat) (hjK : j < K)
    (hbad : ∀ m, m < j → omega ∈ CoreStopped.levelBad r t s
      (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
        (centre n base) omega)
      (centre n base) y (axis y) (sign y) q eps m) :
    Stopped.revealSet d r t s
        (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
          (centre n base) omega)
        (centre n base) (axis y) (sign y) j ⊆
      ((phase (d := d) A r t s K n q eps axis sign).run base (j + 1)
        ((phase (d := d) A r t s K n q eps axis sign).reveal base base omega)
        omega).inspected := by
  classical
  let Rph := phase (d := d) A r t s K n q eps axis sign
  let first := Rph.reveal base base omega
  have hfirstComp : Compatible base omega first := by
    simpa only [first, Rph, ABDAdaptReg.RevealPhase.run_succ,
      ABDAdaptReg.RevealPhase.run_zero] using
        (compatible_run A r t s K n q eps axis sign base 1 omega)
  have hfirstIn : incomingRegion r t n q eps base ⊆ first.inspected := by
    simpa only [first, Rph, ABDAdaptReg.RevealPhase.run_succ,
      ABDAdaptReg.RevealPhase.run_zero] using
        (incoming_complete_after_first A r t s K n q eps axis sign base omega)
  induction j with
  | zero =>
      let current := first
      have hready : ready r t s n q eps axis sign base current y 0 := by
        intro m hm
        exact (Finset.notMem_empty m hm).elim
      intro x hx
      rw [run_succ_last, ABDAdaptReg.RevealPhase.run_zero,
        ABDAdaptReg.RevealPhase.reveal,
        BDDom.Transcript.step_inspected, Finset.mem_union]
      by_cases hxold : x ∈ current.inspected
      · exact Or.inl hxold
      · apply Or.inr
        change x ∈ region r t s K n q eps axis sign base current
        rw [region, if_pos (by simpa only [current] using hfirstIn),
          outgoingRegion, Finset.mem_biUnion]
        refine ⟨y, hy, ?_⟩
        rw [headRegion, Finset.mem_biUnion]
        refine ⟨0, Finset.mem_range.2 hjK, ?_⟩
        rw [if_pos hready, Finset.mem_sdiff]
        have hinEq := incomingTr_eq_outer_of_compatible hfirstComp hfirstIn
        rw [hinEq]
        exact ⟨hx, hxold⟩

  | succ j ih =>
      let current := Rph.run base (j + 1) first omega
      have hcurComp : Compatible base omega current :=
        compatible_run_from A r t s K n q eps axis sign hfirstComp (j + 1)
      have hcurIn : incomingRegion r t n q eps base ⊆ current.inspected :=
        hfirstIn.trans (run_recordExtends_initial A r t s K n q eps axis sign
          base first (j + 1) omega).1
      have hprev : Stopped.revealSet d r t s
          (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
            (centre n base) omega)
          (centre n base) (axis y) (sign y) j ⊆ current.inspected := by
        simpa only [current] using ih (by omega) (fun m hm => hbad m (by omega))
      have hready : ready r t s n q eps axis sign base current y (j + 1) := by
        intro m hm
        have hmj : m ≤ j := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
        have hreadOuter := (revealSet_mono_any hmj).trans hprev
        have hinEq := incomingTr_eq_outer_of_compatible hcurComp hcurIn
        have hreadCurrent : Stopped.revealSet d r t s
            (incomingTr r t n q eps base current) (centre n base)
            (axis y) (sign y) m ⊆ current.inspected := by
          rwa [hinEq]
        exact ⟨hreadCurrent,
          (mem_levelBad_iff_outer_of_compatible hcurComp hcurIn hreadCurrent).2
            (hbad m (by simpa only [Finset.mem_range] using hm))⟩
      intro x hx
      rw [run_succ_last, ABDAdaptReg.RevealPhase.reveal,
        BDDom.Transcript.step_inspected, Finset.mem_union]
      by_cases hxold : x ∈ current.inspected
      · exact Or.inl hxold
      · apply Or.inr
        change x ∈ region r t s K n q eps axis sign base current
        rw [region, if_pos hcurIn, outgoingRegion, Finset.mem_biUnion]
        refine ⟨y, hy, ?_⟩
        rw [headRegion, Finset.mem_biUnion]
        refine ⟨j + 1, Finset.mem_range.2 hjK, ?_⟩
        rw [if_pos hready, Finset.mem_sdiff]
        have hinEq := incomingTr_eq_outer_of_compatible hcurComp hcurIn
        rw [hinEq]
        exact ⟨hx, hxold⟩

theorem prior_levelBad_of_lt_stopLevel
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : Int} {q : unitInterval} {eps : Real}
    {omega : SiteConfig (Site d)}
    (hgood : omega ∉ CoreStopped.noGoodLevel r t s h z y i sigma q eps K)
    {m : Nat}
    (hm : m < CoreStopped.stopLevel r t s h z y i sigma q eps K omega) :
    omega ∈ CoreStopped.levelBad r t s h z y i sigma q eps m := by
  classical
  have hex := CoreStopped.exists_good_of_notMem_noGoodLevel hgood
  rw [CoreStopped.stopLevel, dif_pos hex] at hm
  by_contra hmbad
  exact (Nat.find_min hex hm) ⟨by
    exact hm.trans (Nat.find_spec hex).1, hmbad⟩

theorem notMem_levelBad_stopLevel
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : Int} {q : unitInterval} {eps : Real}
    {omega : SiteConfig (Site d)}
    (hgood : omega ∉ CoreStopped.noGoodLevel r t s h z y i sigma q eps K) :
    omega ∉ CoreStopped.levelBad r t s h z y i sigma q eps
      (CoreStopped.stopLevel r t s h z y i sigma q eps K omega) := by
  classical
  have hex := CoreStopped.exists_good_of_notMem_noGoodLevel hgood
  rw [CoreStopped.stopLevel, dif_pos hex]
  exact (Nat.find_spec hex).2

theorem outer_stop_revealSet_subset_final
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d))
    {y : Site 2} (hy : y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base))
    (hgood : omega ∉ CoreStopped.noGoodLevel r t s
      (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
        (centre n base) omega)
      (centre n base) y (axis y) (sign y) q eps K) :
    Stopped.revealSet d r t s
        (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
          (centre n base) omega)
        (centre n base) (axis y) (sign y)
        (CoreStopped.stopLevel r t s
          (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
            (centre n base) omega)
          (centre n base) y (axis y) (sign y) q eps K omega) ⊆
      ((phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega).inspected := by
  let ell := CoreStopped.stopLevel r t s
    (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
      (centre n base) omega)
    (centre n base) y (axis y) (sign y) q eps K omega
  have hellK : ell < K := CoreStopped.stopLevel_lt hgood
  have hprefix := revealSet_subset_after_outgoing_rounds A r t s K n q eps axis sign
    base omega hy ell hellK (fun m hm => prior_levelBad_of_lt_stopLevel hgood hm)
  have hmono := run_inspected_mono A r t s K n q eps axis sign base
    ((phase (d := d) A r t s K n q eps axis sign).reveal base base omega) omega
    (show ell + 1 ≤ K by omega)
  change _ ⊆ ((phase (d := d) A r t s K n q eps axis sign).run base K
    ((phase (d := d) A r t s K n q eps axis sign).reveal base base omega) omega).inspected
  exact hprefix.trans hmono

theorem incomingRegion_subset_batchReadSupport
    (r t n : Nat) (q : unitInterval) (eps : Real) (base : Tr d) :
    incomingRegion r t n q eps base ⊆
      CoreRes.batchReadSupport d r t base.base (owner r t q eps n base) (centre n base) :=
  CoreBatchFullReveal.incomingRegion_subset_batchReadSupport
    d r t base.base (owner r t q eps n base) (centre n base)

/-- Every query chosen by the scheduler lies in the allocated batch support. -/
theorem region_subset_batchReadSupport
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    {base k : Tr d}
    (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      (MacroExp.emb (y - centre n base) : Site d) = Pi.single (axis y) (sign y)) :
    region r t s K n q eps axis sign base k ⊆
      CoreRes.batchReadSupport d r t base.base (owner r t q eps n base) (centre n base) := by
  classical
  have hzbd : centre n base ∈ base.boundary (zdGraph 2) (box 2 n) 0 := by
    exact MacroExp.pendZ_mem d n (MacroExp.boundary_nonempty_of_not_terminal d n hactive)
  have hzfront : CoreFrontier.Frontier base.base (centre n base) :=
    CoreAcceptedTransition.frontier_of_mem_boundary hadm.sound hzbd
  have hw := owner_spec hadm.preReveal.frontier hzfront
  have hwz : owner r t q eps n base ≠ centre n base := by
    intro heq
    have hzopen : centre n base ∈ base.openV := heq ▸ hw.1
    exact ((MacroExp.mem_pending (d := d)).1 hw.2.1).2
      (Finset.mem_union_left _ hzopen)
  unfold region
  split_ifs with hin
  · intro x hx
    rw [outgoingRegion, Finset.mem_biUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [headRegion, Finset.mem_biUnion] at hxy
    obtain ⟨j, hj, hxj⟩ := hxy
    split at hxj
    · exact CoreBatchFullReveal.revealSet_subset_batchReadSupport
        (q := q) (eps := eps) hd hr hrt hs hbudget hwz hy
          (hsigma y hy) (hemb y hy)
          (↑k.openSites : Set (Site d)) (Finset.mem_range.1 hj)
          (Finset.sdiff_subset hxj)
    · exact (Finset.notMem_empty x hxj).elim
  · exact (Finset.sdiff_subset : incomingRegion r t n q eps base \ k.inspected ⊆
        incomingRegion r t n q eps base) |>.trans
      (incomingRegion_subset_batchReadSupport r t n q eps base)

/-- Every intermediate and final read stays in the old inspected set plus the allocated batch
support.  This is the exact containment consumed by the tagged-cover update. -/
theorem run_inspected_subset
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    {base : Tr d}
    (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      (MacroExp.emb (y - centre n base) : Site d) = Pi.single (axis y) (sign y))
    (m : Nat) (omega : SiteConfig (Site d)) :
    ((phase (d := d) (box 2 n) r t s K n q eps axis sign).run base m base omega).inspected ⊆
      base.inspected ∪
        CoreRes.batchReadSupport d r t base.base
          (owner r t q eps n base) (centre n base) := by
  let Rph := phase (d := d) (box 2 n) r t s K n q eps axis sign
  let S := CoreRes.batchReadSupport d r t base.base
    (owner r t q eps n base) (centre n base)
  have hreg : ∀ k, region r t s K n q eps axis sign base k ⊆ S := by
    intro k
    exact region_subset_batchReadSupport hd hr hrt hs hbudget hadm hactive hsigma hemb
  have aux : ∀ m (k : Tr d), k.inspected ⊆ base.inspected ∪ S →
      (Rph.run base m k omega).inspected ⊆ base.inspected ∪ S := by
    intro m
    induction m with
    | zero =>
        intro k hk
        simpa only [ABDAdaptReg.RevealPhase.run_zero] using hk
    | succ m ih =>
        intro k hk
        rw [ABDAdaptReg.RevealPhase.run_succ]
        apply ih
        intro x hx
        rw [ABDAdaptReg.RevealPhase.reveal, BDDom.Transcript.step_inspected,
          Finset.mem_union] at hx
        exact hx.elim (fun hxI => hk hxI)
          (fun hxR => Finset.mem_union_right _ (hreg k hxR))
  exact aux m base (Finset.subset_union_left)

/-- Reachability-strengthened phase states also satisfy read containment.  Unlike a statement
about arbitrary equal-verdict transcripts, this is strong enough for every quantified phase state
in `ABDAdaptReg.Exploration.commit_admissible`. -/
theorem inspected_subset_of_phase
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    {base k : Tr d}
    (hk : PhaseRel (box 2 n) r t s K n q eps axis sign base k)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      (MacroExp.emb (y - centre n base) : Site d) = Pi.single (axis y) (sign y)) :
    k.inspected ⊆ base.inspected ∪
      CoreRes.batchReadSupport d r t base.base
        (owner r t q eps n base) (centre n base) := by
  have hadm := PhaseRel.admissible_base hk
  induction hk with
  | start _ => exact Finset.subset_union_left
  | @step current hcurrent omega ih =>
      intro x hx
      rw [BDDom.Transcript.step_inspected, Finset.mem_union] at hx
      exact hx.elim (fun hxI => ih hxI) (fun hxR => Finset.mem_union_right _
        (region_subset_batchReadSupport hd hr hrt hs hbudget hadm hactive hsigma hemb hxR))

/-- Every old live reservation not aimed at the examined centre persists through an arbitrary
reachable scheduler prefix. -/
theorem oldLive_bound_of_phase
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    {base k : Tr d}
    (hk : PhaseRel (box 2 n) r t s K n q eps axis sign base k)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      (MacroExp.emb (y - centre n base) : Site d) = Pi.single (axis y) (sign y))
    {u y : Site 2} (hold : CoreTaggedCover.Live r t q eps base.base (u, y))
    (hyz : y ≠ centre n base) : CoreRes.Bound r t q eps k.base u y := by
  have hadm := PhaseRel.admissible_base hk
  have hzbd : centre n base ∈ base.boundary (zdGraph 2) (box 2 n) 0 :=
    MacroExp.pendZ_mem d n (MacroExp.boundary_nonempty_of_not_terminal d n hactive)
  have hzfront := CoreAcceptedTransition.frontier_of_mem_boundary hadm.sound hzbd
  have hw := owner_spec hadm.preReveal.frontier hzfront
  induction hk with
  | start _ => exact hold.2.2
  | @step current hcurrent omega ih =>
      apply CoreRes.bound_damageStep_of_disjoint r t q eps current u y 0
        (region r t s K n q eps axis sign base current) ∅ true omega
      · exact (phase (d := d) (box 2 n) r t s K n q eps axis sign).region_fresh
          base current hcurrent
      · exact CoreRes.readSubset_disjoint_oldLive hd hr
          (region_subset_batchReadSupport hd hr hrt hs hbudget hadm hactive hsigma hemb)
          hw.1 hw.2.1 hold hyz
      · exact ih

/-- Distinct outgoing heads cannot stale one another's reservations.  This is the exact geometric
step used in the manuscript after a direction has stopped: every later selected stub is contained
in its own live edge region, and that region is disjoint from the earlier head's `E(z,y)`. -/
theorem distinct_newHead_liveRegion_disjoint
    (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r) {h : MacroExp.Tr d}
    {z y v : Site 2}
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z)
    (hv : v ∈ CoreFrontier.newHeads (d := d) h z) (hvy : v ≠ y) :
    Disjoint (CoreFresh.liveRegion d r t z v) (MacroExp.E d r t z y) := by
  have haz : (zdGraph 2).Adj z v :=
    MacroExp.adj_of_mem_nbrs
      ((MacroExp.mem_pending (d := d)).1 ((CoreFrontier.mem_newHeads (d := d)).1 hv).1).1
  have hay : (zdGraph 2).Adj z y :=
    MacroExp.adj_of_mem_nbrs
      ((MacroExp.mem_pending (d := d)).1 ((CoreFrontier.mem_newHeads (d := d)).1 hy).1).1
  have hrev : ¬ (z = y ∧ v = z) := by
    rintro ⟨hzy, -⟩
    subst y
    exact (SimpleGraph.irrefl _) hay
  exact (MacroExp.protectedEdges_disjoint hd r t hr haz hay hvy hrev).mono_left
    Finset.sdiff_subset

/-- Final-run specialization of `run_inspected_subset`. -/
theorem final_inspected_subset
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    {base : Tr d}
    (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      (MacroExp.emb (y - centre n base) : Site d) = Pi.single (axis y) (sign y))
    (omega : SiteConfig (Site d)) :
    ((phase (d := d) (box 2 n) r t s K n q eps axis sign).run base
      ((phase (d := d) (box 2 n) r t s K n q eps axis sign).rounds base)
      base omega).inspected ⊆
      base.inspected ∪ MacroExp.E d r t (owner r t q eps n base) (centre n base) ∪
        CoreTaggedCover.liveRegions d r t
          (CoreCoverUpdate.newEdges base.base (centre n base)) := by
  rw [phase_rounds]
  simpa only [CoreRes.batchReadSupport, Finset.union_assoc] using
    run_inspected_subset hd hr hrt hs hbudget hadm hactive hsigma hemb (K + 1) omega

/-! ## Terminal verdict and delivered stopped reservations -/

def stoppedTr (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) (y : Site 2) : MacroExp.Tr d :=
  Stopped.levelTr d r t s (incomingTr r t n q eps base k)
    (centre n base) (axis y) (sign y)
    (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
      (centre n base) y (axis y) (sign y) q eps K
      (↑k.openSites : Set (Site d)))
    (↑k.openSites : Set (Site d))

theorem stoppedTr_inspected
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) (y : Site 2) :
    (stoppedTr r t s K n q eps axis sign base k y).inspected =
      base.inspected ∪ MacroExp.E d r t (owner r t q eps n base) (centre n base) ∪
        Stopped.stub (MacroExp.ctr d r (centre n base)) (axis y) (sign y) r t
          (10 * s * CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
            (centre n base) y (axis y) (sign y) q eps K
            (↑k.openSites : Set (Site d))) := by
  rw [stoppedTr, Stopped.levelTr_inspected, incomingTr,
    AtomTower.incomingTr_inspected]

theorem stopLevel_notMem_levelBad
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {base k : Tr d} {y : Site 2}
    (hgood : (↑k.openSites : Set (Site d)) ∉
      CoreStopped.noGoodLevel r t s (incomingTr r t n q eps base k)
        (centre n base) y (axis y) (sign y) q eps K) :
    (↑k.openSites : Set (Site d)) ∉
      CoreStopped.levelBad r t s (incomingTr r t n q eps base k)
        (centre n base) y (axis y) (sign y) q eps
        (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
          (centre n base) y (axis y) (sign y) q eps K
          (↑k.openSites : Set (Site d))) := by
  classical
  have hex := CoreStopped.exists_good_of_notMem_noGoodLevel hgood
  rw [CoreStopped.stopLevel, dif_pos hex]
  exact (Nat.find_spec hex).2

theorem incomingTr_state_agree
    {r t n : Nat} {q : unitInterval} {eps : Real} {base k : Tr d}
    (hext : RecordExtends k base)
    (hin : incomingRegion r t n q eps base ⊆ k.inspected) :
    ∀ x ∈ (incomingTr r t n q eps base k).inspected,
      (k.state x ↔ (incomingTr r t n q eps base k).state x) := by
  classical
  intro x hx
  have hxU : x ∈ base.inspected ∪
      MacroExp.E d r t (owner r t q eps n base) (centre n base) := by
    simpa only [incomingTr, AtomTower.incomingTr_inspected] using hx
  rw [incomingTr, AtomTower.incomingTr, FRDom.Transcript.step_state]
  constructor
  · intro hkx
    by_cases hxbase : x ∈ base.inspected
    · exact Or.inl ((hext.2 x hxbase).mp hkx)
    · apply Or.inr
      refine ⟨?_, hkx⟩
      rw [AtomTower.incomingRegion, Finset.mem_sdiff]
      exact ⟨(Finset.mem_union.1 hxU).resolve_left hxbase, hxbase⟩
  · rintro (hbase | ⟨-, hkx⟩)
    · exact (hext.2 x (base.base.mem_inspected_of_state hbase)).mpr hbase
    · exact hkx

theorem stoppedTr_state_agree
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {base k : Tr d} {y : Site 2}
    (hext : RecordExtends k base)
    (hin : incomingRegion r t n q eps base ⊆ k.inspected) :
    ∀ x ∈ (stoppedTr r t s K n q eps axis sign base k y).inspected,
      (k.state x ↔ (stoppedTr r t s K n q eps axis sign base k y).state x) := by
  classical
  intro x hx
  let hIn := incomingTr r t n q eps base k
  let ell := CoreStopped.stopLevel r t s hIn (centre n base) y
    (axis y) (sign y) q eps K (↑k.openSites : Set (Site d))
  have hxU : x ∈ hIn.inspected ∪
      Stopped.stub (MacroExp.ctr d r (centre n base)) (axis y) (sign y) r t
        (10 * s * ell) := by
    simpa only [stoppedTr, hIn, ell, Stopped.levelTr_inspected] using hx
  have hInAgree := incomingTr_state_agree hext hin
  change k.state x ↔ (Stopped.levelTr d r t s hIn (centre n base)
    (axis y) (sign y) ell (↑k.openSites : Set (Site d))).state x
  rw [Stopped.levelTr, FRDom.Transcript.step_state]
  constructor
  · intro hkx
    by_cases hxIn : x ∈ hIn.inspected
    · exact Or.inl ((hInAgree x hxIn).mp hkx)
    · apply Or.inr
      refine ⟨?_, hkx⟩
      rw [Stopped.revealSet, Finset.mem_sdiff]
      exact ⟨(Finset.mem_union.1 hxU).resolve_left hxIn, hxIn⟩
  · rintro (hOld | ⟨-, hkx⟩)
    · exact (hInAgree x (hIn.mem_inspected_of_state hOld)).mpr hOld
    · exact hkx

theorem stoppedTr_inspected_subset
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {base k : Tr d} {y : Site 2}
    (hext : RecordExtends k base)
    (hin : incomingRegion r t n q eps base ⊆ k.inspected)
    (hlevel : Stopped.revealSet d r t s (incomingTr r t n q eps base k)
      (centre n base) (axis y) (sign y)
      (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
        (centre n base) y (axis y) (sign y) q eps K
        (↑k.openSites : Set (Site d))) ⊆ k.inspected) :
    (stoppedTr r t s K n q eps axis sign base k y).inspected ⊆ k.inspected := by
  intro x hx
  rw [stoppedTr, Stopped.levelTr, FRDom.Transcript.step_inspected,
    Finset.mem_union] at hx
  rcases hx with hxIn | hxLevel
  · rw [incomingTr, AtomTower.incomingTr_inspected] at hxIn
    rcases Finset.mem_union.1 hxIn with hxbase | hxE
    · exact hext.1 hxbase
    · by_cases hxbase : x ∈ base.inspected
      · exact hext.1 hxbase
      · apply hin
        rw [incomingRegion, AtomTower.incomingRegion, Finset.mem_sdiff]
        exact ⟨hxE, hxbase⟩
  · exact hlevel hxLevel

/-- Stopped-history induction.  Against any later extension carrying a good final level, every
site read by a reachable prefix which lies in the protected edge of `y` already belongs to the
final first-good stopped transcript.  The `v = y` branch is the no-same-head-suffix argument;
`v ≠ y` is discharged by protected-edge disjointness. -/
theorem phase_inspected_sdiff_stoppedTr_disjoint
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    {base k later : Tr d}
    (hk : PhaseRel (box 2 n) r t s K n q eps axis sign base k)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hsigma : ∀ v ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      sign v = 1 ∨ sign v = -1)
    (hemb : ∀ v ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      (MacroExp.emb (v - centre n base) : Site d) = Pi.single (axis v) (sign v))
    {y : Site 2} (hy : y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base))
    (hext : RecordExtends later k)
    (hinLater : incomingRegion r t n q eps base ⊆ later.inspected)
    (hgood : (↑later.openSites : Set (Site d)) ∉
      CoreStopped.noGoodLevel r t s (incomingTr r t n q eps base later)
        (centre n base) y (axis y) (sign y) q eps K) :
    Disjoint (k.inspected \ (stoppedTr r t s K n q eps axis sign base later y).inspected)
      (MacroExp.E d r t (centre n base) y) := by
  classical
  have hadm := PhaseRel.admissible_base hk
  have hzbd : centre n base ∈ base.boundary (zdGraph 2) (box 2 n) 0 :=
    MacroExp.pendZ_mem d n (MacroExp.boundary_nonempty_of_not_terminal d n hactive)
  have hzfront : CoreFrontier.Frontier base.base (centre n base) :=
    CoreAcceptedTransition.frontier_of_mem_boundary hadm.sound hzbd
  have hw := owner_spec hadm.preReveal.frontier hzfront
  have hwz : owner r t q eps n base ≠ centre n base := by
    intro heq
    have hzopen : centre n base ∈ base.openV := heq ▸ hw.1
    exact ((MacroExp.mem_pending (d := d)).1 hw.2.1).2
      (Finset.mem_union_left _ hzopen)
  rw [Finset.disjoint_left]
  intro x hx xE
  rw [Finset.mem_sdiff] at hx
  induction hk generalizing later with
  | start hadm =>
      exact hx.2 (by
        rw [stoppedTr_inspected]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hx.1))
  | @step current hcurrent omega ih =>
      have hstepExt : RecordExtends
          (current.step 0 (region r t s K n q eps axis sign base current) ∅ true omega)
          current :=
        recordExtends_step current 0 _ ∅ true omega
          (region_fresh r t s K n q eps axis sign base current)
      have hcurExt : RecordExtends later current := recordExtends_trans hext hstepExt
      have hxmem := hx.1
      rw [BDDom.Transcript.step_inspected, Finset.mem_union] at hxmem
      rcases hxmem with hxold | hxreg
      · exact ih hcurExt hinLater hgood ⟨hxold, hx.2⟩
      · unfold region at hxreg
        split at hxreg
        next hinCurrent =>
          rw [outgoingRegion, Finset.mem_biUnion] at hxreg
          obtain ⟨v, hv, hxv⟩ := hxreg
          rw [headRegion, Finset.mem_biUnion] at hxv
          obtain ⟨j, hj, hxj⟩ := hxv
          split at hxj
          next hready =>
            have hxReveal : x ∈ Stopped.revealSet d r t s
                (incomingTr r t n q eps base current) (centre n base)
                (axis v) (sign v) j := (Finset.mem_sdiff.1 hxj).1
            by_cases hvy : v = y
            · subst v
              have hinEq := incomingTr_eq_of_recordExtends hinCurrent hcurExt
              let ell := CoreStopped.stopLevel r t s
                (incomingTr r t n q eps base later) (centre n base) y
                (axis y) (sign y) q eps K (↑later.openSites : Set (Site d))
              have hjell : j ≤ ell := by
                by_contra hnot
                have hellj : ell < j := Nat.lt_of_not_ge hnot
                have hreadyEll := hready ell (Finset.mem_range.2 hellj)
                have hbadCurrent := hreadyEll.2
                have hbadCurrent' : (↑current.openSites : Set (Site d)) ∈
                    CoreStopped.levelBad r t s (incomingTr r t n q eps base later)
                      (centre n base) y (axis y) (sign y) q eps ell := by
                  rwa [hinEq] at hbadCurrent
                have hagree :
                    (↑current.openSites : Set (Site d)) ∩
                        ↑(Stopped.revealSet d r t s
                          (incomingTr r t n q eps base later) (centre n base)
                          (axis y) (sign y) ell) =
                      (↑later.openSites : Set (Site d)) ∩
                        ↑(Stopped.revealSet d r t s
                          (incomingTr r t n q eps base later) (centre n base)
                          (axis y) (sign y) ell) := by
                  ext a
                  simp only [Set.mem_inter_iff, Finset.mem_coe]
                  constructor
                  · rintro ⟨haopen, haR⟩
                    exact ⟨(hcurExt.2 a (by
                      rw [← hinEq] at haR
                      exact hreadyEll.1 haR)).mpr haopen, haR⟩
                  · rintro ⟨haopen, haR⟩
                    exact ⟨(hcurExt.2 a (by
                      rw [← hinEq] at haR
                      exact hreadyEll.1 haR)).mp haopen, haR⟩
                have hbadLater : (↑later.openSites : Set (Site d)) ∈
                    CoreStopped.levelBad r t s (incomingTr r t n q eps base later)
                      (centre n base) y (axis y) (sign y) q eps ell :=
                  ((determinedBy_iff _ _).1
                    (CoreStopped.determinedBy_levelBad r t s
                      (incomingTr r t n q eps base later) (centre n base) y
                      (axis y) (sign y) q eps ell)
                    _ _ hagree).mp hbadCurrent'
                exact (stopLevel_notMem_levelBad hgood) hbadLater
              apply hx.2
              rw [stoppedTr_inspected]
              apply Finset.mem_union_right
              have hxReveal' : x ∈ Stopped.revealSet d r t s
                  (incomingTr r t n q eps base later) (centre n base)
                  (axis y) (sign y) j := by rwa [← hinEq]
              exact Finset.sdiff_subset (revealSet_mono_any hjell hxReveal')
            · have hQ : MacroExp.Q d r t (centre n base) ⊆
                  (incomingTr r t n q eps base current).inspected := by
                intro a ha
                rw [incomingTr, AtomTower.incomingTr_inspected]
                exact Finset.mem_union_right _ (CorrMove.Q_subset_E hd r t hr hwz ha)
              have hjdepth : 10 * s * j < 10 * r := by
                have hjK := Finset.mem_range.1 hj
                have : 10 * s * j < 10 * s * K :=
                  Nat.mul_lt_mul_of_pos_left hjK (by omega)
                omega
              have hxLive : x ∈ CoreFresh.liveRegion d r t (centre n base) v :=
                CoreFresh.freshStub_subset_liveRegion hr hrt hjdepth (hsigma v hv)
                  (hemb v hv) hQ hxReveal
              exact Finset.disjoint_left.1
                (distinct_newHead_liveRegion_disjoint hd hr hy hv hvy) hxLive xE
          next _ => exact (Finset.notMem_empty x hxj).elim
        next _ =>
          exact hx.2 (by
            rw [stoppedTr_inspected]
            apply Finset.mem_union_left
            apply Finset.mem_union_right
            have hi : x ∈ incomingRegion r t n q eps base := Finset.sdiff_subset hxreg
            simpa only [incomingRegion, AtomTower.incomingRegion] using
              (Finset.sdiff_subset hi))

/-- A head is finished precisely when a good level exists and its selected first-good prefix has
actually been read.  The second conjunct prevents a verdict from consulting any uninspected bit. -/
def headDone (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) (y : Site 2) : Prop :=
  let hin := incomingTr r t n q eps base k
  let omega : SiteConfig (Site d) := ↑k.openSites
  omega ∉ CoreStopped.noGoodLevel r t s hin (centre n base) y
      (axis y) (sign y) q eps K ∧
    Stopped.revealSet d r t s hin (centre n base) (axis y) (sign y)
      (CoreStopped.stopLevel r t s hin (centre n base) y
        (axis y) (sign y) q eps K omega) ⊆ k.inspected

theorem headDone_final_of_outer_good
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d))
    {y : Site 2} (hy : y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base))
    (hgood : omega ∉ CoreStopped.noGoodLevel r t s
      (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
        (centre n base) omega)
      (centre n base) y (axis y) (sign y) q eps K) :
    headDone r t s K n q eps axis sign base
      ((phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega) y := by
  classical
  let final := (phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega
  let houter := AtomTower.incomingTr d r t base.base (owner r t q eps n base)
    (centre n base) omega
  let ell := CoreStopped.stopLevel r t s houter (centre n base) y
    (axis y) (sign y) q eps K omega
  have hcomp : Compatible base omega final := by
    simpa only [final] using compatible_run A r t s K n q eps axis sign base (K + 1) omega
  have hin : incomingRegion r t n q eps base ⊆ final.inspected := by
    simpa only [final] using incoming_complete_final A r t s K n q eps axis sign base omega
  have hinEq : incomingTr r t n q eps base final = houter := by
    simpa only [houter] using incomingTr_eq_outer_of_compatible hcomp hin
  have hreadOuter : Stopped.revealSet d r t s houter (centre n base)
      (axis y) (sign y) ell ⊆ final.inspected := by
    simpa only [final, houter, ell] using
      outer_stop_revealSet_subset_final A r t s K n q eps axis sign base omega hy hgood
  have hreadFinal : Stopped.revealSet d r t s (incomingTr r t n q eps base final)
      (centre n base) (axis y) (sign y) ell ⊆ final.inspected := by
    rwa [hinEq]
  have hfinalGoodEll : (↑final.openSites : Set (Site d)) ∉
      CoreStopped.levelBad r t s (incomingTr r t n q eps base final)
        (centre n base) y (axis y) (sign y) q eps ell := by
    exact ((mem_levelBad_iff_outer_of_compatible hcomp hin hreadFinal).not).2
      (notMem_levelBad_stopLevel hgood)
  have hellK : ell < K := CoreStopped.stopLevel_lt hgood
  have hfinalGood : (↑final.openSites : Set (Site d)) ∉
      CoreStopped.noGoodLevel r t s (incomingTr r t n q eps base final)
        (centre n base) y (axis y) (sign y) q eps K := by
    intro hall
    exact hfinalGoodEll ((Stopped.mem_allBad_iff _ K _).1 hall ell hellK)
  let ellFinal := CoreStopped.stopLevel r t s (incomingTr r t n q eps base final)
    (centre n base) y (axis y) (sign y) q eps K
    (↑final.openSites : Set (Site d))
  have hstopEq : ellFinal = ell := by
    apply Nat.le_antisymm
    · by_contra hnot
      have hell : ell < ellFinal := Nat.lt_of_not_ge hnot
      exact hfinalGoodEll (prior_levelBad_of_lt_stopLevel hfinalGood hell)
    · by_contra hnot
      have hlt : ellFinal < ell := Nat.lt_of_not_ge hnot
      have hreadFinalStop : Stopped.revealSet d r t s
          (incomingTr r t n q eps base final) (centre n base)
          (axis y) (sign y) ellFinal ⊆ final.inspected := by
        have hm := (revealSet_mono_any (Nat.le_of_lt hlt)).trans hreadOuter
        rwa [← hinEq] at hm
      have hbadOuter : omega ∈ CoreStopped.levelBad r t s houter
          (centre n base) y (axis y) (sign y) q eps ellFinal :=
        prior_levelBad_of_lt_stopLevel hgood hlt
      have hbadFinal := (mem_levelBad_iff_outer_of_compatible hcomp hin hreadFinalStop).2
        (by simpa only [houter] using hbadOuter)
      exact (notMem_levelBad_stopLevel hfinalGood) (by simpa only [ellFinal] using hbadFinal)
  have hdoneFinal : headDone r t s K n q eps axis sign base final y := by
    refine ⟨hfinalGood, ?_⟩
    change Stopped.revealSet d r t s (incomingTr r t n q eps base final)
      (centre n base) (axis y) (sign y) ellFinal ⊆ final.inspected
    rw [hstopEq]
    exact hreadFinal
  simpa only [final] using hdoneFinal

theorem outer_good_of_headDone_final
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d))
    {y : Site 2}
    (hdone : headDone r t s K n q eps axis sign base
      ((phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega) y) :
    omega ∉ CoreStopped.noGoodLevel r t s
      (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
        (centre n base) omega)
      (centre n base) y (axis y) (sign y) q eps K := by
  let final := (phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega
  let ellFinal := CoreStopped.stopLevel r t s (incomingTr r t n q eps base final)
    (centre n base) y (axis y) (sign y) q eps K
    (↑final.openSites : Set (Site d))
  have hcomp : Compatible base omega final := by
    simpa only [final] using compatible_run A r t s K n q eps axis sign base (K + 1) omega
  have hin : incomingRegion r t n q eps base ⊆ final.inspected := by
    simpa only [final] using incoming_complete_final A r t s K n q eps axis sign base omega
  have hdone' : headDone r t s K n q eps axis sign base final y := by
    simpa only [final] using hdone
  have hread : Stopped.revealSet d r t s (incomingTr r t n q eps base final)
      (centre n base) (axis y) (sign y) ellFinal ⊆ final.inspected := by
    simpa only [ellFinal] using hdone'.2
  have houterGood : omega ∉ CoreStopped.levelBad r t s
      (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
        (centre n base) omega)
      (centre n base) y (axis y) (sign y) q eps ellFinal :=
    ((mem_levelBad_iff_outer_of_compatible hcomp hin hread).not).mp
      (notMem_levelBad_stopLevel hdone'.1)
  intro hall
  exact houterGood ((Stopped.mem_allBad_iff _ K _).1 hall ellFinal
    (CoreStopped.stopLevel_lt hdone'.1))

theorem headDone_final_iff_outer_good
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d))
    {y : Site 2} (hy : y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base)) :
    headDone r t s K n q eps axis sign base
        ((phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega) y ↔
      omega ∉ CoreStopped.noGoodLevel r t s
        (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
          (centre n base) omega)
        (centre n base) y (axis y) (sign y) q eps K :=
  ⟨outer_good_of_headDone_final A r t s K n q eps axis sign base omega,
    headDone_final_of_outer_good A r t s K n q eps axis sign base omega hy⟩

theorem incomingTr_substitute_eq
    (r t n : Nat) (q : unitInterval) (eps : Real)
    (base : Tr d) (omega : SiteConfig (Site d)) :
    AtomTower.incomingTr d r t base.base (owner r t q eps n base) (centre n base)
        (substitute (↑base.inspected : Set (Site d)) base.state omega) =
      AtomTower.incomingTr d r t base.base (owner r t q eps n base) (centre n base) omega := by
  apply FRDom.Transcript.step_congr
  intro x hx
  rw [mem_substitute_of_notMem]
  exact fun hxbase => (Finset.mem_sdiff.1 hx).2 hxbase

theorem noGoodLevel_substitute_iff
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d)) (y : Site 2) :
    substitute (↑base.inspected : Set (Site d)) base.state omega ∈
        CoreStopped.noGoodLevel r t s
          (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
            (centre n base)
            (substitute (↑base.inspected : Set (Site d)) base.state omega))
          (centre n base) y (axis y) (sign y) q eps K ↔
      omega ∈ CoreStopped.noGoodLevel r t s
        (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
          (centre n base) omega)
        (centre n base) y (axis y) (sign y) q eps K := by
  classical
  rw [incomingTr_substitute_eq]
  unfold CoreStopped.noGoodLevel
  rw [Stopped.mem_allBad_iff, Stopped.mem_allBad_iff]
  have hagree : ∀ j,
      substitute (↑base.inspected : Set (Site d)) base.state omega ∩
          ↑(Stopped.revealSet d r t s
            (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
              (centre n base) omega)
            (centre n base) (axis y) (sign y) j) =
        omega ∩ ↑(Stopped.revealSet d r t s
          (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
            (centre n base) omega)
          (centre n base) (axis y) (sign y) j) := by
    intro j
    ext x
    simp only [Set.mem_inter_iff, Finset.mem_coe]
    apply and_congr_left
    intro hxR
    apply mem_substitute_of_notMem
    intro hxbase
    exact Finset.disjoint_left.1
      (Stopped.revealSet_fresh d r t s
        (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
          (centre n base) omega)
        (centre n base) (axis y) (sign y) j)
      hxR (by
        rw [AtomTower.incomingTr_inspected]
        exact Finset.mem_union_left _ (Finset.mem_coe.1 hxbase))
  constructor <;> intro hall j hj
  · exact (((determinedBy_iff _ _).1
      (CoreStopped.determinedBy_levelBad r t s
        (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
          (centre n base) omega)
        (centre n base) y (axis y) (sign y) q eps j)
      _ _ (hagree j)).mp (hall j hj))
  · exact (((determinedBy_iff _ _).1
      (CoreStopped.determinedBy_levelBad r t s
        (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
          (centre n base) omega)
        (centre n base) y (axis y) (sign y) q eps j)
      _ _ (hagree j)).mpr (hall j hj))

theorem newHead_mem_pending_incomingTr
    {r t n : Nat} {q : unitInterval} {eps : Real} {base : Tr d}
    {y : Site 2}
    (hy : y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base))
    (omega : SiteConfig (Site d)) :
    y ∈ MacroExp.pending d
      (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
        (centre n base) omega)
      (centre n base) := by
  classical
  have hyp := (CoreFrontier.mem_newHeads (d := d)).1 hy |>.1
  rw [MacroExp.mem_pending] at hyp ⊢
  refine ⟨hyp.1, ?_⟩
  intro hyDet
  rw [AtomTower.incomingTr, FRDom.Transcript.step_openV,
    FRDom.Transcript.step_closedV, if_pos rfl] at hyDet
  simp only [Finset.mem_union, Finset.mem_insert] at hyDet
  rcases hyDet with (hyz | hyo) | hyc
  · subst y
    exact (SimpleGraph.irrefl _)
      (MacroExp.adj_of_mem_nbrs hyp.1)
  · exact hyp.2 (Finset.mem_union_left _ hyo)
  · exact hyp.2 (Finset.mem_union_right _ hyc)

theorem incoming_event_final_iff_substitute
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d)) :
    let final := (phase (d := d) A r t s K n q eps axis sign).run
      base (K + 1) base omega
    (↑final.openSites : Set (Site d)) ∈
        CoreRes.event r t base.base (owner r t q eps n base) (centre n base) ↔
      substitute (↑base.inspected : Set (Site d)) base.state omega ∈
        CoreRes.event r t base.base (owner r t q eps n base) (centre n base) := by
  dsimp only
  let final := (phase (d := d) A r t s K n q eps axis sign).run
    base (K + 1) base omega
  have hcomp : Compatible base omega final := by
    simpa only [final] using compatible_run A r t s K n q eps axis sign base (K + 1) omega
  have hin : incomingRegion r t n q eps base ⊆ final.inspected := by
    simpa only [final] using incoming_complete_final A r t s K n q eps axis sign base omega
  unfold CoreRes.event
  let S : Set (Site d) := ↑(base.inspected ∪
    MacroExp.E d r t (owner r t q eps n base) (centre n base))
  let T : Set (Site d) := ↑(CoreRes.target (d := d) r (centre n base))
  refine (determinedBy_iff _ _).1
    (determinedBy_connWithinSet (zdGraph d) S (MacroExp.emb 0) T)
    _ _ ?_
  ext x
  simp only [S, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_union]
  apply and_congr_left
  intro hxDom
  apply compatible_state_iff_substitute hcomp
  rcases hxDom with hxbase | hxE
  · exact hcomp.1.1 hxbase
  · by_cases hxbase : x ∈ base.inspected
    · exact hcomp.1.1 hxbase
    · apply hin
      rw [incomingRegion, AtomTower.incomingRegion, Finset.mem_sdiff]
      exact ⟨hxE, hxbase⟩

/-- The terminal, transcript-valued batch verdict.  The incoming event and every stopped outgoing
reservation must have been decided positively. -/
def verdict (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) : Prop :=
  incomingRegion r t n q eps base ⊆ k.inspected ∧
    (↑k.openSites : Set (Site d)) ∈
        CoreRes.event r t base.base (owner r t q eps n base) (centre n base) ∧
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
        headDone r t s K n q eps axis sign base k y

theorem verdict_final_iff_substitute_batchSuccess
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base : Tr d) (omega : SiteConfig (Site d)) :
    verdict r t s K n q eps axis sign base
        ((phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega) ↔
      substitute (↑base.inspected : Set (Site d)) base.state omega ∈
        CoreBatchTransition.batchSuccess r t s K base.base
          (owner r t q eps n base) (centre n base) axis sign q eps := by
  classical
  let final := (phase (d := d) A r t s K n q eps axis sign).run
    base (K + 1) base omega
  let pinned := substitute (↑base.inspected : Set (Site d)) base.state omega
  have hin : incomingRegion r t n q eps base ⊆ final.inspected := by
    simpa only [final] using incoming_complete_final A r t s K n q eps axis sign base omega
  have hincoming :
      ((↑final.openSites : Set (Site d)) ∈
          CoreRes.event r t base.base (owner r t q eps n base) (centre n base)) ↔
        pinned ∈ CoreRes.event r t base.base (owner r t q eps n base) (centre n base) := by
    simpa only [final, pinned] using
      incoming_event_final_iff_substitute A r t s K n q eps axis sign base omega
  have hdir : ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      headDone r t s K n q eps axis sign base final y ↔
        pinned ∈ CoreStopped.directionEvent r t s
          (AtomTower.incomingTr d r t base.base (owner r t q eps n base)
            (centre n base) pinned)
          (centre n base) y (axis y) (sign y) q eps K := by
    intro y hy
    have hpending := newHead_mem_pending_incomingTr
      (r := r) (t := t) (n := n) (q := q) (eps := eps) (base := base) hy pinned
    rw [CoreStopped.directionEvent]
    simp only [Set.mem_union, Set.mem_setOf_eq, hpending, not_true_eq_false,
      false_or, Set.mem_compl_iff]
    rw [noGoodLevel_substitute_iff]
    exact headDone_final_iff_outer_good A r t s K n q eps axis sign base omega hy
  change (incomingRegion r t n q eps base ⊆ final.inspected ∧
      (↑final.openSites : Set (Site d)) ∈
        CoreRes.event r t base.base (owner r t q eps n base) (centre n base) ∧
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
        headDone r t s K n q eps axis sign base final y) ↔ _
  rw [and_iff_right hin, hincoming]
  unfold CoreBatchTransition.batchSuccess CoreBatchTransition.batchFailure
    CoreBatchTransition.incomingFailure CoreBatchTransition.directionFailure
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq,
    not_or, not_exists, not_not]
  exact and_congr Iff.rfl (forall_congr' fun y => forall_congr' fun hy => hdir y hy)

/-- A constant event carrying the verdict already stored by `k`.  It is deliberately constant:
the reveal tower has finished before `succ` is queried, so determination by `k.inspected` is
immediate and no stale conditional event is transported across a read. -/
def succ (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) : Set (SiteConfig (Site d)) := by
  classical
  exact if verdict r t s K n q eps axis sign base k then Set.univ else ∅

theorem succ_measurable (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int) (base k : Tr d) :
    MeasurableSet (succ r t s K n q eps axis sign base k) := by
  classical
  unfold succ
  split_ifs <;> simp

theorem succ_determinedBy (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int) (base k : Tr d) :
    DeterminedBy (succ r t s K n q eps axis sign base k)
      (↑k.inspected : Set (Site d)) := by
  classical
  unfold succ
  split_ifs
  · exact determinedBy_univ _
  · rw [determinedBy_iff]
    simp

theorem mem_succ_iff_verdict
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) (omega : SiteConfig (Site d)) :
    omega ∈ succ r t s K n q eps axis sign base k ↔
      verdict r t s K n q eps axis sign base k := by
  classical
  unfold succ
  split_ifs <;> simp_all

/-- Exact interpreter equation.  The composite stopped reveal recognizes the pullback of the
pre-reveal batch event along the base transcript's substitution map.  This is the correct event
identity; raw equality with `batchSuccess` would be false away from configurations respecting the
already recorded base bits. -/
theorem compositeSuccess_eq_substitute_preimage_batchSuccess
    (A : Finset (Site 2)) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int) (base : Tr d) :
    {omega : SiteConfig (Site d) |
      omega ∈ succ r t s K n q eps axis sign base
        ((phase (d := d) A r t s K n q eps axis sign).run base (K + 1) base omega)} =
      substitute (↑base.inspected : Set (Site d)) base.state ⁻¹'
        CoreBatchTransition.batchSuccess r t s K base.base
          (owner r t q eps n base) (centre n base) axis sign q eps := by
  ext omega
  rw [Set.mem_setOf_eq, Set.mem_preimage,
    mem_succ_iff_verdict,
    verdict_final_iff_substitute_batchSuccess]

/-- `headDone` invokes the actual first-good level from `CoreStopped`, not an arbitrary later
level. -/
theorem bound_stopLevel_of_headDone
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {base k : Tr d} {y : Site 2}
    (hdone : headDone r t s K n q eps axis sign base k y) :
    CoreRes.Bound r t q eps
      (Stopped.levelTr d r t s (incomingTr r t n q eps base k)
        (centre n base) (axis y) (sign y)
        (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
          (centre n base) y (axis y) (sign y) q eps K
          (↑k.openSites : Set (Site d)))
        (↑k.openSites : Set (Site d)))
      (centre n base) y := by
  exact CoreStopped.bound_stopLevel hdone.1

/-- Order-free persistence from the selected prefix to the final multi-head reveal, followed by
the empty-coordinate macro commit.  The three extension hypotheses are the exact deterministic
facts a concrete run proof must supply; in particular `hextra` says all later heads avoid
`E(z,y)`. -/
theorem bound_after_commit_of_headDone
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {base k : Tr d} {y : Site 2}
    (hdone : headDone r t s K n q eps axis sign base k y)
    (hsub :
      (Stopped.levelTr d r t s (incomingTr r t n q eps base k)
        (centre n base) (axis y) (sign y)
        (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
          (centre n base) y (axis y) (sign y) q eps K
          (↑k.openSites : Set (Site d)))
        (↑k.openSites : Set (Site d))).inspected ⊆ k.inspected)
    (hstate : ∀ x ∈
      (Stopped.levelTr d r t s (incomingTr r t n q eps base k)
        (centre n base) (axis y) (sign y)
        (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
          (centre n base) y (axis y) (sign y) q eps K
          (↑k.openSites : Set (Site d)))
        (↑k.openSites : Set (Site d))).inspected,
      k.state x ↔
        (Stopped.levelTr d r t s (incomingTr r t n q eps base k)
          (centre n base) (axis y) (sign y)
          (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
            (centre n base) y (axis y) (sign y) q eps K
            (↑k.openSites : Set (Site d)))
          (↑k.openSites : Set (Site d))).state x)
    (hextra : Disjoint
      (k.inspected \
        (Stopped.levelTr d r t s (incomingTr r t n q eps base k)
          (centre n base) (axis y) (sign y)
          (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
            (centre n base) y (axis y) (sign y) q eps K
            (↑k.openSites : Set (Site d)))
          (↑k.openSites : Set (Site d))).inspected)
      (MacroExp.E d r t (centre n base) y))
    (damage : Finset (Site 2)) (b : Bool) (commitOmega : SiteConfig (Site d)) :
    CoreRes.Bound r t q eps (k.step (centre n base) ∅ damage b commitOmega).base
      (centre n base) y := by
  have hbound : CoreRes.Bound r t q eps k.base (centre n base) y :=
    CoreRes.bound_stopLevel_of_extension hdone.1 hsub hstate hextra
  exact CoreRes.bound_emptyCommit r t q eps k (centre n base) y
    (centre n base) damage b commitOmega hbound

/-- Compact name for the three order-free extension facts displayed in
`bound_after_commit_of_headDone`. -/
def StopExtension (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    (base k : Tr d) (y : Site 2) : Prop :=
  let st := Stopped.levelTr d r t s (incomingTr r t n q eps base k)
    (centre n base) (axis y) (sign y)
    (CoreStopped.stopLevel r t s (incomingTr r t n q eps base k)
      (centre n base) y (axis y) (sign y) q eps K
      (↑k.openSites : Set (Site d)))
    (↑k.openSites : Set (Site d))
  st.inspected ⊆ k.inspected ∧
    (∀ x ∈ st.inspected, k.state x ↔ st.state x) ∧
    Disjoint (k.inspected \ st.inspected) (MacroExp.E d r t (centre n base) y)

theorem stopExtension_of_phase_verdict
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    {base k : Tr d}
    (hk : PhaseRel (box 2 n) r t s K n q eps axis sign base k)
    (hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hsigma : ∀ v ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      sign v = 1 ∨ sign v = -1)
    (hemb : ∀ v ∈ CoreFrontier.newHeads (d := d) base.base (centre n base),
      (MacroExp.emb (v - centre n base) : Site d) = Pi.single (axis v) (sign v))
    (hverdict : verdict r t s K n q eps axis sign base k)
    {y : Site 2} (hy : y ∈ CoreFrontier.newHeads (d := d) base.base (centre n base)) :
    StopExtension r t s K n q eps axis sign base k y := by
  have hext : RecordExtends k base := PhaseRel.extends_base hk
  have hdone := hverdict.2.2 y hy
  change (stoppedTr r t s K n q eps axis sign base k y).inspected ⊆ k.inspected ∧
    (∀ x ∈ (stoppedTr r t s K n q eps axis sign base k y).inspected,
      k.state x ↔ (stoppedTr r t s K n q eps axis sign base k y).state x) ∧
    Disjoint (k.inspected \ (stoppedTr r t s K n q eps axis sign base k y).inspected)
      (MacroExp.E d r t (centre n base) y)
  exact ⟨stoppedTr_inspected_subset hext hverdict.1 hdone.2,
    stoppedTr_state_agree hext hverdict.1,
    phase_inspected_sdiff_stoppedTr_disjoint hd hr hrt hs hbudget hk hactive hsigma hemb
      hy (recordExtends_refl k) hverdict.1 hdone.1⟩

theorem bound_after_commit_of_stopExtension
    {r t s K n : Nat} {q : unitInterval} {eps : Real}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int}
    {base k : Tr d} {y : Site 2}
    (hdone : headDone r t s K n q eps axis sign base k y)
    (hext : StopExtension r t s K n q eps axis sign base k y)
    (damage : Finset (Site 2)) (b : Bool) (commitOmega : SiteConfig (Site d)) :
    CoreRes.Bound r t q eps (k.step (centre n base) ∅ damage b commitOmega).base
      (centre n base) y := by
  exact bound_after_commit_of_headDone hdone hext.1 hext.2.1 hext.2.2
    damage b commitOmega

#print axioms KNAll.Site.CoreStoppedReveal.region_subset_batchReadSupport
#print axioms KNAll.Site.CoreStoppedReveal.final_inspected_subset
#print axioms KNAll.Site.CoreStoppedReveal.phase_inspected_sdiff_stoppedTr_disjoint
#print axioms KNAll.Site.CoreStoppedReveal.headDone_final_iff_outer_good
#print axioms KNAll.Site.CoreStoppedReveal.verdict_final_iff_substitute_batchSuccess
#print axioms KNAll.Site.CoreStoppedReveal.compositeSuccess_eq_substitute_preimage_batchSuccess
#print axioms KNAll.Site.CoreStoppedReveal.bound_after_commit_of_headDone

end KNAll.Site.CoreStoppedReveal

end
