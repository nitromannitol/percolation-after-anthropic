import Hypergraph.ReachCoupling
import Hypergraph.BoxConnection
import Hypergraph.SiteThetaMono

/-!
# Finite adaptive domination: every finite radius exactly, infinity afterwards

An adaptive exploration of a finite graph examines one undetermined vertex of the frontier of its
explored component at a time, and it stops only when the explored component has reached the target
or when no undetermined frontier vertex is left.  If every examination succeeds with conditional
probability at least `a` given the complete past, then the explored component reaches the target
at least as often as Bernoulli(`a`) site percolation on the same graph joins the root to the target.

No infinite process is constructed.  The comparison is proved on a finite arena by backward
induction on the number of undetermined vertices, and the passage to infinity is a separate step:
the event that the origin of `ℤ^d` is joined inside the box of radius `n` to the inner boundary of
that box contains the event that its open cluster is infinite, so `θ_d(a)` is a lower bound for it
that does not depend on `n`.

## The two warnings this design answers

`KN/BlockGluing.lean` proves `one_le_of_nextBound_of_runJoin`: an exploration that never stops and
whose successes certify a connection to the root cannot have a one-step bound better than the
trivial one, because the transcript reached by running it against the all-closed configuration
records the root closed and every later success has pinned probability zero.  Here the exploration
stops at such a transcript, since its frontier is empty, and the one-step bound is demanded only at
admissible transcripts that are not terminal.  `KN/ReachCoupling.lean` proves `not_reachTransfer`
and documents why a comparison read off Boolean words cannot see a transcript that depends on the
configuration.  Here nothing is read off words: the comparison is between two pinned probabilities
of configuration events, and the conditional-independence calculus that survives from that file,
`pinnedProb_split` and the tower inequality, is all that is used of it.

## The route

Of the two routes in the manuscript, the backward induction is the one carried out.  The coupling
with auxiliary uniforms would need a product with `[0,1]^ℕ` and a thinning argument; the backward
induction needs only the law of total probability at one fresh coordinate, on both sides.  At a
transcript that is not terminal, with examined vertex `z` and actual pinned success probability
`q ≥ a`, write `v₁` and `v₀` for the Bernoulli(`a`) connection probabilities with `z` pinned open
and pinned closed.  Then `v₀ ≤ v₁` because the connection event is increasing, the Bernoulli(`a`)
value at the current transcript is `a v₁ + (1 - a) v₀` by `pinnedProb_split`, and the actual
continuation is at least `q v₁ + (1 - q) v₀`, which exceeds it by `(q - a)(v₁ - v₀) ≥ 0`.

## Terminal completeness

The run `Exploration.run` is defined here, not by the instantiating exploration, and it continues
for as long as the transcript is not terminal.  A transcript is terminal exactly when the explored
component meets the target or the frontier is empty.  The instantiating exploration supplies only
the vertex examined next, the fresh sites it reads, the success event, and the invariant
`Admissible` its transcripts satisfy; it has no way to stop early.  The hypothesis
`Transcript.Terminal` in `next_mem_boundary`, `region_fresh`, `succ_determinedBy` and
`step_admissible` is what lets the dead end of `BlockGluing` be a transcript at which nothing is
demanded.  Without terminal completeness the statement is false: an exploration allowed to stop
after one failure would compare against the full Bernoulli(`a`) connection probability.

## Main statements

* `le_pinnedProb_inter_of_forall_extend_of_mem`: the tower inequality of `KN/ReachCoupling.lean`
  with the bound demanded only at prescriptions under which the conditioning event holds.
* `Transcript`, `Transcript.step`, `Transcript.boundary`, `Transcript.Terminal`: transcripts of an
  exploration of a finite arena `A` inside an arbitrary graph, and the frontier of the explored
  component.  The root counts as a frontier vertex while it is undetermined.
* `targetConn G A o T`: the root is joined to the target by an open path inside `A`.
* `Transcript.bern`: the Bernoulli(`a`) value of a transcript, the connection probability with the
  determined vertices pinned to their verdicts.
* `Exploration`: the data of an adaptive exploration whose per-step success is a pinned probability.
* `Exploration.bern_le_prob_run`: **the finite adaptive domination**, at every admissible transcript.
* `Exploration.pinnedProb_singleton_le_real_run`: read at a start that knows nothing but that the
  root is open, this is `P(explored component reaches T) ≥ P_a(o ↔ T inside A | o pinned open)`.
* `thetaSiteOn_le_pinnedProb_targetConn`, `thetaSite_le_pinnedProb_box`: the passage to infinity,
  `θ(a) ≤ P_a(o ↔ ∂Λ inside Λ | o pinned open)` for every finite `Λ ∋ o`, and on the boxes of `ℤ^d`.
* `Exploration.thetaSite_le_real_run_box` and `exists_param_thetaSite_le_real_run_box`: the two
  combined on the boxes of `ℤ^d`, with the explicit parameter of `KN/SitePlanarInput.lean`.
* `siteExploration`, `siteExploration_step`, `bern_two_vertex`, `two_vertex_bound`: non-vacuity.
  The exploration reading one vertex at a time meets every hypothesis with the exact density, and on
  the two-vertex graph at density one half the bound is `1/2`.
-/

noncomputable section

namespace KNAll.Site.FRDom

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Part 1: the tower inequality, with the bound demanded only where the event holds -/

section PinnedTower

variable {ι : Type*}

/-- **The tower inequality, restricted to the prescriptions under which `B` holds.**  This is
`le_pinnedProb_inter_of_forall_extend` with the lower bound on `Y` asked for only at prescriptions
`val'` on `R ∪ F` extending `val` for which the event `B` holds; since `B` is determined by
`R ∪ F`, whether it holds under `val'` is decided by the substituted empty configuration.  The
restriction is what lets an exploration be required to keep its transcripts admissible only along
the outcomes it actually produces. -/
theorem le_pinnedProb_inter_of_forall_extend_of_mem (p : ι → unitInterval) {c : ℝ}
    {B Y : Set (Set ι)} (hBm : MeasurableSet B) (hYm : MeasurableSet Y) :
    ∀ (F : Finset ι) (R : Set ι), Disjoint (↑F : Set ι) R → ∀ val : ι → Prop,
      DeterminedBy B (R ∪ ↑F) →
      (∀ val' : ι → Prop, (∀ j ∈ R, (val' j ↔ val j)) →
        substitute (R ∪ ↑F) val' ∅ ∈ B → c ≤ pinnedProb p (R ∪ ↑F) val' Y) →
      c * pinnedProb p R val B ≤ pinnedProb p R val (B ∩ Y) := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro R _ val hB hstep
    simp only [Finset.coe_empty, Set.union_empty] at hB hstep
    rcases substitute_preimage_of_determinedBy val hB with hu | hu
    · have h1 : pinnedProb p R val B = 1 := by rw [pinnedProb, hu]; exact probReal_univ
      have h2 : pinnedProb p R val (B ∩ Y) = pinnedProb p R val Y := by
        rw [pinnedProb, pinnedProb, Set.preimage_inter, hu, Set.univ_inter]
      have hmem : substitute R val ∅ ∈ B := by
        have : (∅ : Set ι) ∈ substitute R val ⁻¹' B := by rw [hu]; exact Set.mem_univ _
        exact this
      rw [h1, h2, mul_one]
      exact hstep val (fun _ _ => Iff.rfl) hmem
    · have h1 : pinnedProb p R val B = 0 := by rw [pinnedProb, hu, measureReal_empty]
      rw [h1, mul_zero]
      exact pinnedProb_nonneg_coord _ _ _ _
  | insert i F hiF ih =>
    intro R hdisj val hB hstep
    have hiF' : (i : ι) ∈ (insert i F : Finset ι) := Finset.mem_insert_self i F
    have hiR : i ∉ R := Set.disjoint_left.1 hdisj (by exact_mod_cast hiF')
    have hFR : Disjoint (↑F : Set ι) R :=
      hdisj.mono_left (by exact_mod_cast Finset.subset_insert i F)
    have hset : R ∪ (↑(insert i F) : Set ι) = insert i R ∪ (↑F : Set ι) := by
      rw [Finset.coe_insert, Set.union_insert, Set.insert_union]
    have hdisj' : Disjoint (↑F : Set ι) (insert i R) := by
      rw [Set.disjoint_left]
      intro j hj hj'
      rcases Set.mem_insert_iff.1 hj' with rfl | hj''
      · exact hiF (Finset.mem_coe.1 hj)
      · exact Set.disjoint_left.1 hFR hj hj''
    have hB' : DeterminedBy B (insert i R ∪ (↑F : Set ι)) := by rwa [hset] at hB
    have hstep' : ∀ (b : Prop) (val' : ι → Prop),
        (∀ j ∈ insert i R, (val' j ↔ setVal val i b j)) →
          substitute (insert i R ∪ (↑F : Set ι)) val' ∅ ∈ B →
          c ≤ pinnedProb p (insert i R ∪ (↑F : Set ι)) val' Y := by
      intro b val' hval' hmem
      rw [← hset] at hmem ⊢
      refine hstep val' (fun j hj => ?_) hmem
      have hji : j ≠ i := fun h => hiR (h ▸ hj)
      exact (hval' j (Set.mem_insert_of_mem i hj)).trans (setVal_of_ne val hji b)
    have hT := ih (insert i R) hdisj' (setVal val i True) hB' (hstep' True)
    have hF := ih (insert i R) hdisj' (setVal val i False) hB' (hstep' False)
    have hp0 : (0 : ℝ) ≤ (p i : ℝ) := (p i).2.1
    have hp1 : (0 : ℝ) ≤ 1 - (p i : ℝ) := by linarith [(p i).2.2]
    have h1 := mul_le_mul_of_nonneg_left hT hp0
    have h2 := mul_le_mul_of_nonneg_left hF hp1
    rw [pinnedProb_split p hiR val hBm, pinnedProb_split p hiR val (hBm.inter hYm)]
    linarith

/-- Raising the prescribed values on the pinned set can only raise the pinned probability of an
increasing event. -/
theorem pinnedProb_mono_val (p : ι → unitInterval) (R : Set ι) {val val' : ι → Prop}
    (hv : ∀ i ∈ R, val i → val' i) {E : Set (Set ι)} (hE : IsUpperSet E) :
    pinnedProb p R val E ≤ pinnedProb p R val' E := by
  unfold pinnedProb
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  simp only [Set.mem_preimage] at hω ⊢
  refine hE (fun i hi => ?_) hω
  by_cases hiR : i ∈ R
  · rw [mem_substitute_of_mem val hiR] at hi
    rw [mem_substitute_of_mem val' hiR]
    exact hv i hiR hi
  · rw [mem_substitute_of_notMem val hiR] at hi
    rw [mem_substitute_of_notMem val' hiR]
    exact hi

/-- Pinning coordinates open can only raise the probability of an increasing event. -/
theorem real_le_pinnedProb_of_isUpperSet (p : ι → unitInterval) (R : Set ι) {E : Set (Set ι)}
    (hE : IsUpperSet E) :
    (prodBernoulli p).real E ≤ pinnedProb p R (fun _ => True) E := by
  unfold pinnedProb
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  simp only [Set.mem_preimage]
  refine hE (fun i hi => ?_) hω
  by_cases hiR : i ∈ R
  · rw [mem_substitute_of_mem _ hiR]
    trivial
  · rw [mem_substitute_of_notMem _ hiR]
    exact hi

end PinnedTower

/-! ## Part 2: the Bernoulli benchmark on a finite arena -/

section Target

variable {V : Type*} (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V)

/-- The root `o` is joined to some vertex of the target `T` by a path of open vertices all lying in
the arena `A`.  This is the event the Bernoulli benchmark computes. -/
def targetConn : Set (Set V) := ⋃ t ∈ T, connWithin G (↑A : Set V) o t

theorem mem_targetConn_iff (ω : Set V) :
    ω ∈ targetConn G A o T ↔ ∃ t ∈ T, ω ∈ connWithin G (↑A : Set V) o t := by
  simp [targetConn]

/-- The benchmark event is decided by the sites of the arena. -/
theorem determinedBy_targetConn : DeterminedBy (targetConn G A o T) (↑A : Set V) := by
  rw [determinedBy_iff]
  intro ω ω' hωω'
  rw [mem_targetConn_iff, mem_targetConn_iff]
  exact exists_congr fun t => and_congr_right fun _ =>
    (determinedBy_iff _ _).1 (determinedBy_connWithin G (↑A : Set V) o t) ω ω' hωω'

theorem measurableSet_targetConn : MeasurableSet (targetConn G A o T) :=
  (determinedBy_targetConn G A o T).measurableSet_of_finset

/-- Opening further sites cannot destroy a connection. -/
theorem isUpperSet_targetConn : IsUpperSet (targetConn G A o T) := by
  intro ω ω' hle hω
  rw [mem_targetConn_iff] at hω ⊢
  obtain ⟨t, ht, h⟩ := hω
  exact ⟨t, ht, isUpperSet_connWithin G (↑A : Set V) o t hle h⟩

end Target

/-! ## Part 3: transcripts -/

section TranscriptSection

variable {κ V : Type*}

/-- **A transcript of the exploration.**  The sites read so far with the states found, and the
vertices of the arena already determined, with their verdicts.  The vertices declared open are
`openV`, those declared closed are `closedV`; the transcript carries no order of examination. -/
@[ext]
structure Transcript (κ V : Type*) where
  /-- The sites whose state has been read. -/
  inspected : Finset κ
  /-- Those of them that were found open. -/
  openSites : Finset κ
  /-- Only inspected sites have a recorded state. -/
  openSites_subset : openSites ⊆ inspected
  /-- The vertices declared open. -/
  openV : Finset V
  /-- The vertices declared closed. -/
  closedV : Finset V

namespace Transcript

variable (h : Transcript κ V)

/-- The recorded states, as the value function `substitute` consumes. -/
def state : κ → Prop := fun x => x ∈ h.openSites

theorem state_iff (x : κ) : h.state x ↔ x ∈ h.openSites := Iff.rfl

theorem mem_inspected_of_state {x : κ} (hx : h.state x) : x ∈ h.inspected :=
  h.openSites_subset hx

/-- The probability of `E` after the transcript: the read sites are overwritten by their recorded
states and an ordinary product probability is taken. -/
def prob (p : κ → unitInterval) (E : Set (Set κ)) : ℝ :=
  pinnedProb p (↑h.inspected : Set κ) h.state E

theorem prob_eq (p : κ → unitInterval) (E : Set (Set κ)) :
    h.prob p E = pinnedProb p (↑h.inspected : Set κ) h.state E := rfl

theorem prob_nonneg (p : κ → unitInterval) (E : Set (Set κ)) : 0 ≤ h.prob p E :=
  pinnedProb_nonneg_coord _ _ _ _

theorem prob_le_one (p : κ → unitInterval) (E : Set (Set κ)) : h.prob p E ≤ 1 :=
  pinnedProb_le_one_coord _ _ _ _

/-- The explored component: the open cluster of the root in the configuration of the vertices
declared open.  It is empty while the root is undetermined or declared closed. -/
def explored (G : SimpleGraph V) (o : V) : Set V := siteCluster G (↑h.openV : Set V) o

/-- **The frontier.**  The undetermined vertices of the arena that are the root or are adjacent to
the explored component.  The exploration must examine one of them next, and it is terminal when
there is none. -/
def boundary (G : SimpleGraph V) (A : Finset V) (o : V) : Set V :=
  {v | v ∈ A ∧ v ∉ h.openV ∧ v ∉ h.closedV ∧ (v = o ∨ ∃ u ∈ h.explored G o, G.Adj u v)}

/-- The explored component meets the target. -/
def Reaches (G : SimpleGraph V) (o : V) (T : Set V) : Prop := ∃ t ∈ T, t ∈ h.explored G o

/-- **Terminal completeness.**  A transcript is terminal when the target has been reached or the
frontier is empty, and only then. -/
def Terminal (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) : Prop :=
  h.Reaches G o T ∨ h.boundary G A o = ∅

variable [DecidableEq V]

/-- The number of vertices of the arena not yet determined.  The backward induction runs on it. -/
def undetermined (A : Finset V) : ℕ := (A \ (h.openV ∪ h.closedV)).card

theorem boundary_subset_sdiff (G : SimpleGraph V) (A : Finset V) (o : V) :
    h.boundary G A o ⊆ (↑(A \ (h.openV ∪ h.closedV)) : Set V) := by
  rintro v ⟨hvA, hvo, hvc, -⟩
  simp [hvA, hvo, hvc]

/-- With no undetermined vertex left the transcript is terminal. -/
theorem terminal_of_undetermined_eq_zero (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V)
    (h0 : h.undetermined A = 0) : h.Terminal G A o T := by
  refine Or.inr (Set.eq_empty_of_subset_empty ?_)
  refine (h.boundary_subset_sdiff G A o).trans ?_
  rw [undetermined, Finset.card_eq_zero] at h0
  rw [h0, Finset.coe_empty]

/-! ### The Bernoulli value of a transcript -/

/-- **The Bernoulli(`a`) value of a transcript.**  The probability, under independent site
percolation at density `a` on the arena's ambient graph, that the root is joined to the target
inside the arena, with every determined vertex pinned to its verdict. -/
def bern (a : unitInterval) (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) : ℝ :=
  pinnedProb (fun _ : V => a) (↑(h.openV ∪ h.closedV) : Set V) (fun v => v ∈ h.openV)
    (targetConn G A o T)

variable (a : unitInterval) (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V)

theorem bern_nonneg : 0 ≤ h.bern a G A o T := pinnedProb_nonneg_coord _ _ _ _

theorem bern_le_one : h.bern a G A o T ≤ 1 := pinnedProb_le_one_coord _ _ _ _

/-- **A dead end has Bernoulli value zero.**  If the frontier is empty and the target has not been
reached, no open path inside the arena can leave the explored component, so the pinned
Bernoulli configuration never joins the root to the target. -/
theorem bern_eq_zero_of_boundary_eq_empty (hb : h.boundary G A o = ∅) (hr : ¬ h.Reaches G o T) :
    h.bern a G A o T = 0 := by
  unfold bern pinnedProb
  have hpre : substitute (↑(h.openV ∪ h.closedV) : Set V) (fun v => v ∈ h.openV) ⁻¹'
      targetConn G A o T = ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    set ω' := substitute (↑(h.openV ∪ h.closedV) : Set V) (fun v => v ∈ h.openV) ω with hω'
    intro hmem
    rw [mem_targetConn_iff] at hmem
    obtain ⟨t, ht, ⟨hoA, hreach⟩⟩ := hmem
    -- the pinned configuration reads the verdicts on the determined vertices
    have hval : ∀ v, v ∈ h.openV ∪ h.closedV → (v ∈ ω' ↔ v ∈ h.openV) := fun v hv =>
      mem_substitute_of_mem (fun v => v ∈ h.openV) (Finset.mem_coe.2 hv)
    -- the root is declared open
    have hoV : o ∈ h.openV := by
      by_contra hoo
      by_cases hoc : o ∈ h.closedV
      · exact hoo ((hval o (Finset.mem_union_right _ hoc)).1 hoA.1)
      · have : o ∈ h.boundary G A o := ⟨Finset.mem_coe.1 hoA.2, hoo, hoc, Or.inl rfl⟩
        rw [hb] at this
        exact this
    -- every vertex reachable from the root inside the pinned arena lies in the explored component
    have hwalk : ∀ {u v : V}, (openSiteGraph G (ω' ∩ (↑A : Set V))).Walk u v →
        u ∈ h.explored G o → v ∈ h.explored G o := by
      intro u v w
      induction w with
      | nil => exact id
      | @cons a c _ hac w ih =>
        intro ha
        refine ih ?_
        obtain ⟨hGac, haω, hcω⟩ := (openSiteGraph_adj_iff' G _ a c).1 hac
        have hcV : c ∈ h.openV := by
          by_contra hco
          by_cases hcc : c ∈ h.closedV
          · exact hco ((hval c (Finset.mem_union_right _ hcc)).1 hcω.1)
          · have : c ∈ h.boundary G A o := ⟨Finset.mem_coe.1 hcω.2, hco, hcc, Or.inr ⟨a, ha, hGac⟩⟩
            rw [hb] at this
            exact this
        have haV : a ∈ h.openV := Finset.mem_coe.1 (mem_of_mem_siteCluster G _ ha)
        refine ⟨Finset.mem_coe.2 hoV, ha.2.trans (SimpleGraph.Adj.reachable ?_)⟩
        exact (openSiteGraph_adj_iff' G (↑h.openV : Set V) a c).2
          ⟨hGac, Finset.mem_coe.2 haV, Finset.mem_coe.2 hcV⟩
    obtain ⟨w⟩ := hreach
    exact hr ⟨t, ht, hwalk w (mem_siteCluster_self G _ (Finset.mem_coe.2 hoV))⟩
  rw [hpre, measureReal_empty]

/-- **A terminal transcript is already dominated.**  Either the target has been reached, and the
event that it has is sure, or the frontier is empty and the Bernoulli value is zero. -/
theorem bern_le_prob_of_terminal (p : κ → unitInterval) (hT : h.Terminal G A o T) :
    h.bern a G A o T ≤ h.prob p {_ω : Set κ | h.Reaches G o T} := by
  by_cases hr : h.Reaches G o T
  · have hset : {_ω : Set κ | h.Reaches G o T} = Set.univ := Set.eq_univ_of_forall fun _ => hr
    rw [hset, prob_eq, pinnedProb_univ]
    exact h.bern_le_one a G A o T
  · have hb : h.boundary G A o = ∅ := hT.resolve_left hr
    rw [h.bern_eq_zero_of_boundary_eq_empty a G A o T hb hr]
    exact h.prob_nonneg _ _

/-! ### One examination -/

variable [DecidableEq κ]

open Classical in
/-- **One examination.**  The sites of `F` are read from `ω` and their states recorded; the vertex
`z` is declared open when `b` is `true` and closed otherwise. -/
def step (z : V) (F : Finset κ) (b : Bool) (ω : Set κ) : Transcript κ V where
  inspected := h.inspected ∪ F
  openSites := h.openSites ∪ F.filter (fun x => x ∈ ω)
  openSites_subset := Finset.union_subset_union h.openSites_subset (Finset.filter_subset _ _)
  openV := if b then insert z h.openV else h.openV
  closedV := if b then h.closedV else insert z h.closedV

variable {z : V} {F : Finset κ} {b : Bool} {ω : Set κ}

@[simp] theorem step_inspected : (h.step z F b ω).inspected = h.inspected ∪ F := rfl

@[simp] theorem step_openV : (h.step z F b ω).openV = if b then insert z h.openV else h.openV :=
  rfl

@[simp] theorem step_closedV :
    (h.step z F b ω).closedV = if b then h.closedV else insert z h.closedV := rfl

theorem step_state (x : κ) : (h.step z F b ω).state x ↔ h.state x ∨ (x ∈ F ∧ x ∈ ω) := by
  classical
  simp [state, step, Finset.mem_union, Finset.mem_filter]

/-- The examination reads the configuration only on the sites it reads. -/
theorem step_congr {ω ω' : Set κ} (hagree : ∀ x ∈ F, (x ∈ ω ↔ x ∈ ω')) :
    h.step z F b ω = h.step z F b ω' := by
  classical
  refine Transcript.ext rfl ?_ rfl rfl
  simp only [step]
  congr 1
  exact Finset.filter_congr fun x hx => hagree x hx

/-- After the examination the determined set has grown by the examined vertex, whatever the
verdict. -/
theorem step_determined :
    (h.step z F b ω).openV ∪ (h.step z F b ω).closedV = insert z (h.openV ∪ h.closedV) := by
  cases b <;> simp [Finset.insert_union, Finset.union_insert]

theorem coe_step_determined :
    (↑((h.step z F b ω).openV ∪ (h.step z F b ω).closedV) : Set V)
      = insert z (↑(h.openV ∪ h.closedV) : Set V) := by
  rw [step_determined, Finset.coe_insert]

/-- Examining an undetermined vertex of the arena determines one more vertex. -/
theorem undetermined_step {A : Finset V} (hzA : z ∈ A) (hzo : z ∉ h.openV) (hzc : z ∉ h.closedV) :
    (h.step z F b ω).undetermined A + 1 = h.undetermined A := by
  unfold undetermined
  rw [step_determined, Finset.sdiff_insert]
  exact Finset.card_erase_add_one (Finset.mem_sdiff.2 ⟨hzA, by simp [hzo, hzc]⟩)

/-- **The examination reads only its own sites.**  Splitting by the pattern found on `F` turns an
event about a transcript depending on the configuration into a finite union of events about fixed
transcripts. -/
theorem setOf_step_eq_biUnion (Q : Transcript κ V → Set κ → Prop) :
    {ω : Set κ | Q (h.step z F b ω) ω}
      = ⋃ σ ∈ F.powerset,
          (localCylinder (↑F : Set κ) (↑σ : Set κ) ∩ {ω | Q (h.step z F b (↑σ : Set κ)) ω}) := by
  classical
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop,
    Finset.mem_powerset]
  constructor
  · intro hω
    refine ⟨F.filter (fun x => x ∈ ω), Finset.filter_subset _ _, ?_, ?_⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at *
      exact ⟨fun hxω => ⟨hx, hxω⟩, fun hxω => hxω.2⟩
    · have hEq : h.step z F b ω = h.step z F b (↑(F.filter (fun x => x ∈ ω)) : Set κ) := by
        refine h.step_congr fun x hx => ?_
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨fun hxω => ⟨hx, hxω⟩, fun hxω => hxω.2⟩
      rwa [← hEq]
  · rintro ⟨σ, -, hcyl, hrun⟩
    have hEq : h.step z F b ω = h.step z F b (↑σ : Set κ) :=
      h.step_congr fun x hx => hcyl x (Finset.mem_coe.2 hx)
    rwa [hEq]

/-- The Bernoulli value of the transcript after an examination does not depend on the states
read: it reads only the verdicts. -/
theorem bern_step_congr (ω' : Set κ) :
    (h.step z F b ω).bern a G A o T = (h.step z F b ω').bern a G A o T := rfl

/-- **The Bernoulli value splits at an undetermined vertex.**  This is `pinnedProb_split` at `z`,
with the two prescriptions identified with the transcripts after a success and after a failure. -/
theorem bern_split (hzo : z ∉ h.openV) (hzc : z ∉ h.closedV) (ω₁ ω₀ : Set κ) :
    h.bern a G A o T
      = (a : ℝ) * (h.step z F true ω₁).bern a G A o T
        + (1 - (a : ℝ)) * (h.step z F false ω₀).bern a G A o T := by
  have hzS : z ∉ (↑(h.openV ∪ h.closedV) : Set V) := by simp [hzo, hzc]
  have hsplit := pinnedProb_split (fun _ : V => a) hzS (fun v => v ∈ h.openV)
    (measurableSet_targetConn G A o T)
  have hT : pinnedProb (fun _ : V => a) (insert z (↑(h.openV ∪ h.closedV) : Set V))
      (setVal (fun v => v ∈ h.openV) z True) (targetConn G A o T)
      = (h.step z F true ω₁).bern a G A o T := by
    unfold bern
    rw [coe_step_determined]
    refine pinnedProb_congr_val _ _ (fun v _ => ?_) _
    simp only [step_openV, if_true]
    by_cases hvz : v = z
    · subst hvz
      rw [setVal_self]
      simp
    · rw [setVal_of_ne _ hvz]
      simp [hvz]
  have hF : pinnedProb (fun _ : V => a) (insert z (↑(h.openV ∪ h.closedV) : Set V))
      (setVal (fun v => v ∈ h.openV) z False) (targetConn G A o T)
      = (h.step z F false ω₀).bern a G A o T := by
    unfold bern
    rw [coe_step_determined]
    refine pinnedProb_congr_val _ _ (fun v _ => ?_) _
    simp only [step_openV, Bool.false_eq_true, if_false]
    by_cases hvz : v = z
    · subst hvz
      rw [setVal_self]
      simp [hzo]
    · rw [setVal_of_ne _ hvz]
  rw [bern, hsplit, hT, hF]

/-- **Monotonicity.**  Declaring the examined vertex open gives a larger Bernoulli value than
declaring it closed. -/
theorem bern_step_false_le_true (ω₁ ω₀ : Set κ) :
    (h.step z F false ω₀).bern a G A o T ≤ (h.step z F true ω₁).bern a G A o T := by
  unfold bern
  rw [coe_step_determined, coe_step_determined]
  refine pinnedProb_mono_val _ _ (fun v _ hv => ?_) (isUpperSet_targetConn G A o T)
  simp only [step_openV, Bool.false_eq_true, if_false] at hv
  simp only [step_openV, if_true]
  exact Finset.mem_insert_of_mem hv

end Transcript

end TranscriptSection

/-! ## Part 4: explorations and the domination -/

/-- **An adaptive exploration of a finite arena.**  The arena is the finite vertex set `A` of an
arbitrary graph `G`, with root `o` and target `T`; the configuration space is that of the sites
`κ`, on which the exploration reads.

At every admissible transcript that is not terminal, `next` names a frontier vertex, `region` the
fresh sites read to decide it, and `succ` the event that the verdict is "open", decided by the
sites read so far together with the fresh ones.  `Admissible` is the invariant of the transcripts
the exploration produces: it must hold after each examination along the verdict the examination
actually returns.  The one-step lower bound is not part of the data; it is the hypothesis of
`Exploration.bern_le_prob_run`. -/
structure Exploration (κ : Type*) [DecidableEq κ] {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) where
  /-- The density of the underlying site percolation on `κ`. -/
  density : κ → unitInterval
  /-- The transcripts the exploration can produce. -/
  Admissible : Transcript κ V → Prop
  /-- The vertex examined next. -/
  next : Transcript κ V → V
  /-- The fresh sites read at the next examination. -/
  region : Transcript κ V → Finset κ
  /-- The event that the next examination declares its vertex open. -/
  succ : Transcript κ V → Set (Set κ)
  /-- The success events are measurable. -/
  succ_measurable : ∀ h, MeasurableSet (succ h)
  /-- The vertex examined next lies on the frontier. -/
  next_mem_boundary : ∀ h, Admissible h → ¬ h.Terminal G A o T → next h ∈ h.boundary G A o
  /-- The sites read next have not been read before. -/
  region_fresh : ∀ h, Admissible h → ¬ h.Terminal G A o T → Disjoint (region h) h.inspected
  /-- The verdict is decided by the sites read once the examination is over. -/
  succ_determinedBy : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    DeterminedBy (succ h) (↑(h.inspected ∪ region h) : Set κ)
  /-- An examination keeps the transcript admissible, along the verdict it actually returns. -/
  step_admissible : ∀ h, Admissible h → ¬ h.Terminal G A o T → ∀ (b : Bool) (ω : Set κ),
    (b = true ↔ ω ∈ succ h) → Admissible (h.step (next h) (region h) b ω)

namespace Exploration

variable {κ V : Type*} [DecidableEq κ] [DecidableEq V] {G : SimpleGraph V} {A : Finset V} {o : V}
  {T : Set V} (E : Exploration κ G A o T)

open Classical in
/-- The verdict of the next examination, read off the configuration. -/
def bit (h : Transcript κ V) (ω : Set κ) : Bool := decide (ω ∈ E.succ h)

theorem bit_eq_true_iff (h : Transcript κ V) (ω : Set κ) : E.bit h ω = true ↔ ω ∈ E.succ h := by
  unfold bit
  simp

theorem bit_of_mem {h : Transcript κ V} {ω : Set κ} (hω : ω ∈ E.succ h) : E.bit h ω = true :=
  (E.bit_eq_true_iff h ω).2 hω

theorem bit_of_notMem {h : Transcript κ V} {ω : Set κ} (hω : ω ∉ E.succ h) :
    E.bit h ω = false := by
  have := (E.bit_eq_true_iff h ω).not.2 hω
  simpa using this

open Classical in
/-- **The run.**  Examinations are performed for as long as the transcript is not terminal, and
`n` of them at most.  The exploration supplies the data of each examination; when to stop is not
its choice. -/
def run (E : Exploration κ G A o T) : ℕ → Transcript κ V → Set κ → Transcript κ V
  | 0, h, _ => h
  | n + 1, h, ω =>
    if h.Terminal G A o T then h else E.run n (h.step (E.next h) (E.region h) (E.bit h ω) ω) ω

@[simp] theorem run_zero (h : Transcript κ V) (ω : Set κ) : E.run 0 h ω = h := rfl

theorem run_succ_of_terminal {h : Transcript κ V} (hT : h.Terminal G A o T) (n : ℕ) (ω : Set κ) :
    E.run (n + 1) h ω = h := by
  simp [run, hT]

theorem run_succ_of_not_terminal {h : Transcript κ V} (hT : ¬ h.Terminal G A o T) (n : ℕ)
    (ω : Set κ) :
    E.run (n + 1) h ω = E.run n (h.step (E.next h) (E.region h) (E.bit h ω) ω) ω := by
  simp [run, hT]

/-- The transcript after `n` examinations is terminal as soon as `n` is at least the number of
undetermined vertices: the run is complete. -/
theorem terminal_run :
    ∀ (n : ℕ) (h : Transcript κ V), E.Admissible h → h.undetermined A ≤ n →
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
      obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
      refine ih _ (E.step_admissible h hadm hT _ ω (E.bit_eq_true_iff h ω)) ?_ ω
      have := h.undetermined_step (F := E.region h) (b := E.bit h ω) (ω := ω) hzA hzo hzc
      omega

/-! ### Measurability of events read off a run -/

/-- **The first verdict splits the run.** -/
theorem setOf_run_succ_eq {h : Transcript κ V} (hT : ¬ h.Terminal G A o T)
    (P : Transcript κ V → Prop) (n : ℕ) :
    {ω : Set κ | P (E.run (n + 1) h ω)}
      = (E.succ h ∩ {ω | P (E.run n (h.step (E.next h) (E.region h) true ω) ω)})
        ∪ ((E.succ h)ᶜ ∩ {ω | P (E.run n (h.step (E.next h) (E.region h) false ω) ω)}) := by
  ext ω
  by_cases hω : ω ∈ E.succ h
  · rw [Set.mem_setOf_eq, E.run_succ_of_not_terminal hT, E.bit_of_mem hω]
    simp [hω]
  · rw [Set.mem_setOf_eq, E.run_succ_of_not_terminal hT, E.bit_of_notMem hω]
    simp [hω]

/-- Events read off a run are measurable. -/
theorem measurableSet_setOf_run (P : Transcript κ V → Prop) :
    ∀ (n : ℕ) (h : Transcript κ V), MeasurableSet {ω : Set κ | P (E.run n h ω)} := by
  intro n
  induction n with
  | zero =>
    intro h
    simp only [run_zero]
    exact MeasurableSet.const _
  | succ n ih =>
    intro h
    by_cases hT : h.Terminal G A o T
    · have hset : {ω : Set κ | P (E.run (n + 1) h ω)} = {_ω : Set κ | P h} := by
        ext ω
        rw [Set.mem_setOf_eq, E.run_succ_of_terminal hT]
        rfl
      rw [hset]
      exact MeasurableSet.const _
    · have hstepmeas : ∀ (b : Bool),
          MeasurableSet {ω : Set κ | P (E.run n (h.step (E.next h) (E.region h) b ω) ω)} := by
        intro b
        rw [h.setOf_step_eq_biUnion (fun h' ω => P (E.run n h' ω))]
        exact Finset.measurableSet_biUnion _ fun σ _ =>
          (measurableSet_localCylinder (E.region h).finite_toSet.countable _).inter (ih _)
      rw [E.setOf_run_succ_eq hT P n]
      exact ((E.succ_measurable h).inter (hstepmeas true)).union
        ((E.succ_measurable h).compl.inter (hstepmeas false))

/-- Events read off a run started by one examination are measurable. -/
theorem measurableSet_setOf_run_step (P : Transcript κ V → Prop) (n : ℕ) (h : Transcript κ V)
    (z : V) (F : Finset κ) (b : Bool) :
    MeasurableSet {ω : Set κ | P (E.run n (h.step z F b ω) ω)} := by
  rw [h.setOf_step_eq_biUnion (fun h' ω => P (E.run n h' ω))]
  exact Finset.measurableSet_biUnion _ fun σ _ =>
    (measurableSet_localCylinder F.finite_toSet.countable _).inter (E.measurableSet_setOf_run P n _)

/-! ### The domination -/

/-- **Finite adaptive domination.**  If at every admissible transcript that is not terminal the
next examination succeeds with pinned probability at least `a`, then at every admissible transcript
the probability, pinned by the transcript, that a complete run reaches the target is at least the
Bernoulli(`a`) value of the transcript.

The induction is on the number of examinations allowed, which must be at least the number of
undetermined vertices so that the run is complete.  At a terminal transcript
`Transcript.bern_le_prob_of_terminal` applies.  Otherwise the run splits along the verdict of the
next examination, the two branches are bounded below uniformly over the patterns the fresh sites
can show by the induction hypothesis, `le_pinnedProb_inter_of_forall_extend_of_mem` averages those
bounds against the true weight of the verdict, and `Transcript.bern_split` with
`Transcript.bern_step_false_le_true` shows that raising that weight from `a` to its true value can
only help. -/
theorem bern_le_prob_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : ℝ) ≤ h.prob E.density (E.succ h)) :
    ∀ (n : ℕ) (h : Transcript κ V), E.Admissible h → h.undetermined A ≤ n →
      h.bern a G A o T ≤ h.prob E.density {ω | (E.run n h ω).Reaches G o T} := by
  intro n
  induction n with
  | zero =>
    intro h _ hn
    have hT : h.Terminal G A o T := h.terminal_of_undetermined_eq_zero G A o T (Nat.le_zero.1 hn)
    simpa only [run_zero] using h.bern_le_prob_of_terminal a G A o T E.density hT
  | succ n ih =>
    intro h hadm hn
    by_cases hT : h.Terminal G A o T
    · have hset : {ω : Set κ | (E.run (n + 1) h ω).Reaches G o T}
          = {_ω : Set κ | h.Reaches G o T} := by
        ext ω
        rw [Set.mem_setOf_eq, E.run_succ_of_terminal hT]
        rfl
      rw [hset]
      exact h.bern_le_prob_of_terminal a G A o T E.density hT
    · obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
      have hfresh : Disjoint (↑(E.region h) : Set κ) (↑h.inspected : Set κ) :=
        Finset.disjoint_coe.2 (E.region_fresh h hadm hT)
      have hund : ∀ (b : Bool) (ω : Set κ),
          (h.step (E.next h) (E.region h) b ω).undetermined A ≤ n := by
        intro b ω
        have := h.undetermined_step (F := E.region h) (b := b) (ω := ω) hzA hzo hzc
        omega
      -- The uniform branch bound, averaged against the weight of the verdict.
      have key : ∀ (b : Bool) (B : Set (Set κ)),
          DeterminedBy B ((↑h.inspected : Set κ) ∪ ↑(E.region h)) → MeasurableSet B →
          (∀ ω₀ ∈ B, (b = true ↔ ω₀ ∈ E.succ h)) →
          (h.step (E.next h) (E.region h) b ∅).bern a G A o T * h.prob E.density B
            ≤ h.prob E.density
                (B ∩ {ω | (E.run n (h.step (E.next h) (E.region h) b ω) ω).Reaches G o T}) := by
        intro b B hBdet hBm hbB
        rw [Transcript.prob_eq, Transcript.prob_eq]
        refine le_pinnedProb_inter_of_forall_extend_of_mem E.density hBm
          (E.measurableSet_setOf_run_step (fun h' => h'.Reaches G o T) n h _ _ b)
          (E.region h) (↑h.inspected : Set κ) hfresh h.state hBdet ?_
        intro val' hval' hmem
        set S : Set κ := (↑h.inspected : Set κ) ∪ ↑(E.region h) with hS
        set ω₀ : Set κ := substitute S val' ∅ with hω₀
        have hsub : (↑(E.region h) : Set κ) ⊆ S := Set.subset_union_right
        have hconst : ∀ ω : Set κ,
            h.step (E.next h) (E.region h) b (substitute S val' ω)
              = h.step (E.next h) (E.region h) b ω₀ := by
          intro ω
          refine h.step_congr fun x hx => ?_
          rw [mem_substitute_of_mem val' (hsub (Finset.mem_coe.2 hx)),
            mem_substitute_of_mem val' (hsub (Finset.mem_coe.2 hx))]
        have hpre : pinnedProb E.density S val'
              {ω | (E.run n (h.step (E.next h) (E.region h) b ω) ω).Reaches G o T}
            = pinnedProb E.density S val'
              {ω | (E.run n (h.step (E.next h) (E.region h) b ω₀) ω).Reaches G o T} := by
          unfold pinnedProb
          congr 1
          ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq, hconst ω]
        have hinsp : (↑(h.step (E.next h) (E.region h) b ω₀).inspected : Set κ) = S := by
          rw [Transcript.step_inspected, Finset.coe_union]
        have hstate : ∀ x ∈ S, (val' x ↔ (h.step (E.next h) (E.region h) b ω₀).state x) := by
          intro x hx
          rw [Transcript.step_state]
          rcases hx with hx | hx
          · have hxF : x ∉ E.region h := fun hxF =>
              Set.disjoint_left.1 hfresh (Finset.mem_coe.2 hxF) hx
            rw [hval' x hx]
            constructor
            · exact fun hv => Or.inl hv
            · rintro (hv | ⟨hxF', -⟩)
              · exact hv
              · exact absurd hxF' hxF
          · have hxI : x ∉ h.inspected := fun hxI =>
              Set.disjoint_left.1 hfresh hx (Finset.mem_coe.2 hxI)
            have hst : ¬ h.state x := fun hs => hxI (h.mem_inspected_of_state hs)
            have hxω₀ : x ∈ ω₀ ↔ val' x := mem_substitute_of_mem val' (hsub hx)
            constructor
            · exact fun hv => Or.inr ⟨Finset.mem_coe.1 hx, hxω₀.2 hv⟩
            · rintro (hs | ⟨-, hω⟩)
              · exact absurd hs hst
              · exact hxω₀.1 hω
        have hstep2 : pinnedProb E.density S val'
              {ω | (E.run n (h.step (E.next h) (E.region h) b ω₀) ω).Reaches G o T}
            = (h.step (E.next h) (E.region h) b ω₀).prob E.density
              {ω | (E.run n (h.step (E.next h) (E.region h) b ω₀) ω).Reaches G o T} := by
          rw [Transcript.prob_eq, hinsp]
          exact pinnedProb_congr_val E.density _ hstate _
        rw [hpre, hstep2]
        have hadm₁ : E.Admissible (h.step (E.next h) (E.region h) b ω₀) :=
          E.step_admissible h hadm hT b ω₀ (hbB ω₀ hmem)
        exact ih _ hadm₁ (hund b ω₀)
      have hJdet : DeterminedBy (E.succ h) ((↑h.inspected : Set κ) ∪ ↑(E.region h)) := by
        have := E.succ_determinedBy h hadm hT
        rwa [Finset.coe_union] at this
      have hJm : MeasurableSet (E.succ h) := E.succ_measurable h
      have hkeyT := key true (E.succ h) hJdet hJm (fun ω₀ hω₀ => by simp [hω₀])
      have hkeyF := key false (E.succ h)ᶜ (determinedBy_compl hJdet) hJm.compl
        (fun ω₀ hω₀ => by simpa using hω₀)
      have hq : (a : ℝ) ≤ h.prob E.density (E.succ h) := hstep h hadm hT
      have hq1 : h.prob E.density (E.succ h) ≤ 1 := h.prob_le_one _ _
      have hqc : h.prob E.density (E.succ h)ᶜ = 1 - h.prob E.density (E.succ h) := by
        rw [Transcript.prob_eq, Transcript.prob_eq]
        exact pinnedProb_compl _ _ _ hJm
      have hsplit : h.prob E.density {ω : Set κ | (E.run (n + 1) h ω).Reaches G o T}
          = h.prob E.density (E.succ h
              ∩ {ω | (E.run n (h.step (E.next h) (E.region h) true ω) ω).Reaches G o T})
            + h.prob E.density ((E.succ h)ᶜ
              ∩ {ω | (E.run n (h.step (E.next h) (E.region h) false ω) ω).Reaches G o T}) := by
        rw [Transcript.prob_eq, Transcript.prob_eq, Transcript.prob_eq,
          E.setOf_run_succ_eq hT (fun h' => h'.Reaches G o T) n]
        refine pinnedProb_union _ _ _ (Set.disjoint_left.2 fun ω hω hω' => hω'.1 hω.1) ?_
        exact hJm.compl.inter
          (E.measurableSet_setOf_run_step (fun h' => h'.Reaches G o T) n h _ _ false)
      have hbern := h.bern_split a G A o T (F := E.region h) hzo hzc (∅ : Set κ) (∅ : Set κ)
      have hmono := h.bern_step_false_le_true a G A o T (z := E.next h) (F := E.region h)
        (∅ : Set κ) (∅ : Set κ)
      rw [hqc] at hkeyF
      have hprod : (0 : ℝ) ≤ (h.prob E.density (E.succ h) - a)
          * ((h.step (E.next h) (E.region h) true ∅).bern a G A o T
            - (h.step (E.next h) (E.region h) false ∅).bern a G A o T) :=
        mul_nonneg (by linarith) (by linarith)
      rw [hbern, hsplit]
      nlinarith [hkeyT, hkeyF, hprod]

/-- **The domination at a start that knows nothing but that the root is open.**  The explored
component of a complete run reaches the target at least as often as Bernoulli(`a`) site
percolation on the arena joins the root to the target with the root pinned open. -/
theorem pinnedProb_singleton_le_real_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : ℝ) ≤ h.prob E.density (E.succ h))
    (h₀ : Transcript κ V) (hadm : E.Admissible h₀) (hins : h₀.inspected = ∅)
    (hopen : h₀.openV = {o}) (hclosed : h₀.closedV = ∅) (n : ℕ) (hn : h₀.undetermined A ≤ n) :
    pinnedProb (fun _ : V => a) {o} (fun _ => True) (targetConn G A o T)
      ≤ (prodBernoulli E.density).real {ω | (E.run n h₀ ω).Reaches G o T} := by
  have hmain := E.bern_le_prob_run hstep n h₀ hadm hn
  rw [Transcript.prob_eq, hins, Finset.coe_empty, pinnedProb_empty] at hmain
  refine le_trans (le_of_eq ?_) hmain
  unfold Transcript.bern
  rw [hopen, hclosed, Finset.union_empty, Finset.coe_singleton]
  refine pinnedProb_congr_val _ _ (fun v hv => ?_) _
  rw [Set.mem_singleton_iff] at hv
  simp [hv]

/-- **The domination at a start that knows nothing.**  With the root undetermined the exploration
examines it first, and the comparison is with the unpinned connection probability. -/
theorem real_le_real_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : ℝ) ≤ h.prob E.density (E.succ h))
    (h₀ : Transcript κ V) (hadm : E.Admissible h₀) (hins : h₀.inspected = ∅)
    (hopen : h₀.openV = ∅) (hclosed : h₀.closedV = ∅) (n : ℕ) (hn : h₀.undetermined A ≤ n) :
    (prodBernoulli (fun _ : V => a)).real (targetConn G A o T)
      ≤ (prodBernoulli E.density).real {ω | (E.run n h₀ ω).Reaches G o T} := by
  have hmain := E.bern_le_prob_run hstep n h₀ hadm hn
  rw [Transcript.prob_eq, hins, Finset.coe_empty, pinnedProb_empty] at hmain
  refine le_trans (le_of_eq ?_) hmain
  unfold Transcript.bern
  rw [hopen, hclosed, Finset.union_empty, Finset.coe_empty, pinnedProb_empty]

end Exploration

/-! ## Part 5: the passage to infinity -/

section Infinity

variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [G.LocallyFinite]

/-- **An open walk leaving a finite set passes through its inner boundary**, and its initial
segment up to that point is an open path inside the set. -/
theorem exists_innerBoundary_connWithin (Λ : Finset V) (ω : Set V) :
    ∀ {u v : V} (_ : (openSiteGraph G ω).Walk u v), u ∈ Λ → v ∉ Λ →
      ∃ b ∈ innerBoundary G Λ, ω ∈ connWithin G (↑Λ : Set V) u b := by
  intro u v w
  induction w with
  | nil => intro hu hv; exact absurd hu hv
  | @cons a c _ hac w ih =>
    intro ha hv
    obtain ⟨hGac, haω, hcω⟩ := (openSiteGraph_adj_iff' G ω a c).1 hac
    by_cases hc : c ∈ Λ
    · obtain ⟨b, hb, hcb⟩ := ih hc hv
      refine ⟨b, hb, ⟨⟨haω, Finset.mem_coe.2 ha⟩, (SimpleGraph.Adj.reachable ?_).trans hcb.2⟩⟩
      exact (openSiteGraph_adj_iff' G (ω ∩ (↑Λ : Set V)) a c).2
        ⟨hGac, ⟨haω, Finset.mem_coe.2 ha⟩, ⟨hcω, Finset.mem_coe.2 hc⟩⟩
    · refine ⟨a, ?_, ⟨⟨haω, Finset.mem_coe.2 ha⟩, SimpleGraph.Reachable.refl a⟩⟩
      rw [mem_innerBoundary_iff]
      exact ⟨ha, c, hc, hGac⟩

/-- **An infinite cluster reaches the inner boundary of every finite set containing its root,
inside that set.** -/
theorem mem_targetConn_of_infinite (Λ : Finset V) {o : V} (ho : o ∈ Λ) {ω : Set V}
    (hinf : (siteCluster G ω o).Infinite) :
    ω ∈ targetConn G Λ o (↑(innerBoundary G Λ) : Set V) := by
  obtain ⟨y, ⟨-, hr⟩, hyΛ⟩ := hinf.exists_notMem_finset Λ
  obtain ⟨w⟩ := hr
  obtain ⟨b, hb, hconn⟩ := exists_innerBoundary_connWithin G Λ ω w ho hyΛ
  exact (mem_targetConn_iff G Λ o _ ω).2 ⟨b, Finset.mem_coe.2 hb, hconn⟩

/-- **The passage to infinity.**  The percolation probability is a lower bound, uniform in the
finite set `Λ`, for the probability that the root is joined inside `Λ` to the inner boundary of
`Λ`.  No continuity argument is needed for this direction: the infinite-cluster event is contained
in each of the finite events. -/
theorem thetaSiteOn_le_real_targetConn (Λ : Finset V) {o : V} (ho : o ∈ Λ) (p : unitInterval) :
    thetaSiteOn G o p
      ≤ (prodBernoulli (fun _ : V => p)).real (targetConn G Λ o (↑(innerBoundary G Λ) : Set V)) :=
  measureReal_mono (fun _ hω => mem_targetConn_of_infinite G Λ ho hω) (measure_ne_top _ _)

/-- The same with the root pinned open, the form the domination compares against. -/
theorem thetaSiteOn_le_pinnedProb_targetConn (Λ : Finset V) {o : V} (ho : o ∈ Λ)
    (p : unitInterval) :
    thetaSiteOn G o p
      ≤ pinnedProb (fun _ : V => p) {o} (fun _ => True)
          (targetConn G Λ o (↑(innerBoundary G Λ) : Set V)) :=
  (thetaSiteOn_le_real_targetConn G Λ ho p).trans
    (real_le_pinnedProb_of_isUpperSet _ _ (isUpperSet_targetConn G Λ o _))

end Infinity

/-! ### On the boxes of `ℤ^d` -/

section Boxes

variable {d : ℕ}

/-- `θ_d(a) ≤ P_a(0 ↔ ∂[-n,n]^d inside [-n,n]^d | 0 pinned open)` for every `n`. -/
theorem thetaSite_le_pinnedProb_box (n : ℕ) (a : unitInterval) :
    thetaSite d a
      ≤ pinnedProb (fun _ : Site d => a) {0} (fun _ => True)
          (targetConn (zdGraph d) (box d n) 0 (↑(innerBoundary (zdGraph d) (box d n)) : Set (Site d))) :=
  thetaSiteOn_le_pinnedProb_targetConn (zdGraph d) (box d n) (zero_mem_box d n) a

/-- **The explicit parameter.**  For `d ≥ 2` there is `a < 1` at which the origin percolates, and
`θ_d(a) > 0` then bounds the pinned box connection probabilities from below uniformly in `n`. -/
theorem exists_param_thetaSite_pos_le_box [NeZero d] (hd : 2 ≤ d) :
    ∃ a : unitInterval, (a : ℝ) < 1 ∧ 0 < thetaSite d a ∧ ∀ n : ℕ,
      thetaSite d a
        ≤ pinnedProb (fun _ : Site d => a) {0} (fun _ => True)
            (targetConn (zdGraph d) (box d n) 0
              (↑(innerBoundary (zdGraph d) (box d n)) : Set (Site d))) := by
  obtain ⟨a, ha1, hapos⟩ := exists_thetaSite_pos d hd
  exact ⟨a, ha1, hapos, fun n => thetaSite_le_pinnedProb_box n a⟩

namespace Exploration

variable {κ : Type*} [DecidableEq κ] {n : ℕ}

/-- **Finite adaptive domination on the boxes of `ℤ^d`, uniformly in the radius.**  An exploration
of the box of radius `n` towards its inner boundary, every step of which succeeds with pinned
probability at least `a`, reaches the boundary from a start that knows only that the origin is open
with probability at least `θ_d(a)`, whatever `n`. -/
theorem thetaSite_le_real_run_box
    (E : Exploration κ (zdGraph d) (box d n) 0
      (↑(innerBoundary (zdGraph d) (box d n)) : Set (Site d)))
    {a : unitInterval}
    (hstep : ∀ h, E.Admissible h →
      ¬ h.Terminal (zdGraph d) (box d n) 0 (↑(innerBoundary (zdGraph d) (box d n)) : Set (Site d)) →
      (a : ℝ) ≤ h.prob E.density (E.succ h))
    (h₀ : Transcript κ (Site d)) (hadm : E.Admissible h₀) (hins : h₀.inspected = ∅)
    (hopen : h₀.openV = {0}) (hclosed : h₀.closedV = ∅) (m : ℕ)
    (hm : h₀.undetermined (box d n) ≤ m) :
    thetaSite d a
      ≤ (prodBernoulli E.density).real
          {ω | (E.run m h₀ ω).Reaches (zdGraph d) 0
            (↑(innerBoundary (zdGraph d) (box d n)) : Set (Site d))} :=
  (thetaSite_le_pinnedProb_box n a).trans
    (E.pinnedProb_singleton_le_real_run hstep h₀ hadm hins hopen hclosed m hm)

end Exploration

/-- **The conclusion the renormalisation needs, with the parameter made explicit.**  For `d ≥ 2`
there are `a < 1` and `η > 0` such that every exploration of every box of `ℤ^d` towards its inner
boundary whose steps succeed with pinned probability at least `a` reaches the boundary with
probability at least `η`, from a start knowing only that the origin is open. -/
theorem exists_param_thetaSite_le_real_run_box [NeZero d] (hd : 2 ≤ d) :
    ∃ a : unitInterval, (a : ℝ) < 1 ∧ ∃ η : ℝ, 0 < η ∧
      ∀ (n : ℕ) (κ : Type) [DecidableEq κ]
        (E : Exploration κ (zdGraph d) (box d n) 0
          (↑(innerBoundary (zdGraph d) (box d n)) : Set (Site d))),
        (∀ h, E.Admissible h →
          ¬ h.Terminal (zdGraph d) (box d n) 0
            (↑(innerBoundary (zdGraph d) (box d n)) : Set (Site d)) →
          (a : ℝ) ≤ h.prob E.density (E.succ h)) →
        ∀ (h₀ : Transcript κ (Site d)), E.Admissible h₀ → h₀.inspected = ∅ →
          h₀.openV = {0} → h₀.closedV = ∅ → ∀ m : ℕ, h₀.undetermined (box d n) ≤ m →
          η ≤ (prodBernoulli E.density).real
            {ω | (E.run m h₀ ω).Reaches (zdGraph d) 0
              (↑(innerBoundary (zdGraph d) (box d n)) : Set (Site d))} := by
  obtain ⟨a, ha1, hapos⟩ := exists_thetaSite_pos d hd
  refine ⟨a, ha1, thetaSite d a, hapos, ?_⟩
  intro n κ _ E hstep h₀ hadm hins hopen hclosed m hm
  exact E.thetaSite_le_real_run_box hstep h₀ hadm hins hopen hclosed m hm

end Boxes

/-! ## Part 6: non-vacuity

The exploration reading one vertex of the arena at a time, calling it open when it is open, meets
every hypothesis of `Exploration` with the one-step bound holding at the exact density.  On the
two-vertex graph at density one half the Bernoulli value of the pinned start is exactly `1/2`, so
the domination there is the statement `1/2 ≤ P(reach)`, a bound that is neither `0` nor `1`. -/

section SiteExploration

variable {V : Type*} (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V)

open Classical in
/-- A frontier vertex, when there is one. -/
def pickBoundary (h : Transcript V V) : V :=
  if hne : (h.boundary G A o).Nonempty then hne.choose else o

theorem pickBoundary_mem {h : Transcript V V} (hne : (h.boundary G A o).Nonempty) :
    pickBoundary G A o h ∈ h.boundary G A o := by
  unfold pickBoundary
  rw [dif_pos hne]
  exact hne.choose_spec

theorem boundary_nonempty_of_not_terminal {h : Transcript V V} (hT : ¬ h.Terminal G A o T) :
    (h.boundary G A o).Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun he => hT (Or.inr he)

variable [DecidableEq V]

/-- **The one-vertex exploration.**  The sites are the vertices themselves, the next examination
reads the frontier vertex it examines, and the verdict is the state of that vertex.  Admissible
transcripts have read only determined vertices. -/
def siteExploration (a : unitInterval) : Exploration V G A o T where
  density _ := a
  Admissible h := h.inspected ⊆ h.openV ∪ h.closedV
  next h := pickBoundary G A o h
  region h := {pickBoundary G A o h}
  succ h := {ω | pickBoundary G A o h ∈ ω}
  succ_measurable _ := measurableSet_mem _
  next_mem_boundary _ _ hT := pickBoundary_mem G A o (boundary_nonempty_of_not_terminal G A o T hT)
  region_fresh h hadm hT := by
    obtain ⟨-, hzo, hzc, -⟩ := pickBoundary_mem G A o (boundary_nonempty_of_not_terminal G A o T hT)
    rw [Finset.disjoint_singleton_left]
    intro hz
    have := hadm hz
    simp [hzo, hzc] at this
  succ_determinedBy h _ _ := by
    refine (determinedBy_setOf_mem_coord (pickBoundary G A o h)).mono ?_
    rw [Set.singleton_subset_iff, Finset.coe_union, Finset.coe_singleton]
    exact Set.mem_union_right _ (Set.mem_singleton _)
  step_admissible h hadm _ b ω _ := by
    rw [Transcript.step_inspected, Transcript.step_determined]
    exact Finset.union_subset (hadm.trans (Finset.subset_insert _ _))
      (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _))

/-- **The one-step bound holds with the exact density.**  The vertex examined next has not been
read, so pinning the transcript does not move its probability of being open. -/
theorem siteExploration_step (a : unitInterval) (h : Transcript V V)
    (hadm : (siteExploration G A o T a).Admissible h) (hT : ¬ h.Terminal G A o T) :
    (a : ℝ) ≤ h.prob (siteExploration G A o T a).density ((siteExploration G A o T a).succ h) := by
  obtain ⟨-, hzo, hzc, -⟩ := pickBoundary_mem G A o (boundary_nonempty_of_not_terminal G A o T hT)
  have hz : pickBoundary G A o h ∉ h.inspected := fun hz => by
    have := hadm hz
    simp [hzo, hzc] at this
  have hdet : DeterminedBy {ω : Set V | pickBoundary G A o h ∈ ω} ((↑h.inspected : Set V)ᶜ) := by
    refine (determinedBy_setOf_mem_coord _).mono ?_
    rw [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]
    exact hz
  show (a : ℝ) ≤ pinnedProb (fun _ : V => a) (↑h.inspected : Set V) h.state
    {ω : Set V | pickBoundary G A o h ∈ ω}
  rw [pinnedProb_eq_of_determinedBy_compl _ _ _ hdet, prodBernoulli_real_setOf_mem]

end SiteExploration

section TwoVertex

/-- On the two-vertex graph with the root pinned open, the benchmark is the event that the other
vertex is open, of probability exactly `a`. -/
theorem bern_two_vertex (a : unitInterval) :
    pinnedProb (fun _ : Bool => a) {false} (fun _ => True)
        (targetConn (⊤ : SimpleGraph Bool) Finset.univ false {true}) = (a : ℝ) := by
  have hset : substitute ({false} : Set Bool) (fun _ => True) ⁻¹'
      targetConn (⊤ : SimpleGraph Bool) Finset.univ false {true} = {ω : Set Bool | true ∈ ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [mem_targetConn_iff]
    simp only [Set.mem_singleton_iff, exists_eq_left]
    have hf : false ∈ substitute ({false} : Set Bool) (fun _ => True) ω :=
      (mem_substitute_of_mem (fun _ => True) (Set.mem_singleton false)).2 trivial
    have ht : true ∈ substitute ({false} : Set Bool) (fun _ => True) ω ↔ true ∈ ω :=
      mem_substitute_of_notMem (fun _ => True) (by simp)
    constructor
    · rintro ⟨-, hr⟩
      have hmem := mem_of_mem_siteCluster (⊤ : SimpleGraph Bool) _
        ⟨(⟨hf, by simp⟩ : false ∈ substitute ({false} : Set Bool) (fun _ => True) ω
          ∩ (↑(Finset.univ : Finset Bool) : Set Bool)), hr⟩
      exact ht.1 hmem.1
    · intro h
      refine ⟨⟨hf, by simp⟩, SimpleGraph.Adj.reachable ?_⟩
      exact (openSiteGraph_adj_iff' (⊤ : SimpleGraph Bool) _ false true).2
        ⟨by simp, ⟨hf, by simp⟩, ⟨ht.2 h, by simp⟩⟩
  rw [pinnedProb, hset, prodBernoulli_real_setOf_mem]

/-- **A bound that is neither zero nor one.**  The one-vertex exploration of the two-vertex graph
at density `half`, started knowing the root open, reaches the other vertex with probability at
least `1/2`.  The constant `half` is `Percolation.Literature.half`. -/
theorem two_vertex_bound :
    (1 / 2 : ℝ) ≤ (prodBernoulli (fun _ : Bool => half)).real
      {ω | ((siteExploration (⊤ : SimpleGraph Bool) Finset.univ false {true} half).run 2
        ⟨∅, ∅, Finset.Subset.refl _, {false}, ∅⟩ ω).Reaches (⊤ : SimpleGraph Bool) false {true}} := by
  have h := (siteExploration (⊤ : SimpleGraph Bool) Finset.univ false {true} half)
    |>.pinnedProb_singleton_le_real_run
      (siteExploration_step (⊤ : SimpleGraph Bool) Finset.univ false {true} half)
      ⟨∅, ∅, Finset.Subset.refl _, {false}, ∅⟩ (Finset.empty_subset _) rfl rfl rfl 2
      ((Finset.card_le_univ _).trans (by simp))
  rw [bern_two_vertex, coe_half] at h
  exact h

end TwoVertex

end KNAll.Site.FRDom

end

section AxiomCheck

open KNAll.Site.FRDom

#print axioms KNAll.Site.FRDom.le_pinnedProb_inter_of_forall_extend_of_mem
#print axioms KNAll.Site.FRDom.Transcript.bern_eq_zero_of_boundary_eq_empty
#print axioms KNAll.Site.FRDom.Transcript.bern_split
#print axioms KNAll.Site.FRDom.Exploration.terminal_run
#print axioms KNAll.Site.FRDom.Exploration.measurableSet_setOf_run
#print axioms KNAll.Site.FRDom.Exploration.bern_le_prob_run
#print axioms KNAll.Site.FRDom.Exploration.pinnedProb_singleton_le_real_run
#print axioms KNAll.Site.FRDom.Exploration.real_le_real_run
#print axioms KNAll.Site.FRDom.thetaSiteOn_le_pinnedProb_targetConn
#print axioms KNAll.Site.FRDom.thetaSite_le_pinnedProb_box
#print axioms KNAll.Site.FRDom.exists_param_thetaSite_pos_le_box
#print axioms KNAll.Site.FRDom.Exploration.thetaSite_le_real_run_box
#print axioms KNAll.Site.FRDom.exists_param_thetaSite_le_real_run_box
#print axioms KNAll.Site.FRDom.siteExploration_step
#print axioms KNAll.Site.FRDom.bern_two_vertex
#print axioms KNAll.Site.FRDom.two_vertex_bound

end AxiomCheck
