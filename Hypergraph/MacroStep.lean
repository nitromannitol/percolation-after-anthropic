import Hypergraph.MacroDomination
import Hypergraph.PinnedProb
import Hypergraph.MacroToSlab

/-!
# The one-step contract of the block exploration

The renormalisation examines the blocks of a coarse lattice one at a time.  Its central claim is a
statement about a single step: after any finite history of the exploration, the next block examined
is joined to the growing cluster with conditional probability at least `1 - rho`.  This module
states that claim and proves everything about it that does not involve the geometry.

The surrounding pieces are already in place.  `KN.Exploration` turns a uniform lower bound on the
conditional success probability into a comparison with independent Bernoulli trials, and
`KNAll.Site.thetaSiteOn_pos_of_cells` turns a supply of occupied blocks into an infinite cluster.
What was missing is the statement in between.

## Conditioning without denominators

A conditional probability would carry a positive-denominator side condition through every statement.
Following `KN/PinnedProb.lean`, the history is instead *substituted* into the configuration: the
inspected sites are overwritten by their recorded states and an ordinary product probability is
taken.  `MacroHistory.prob` is that quantity, and it is total, defined even for a history the
measure gives probability zero.  Every probability below is of this kind; none is a ratio.

## What is stated and what is proved

* `MacroHistory` records a finite transcript: the inspected sites, which of them are open, and the
  blocks already declared occupied.  The states are recorded as a `Finset` of open sites together
  with the containment `openSites ⊆ inspected`, rather than as a partial function; membership in a
  `Finset` is decidable and the substituted value function `MacroHistory.state` reads off directly.
* `MacroHistory.prob_eq_of_determinedBy_compl` and `MacroHistory.prob_extends_eq` are the two facts
  that make a pinned probability usable: pinning coordinates the event cannot see does nothing, and
  extending a history by sites the event cannot see does nothing.
* `MacroSetup` is the data the geometry has to supply, and `MacroSetup.StepBound` is the one-step
  contract for one such setup.  `MacroStepBound` is the contract as a proposition of `d` and `rho`
  alone, with `PinnedSiteGluing` carried as an explicit hypothesis so that the dependence on the
  gluing inequality is visible in the statement.  It is an interface: nothing here proves it.
* `MacroSetup.exploration` builds a `KN.Exploration` out of the history type, and
  `MacroSetup.le_reachProb_of_le_bernoulli` feeds it to `KN.Exploration.le_reachProb_of_le_bernoulli`.
  This is the one place where the one-step contract is actually consumed.
* `thetaSiteOn_pos_of_reachTransfer` combines that with `thetaSiteOn_pos_of_cells`, and
  `thetaSiteOn_pos_of_reachTransfer_comap` is the form the slab uses, where the cells are the traces
  of the blocks.  Both carry one further hypothesis, `ReachTransfer`.  `KN.walkProb` is a formal
  recursion on Boolean words, not a measure on configurations, and nothing in the development
  identifies the two; the coupling that does is a separate workstream, so it appears here as a named
  hypothesis rather than as a proof.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Two further facts about pinned probabilities

`KN/PinnedProb.lean` proves what is needed to move the pinned set.  Moving the pinned *values*, and
the elementary range bounds, are recorded here. -/

section Pinned

variable {ι : Type*}

/-- Substitution reads the prescribed values only on the pinned set, so two prescriptions agreeing
there give the same substituted configuration. -/
theorem substitute_congr {R : Set ι} {val val' : ι → Prop} (hv : ∀ i ∈ R, (val i ↔ val' i))
    (ω : Set ι) : substitute R val ω = substitute R val' ω := by
  ext i
  by_cases hi : i ∈ R
  · rw [mem_substitute_of_mem val hi, mem_substitute_of_mem val' hi]
    exact hv i hi
  · rw [mem_substitute_of_notMem val hi, mem_substitute_of_notMem val' hi]

/-- Two prescriptions agreeing on the pinned set give the same pinned probability. -/
theorem pinnedProb_congr_val (p : ι → unitInterval) (R : Set ι) {val val' : ι → Prop}
    (hv : ∀ i ∈ R, (val i ↔ val' i)) (A : Set (Set ι)) :
    pinnedProb p R val A = pinnedProb p R val' A := by
  have h : substitute R val = substitute R val' := funext (substitute_congr hv)
  simp only [pinnedProb, h]

-- Named `_coord`: `KN/SiteFiniteEnergy.lean` declares `pinnedProb_nonneg` and
-- `pinnedProb_le_one` in this namespace for site configurations, and having both made these
-- modules mutually un-importable.  These are the versions generic in the coordinate type.
theorem pinnedProb_nonneg_coord (p : ι → unitInterval) (R : Set ι) (val : ι → Prop) (A : Set (Set ι)) :
    0 ≤ pinnedProb p R val A := by
  simp only [pinnedProb]
  exact measureReal_nonneg

theorem pinnedProb_le_one_coord (p : ι → unitInterval) (R : Set ι) (val : ι → Prop) (A : Set (Set ι)) :
    pinnedProb p R val A ≤ 1 := by
  simp only [pinnedProb]
  exact measureReal_le_one

end Pinned

/-! ## Target 1: a finite history -/

/-- **A finite transcript of the exploration.**  `inspected` is the finite set of sites whose state
has been read, `openSites` is the subset of them found open, and `occupied` is the finite set of
coarse blocks already declared occupied.

Recording the states as a `Finset` of open sites, rather than as a partial function on `inspected`,
keeps everything decidable and makes the substituted value function of `KN/PinnedProb.lean` a plain
membership test.  Nothing here is a filtration: a history is a finite piece of data. -/
structure MacroHistory (d : ℕ) (M : Type*) where
  /-- The sites whose state has been read. -/
  inspected : Finset (Site d)
  /-- Those of them that were found open. -/
  openSites : Finset (Site d)
  /-- Only inspected sites have a recorded state. -/
  openSites_subset : openSites ⊆ inspected
  /-- The blocks already declared occupied. -/
  occupied : Finset M

namespace MacroHistory

variable {d : ℕ} {M : Type*}

/-- The recorded states, as the value function that `substitute` and `pinnedProb` consume: a site
is prescribed open exactly when it is one of the open inspected sites. -/
def state (h : MacroHistory d M) : Site d → Prop := fun x => x ∈ h.openSites

theorem state_iff (h : MacroHistory d M) (x : Site d) : h.state x ↔ x ∈ h.openSites := Iff.rfl

/-- A site recorded open has been inspected. -/
theorem mem_inspected_of_state {h : MacroHistory d M} {x : Site d} (hx : h.state x) :
    x ∈ h.inspected :=
  h.openSites_subset hx

/-! ### Growing a history -/

/-- `h'` extends `h`: it has inspected at least as many sites, and it records the same states on the
sites `h` had already inspected. -/
structure Extends (h' h : MacroHistory d M) : Prop where
  /-- Nothing already inspected is forgotten. -/
  inspected_subset : h.inspected ⊆ h'.inspected
  /-- Nothing already recorded is revised. -/
  state_agree : ∀ x ∈ h.inspected, (h'.state x ↔ h.state x)

theorem Extends.refl (h : MacroHistory d M) : h.Extends h :=
  ⟨Finset.Subset.refl _, fun _ _ => Iff.rfl⟩

theorem Extends.trans {h h' h'' : MacroHistory d M} (h1 : h''.Extends h') (h2 : h'.Extends h) :
    h''.Extends h :=
  ⟨h2.inspected_subset.trans h1.inspected_subset,
    fun x hx => (h1.state_agree x (h2.inspected_subset hx)).trans (h2.state_agree x hx)⟩

/-! ## Target 2: conditioning without denominators -/

/-- **The probability of `A` after the history `h`.**  The inspected sites are overwritten by their
recorded states and an ordinary product probability is taken; no ratio is formed, and the quantity
is defined for every history, including one of probability zero. -/
def prob (h : MacroHistory d M) (p : Site d → unitInterval) (A : Set (SiteConfig (Site d))) : ℝ :=
  pinnedProb p (↑h.inspected : Set (Site d)) h.state A

theorem prob_eq (h : MacroHistory d M) (p : Site d → unitInterval)
    (A : Set (SiteConfig (Site d))) :
    h.prob p A = pinnedProb p (↑h.inspected : Set (Site d)) h.state A := rfl

theorem prob_nonneg (h : MacroHistory d M) (p : Site d → unitInterval)
    (A : Set (SiteConfig (Site d))) : 0 ≤ h.prob p A :=
  pinnedProb_nonneg_coord _ _ _ _

theorem prob_le_one (h : MacroHistory d M) (p : Site d → unitInterval)
    (A : Set (SiteConfig (Site d))) : h.prob p A ≤ 1 :=
  pinnedProb_le_one_coord _ _ _ _

/-- **Pinning what the event cannot see.**  An event determined by the sites outside the inspected
set has the same probability after the history as before it.  This is
`pinnedProb_eq_of_determinedBy_compl`, read at a history. -/
theorem prob_eq_of_determinedBy_compl (h : MacroHistory d M) (p : Site d → unitInterval)
    {A : Set (SiteConfig (Site d))} (hA : DeterminedBy A (↑h.inspected : Set (Site d))ᶜ) :
    h.prob p A = (prodBernoulli p).real A :=
  pinnedProb_eq_of_determinedBy_compl p _ _ hA

/-- **Extending by what the event cannot see.**  If `A` is determined by the sites of `F`, and the
sites inspected by `h'` but not by `h` avoid `F`, then the two histories give `A` the same
probability.  This is `pinnedProb_union_eq`, read at a pair of histories; the agreement of the two
records on `h.inspected` is what lets the pinned values be compared. -/
theorem prob_extends_eq {h h' : MacroHistory d M} (hext : h'.Extends h)
    (p : Site d → unitInterval) {A : Set (SiteConfig (Site d))} {F : Set (Site d)}
    (hA : DeterminedBy A F)
    (hdisj : Disjoint ((↑h'.inspected : Set (Site d)) \ ↑h.inspected) F) :
    h'.prob p A = h.prob p A := by
  have hsub : (↑h.inspected : Set (Site d)) ⊆ ↑h'.inspected :=
    Finset.coe_subset.2 hext.inspected_subset
  have hunion : (↑h.inspected : Set (Site d)) ∪ ((↑h'.inspected : Set (Site d)) \ ↑h.inspected)
      = (↑h'.inspected : Set (Site d)) := by
    rw [Set.union_sdiff_self, Set.union_eq_self_of_subset_left hsub]
  have hTS : Disjoint ((↑h'.inspected : Set (Site d)) \ ↑h.inspected)
      (F \ (↑h.inspected : Set (Site d))) := hdisj.mono_right Set.sdiff_subset
  have key : pinnedProb p ((↑h.inspected : Set (Site d)) ∪
        ((↑h'.inspected : Set (Site d)) \ ↑h.inspected)) h'.state A
      = pinnedProb p (↑h.inspected : Set (Site d)) h'.state A :=
    pinnedProb_union_eq p h'.state hA hTS
  rw [hunion] at key
  have hval : pinnedProb p (↑h.inspected : Set (Site d)) h'.state A
      = pinnedProb p (↑h.inspected : Set (Site d)) h.state A :=
    pinnedProb_congr_val p _ (fun x hx => hext.state_agree x (Finset.mem_coe.1 hx)) A
  rw [prob_eq, prob_eq, key, hval]

end MacroHistory

/-! ## Target 3: the one-step contract

The contract needs the data it speaks about: which blocks there are, where they sit, at what density
the sites are open, what "joined" means for a block, which histories the exploration can produce and
in what order it examines the blocks.  `MacroSetup` collects exactly that, and nothing more.  None of
it is constructed here; the construction is the geometric workstream. -/

/-- **The data of a block exploration.**  A coarse index type, a block of sites for each index, the
density of the underlying site percolation, the event that a block is joined to the growing cluster,
and the exploration itself: which histories are reachable, which block is examined next, and how the
history grows once the answer is known.

The two hypotheses `step_extends` and `next_notMem_occupied` say that the exploration never revises a
recorded state and never re-examines a block it has already declared occupied. -/
structure MacroSetup (d : ℕ) where
  /-- The coarse lattice: one index per block. -/
  Index : Type
  /-- The sites belonging to a block. -/
  block : Index → Set (Site d)
  /-- Distinct blocks are disjoint, which is what lets occupied blocks be counted. -/
  block_disjoint : ∀ m m' : Index, m ≠ m' → Disjoint (block m) (block m')
  /-- The density of the underlying site percolation. -/
  density : Site d → unitInterval
  /-- The event that a block is joined to the growing cluster. -/
  joined : Index → Set (SiteConfig (Site d))
  /-- The histories the exploration can produce. -/
  Admissible : MacroHistory d Index → Prop
  /-- The history the exploration starts from. -/
  start : MacroHistory d Index
  /-- The starting history is admissible. -/
  start_admissible : Admissible start
  /-- The block examined after a given history. -/
  next : MacroHistory d Index → Index
  /-- How the history grows once the examined block has answered. -/
  step : MacroHistory d Index → Bool → MacroHistory d Index
  /-- A step of the exploration keeps the history admissible. -/
  step_admissible : ∀ h b, Admissible h → Admissible (step h b)
  /-- A step only adds information: no recorded state is revised. -/
  step_extends : ∀ h b, (step h b).Extends h
  /-- The block examined next is pending: it has not already been declared occupied. -/
  next_notMem_occupied : ∀ h, Admissible h → next h ∉ h.occupied

variable {d : ℕ}

/-- **The one-step contract for one setup.**  After every admissible history, every block still
pending examination is joined with probability at least `1 - rho`, the probability being the pinned
one of `MacroHistory.prob` rather than a conditional probability.

Note: this over-quantifies.  It demands the bound at every block outside `occupied`, but a
block already examined and failed is still outside `occupied` and has small conditional
probability, so the geometry cannot supply it.  Only `S.next h` is ever used; see
`KNAll.Site.SiteWalk.NextBound` in `KN/ReachCoupling.lean` for the usable form, together with
`SiteWalk.StepBound.nextBound`. -/
def MacroSetup.StepBound (S : MacroSetup d) (rho : ℝ) : Prop :=
  ∀ h : MacroHistory d S.Index, S.Admissible h →
    ∀ m : S.Index, m ∉ h.occupied → 1 - rho ≤ h.prob S.density (S.joined m)

/-- **The one-step contract.**  The gluing inequality yields a block exploration whose every step
succeeds with probability at least `1 - rho`.

`PinnedSiteGluing` is a hypothesis of the definition, so that any consumer of `MacroStepBound`
displays the inequality it rests on.  This is an interface: the geometric construction that would
discharge it is a separate workstream and is not attempted here. -/
def MacroStepBound (d : ℕ) (rho : ℝ) : Prop :=
  PinnedSiteGluing → ∃ S : MacroSetup d, S.StepBound rho

/-! ## Target 4: from the one-step contract to a lower bound on the explored cluster

A run of the exploration is a word in `List Bool`, read left to right in the order the blocks are
examined.  The history after a run is the left fold of `step` over the word, and the block examined
next and its conditional success probability are functions of that history.  That is exactly a
`KN.Exploration`, whose uniform lower bound is the one-step contract. -/

/-! ### The size of the explored cluster, as an event of words -/

/-- The number of blocks declared occupied along a run. -/
def numJoined : List Bool → ℕ
  | [] => 0
  | true :: w => numJoined w + 1
  | false :: w => numJoined w

/-- The event that a run declares at least `k` blocks occupied.  This is the word form of "the
explored coarse cluster reaches size `k`". -/
def reachesSize (k : ℕ) (w : List Bool) : Prop := k ≤ numJoined w

/-- Turning failures into successes can only raise the count. -/
theorem numJoined_le_of_wordLE {u v : List Bool} (huv : WordLE u v) :
    numJoined u ≤ numJoined v := by
  induction huv with
  | nil => exact le_rfl
  | @cons a b l₁ l₂ hab _ ih =>
    cases a with
    | false =>
      cases b with
      | false => exact ih
      | true => exact Nat.le_succ_of_le ih
    | true =>
      have hb : b = true := hab rfl
      subst hb
      exact Nat.succ_le_succ ih

/-- Reaching a given size is upward closed, which is the only property of the target that the
Bernoulli comparison needs. -/
theorem monoWord_reachesSize (k : ℕ) : MonoWord (reachesSize k) := by
  intro u v hlen hget hu
  have hu' : k ≤ numJoined u := hu
  exact hu'.trans (numJoined_le_of_wordLE (List.forall₂_iff_get.2 ⟨hlen, hget⟩))

namespace MacroSetup

variable (S : MacroSetup d)

/-! ### The history after a run -/

/-- The history the exploration holds after the run `w`, read left to right. -/
def hist (w : List Bool) : MacroHistory d S.Index := w.foldl S.step S.start

@[simp] theorem hist_nil : S.hist [] = S.start := rfl

theorem hist_append_singleton (w : List Bool) (b : Bool) :
    S.hist (w ++ [b]) = S.step (S.hist w) b := by
  simp [hist]

theorem admissible_foldl :
    ∀ (w : List Bool) (h : MacroHistory d S.Index),
      S.Admissible h → S.Admissible (w.foldl S.step h) := by
  intro w
  induction w with
  | nil => intro h hh; exact hh
  | cons b w ih =>
    intro h hh
    exact ih (S.step h b) (S.step_admissible h b hh)

theorem hist_admissible (w : List Bool) : S.Admissible (S.hist w) :=
  S.admissible_foldl w S.start S.start_admissible

theorem hist_extends_step (w : List Bool) (b : Bool) :
    (S.hist (w ++ [b])).Extends (S.hist w) := by
  rw [S.hist_append_singleton w b]
  exact S.step_extends (S.hist w) b

/-- Continuing a run only adds information to the history. -/
theorem hist_extends_append (w v : List Bool) : (S.hist (w ++ v)).Extends (S.hist w) := by
  induction v generalizing w with
  | nil =>
    rw [List.append_nil]
    exact MacroHistory.Extends.refl (S.hist w)
  | cons b v ih =>
    have hrw : w ++ b :: v = (w ++ [b]) ++ v := by simp
    rw [hrw]
    exact (ih (w ++ [b])).trans (S.hist_extends_step w b)

/-- **The irrelevant continuation.**  An event determined by sites that the continuation never
inspects has the same probability after the longer run as after the shorter one. -/
theorem prob_hist_append_eq (w v : List Bool) {A : Set (SiteConfig (Site d))} {F : Set (Site d)}
    (hA : DeterminedBy A F)
    (hdisj : Disjoint ((↑(S.hist (w ++ v)).inspected : Set (Site d)) \
      ↑(S.hist w).inspected) F) :
    (S.hist (w ++ v)).prob S.density A = (S.hist w).prob S.density A :=
  MacroHistory.prob_extends_eq (S.hist_extends_append w v) S.density hA hdisj

/-- The trace of the blocks on another vertex set is again a pairwise disjoint family, which is the
form `thetaSiteOn_pos_of_cells` asks for.  On the slab, `f` is the inclusion into `ℤ^d`. -/
theorem disjoint_comap_block {V : Type*} (f : V → Site d) (m m' : S.Index) (hne : m ≠ m') :
    Disjoint (f ⁻¹' S.block m) (f ⁻¹' S.block m') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  exact Set.disjoint_left.1 (S.block_disjoint m m' hne) hy hy'

/-! ### The exploration -/

/-- The conditional probability, in the pinned sense, that the block examined after the run `w` is
joined to the growing cluster. -/
def stepProb (w : List Bool) : ℝ :=
  (S.hist w).prob S.density (S.joined (S.next (S.hist w)))

theorem stepProb_le_one (w : List Bool) : S.stepProb w ≤ 1 :=
  MacroHistory.prob_le_one _ _ _

theorem stepProb_nonneg (w : List Bool) : 0 ≤ S.stepProb w :=
  MacroHistory.prob_nonneg _ _ _

/-- The one-step contract, read after a run: the history reached is admissible and the block
examined next is pending, so the contract applies to it. -/
theorem le_stepProb {rho : ℝ} (hS : S.StepBound rho) (w : List Bool) :
    1 - rho ≤ S.stepProb w :=
  hS (S.hist w) (S.hist_admissible w) (S.next (S.hist w))
    (S.next_notMem_occupied (S.hist w) (S.hist_admissible w))

/-- **The exploration built from the history type.**  Its vertex type is the coarse lattice, its
examination order is `next` read along the run, and its conditional success probability is the
pinned probability that the examined block is joined.  The one-step contract is precisely the
uniform lower bound that `KN.Exploration` asks for. -/
def exploration {rho : ℝ} (hrho : rho ≤ 1) (hS : S.StepBound rho) :
    Exploration S.Index (1 - rho) where
  nextVertex w := S.next (S.hist w)
  succProb := S.stepProb
  a_nonneg := by linarith
  le_succProb := S.le_stepProb hS
  succProb_le_one := S.stepProb_le_one

@[simp] theorem exploration_succProb {rho : ℝ} (hrho : rho ≤ 1) (hS : S.StepBound rho) :
    (S.exploration hrho hS).succProb = S.stepProb := rfl

@[simp] theorem exploration_nextVertex {rho : ℝ} (hrho : rho ≤ 1) (hS : S.StepBound rho)
    (w : List Bool) : (S.exploration hrho hS).nextVertex w = S.next (S.hist w) := rfl

/-- **The domination.**  An exploration meeting the one-step contract reaches any upward-closed
target at least as often as independent Bernoulli(`1 - rho`) trials do. -/
theorem bernoulliReachProb_le {rho : ℝ} (hrho : rho ≤ 1) (hS : S.StepBound rho)
    (reaches : List Bool → Prop) (hreaches : MonoWord reaches) (n : ℕ) :
    bernoulliReachProb (1 - rho) reaches n ≤ (S.exploration hrho hS).reachProb reaches n :=
  (S.exploration hrho hS).bernoulliReachProb_le reaches hreaches n

/-- **Target 4.**  A lower bound on the Bernoulli(`1 - rho`) probability of reaching the target,
valid for every number of steps, is inherited by the exploration.  This is
`KN.Exploration.le_reachProb_of_le_bernoulli` applied to `MacroSetup.exploration`. -/
theorem le_reachProb_of_le_bernoulli {rho c : ℝ} (hrho : rho ≤ 1) (hS : S.StepBound rho)
    (reaches : List Bool → Prop) (hreaches : MonoWord reaches)
    (hc : ∀ n, c ≤ bernoulliReachProb (1 - rho) reaches n) (n : ℕ) :
    c ≤ (S.exploration hrho hS).reachProb reaches n :=
  (S.exploration hrho hS).le_reachProb_of_le_bernoulli reaches hreaches hc n

/-- **Target 4 at a target size.**  The explored coarse cluster reaches size `k` in `n` steps at
least as often as `n` Bernoulli(`1 - rho`) trials produce `k` successes.  Unlike the previous
statement this reads the Bernoulli bound at the one step count it is used at, which matters because
`bernoulliReachProb a (reachesSize k) n` vanishes for `n < k`. -/
theorem le_reachProb_reachesSize {rho c : ℝ} (hrho : rho ≤ 1) (hS : S.StepBound rho) (k n : ℕ)
    (hc : c ≤ bernoulliReachProb (1 - rho) (reachesSize k) n) :
    c ≤ (S.exploration hrho hS).reachProb (reachesSize k) n :=
  hc.trans (S.bernoulliReachProb_le hrho hS (reachesSize k) (monoWord_reachesSize k) n)

end MacroSetup

/-- **Target 4, from the interface.**  `MacroStepBound` hands back a setup, and the setup hands back
the comparison.  The setup is existentially bound because `MacroStepBound` asserts its existence;
`PinnedSiteGluing` is displayed, as it is a hypothesis of `MacroStepBound`. -/
theorem exists_exploration_le_reachProb (hgl : PinnedSiteGluing) {rho c : ℝ} (hrho : rho ≤ 1)
    (hM : MacroStepBound d rho) (k n : ℕ)
    (hc : c ≤ bernoulliReachProb (1 - rho) (reachesSize k) n) :
    ∃ (S : MacroSetup d) (hS : S.StepBound rho),
      c ≤ (S.exploration hrho hS).reachProb (reachesSize k) n := by
  obtain ⟨S, hS⟩ := hM hgl
  exact ⟨S, hS, S.le_reachProb_reachesSize hrho hS k n hc⟩

/-! ## Target 5: an infinite cluster in the slab

`thetaSiteOn_pos_of_cells` needs a lower bound, uniform in `n`, on the *measure* of the event that
`n` disjoint cells each contribute a site of the cluster of `x`.  What the exploration provides is a
lower bound on `KN.Exploration.reachProb`, which is a formal recursion on Boolean words.  Nothing in
the development identifies the two, and the coupling that would is not built here, so it appears as
the named hypothesis `ReachTransfer`. -/

/-- **The bridge from words to configurations.**  A run of `steps k` steps that declares `k` blocks
occupied is witnessed, in the product measure, by `k` cells each contributing a site of the cluster
of `x`.

REFUTED.  This does not follow from the one-step contract, and `MacroSetup` is too weak to make it
true: the structure has no field relating `joined`, `step`, `occupied` and the configuration, so the
word a run produces is tied to nothing the measure sees.  `KNAll.Site.not_reachTransfer` of
`KN/ReachCoupling.lean` exhibits a `MacroSetup` satisfying every field and the full
`MacroSetup.StepBound 0` whose exploration reaches size one with probability one while the
corresponding configuration event is empty.  The definition is kept only so that the refutation can
be stated.  The correct statement is `KNAll.Site.SiteWalk.bernoulliReachProb_le_prob_run`, whose
transcript is a genuine function of the configuration; use that instead. -/
def ReachTransfer {V M : Type*} {a : ℝ} (G : SimpleGraph V) (x : V) (p : unitInterval)
    (cell : M → Set V) (E : Exploration M a) (steps : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, E.reachProb (reachesSize k) (steps k) ≤
    (siteBernoulli (fun _ : V => p)).real
      {ω | ∃ (occ : Finset M) (rep : M → V), k ≤ occ.card ∧
            (∀ m ∈ occ, rep m ∈ cell m) ∧ (∀ m ∈ occ, rep m ∈ siteCluster G ω x)}

/-- **Target 5.**  The one-step contract, a Bernoulli(`1 - rho`) lower bound uniform in the target
size, and the transfer, together give an infinite open cluster at `x`.

Read on the slab graph, with `cell` the trace of the blocks on the slab, this is the conclusion the
renormalisation is aimed at.  The hypothesis `hbern` is percolation of the coarse lattice at density
`1 - rho`, in the word form the comparison produces: whatever size is asked for, some number of steps
attains it with probability at least `c`. -/
theorem thetaSiteOn_pos_of_reachTransfer {V : Type*} [Countable V] (S : MacroSetup d)
    (G : SimpleGraph V) (x : V) (p : unitInterval) (cell : S.Index → Set V)
    (hdisj : ∀ m m' : S.Index, m ≠ m' → Disjoint (cell m) (cell m'))
    {rho c : ℝ} (hrho : rho ≤ 1) (hS : S.StepBound rho) (hc : 0 < c) (steps : ℕ → ℕ)
    (hbern : ∀ k : ℕ, c ≤ bernoulliReachProb (1 - rho) (reachesSize k) (steps k))
    (htrans : ReachTransfer G x p cell (S.exploration hrho hS) steps) :
    0 < thetaSiteOn G x p := by
  refine thetaSiteOn_pos_of_cells G x p cell hdisj c hc fun k => ?_
  exact (S.le_reachProb_reachesSize hrho hS k (steps k) (hbern k)).trans (htrans k)

/-- **Target 5 with the cells supplied by the setup.**  The cells are the traces of the blocks under
a map `f` of the ambient vertex set into `ℤ^d`, the inclusion of the slab in the intended reading, so
that their disjointness comes from `MacroSetup.block_disjoint` rather than being assumed. -/
theorem thetaSiteOn_pos_of_reachTransfer_comap {V : Type*} [Countable V] (S : MacroSetup d)
    (G : SimpleGraph V) (x : V) (p : unitInterval) (f : V → Site d)
    {rho c : ℝ} (hrho : rho ≤ 1) (hS : S.StepBound rho) (hc : 0 < c) (steps : ℕ → ℕ)
    (hbern : ∀ k : ℕ, c ≤ bernoulliReachProb (1 - rho) (reachesSize k) (steps k))
    (htrans : ReachTransfer G x p (fun m => f ⁻¹' S.block m) (S.exploration hrho hS) steps) :
    0 < thetaSiteOn G x p :=
  thetaSiteOn_pos_of_reachTransfer S G x p _ (S.disjoint_comap_block f) hrho hS hc steps hbern htrans

end KNAll.Site

end
