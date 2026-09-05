import Hypergraph.MacroStep

/-!
# Coupling the formal reach recursion to the product measure

`KN/AdaptiveDomination.lean` proves a comparison between two laws on Boolean words, and
`KN/MacroStep.lean` states the one-step contract of a block exploration against the product measure.
Nothing in between identified `KN.walkProb`, a recursion on `List Bool`, with any probability
computed under `prodBernoulli`.  This file supplies the missing link.

## Part 1: pinned probabilities split along a fresh coordinate

`pinnedProb_split` is the law of total probability for a single coordinate outside the pinned set,
and `le_pinnedProb_inter_of_forall_extend` iterates it over a finite fresh set: a bound on the
pinned probability of `Y` valid for *every* prescription on `R ∪ F` extending the one on `R`
survives averaging over the fresh coordinates, and does so with the weight of any event `B`
determined by `R ∪ F` attached.  This is the conditional-independence ingredient, and freshness,
`Disjoint ↑F R`, is where it enters.

## Part 2: an exploration that reads an actual configuration

`SiteWalk` is a block exploration whose transcript is a genuine function of the configuration:
`SiteWalk.step` records the true states of the examined block and `SiteWalk.bit` records whether the
block was joined, so `SiteWalk.run` is the Boolean word the exploration reads off `ω`.  The main
theorem `SiteWalk.walkProb_le_prob_run` bounds the Bernoulli(`1 - rho`) reach probability of an
upward-closed word event below by the pinned probability of the corresponding configuration event,
`SiteWalk.bernoulliReachProb_le_prob_run` reads it at the empty transcript, where the pinning is
vacuous and the bound is against `prodBernoulli` itself, and `SiteWalk.thetaSiteOn_pos` turns that
into a positive percolation probability through `thetaSiteOn_pos_of_cells`.

The one-step bound is the named hypothesis `SiteWalk.NextBound`: after every admissible transcript
the block examined next is joined with pinned probability at least `1 - rho`.  It is implied by
`SiteWalk.StepBound`, which is `MacroSetup.StepBound` transcribed, but it is strictly weaker and it
is what the coupling consumes; `StepBound` asks the same of every pending block, including blocks
already examined and found wanting, which for the intended reading of `joined` is not a bound the
geometry can supply.

## Part 3: the hypotheses are satisfiable

`siteWalkOfInjection` is an exploration reading one fresh site at a time, for which
`SiteWalk.siteWalkOfInjection_nextBound` computes the one-step probability to be exactly the
density.  It witnesses that the hypotheses above are not vacuous.

## Part 4: what happens to `ReachTransfer`

`KNAll.Site.ReachTransfer` asks for `E.reachProb ≤ μ(...)` with `E = S.exploration hrho hS`, whose
step probability is read at the single transcript `S.hist w` attached to the word `w`.  It is not
merely unproved: `not_reachTransfer` exhibits a `MacroSetup` satisfying every field and the full
strength of `MacroSetup.StepBound` at `rho = 0` for which `ReachTransfer` is false.  The reason is
that `MacroSetup` relates `joined`, `step` and `occupied` to nothing: the word a run produces is not
tied to any configuration, so no inequality against the product measure can hold.  Two further
things go wrong even once such a link is added.  The transcript of a genuine exploration is not a
function of the word, since examining a block reveals the states of all of its sites while the word
records only the Boolean summary, so `walkProb S.stepProb` reads the step probability at one
transcript among many and need not dominate the truth.  And the composite the renormalisation
consumes is `c ≤ μ(...)`; the intermediate `E.reachProb` is inessential, and it is the composite
that is proved here.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Part 1: pinned probabilities and fresh coordinates -/

section PinnedTower

variable {ι : Type*}

/-- A configuration already agreeing with the prescription on the pinned set is unchanged by
substitution. -/
theorem substitute_eq_self {R : Set ι} {val : ι → Prop} {ω : Set ι}
    (h : ∀ i ∈ R, (i ∈ ω ↔ val i)) : substitute R val ω = ω := by
  ext i
  by_cases hi : i ∈ R
  · rw [mem_substitute_of_mem val hi]
    exact (h i hi).symm
  · rw [mem_substitute_of_notMem val hi]

/-- On the pinned set the substituted configuration is the prescription, whatever was substituted
into. -/
theorem substitute_inter_eq (R : Set ι) (val : ι → Prop) (ω : Set ι) :
    substitute R val ω ∩ R = {i | i ∈ R ∧ val i} := by
  ext i
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hs, hi⟩
    exact ⟨hi, (mem_substitute_of_mem val hi).1 hs⟩
  · rintro ⟨hi, hv⟩
    exact ⟨(mem_substitute_of_mem val hi).2 hv, hi⟩

/-- The substituted event is determined by the coordinates outside the pinned set: substitution
overwrites everything the pinning can see. -/
theorem determinedBy_substitute_preimage (R : Set ι) (val : ι → Prop) (A : Set (Set ι)) :
    DeterminedBy (substitute R val ⁻¹' A) Rᶜ := by
  rw [determinedBy_iff]
  intro ω ω' hω
  have hEq : substitute R val ω = substitute R val ω' := by
    ext i
    by_cases hi : i ∈ R
    · rw [mem_substitute_of_mem val hi, mem_substitute_of_mem val hi]
    · rw [mem_substitute_of_notMem val hi, mem_substitute_of_notMem val hi]
      have hic : i ∈ Rᶜ := hi
      exact ⟨fun hiω => ((Set.ext_iff.1 hω i).1 ⟨hiω, hic⟩).1,
        fun hiω => ((Set.ext_iff.1 hω i).2 ⟨hiω, hic⟩).1⟩
  simp only [Set.mem_preimage, hEq]

/-- The complement of an event determined by `K` is determined by `K`. -/
theorem determinedBy_compl {A : Set (Set ι)} {K : Set ι} (h : DeterminedBy A K) :
    DeterminedBy Aᶜ K := by
  rw [determinedBy_iff] at h ⊢
  intro ω ω' hω
  simp only [Set.mem_compl_iff, h ω ω' hω]

/-- Substitution is measurable, so substituted events are measurable. -/
theorem measurableSet_substitute_preimage (R : Set ι) (val : ι → Prop) {A : Set (Set ι)}
    (hA : MeasurableSet A) : MeasurableSet (substitute R val ⁻¹' A) :=
  measurable_substitute R val hA

/-- An event determined by the pinned set is pinned to a truth value: its substituted preimage is
everything or nothing. -/
theorem substitute_preimage_of_determinedBy {R : Set ι} (val : ι → Prop) {A : Set (Set ι)}
    (hA : DeterminedBy A R) :
    substitute R val ⁻¹' A = Set.univ ∨ substitute R val ⁻¹' A = ∅ := by
  by_cases hne : (substitute R val ⁻¹' A).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hne
    refine Or.inl (Set.eq_univ_of_forall fun ω => ?_)
    refine ((determinedBy_iff A R).1 hA (substitute R val ω) (substitute R val ω₀) ?_).2 hω₀
    rw [substitute_inter_eq, substitute_inter_eq]
  · exact Or.inr (Set.not_nonempty_iff_eq_empty.1 hne)

@[simp] theorem pinnedProb_univ (p : ι → unitInterval) (R : Set ι) (val : ι → Prop) :
    pinnedProb p R val (Set.univ : Set (Set ι)) = 1 := by
  rw [pinnedProb, Set.preimage_univ]
  exact probReal_univ

@[simp] theorem pinnedProb_emptyEvent (p : ι → unitInterval) (R : Set ι) (val : ι → Prop) :
    pinnedProb p R val (∅ : Set (Set ι)) = 0 := by
  rw [pinnedProb, Set.preimage_empty, measureReal_empty]

/-- Pinned probability is additive on disjoint events. -/
theorem pinnedProb_union (p : ι → unitInterval) (R : Set ι) (val : ι → Prop)
    {A B : Set (Set ι)} (hd : Disjoint A B) (hB : MeasurableSet B) :
    pinnedProb p R val (A ∪ B) = pinnedProb p R val A + pinnedProb p R val B := by
  rw [pinnedProb, pinnedProb, pinnedProb, Set.preimage_union]
  exact measureReal_union (hd.preimage _) (measurableSet_substitute_preimage R val hB)

/-- Pinned probability of a complement. -/
theorem pinnedProb_compl (p : ι → unitInterval) (R : Set ι) (val : ι → Prop)
    {A : Set (Set ι)} (hA : MeasurableSet A) :
    pinnedProb p R val Aᶜ = 1 - pinnedProb p R val A := by
  have hpre : substitute R val ⁻¹' Aᶜ = (substitute R val ⁻¹' A)ᶜ := Set.preimage_compl
  rw [pinnedProb, pinnedProb, hpre,
    measureReal_compl (measurableSet_substitute_preimage R val hA), probReal_univ]

/-- Prescribing one further value. -/
def setVal (val : ι → Prop) (i : ι) (b : Prop) : ι → Prop :=
  fun j => (j = i ∧ b) ∨ (j ≠ i ∧ val j)

theorem setVal_self (val : ι → Prop) (i : ι) (b : Prop) : setVal val i b i ↔ b := by
  simp [setVal]

theorem setVal_of_ne (val : ι → Prop) {i j : ι} (h : j ≠ i) (b : Prop) :
    setVal val i b j ↔ val j := by
  simp [setVal, h]

/-- **The law of total probability at one fresh coordinate.**  Pinning `R` and then averaging over
the state of a coordinate `i ∉ R` is the same as pinning `R` alone.  This is the only place where
the product structure of `prodBernoulli` is used; it enters through
`prodBernoulli_real_inter_of_determinedBy`, independence of `{i ∈ ω}` from everything determined by
the other coordinates. -/
theorem pinnedProb_split (p : ι → unitInterval) {R : Set ι} {i : ι} (hi : i ∉ R)
    (val : ι → Prop) {A : Set (Set ι)} (hA : MeasurableSet A) :
    pinnedProb p R val A
      = (p i : ℝ) * pinnedProb p (insert i R) (setVal val i True) A
        + (1 - (p i : ℝ)) * pinnedProb p (insert i R) (setVal val i False) A := by
  classical
  set C : Set (Set ι) := {ω : Set ι | i ∈ ω} with hCdef
  have hCm : MeasurableSet C := measurableSet_mem i
  have hCcompl : Cᶜ = {ω : Set ι | i ∉ ω} := rfl
  have hCd : DeterminedBy C (↑({i} : Finset ι) : Set ι) := by
    rw [determinedBy_iff]
    intro ω ω' hω
    have h2 := Set.ext_iff.1 hω i
    simp only [Finset.coe_singleton, Set.mem_inter_iff, Set.mem_singleton_iff, and_true] at h2
    simp only [hCdef, Set.mem_setOf_eq]
    exact h2
  -- the two substitutions agree with the unextended one on the two halves
  have hagree : ∀ (b : Prop) (ω : Set ι), (i ∈ ω ↔ b) →
      substitute R val ω = substitute (insert i R) (setVal val i b) ω := by
    intro b ω hb
    ext j
    by_cases hji : j = i
    · rw [hji, mem_substitute_of_notMem val hi,
        mem_substitute_of_mem (setVal val i b) (Set.mem_insert i R), setVal_self]
      exact hb
    · by_cases hjR : j ∈ R
      · rw [mem_substitute_of_mem val hjR,
          mem_substitute_of_mem (setVal val i b) (Set.mem_insert_of_mem i hjR),
          setVal_of_ne val hji]
      · have hj : j ∉ insert i R := by simp [hji, hjR]
        rw [mem_substitute_of_notMem val hjR, mem_substitute_of_notMem (setVal val i b) hj]
  set sT := substitute (insert i R) (setVal val i True) with hsT
  set sF := substitute (insert i R) (setVal val i False) with hsF
  have keyT : substitute R val ⁻¹' A ∩ C = sT ⁻¹' A ∩ C := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, and_congr_left_iff]
    intro hω
    rw [hagree True ω (by simpa [hCdef] using hω)]
  have keyF : substitute R val ⁻¹' A ∩ Cᶜ = sF ⁻¹' A ∩ Cᶜ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, and_congr_left_iff]
    intro hω
    rw [hagree False ω (by simpa [hCcompl] using hω)]
  have hsplit : ∀ X : Set (Set ι), MeasurableSet X →
      (prodBernoulli p).real X
        = (prodBernoulli p).real (X ∩ C) + (prodBernoulli p).real (X ∩ Cᶜ) := by
    intro X hX
    have hXeq : X = (X ∩ C) ∪ (X ∩ Cᶜ) := by
      rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
    conv_lhs => rw [hXeq]
    exact measureReal_union (Set.disjoint_left.2 fun ω hω hω' => hω'.2 hω.2) (hX.inter hCm.compl)
  -- independence of the coordinate `i` from the substituted events
  have hdT : DeterminedBy (sT ⁻¹' A) (↑({i} : Finset ι) : Set ι)ᶜ := by
    refine (determinedBy_substitute_preimage (insert i R) (setVal val i True) A).mono ?_
    simp only [Finset.coe_singleton]
    exact Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 (Set.mem_insert i R))
  have hdF : DeterminedBy (sF ⁻¹' A) (↑({i} : Finset ι) : Set ι)ᶜ := by
    refine (determinedBy_substitute_preimage (insert i R) (setVal val i False) A).mono ?_
    simp only [Finset.coe_singleton]
    exact Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 (Set.mem_insert i R))
  have hindT : (prodBernoulli p).real (C ∩ sT ⁻¹' A)
      = (prodBernoulli p).real C * (prodBernoulli p).real (sT ⁻¹' A) :=
    prodBernoulli_real_inter_of_determinedBy p {i} hCd hdT hCm
      (measurableSet_substitute_preimage _ _ hA)
  have hindF : (prodBernoulli p).real (Cᶜ ∩ sF ⁻¹' A)
      = (prodBernoulli p).real Cᶜ * (prodBernoulli p).real (sF ⁻¹' A) :=
    prodBernoulli_real_inter_of_determinedBy p {i} (determinedBy_compl hCd) hdF hCm.compl
      (measurableSet_substitute_preimage _ _ hA)
  have hCval : (prodBernoulli p).real C = (p i : ℝ) := prodBernoulli_real_setOf_mem p i
  have hCcval : (prodBernoulli p).real Cᶜ = 1 - (p i : ℝ) := by
    rw [hCcompl]; exact prodBernoulli_real_setOf_notMem p i
  calc pinnedProb p R val A
      = (prodBernoulli p).real (substitute R val ⁻¹' A ∩ C)
        + (prodBernoulli p).real (substitute R val ⁻¹' A ∩ Cᶜ) := by
        rw [pinnedProb]
        exact hsplit _ (measurableSet_substitute_preimage _ _ hA)
    _ = (prodBernoulli p).real (C ∩ sT ⁻¹' A) + (prodBernoulli p).real (Cᶜ ∩ sF ⁻¹' A) := by
        rw [keyT, keyF, Set.inter_comm (sT ⁻¹' A) C, Set.inter_comm (sF ⁻¹' A) Cᶜ]
    _ = (p i : ℝ) * pinnedProb p (insert i R) (setVal val i True) A
        + (1 - (p i : ℝ)) * pinnedProb p (insert i R) (setVal val i False) A := by
        rw [hindT, hindF, hCval, hCcval, pinnedProb, pinnedProb]

/-- **The tower inequality over a finite fresh set.**  Suppose the lower bound `c` for the pinned
probability of `Y` holds for *every* prescription on `R ∪ F` that extends the one already fixed on
`R`.  Then it survives averaging over the fresh coordinates, carrying the weight of any event `B`
determined by `R ∪ F`.

This is the conditional-independence step, and freshness is where it enters: the hypothesis
`Disjoint ↑F R` is what makes `pinnedProb_split` applicable at each coordinate of `F` in turn, so
that the average is a genuine law of total probability rather than a re-reading of coordinates whose
state has already been fixed. -/
theorem le_pinnedProb_inter_of_forall_extend (p : ι → unitInterval) {c : ℝ}
    {B Y : Set (Set ι)} (hBm : MeasurableSet B) (hYm : MeasurableSet Y) :
    ∀ (F : Finset ι) (R : Set ι), Disjoint (↑F : Set ι) R → ∀ val : ι → Prop,
      DeterminedBy B (R ∪ ↑F) →
      (∀ val' : ι → Prop, (∀ j ∈ R, (val' j ↔ val j)) → c ≤ pinnedProb p (R ∪ ↑F) val' Y) →
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
      rw [h1, h2, mul_one]
      exact hstep val fun _ _ => Iff.rfl
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
          c ≤ pinnedProb p (insert i R ∪ (↑F : Set ι)) val' Y := by
      intro b val' hval'
      rw [← hset]
      refine hstep val' fun j hj => ?_
      have hji : j ≠ i := fun h => hiR (h ▸ hj)
      exact (hval' j (Set.mem_insert_of_mem i hj)).trans (setVal_of_ne val hji b)
    have hT := ih (insert i R) hdisj' (setVal val i True) hB'
      (hstep' True)
    have hF := ih (insert i R) hdisj' (setVal val i False) hB'
      (hstep' False)
    have hp0 : (0 : ℝ) ≤ (p i : ℝ) := (p i).2.1
    have hp1 : (0 : ℝ) ≤ 1 - (p i : ℝ) := by linarith [(p i).2.2]
    have h1 := mul_le_mul_of_nonneg_left hT hp0
    have h2 := mul_le_mul_of_nonneg_left hF hp1
    rw [pinnedProb_split p hiR val hBm, pinnedProb_split p hiR val (hBm.inter hYm)]
    linarith

end PinnedTower

/-! ## Part 2: an exploration that reads an actual configuration

The transcript of a genuine exploration is a function of the configuration, not of the Boolean word
alone: examining a block reveals the states of all of its sites, and the Boolean answer is only a
summary of them.  `SiteWalk` is the corresponding data, `SiteWalk.step` records the true states of
the examined block, and `SiteWalk.run` reads off the word. -/

variable {d : ℕ}

/-- Two transcripts with equal fields are equal. -/
theorem MacroHistory.eq_of_fields {M : Type*} {h h' : MacroHistory d M}
    (hi : h.inspected = h'.inspected) (ho : h.openSites = h'.openSites)
    (hoc : h.occupied = h'.occupied) : h = h' := by
  obtain ⟨i1, o1, s1, c1⟩ := h
  obtain ⟨i2, o2, s2, c2⟩ := h'
  simp only at hi ho hoc
  subst hi; subst ho; subst hoc
  rfl

/-- **A block exploration of site percolation.**  A coarse index type with a finite block of sites
for each index, a density, the event that a block is joined to the growing cluster, the histories
the exploration can produce, and the block examined after a given history.

The three hypotheses that carry content are the last three.  `next_notMem_occupied` says the
exploration always has a pending block to examine, so it takes a genuine step at every index and
never stops for want of a candidate.  `next_block_fresh` says the block examined next has not been
looked at before: this is the freshness that the conditional-independence step needs.
`joined_determinedBy` says the answer is decided by what has been inspected once the examination is
over. -/
structure SiteWalk (d : ℕ) where
  /-- The coarse lattice: one index per block. -/
  Index : Type
  /-- Blocks can be told apart; this keeps the occupied set a `Finset`. -/
  decEq : DecidableEq Index
  /-- The sites of a block, a finite set. -/
  block : Index → Finset (Site d)
  /-- Distinct blocks are disjoint, which is what lets occupied blocks be counted. -/
  block_disjoint : ∀ m m' : Index, m ≠ m' →
    Disjoint (↑(block m) : Set (Site d)) (↑(block m') : Set (Site d))
  /-- The density of the underlying site percolation. -/
  density : Site d → unitInterval
  /-- The event that a block is joined to the growing cluster. -/
  joined : Index → Set (SiteConfig (Site d))
  /-- The joining events are measurable. -/
  joined_measurable : ∀ m, MeasurableSet (joined m)
  /-- The transcripts the exploration can produce. -/
  Admissible : MacroHistory d Index → Prop
  /-- The transcript the exploration starts from. -/
  start : MacroHistory d Index
  /-- The starting transcript is admissible. -/
  start_admissible : Admissible start
  /-- The exploration starts knowing nothing. -/
  start_inspected : start.inspected = ∅
  /-- The exploration starts having declared nothing occupied. -/
  start_occupied : start.occupied = ∅
  /-- The block examined after a given transcript. -/
  next : MacroHistory d Index → Index
  /-- There is always a pending block: the exploration never stops for want of a candidate. -/
  next_notMem_occupied : ∀ h, Admissible h → next h ∉ h.occupied
  /-- The block examined next has not been inspected before. -/
  next_block_fresh : ∀ h, Admissible h →
    Disjoint (↑(block (next h)) : Set (Site d)) (↑h.inspected : Set (Site d))
  /-- The answer is decided by the sites inspected by the end of the examination. -/
  joined_determinedBy : ∀ h, Admissible h →
    DeterminedBy (joined (next h))
      ((↑h.inspected : Set (Site d)) ∪ (↑(block (next h)) : Set (Site d)))

instance instDecidableEqIndex (S : SiteWalk d) : DecidableEq S.Index := S.decEq

namespace SiteWalk

variable (S : SiteWalk d)

open scoped Classical in
/-- **One examination.**  The block `S.next h` is inspected, the true states of its sites in `ω` are
recorded, and the block is declared occupied exactly when the recorded answer `b` is `true`. -/
def step (h : MacroHistory d S.Index) (b : Bool) (ω : SiteConfig (Site d)) :
    MacroHistory d S.Index where
  inspected := h.inspected ∪ S.block (S.next h)
  openSites := h.openSites ∪ (S.block (S.next h)).filter (fun x => x ∈ ω)
  openSites_subset := Finset.union_subset_union h.openSites_subset (Finset.filter_subset _ _)
  occupied := if b then insert (S.next h) h.occupied else h.occupied

open scoped Classical in
/-- **The answer.**  The examined block is joined, or it is not. -/
def bit (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) : Bool :=
  if ω ∈ S.joined (S.next h) then true else false

/-- The Boolean word produced by `n` examinations started from the transcript `h`. -/
def run (S : SiteWalk d) : ℕ → MacroHistory d S.Index → SiteConfig (Site d) → List Bool
  | 0, _, _ => []
  | n + 1, h, ω => S.bit h ω :: S.run n (S.step h (S.bit h ω) ω) ω

/-- The transcript reached after `n` examinations. -/
def runHist (S : SiteWalk d) :
    ℕ → MacroHistory d S.Index → SiteConfig (Site d) → MacroHistory d S.Index
  | 0, h, _ => h
  | n + 1, h, ω => S.runHist n (S.step h (S.bit h ω) ω) ω

@[simp] theorem run_zero (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) :
    S.run 0 h ω = [] := rfl

theorem run_succ (n : ℕ) (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) :
    S.run (n + 1) h ω = S.bit h ω :: S.run n (S.step h (S.bit h ω) ω) ω := by
  simp [run]

@[simp] theorem runHist_zero (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) :
    S.runHist 0 h ω = h := rfl

theorem runHist_succ (n : ℕ) (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) :
    S.runHist (n + 1) h ω = S.runHist n (S.step h (S.bit h ω) ω) ω := by
  simp [runHist]

theorem bit_eq_true_iff (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) :
    S.bit h ω = true ↔ ω ∈ S.joined (S.next h) := by
  classical
  by_cases hω : ω ∈ S.joined (S.next h) <;> simp [bit, hω]

theorem bit_of_mem {h : MacroHistory d S.Index} {ω : SiteConfig (Site d)}
    (hω : ω ∈ S.joined (S.next h)) : S.bit h ω = true := (S.bit_eq_true_iff h ω).2 hω

theorem bit_of_notMem {h : MacroHistory d S.Index} {ω : SiteConfig (Site d)}
    (hω : ω ∉ S.joined (S.next h)) : S.bit h ω = false := by
  classical
  simp [bit, hω]

@[simp] theorem step_inspected (h : MacroHistory d S.Index) (b : Bool)
    (ω : SiteConfig (Site d)) :
    (S.step h b ω).inspected = h.inspected ∪ S.block (S.next h) := rfl

theorem step_state (h : MacroHistory d S.Index) (b : Bool) (ω : SiteConfig (Site d))
    (x : Site d) :
    (S.step h b ω).state x ↔ (h.state x ∨ (x ∈ S.block (S.next h) ∧ x ∈ ω)) := by
  classical
  simp [MacroHistory.state, step, Finset.mem_union, Finset.mem_filter]

theorem step_occupied_true (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) :
    (S.step h true ω).occupied = insert (S.next h) h.occupied := by
  simp [step]

theorem step_occupied_false (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) :
    (S.step h false ω).occupied = h.occupied := by
  simp [step]

/-- The examination reads the configuration only on the block it examines. -/
theorem step_congr (h : MacroHistory d S.Index) (b : Bool) {ω ω' : SiteConfig (Site d)}
    (hagree : ∀ x ∈ S.block (S.next h), (x ∈ ω ↔ x ∈ ω')) :
    S.step h b ω = S.step h b ω' := by
  classical
  refine MacroHistory.eq_of_fields rfl ?_ rfl
  simp only [step]
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  simpa using hagree x hx


/-! ### The word event after one examination -/

/-- **The first answer splits the run.**  On the event that the examined block is joined the run
begins with `true` and continues from the transcript that records the block as occupied; off it the
run begins with `false`. -/
theorem run_succ_setOf (n : ℕ) (h : MacroHistory d S.Index) (A : List Bool → Prop) :
    {ω : SiteConfig (Site d) | A (S.run (n + 1) h ω)}
      = (S.joined (S.next h) ∩ {ω | A (true :: S.run n (S.step h true ω) ω)})
        ∪ ((S.joined (S.next h))ᶜ ∩ {ω | A (false :: S.run n (S.step h false ω) ω)}) := by
  ext ω
  by_cases hω : ω ∈ S.joined (S.next h)
  · rw [Set.mem_setOf_eq, S.run_succ, S.bit_of_mem hω]
    simp [hω]
  · rw [Set.mem_setOf_eq, S.run_succ, S.bit_of_notMem hω]
    simp [hω]

/-- **The examination reads only its own block.**  Splitting the configuration space by the pattern
of the examined block turns a run whose transcript depends on the configuration into a finite union
of runs from fixed transcripts. -/
theorem setOf_step_eq_biUnion (n : ℕ) (h : MacroHistory d S.Index) (b : Bool)
    (A : List Bool → Prop) :
    {ω : SiteConfig (Site d) | A (S.run n (S.step h b ω) ω)}
      = ⋃ σ ∈ (S.block (S.next h)).powerset,
          (localCylinder (↑(S.block (S.next h)) : Set (Site d)) (↑σ : Set (Site d))
            ∩ {ω | A (S.run n (S.step h b (↑σ : Set (Site d))) ω)}) := by
  classical
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop,
    Finset.mem_powerset]
  constructor
  · intro hω
    refine ⟨(S.block (S.next h)).filter (fun x => x ∈ ω), Finset.filter_subset _ _, ?_, ?_⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe] at *
      exact ⟨fun hxω => ⟨hx, hxω⟩, fun hxω => hxω.2⟩
    · have hEq : S.step h b ω
          = S.step h b (↑((S.block (S.next h)).filter (fun x => x ∈ ω)) : Set (Site d)) := by
        refine S.step_congr h b fun x hx => ?_
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨fun hxω => ⟨hx, hxω⟩, fun hxω => hxω.2⟩
      rwa [← hEq]
  · rintro ⟨σ, -, hcyl, hrun⟩
    have hEq : S.step h b ω = S.step h b (↑σ : Set (Site d)) :=
      S.step_congr h b fun x hx => hcyl x (Finset.mem_coe.2 hx)
    rwa [hEq]

/-- Events read off a run are measurable. -/
theorem measurableSet_setOf_run :
    ∀ (n : ℕ) (h : MacroHistory d S.Index) (A : List Bool → Prop),
      MeasurableSet {ω : SiteConfig (Site d) | A (S.run n h ω)} := by
  intro n
  induction n with
  | zero =>
    intro h A
    by_cases hA : A []
    · have hset : {ω : SiteConfig (Site d) | A (S.run 0 h ω)} = Set.univ :=
        Set.eq_univ_of_forall fun _ => hA
      rw [hset]; exact MeasurableSet.univ
    · have hset : {ω : SiteConfig (Site d) | A (S.run 0 h ω)} = ∅ := by
        ext ω; simpa using hA
      rw [hset]; exact MeasurableSet.empty
  | succ n ih =>
    intro h A
    have hstepmeas : ∀ (b : Bool) (A' : List Bool → Prop),
        MeasurableSet {ω : SiteConfig (Site d) | A' (S.run n (S.step h b ω) ω)} := by
      intro b A'
      rw [S.setOf_step_eq_biUnion n h b A']
      exact Finset.measurableSet_biUnion _ fun σ _ =>
        (measurableSet_localCylinder (S.block (S.next h)).finite_toSet.countable _).inter
          (ih _ _)
    rw [S.run_succ_setOf n h A]
    exact ((S.joined_measurable (S.next h)).inter
        (hstepmeas true fun w => A (true :: w))).union
      ((S.joined_measurable (S.next h)).compl.inter (hstepmeas false fun w => A (false :: w)))

/-- Events read off a run started by one examination are measurable. -/
theorem measurableSet_setOf_run_step (n : ℕ) (h : MacroHistory d S.Index) (b : Bool)
    (A : List Bool → Prop) :
    MeasurableSet {ω : SiteConfig (Site d) | A (S.run n (S.step h b ω) ω)} := by
  rw [S.setOf_step_eq_biUnion n h b A]
  exact Finset.measurableSet_biUnion _ fun σ _ =>
    (measurableSet_localCylinder (S.block (S.next h)).finite_toSet.countable _).inter
      (S.measurableSet_setOf_run n _ A)

/-- Under a pinning that fixes the examined block, the examination has a definite outcome: the
transcript it produces does not depend on the configuration substituted into. -/
theorem step_substitute_const (h : MacroHistory d S.Index) (b : Bool) {K : Set (Site d)}
    (hK : (↑(S.block (S.next h)) : Set (Site d)) ⊆ K) (val : Site d → Prop)
    (ω ω' : SiteConfig (Site d)) :
    S.step h b (substitute K val ω) = S.step h b (substitute K val ω') := by
  refine S.step_congr h b fun x hx => ?_
  have hxK : x ∈ K := hK (Finset.mem_coe.2 hx)
  rw [mem_substitute_of_mem val hxK, mem_substitute_of_mem val hxK]

/-! ### The one-step contract -/

/-- **The one-step contract**, in the shape `MacroSetup.StepBound` has it: after every admissible
transcript, *every* block still pending examination is joined with pinned probability at least
`1 - rho`.  This is taken as a hypothesis; establishing it is the geometric workstream. -/
def StepBound (S : SiteWalk d) (rho : ℝ) : Prop :=
  ∀ h : MacroHistory d S.Index, S.Admissible h →
    ∀ m : S.Index, m ∉ h.occupied → 1 - rho ≤ h.prob S.density (S.joined m)

/-- **The one-step contract at the block actually examined.**  This is all the coupling consumes,
and it is strictly weaker than `StepBound`, which asks the same of every pending block, including
blocks the exploration has already inspected and found wanting.  For an exploration whose `joined m`
means "block `m` is joined to the growing cluster", a block that has been examined and failed is
still pending, and its pinned probability of being joined is small; so `StepBound` is not a bound
the geometry can be expected to supply, whereas `NextBound` is. -/
def NextBound (S : SiteWalk d) (rho : ℝ) : Prop :=
  ∀ h : MacroHistory d S.Index, S.Admissible h →
    1 - rho ≤ h.prob S.density (S.joined (S.next h))

theorem StepBound.nextBound {S : SiteWalk d} {rho : ℝ} (hS : S.StepBound rho) :
    S.NextBound rho :=
  fun h hh => hS h hh (S.next h) (S.next_notMem_occupied h hh)

end SiteWalk

/-! ### Two facts about the constant walk -/

/-- The constant law does not read the history, so a continuation of `u` is a fresh run against the
shifted event. -/
theorem walkProb_const_shift (a : ℝ) :
    ∀ (n : ℕ) (A : List Bool → Prop) (u : List Bool),
      walkProb (fun _ => a) A n u = walkProb (fun _ => a) (fun w => A (u ++ w)) n [] := by
  intro n
  induction n with
  | zero =>
    intro A u
    simp only [walkProb_zero]
    rw [List.append_nil]
  | succ n ih =>
    intro A u
    rw [walkProb_succ, walkProb_succ, ih A (u ++ [true]), ih A (u ++ [false]),
      ih (fun w => A (u ++ w)) ([] ++ [true]), ih (fun w => A (u ++ w)) ([] ++ [false])]
    simp only [List.nil_append, List.append_assoc]

theorem walkProb_const_cons (a : ℝ) (A : List Bool → Prop) (n : ℕ) (b : Bool) :
    walkProb (fun _ => a) A n [b] = walkProb (fun _ => a) (fun w => A (b :: w)) n [] := by
  rw [walkProb_const_shift a n A [b]]
  simp only [List.singleton_append]

/-- Prefixing a fixed answer preserves upward closure. -/
theorem monoWord_cons {A : List Bool → Prop} (hA : MonoWord A) (b : Bool) :
    MonoWord fun w => A (b :: w) := by
  intro u v hlen hget hu
  exact hA.of_wordLE (List.Forall₂.cons (fun hb => hb) (List.forall₂_iff_get.2 ⟨hlen, hget⟩)) hu

/-- Turning the first answer from a failure into a success cannot leave an upward-closed event. -/
theorem monoWord_false_imp_true {A : List Bool → Prop} (hA : MonoWord A) (w : List Bool)
    (hw : A (false :: w)) : A (true :: w) :=
  hA.of_wordLE (List.Forall₂.cons (fun _ => rfl) (WordLE.refl w)) hw

/-! ### The coupling -/

namespace SiteWalk

variable (S : SiteWalk d)

/-- **The coupling.**  For an exploration that reads an actual configuration, the Bernoulli(`1 - rho`)
reach probability of an upward-closed word event is a genuine lower bound for the probability, under
the product measure pinned by the transcript, of the corresponding configuration event.

The induction is on the number of examinations.  At each step the configuration event splits along
the answer to the current examination; the two branches are bounded below, uniformly over the
patterns the examined block can show, by the induction hypothesis, and
`le_pinnedProb_inter_of_forall_extend` averages those uniform bounds against the true weight of the
answer.  That weight is at least `1 - rho` by the one-step contract, and raising it from `1 - rho`
to its true value can only help because the target is upward closed. -/
theorem walkProb_le_prob_run {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hadm : ∀ (h : MacroHistory d S.Index) (b : Bool) (ω : SiteConfig (Site d)),
      S.Admissible h → S.Admissible (S.step h b ω))
    (hS : S.NextBound rho) :
    ∀ (n : ℕ) (h : MacroHistory d S.Index), S.Admissible h →
      ∀ A : List Bool → Prop, MonoWord A →
        walkProb (fun _ => 1 - rho) A n [] ≤ h.prob S.density {ω | A (S.run n h ω)} := by
  have ha0 : (0 : ℝ) ≤ 1 - rho := by linarith
  have ha1 : (1 : ℝ) - rho ≤ 1 := by linarith
  intro n
  induction n with
  | zero =>
    intro h _ A _
    by_cases hA : A []
    · have hset : {ω : SiteConfig (Site d) | A (S.run 0 h ω)} = Set.univ :=
        Set.eq_univ_of_forall fun _ => hA
      have hp : h.prob S.density {ω : SiteConfig (Site d) | A (S.run 0 h ω)} = 1 := by
        rw [MacroHistory.prob_eq, hset, pinnedProb_univ]
      rw [walkProb_zero, if_pos hA, hp]
    · rw [walkProb_zero, if_neg hA]
      exact MacroHistory.prob_nonneg _ _ _
  | succ n ih =>
    intro h hadmh A hA
    have hXt0 : (0 : ℝ) ≤ walkProb (fun _ => 1 - rho) (fun w => A (true :: w)) n [] :=
      walkProb_nonneg _ (fun _ => ha0) (fun _ => ha1) _ _ _
    have hXf0 : (0 : ℝ) ≤ walkProb (fun _ => 1 - rho) (fun w => A (false :: w)) n [] :=
      walkProb_nonneg _ (fun _ => ha0) (fun _ => ha1) _ _ _
    have hXfe : walkProb (fun _ => 1 - rho) (fun w => A (false :: w)) n []
        ≤ walkProb (fun _ => 1 - rho) (fun w => A (true :: w)) n [] :=
      walkProb_mono_event _ (fun _ => ha0) (fun _ => ha1) _ _
        (fun w hw => monoWord_false_imp_true hA w hw) n []
    have hlhs : walkProb (fun _ => 1 - rho) A (n + 1) []
        = (1 - rho) * walkProb (fun _ => 1 - rho) (fun w => A (true :: w)) n []
          + (1 - (1 - rho)) * walkProb (fun _ => 1 - rho) (fun w => A (false :: w)) n [] := by
      rw [walkProb_succ]
      simp only [List.nil_append]
      rw [walkProb_const_cons, walkProb_const_cons]
    -- The uniform branch bound, averaged against the weight of any event the examination decides.
    have key : ∀ (b : Bool) (B : Set (SiteConfig (Site d))),
        DeterminedBy B ((↑h.inspected : Set (Site d)) ∪ (↑(S.block (S.next h)) : Set (Site d))) →
        MeasurableSet B →
        walkProb (fun _ => 1 - rho) (fun w => A (b :: w)) n [] * h.prob S.density B
          ≤ h.prob S.density (B ∩ {ω | A (b :: S.run n (S.step h b ω) ω)}) := by
      intro b B hBdet hBm
      rw [MacroHistory.prob_eq, MacroHistory.prob_eq]
      refine le_pinnedProb_inter_of_forall_extend S.density hBm
        (S.measurableSet_setOf_run_step n h b fun w => A (b :: w))
        (S.block (S.next h)) (↑h.inspected : Set (Site d))
        (S.next_block_fresh h hadmh) h.state hBdet ?_
      intro val' hval'
      have hsub : (↑(S.block (S.next h)) : Set (Site d))
          ⊆ (↑h.inspected : Set (Site d)) ∪ (↑(S.block (S.next h)) : Set (Site d)) :=
        Set.subset_union_right
      have hconst : ∀ ω : SiteConfig (Site d),
          S.step h b (substitute ((↑h.inspected : Set (Site d))
              ∪ (↑(S.block (S.next h)) : Set (Site d))) val' ω)
            = S.step h b (substitute ((↑h.inspected : Set (Site d))
              ∪ (↑(S.block (S.next h)) : Set (Site d))) val' ∅) :=
        fun ω => S.step_substitute_const h b hsub val' ω ∅
      have hpre : pinnedProb S.density ((↑h.inspected : Set (Site d))
            ∪ (↑(S.block (S.next h)) : Set (Site d))) val'
              {ω | A (b :: S.run n (S.step h b ω) ω)}
          = pinnedProb S.density ((↑h.inspected : Set (Site d))
            ∪ (↑(S.block (S.next h)) : Set (Site d))) val'
              {ω | A (b :: S.run n (S.step h b (substitute ((↑h.inspected : Set (Site d))
                ∪ (↑(S.block (S.next h)) : Set (Site d))) val' ∅)) ω)} := by
        unfold pinnedProb
        congr 1
        ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq, hconst ω]
      have hinsp : (↑(S.step h b (substitute ((↑h.inspected : Set (Site d))
            ∪ (↑(S.block (S.next h)) : Set (Site d))) val' ∅)).inspected : Set (Site d))
          = (↑h.inspected : Set (Site d)) ∪ (↑(S.block (S.next h)) : Set (Site d)) := by
        rw [S.step_inspected, Finset.coe_union]
      have hstate : ∀ x ∈ (↑h.inspected : Set (Site d))
            ∪ (↑(S.block (S.next h)) : Set (Site d)),
          (val' x ↔ (S.step h b (substitute ((↑h.inspected : Set (Site d))
            ∪ (↑(S.block (S.next h)) : Set (Site d))) val' ∅)).state x) := by
        intro x hx
        rw [S.step_state]
        constructor
        · intro hv
          rcases hx with hx | hx
          · exact Or.inl ((hval' x hx).1 hv)
          · refine Or.inr ⟨Finset.mem_coe.1 hx, ?_⟩
            exact (mem_substitute_of_mem val' (hsub hx)).2 hv
        · rintro (hv | ⟨hxb, hv⟩)
          · exact (hval' x (MacroHistory.mem_inspected_of_state hv)).2 hv
          · exact (mem_substitute_of_mem val' (hsub (Finset.mem_coe.2 hxb))).1 hv
      have hstep2 : pinnedProb S.density ((↑h.inspected : Set (Site d))
            ∪ (↑(S.block (S.next h)) : Set (Site d))) val'
              {ω | A (b :: S.run n (S.step h b (substitute ((↑h.inspected : Set (Site d))
                ∪ (↑(S.block (S.next h)) : Set (Site d))) val' ∅)) ω)}
          = (S.step h b (substitute ((↑h.inspected : Set (Site d))
              ∪ (↑(S.block (S.next h)) : Set (Site d))) val' ∅)).prob S.density
              {ω | A (b :: S.run n (S.step h b (substitute ((↑h.inspected : Set (Site d))
                ∪ (↑(S.block (S.next h)) : Set (Site d))) val' ∅)) ω)} := by
        rw [MacroHistory.prob_eq, hinsp]
        exact pinnedProb_congr_val S.density _ hstate _
      rw [hpre, hstep2]
      exact ih _ (hadm h b _ hadmh) (fun w => A (b :: w)) (monoWord_cons hA b)
    have hJdet : DeterminedBy (S.joined (S.next h))
        ((↑h.inspected : Set (Site d)) ∪ (↑(S.block (S.next h)) : Set (Site d))) :=
      S.joined_determinedBy h hadmh
    have hJm : MeasurableSet (S.joined (S.next h)) := S.joined_measurable _
    have hkeyT := key true (S.joined (S.next h)) hJdet hJm
    have hkeyF := key false (S.joined (S.next h))ᶜ (determinedBy_compl hJdet) hJm.compl
    have hq : 1 - rho ≤ h.prob S.density (S.joined (S.next h)) := hS h hadmh
    have hq1 : h.prob S.density (S.joined (S.next h)) ≤ 1 := MacroHistory.prob_le_one _ _ _
    have hqc : h.prob S.density (S.joined (S.next h))ᶜ
        = 1 - h.prob S.density (S.joined (S.next h)) := by
      rw [MacroHistory.prob_eq, MacroHistory.prob_eq]
      exact pinnedProb_compl _ _ _ hJm
    have hsplit : h.prob S.density {ω : SiteConfig (Site d) | A (S.run (n + 1) h ω)}
        = h.prob S.density (S.joined (S.next h)
            ∩ {ω | A (true :: S.run n (S.step h true ω) ω)})
          + h.prob S.density ((S.joined (S.next h))ᶜ
            ∩ {ω | A (false :: S.run n (S.step h false ω) ω)}) := by
      rw [MacroHistory.prob_eq, MacroHistory.prob_eq, MacroHistory.prob_eq,
        S.run_succ_setOf n h A]
      refine pinnedProb_union _ _ _ (Set.disjoint_left.2 fun ω hω hω' => hω'.1 hω.1) ?_
      exact hJm.compl.inter (S.measurableSet_setOf_run_step n h false fun w => A (false :: w))
    rw [hqc] at hkeyF
    have hprod : (0 : ℝ) ≤ (h.prob S.density (S.joined (S.next h)) - (1 - rho))
        * (walkProb (fun _ => 1 - rho) (fun w => A (true :: w)) n []
           - walkProb (fun _ => 1 - rho) (fun w => A (false :: w)) n []) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hlhs, hsplit]
    nlinarith [hkeyT, hkeyF, hprod]

end SiteWalk

/-! ### Counting the blocks declared occupied -/

@[simp] theorem numJoined_cons_true (w : List Bool) : numJoined (true :: w) = numJoined w + 1 := rfl

@[simp] theorem numJoined_cons_false (w : List Bool) : numJoined (false :: w) = numJoined w := rfl

namespace SiteWalk

variable (S : SiteWalk d)

theorem occupied_subset_step (h : MacroHistory d S.Index) (b : Bool)
    (ω : SiteConfig (Site d)) : h.occupied ⊆ (S.step h b ω).occupied := by
  cases b with
  | false => rw [S.step_occupied_false]
  | true => rw [S.step_occupied_true]; exact Finset.subset_insert _ _

/-- A block declared occupied along a run was joined in the configuration the run reads. -/
theorem mem_occupied_runHist :
    ∀ (n : ℕ) (h : MacroHistory d S.Index) (ω : SiteConfig (Site d)) (m : S.Index),
      m ∈ (S.runHist n h ω).occupied → m ∈ h.occupied ∨ ω ∈ S.joined m := by
  intro n
  induction n with
  | zero => intro h ω m hm; exact Or.inl hm
  | succ n ih =>
    intro h ω m hm
    rw [S.runHist_succ] at hm
    rcases ih (S.step h (S.bit h ω) ω) ω m hm with h1 | h2
    · cases hb : S.bit h ω with
      | false =>
        rw [hb, S.step_occupied_false] at h1
        exact Or.inl h1
      | true =>
        rw [hb, S.step_occupied_true] at h1
        rcases Finset.mem_insert.1 h1 with rfl | h1'
        · exact Or.inr ((S.bit_eq_true_iff h ω).1 hb)
        · exact Or.inl h1'
    · exact Or.inr h2

/-- **The successes along a run are distinct blocks.**  Each `true` in the word declares a block
occupied that was pending, so the occupied set grows by one; the count of successes is therefore at
most the number of blocks declared occupied. -/
theorem add_numJoined_le_card_runHist
    (hadm : ∀ (h : MacroHistory d S.Index) (b : Bool) (ω : SiteConfig (Site d)),
      S.Admissible h → S.Admissible (S.step h b ω)) :
    ∀ (n : ℕ) (h : MacroHistory d S.Index), S.Admissible h → ∀ ω : SiteConfig (Site d),
      h.occupied.card + numJoined (S.run n h ω) ≤ (S.runHist n h ω).occupied.card := by
  intro n
  induction n with
  | zero => intro h _ ω; simp [numJoined]
  | succ n ih =>
    intro h hadmh ω
    rw [S.run_succ, S.runHist_succ]
    cases hb : S.bit h ω with
    | false =>
      have h1 := ih (S.step h false ω) (hadm h false ω hadmh) ω
      rw [S.step_occupied_false] at h1
      simpa using h1
    | true =>
      have h1 := ih (S.step h true ω) (hadm h true ω hadmh) ω
      rw [S.step_occupied_true,
        Finset.card_insert_of_notMem (S.next_notMem_occupied h hadmh)] at h1
      simp only [numJoined_cons_true]
      omega

/-! ### The transfer -/

/-- **The transfer.**  The Bernoulli(`1 - rho`) reach probability of an upward-closed word event is
a lower bound for the product-measure probability of the corresponding configuration event.  This is
the statement `ReachTransfer` was standing in for, proved rather than assumed. -/
theorem bernoulliReachProb_le_prob_run {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hadm : ∀ (h : MacroHistory d S.Index) (b : Bool) (ω : SiteConfig (Site d)),
      S.Admissible h → S.Admissible (S.step h b ω))
    (hS : S.NextBound rho) (A : List Bool → Prop) (hA : MonoWord A) (n : ℕ) :
    bernoulliReachProb (1 - rho) A n
      ≤ (prodBernoulli S.density).real {ω : SiteConfig (Site d) | A (S.run n S.start ω)} := by
  have hmain := S.walkProb_le_prob_run hrho0 hrho1 hadm hS n S.start S.start_admissible A hA
  rwa [MacroHistory.prob_eq, S.start_inspected, Finset.coe_empty, pinnedProb_empty] at hmain

/-- **An infinite cluster from the exploration.**  A lower bound `c > 0` on the Bernoulli(`1 - rho`)
probability of reaching every target size, together with the one-step contract and the hypothesis
that a joined block contributes a site of the cluster of `x`, makes the percolation probability at
`x` positive.

This is the conclusion `thetaSiteOn_pos_of_reachTransfer` reaches from `ReachTransfer`; here the
transfer is proved, not assumed. -/
theorem thetaSiteOn_pos (G : SimpleGraph (Site d)) (x : Site d) (p : unitInterval)
    (hden : S.density = fun _ => p)
    (hadm : ∀ (h : MacroHistory d S.Index) (b : Bool) (ω : SiteConfig (Site d)),
      S.Admissible h → S.Admissible (S.step h b ω))
    (hjoin : ∀ (m : S.Index) (ω : SiteConfig (Site d)), ω ∈ S.joined m →
      ∃ y ∈ (↑(S.block m) : Set (Site d)), y ∈ siteCluster G ω x)
    {rho c : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hS : S.NextBound rho) (hc : 0 < c)
    (steps : ℕ → ℕ)
    (hbern : ∀ k : ℕ, c ≤ bernoulliReachProb (1 - rho) (reachesSize k) (steps k)) :
    0 < thetaSiteOn G x p := by
  classical
  refine thetaSiteOn_pos_of_cells G x p (fun m => (↑(S.block m) : Set (Site d)))
    S.block_disjoint c hc fun k => ?_
  refine ((hbern k).trans (S.bernoulliReachProb_le_prob_run hrho0 hrho1 hadm hS
    (reachesSize k) (monoWord_reachesSize k) (steps k))).trans ?_
  rw [hden]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω hω
  have hcount := S.add_numJoined_le_card_runHist hadm (steps k) S.start S.start_admissible ω
  rw [S.start_occupied, Finset.card_empty, Nat.zero_add] at hcount
  have hcard : k ≤ (S.runHist (steps k) S.start ω).occupied.card :=
    le_trans hω hcount
  have hex : ∀ m ∈ (S.runHist (steps k) S.start ω).occupied,
      ∃ y, y ∈ (↑(S.block m) : Set (Site d)) ∧ y ∈ siteCluster G ω x := by
    intro m hm
    rcases S.mem_occupied_runHist (steps k) S.start ω m hm with h1 | h2
    · rw [S.start_occupied] at h1
      exact absurd h1 (Finset.notMem_empty m)
    · obtain ⟨y, hy1, hy2⟩ := hjoin m ω h2
      exact ⟨y, hy1, hy2⟩
  choose! rep hrep1 hrep2 using hex
  exact ⟨_, rep, hcard, hrep1, hrep2⟩

end SiteWalk

/-! ## Part 3: the hypotheses are satisfiable

The hypotheses of `SiteWalk` together with `NextBound` are not vacuous, and they are satisfiable by
an exploration whose one-step bound is a genuine statement about the product measure rather than a
tautology.  The exploration below reads one fresh site at a time along an injection `site : ℕ → ℤ^d`
and calls the examination a success when that site is open; the examined site has never been read
before, so its conditional probability of being open is exactly `p` whatever the transcript says. -/

/-- The event that a given coordinate is present is determined by that coordinate.

Named `_coord` because `KN/SiteSlabGeometry.lean` already has `determinedBy_setOf_mem_coord` in this
namespace for site configurations; declaring both made `KN.ReachCoupling` and `KN.GateTwoChain`
mutually un-importable. -/
theorem determinedBy_setOf_mem_coord {ι : Type*} (i : ι) :
    DeterminedBy {ω : Set ι | i ∈ ω} ({i} : Set ι) := by
  rw [determinedBy_iff]
  intro ω ω' hω
  have h := Set.ext_iff.1 hω i
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, and_true] at h
  exact h

/-- **The one-site exploration along an injection.**  The `n`-th examination reads the site
`site n`, and calls it a success when the site is open. -/
def siteWalkOfInjection (d : ℕ) (site : ℕ → Site d) (hsite : Function.Injective site)
    (p : unitInterval) : SiteWalk d where
  Index := ℕ
  decEq := inferInstance
  block k := {site k}
  block_disjoint := by
    intro k l hkl
    simp only [Finset.coe_singleton]
    rw [Set.disjoint_singleton]
    exact fun hEq => hkl (hsite hEq)
  density _ := p
  joined k := {ω | site k ∈ ω}
  joined_measurable k := measurableSet_mem (site k)
  Admissible h := ∃ n : ℕ, h.inspected = (Finset.range n).image site ∧ h.occupied ⊆ Finset.range n
  start := ⟨∅, ∅, Finset.Subset.refl _, ∅⟩
  start_admissible := ⟨0, by simp, by simp⟩
  start_inspected := rfl
  start_occupied := rfl
  next h := h.inspected.card
  next_notMem_occupied := by
    rintro h ⟨n, hn, hocc⟩
    have hcard : h.inspected.card = n := by
      rw [hn, Finset.card_image_of_injective _ hsite, Finset.card_range]
    rw [hcard]
    exact fun hmem => absurd (Finset.mem_range.1 (hocc hmem)) (lt_irrefl n)
  next_block_fresh := by
    rintro h ⟨n, hn, hocc⟩
    have hcard : h.inspected.card = n := by
      rw [hn, Finset.card_image_of_injective _ hsite, Finset.card_range]
    have hfresh : site n ∉ (Finset.range n).image site := by
      simp only [Finset.mem_image, Finset.mem_range]
      rintro ⟨k, hk, hkeq⟩
      exact absurd (hsite hkeq) (Nat.ne_of_lt hk)
    rw [hcard, hn, Finset.disjoint_coe]
    exact Finset.disjoint_singleton_left.2 hfresh
  joined_determinedBy := by
    intro h _
    refine (determinedBy_setOf_mem_coord (site h.inspected.card)).mono ?_
    simp only [Finset.coe_singleton]
    exact Set.subset_union_right

namespace SiteWalk

/-- Every step of the one-site exploration keeps the transcript admissible. -/
theorem siteWalkOfInjection_step_admissible (d : ℕ) (site : ℕ → Site d)
    (hsite : Function.Injective site) (p : unitInterval)
    (h : MacroHistory d (siteWalkOfInjection d site hsite p).Index) (b : Bool)
    (ω : SiteConfig (Site d)) (hh : (siteWalkOfInjection d site hsite p).Admissible h) :
    (siteWalkOfInjection d site hsite p).Admissible
      ((siteWalkOfInjection d site hsite p).step h b ω) := by
  classical
  obtain ⟨n, hn, hocc⟩ := hh
  have hcard : h.inspected.card = n := by
    rw [hn, Finset.card_image_of_injective _ hsite, Finset.card_range]
  refine ⟨n + 1, ?_, ?_⟩
  · show h.inspected ∪ {site h.inspected.card} = (Finset.range (n + 1)).image site
    rw [hcard, hn, Finset.range_add_one, Finset.image_insert, Finset.union_comm,
      Finset.insert_eq]
  · show (if b then insert h.inspected.card h.occupied else h.occupied) ⊆ Finset.range (n + 1)
    rw [hcard]
    have hmono : h.occupied ⊆ Finset.range (n + 1) := fun a ha =>
      Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 (hocc ha)))
    cases b with
    | false => simpa using hmono
    | true =>
      exact Finset.insert_subset (Finset.mem_range.2 (Nat.lt_succ_self n)) hmono

/-- **The one-step bound holds, and holds with the true density.**  The site examined next has never
been read, so pinning the transcript does not move its probability of being open. -/
theorem siteWalkOfInjection_nextBound (d : ℕ) (site : ℕ → Site d)
    (hsite : Function.Injective site) (p : unitInterval) :
    (siteWalkOfInjection d site hsite p).NextBound (1 - (p : ℝ)) := by
  intro h hh
  obtain ⟨n, hn, hocc⟩ := hh
  have hcard : h.inspected.card = n := by
    rw [hn, Finset.card_image_of_injective _ hsite, Finset.card_range]
  have hfresh : site n ∉ h.inspected := by
    rw [hn]
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨k, hk, hkeq⟩
    exact absurd (hsite hkeq) (Nat.ne_of_lt hk)
  have hdet : DeterminedBy {ω : SiteConfig (Site d) | site n ∈ ω}
      ((↑h.inspected : Set (Site d))ᶜ) := by
    refine (determinedBy_setOf_mem_coord (site n)).mono ?_
    rw [Set.singleton_subset_iff, Set.mem_compl_iff, Finset.mem_coe]
    exact hfresh
  have hgoal : h.prob (siteWalkOfInjection d site hsite p).density
      ((siteWalkOfInjection d site hsite p).joined
        ((siteWalkOfInjection d site hsite p).next h))
      = h.prob (fun _ => p) {ω : SiteConfig (Site d) | site n ∈ ω} := by
    show h.prob (fun _ => p) {ω : SiteConfig (Site d) | site h.inspected.card ∈ ω} = _
    rw [hcard]
  rw [hgoal, MacroHistory.prob_eq_of_determinedBy_compl h _ hdet,
    prodBernoulli_real_setOf_mem, sub_sub_cancel]

/-- **Non-vacuity of the transfer.**  For the one-site exploration the transfer of
`bernoulliReachProb_le_prob_run` is a statement with content: the Bernoulli(`p`) reach probability of
an upward-closed word event is a lower bound for the product-measure probability that the states of
the sites `site 0, site 1, …` read along the run form a word in that event. -/
theorem siteWalkOfInjection_transfer (d : ℕ) (site : ℕ → Site d)
    (hsite : Function.Injective site) (p : unitInterval) (A : List Bool → Prop)
    (hA : MonoWord A) (n : ℕ) :
    bernoulliReachProb (p : ℝ) A n
      ≤ (prodBernoulli (fun _ : Site d => p)).real
          {ω | A ((siteWalkOfInjection d site hsite p).run n
            (siteWalkOfInjection d site hsite p).start ω)} := by
  have hb := (siteWalkOfInjection d site hsite p).bernoulliReachProb_le_prob_run
    (rho := 1 - (p : ℝ)) (by linarith [(p.2.2 : (p : ℝ) ≤ 1)])
    (by linarith [(p.2.1 : (0 : ℝ) ≤ (p : ℝ))])
    (fun h b ω hh => siteWalkOfInjection_step_admissible d site hsite p h b ω hh)
    (siteWalkOfInjection_nextBound d site hsite p) A hA n
  rwa [sub_sub_cancel] at hb

end SiteWalk

/-! ## Part 4: `ReachTransfer` is false at the generality it is stated

`MacroSetup` carries no hypothesis relating `joined`, `step` and `occupied` to one another or to a
configuration, so the Boolean word a run produces is not tied to anything the product measure can
see.  The setup below satisfies every field of `MacroSetup` and the full strength of
`MacroSetup.StepBound` at `rho = 0`, yet its reach probability is `1` while the configuration event
`ReachTransfer` compares it with is empty.  So `ReachTransfer` does not follow from `StepBound`, and
the seam cannot be closed without adding to `MacroSetup` the link that `SiteWalk` supplies: an
examination that reads the configuration, on a block disjoint from everything read before. -/

/-- A `MacroSetup` in which every examination succeeds and nothing is ever inspected. -/
def trivialSetup (d : ℕ) (q : Site d → unitInterval) : MacroSetup d where
  Index := ℕ
  block _ := (∅ : Set (Site d))
  block_disjoint _ _ _ := by simp
  density := q
  joined _ := Set.univ
  Admissible h := h.occupied = ∅
  start := ⟨∅, ∅, Finset.Subset.refl _, ∅⟩
  start_admissible := rfl
  next _ := 0
  step h _ := h
  step_admissible _ _ hh := hh
  step_extends h _ := MacroHistory.Extends.refl h
  next_notMem_occupied h hh := by rw [hh]; exact Finset.notMem_empty 0

theorem trivialSetup_stepBound (d : ℕ) (q : Site d → unitInterval) :
    (trivialSetup d q).StepBound 0 := by
  intro h _ m _
  have h1 : h.prob (trivialSetup d q).density ((trivialSetup d q).joined m) = 1 := by
    rw [MacroHistory.prob_eq]
    exact pinnedProb_univ _ _ _
  rw [h1, sub_zero]

/-- **`ReachTransfer` is not implied by the one-step contract.**  For the setup above the formal
reach probability of "at least one block occupied in one step" is `1`, while the configuration event
it is compared with is empty, whatever graph, root, density and cell family are chosen — here the
cells are taken empty. -/
theorem not_reachTransfer (d : ℕ) (G : SimpleGraph (Site d)) (x : Site d)
    (p : unitInterval) (q : Site d → unitInterval) :
    ¬ ReachTransfer G x p (fun _ : (trivialSetup d q).Index => (∅ : Set (Site d)))
      ((trivialSetup d q).exploration (by norm_num : (0 : ℝ) ≤ 1)
        (trivialSetup_stepBound d q)) id := by
  intro hT
  have hsp : ∀ w : List Bool, (trivialSetup d q).stepProb w = 1 := by
    intro w
    show ((trivialSetup d q).hist w).prob (trivialSetup d q).density Set.univ = 1
    rw [MacroHistory.prob_eq]
    exact pinnedProb_univ _ _ _
  have hreach : ((trivialSetup d q).exploration (by norm_num : (0 : ℝ) ≤ 1)
      (trivialSetup_stepBound d q)).reachProb (reachesSize 1) 1 = 1 := by
    rw [Exploration.reachProb, walkProb_succ]
    simp only [MacroSetup.exploration_succProb, hsp, walkProb_zero, List.nil_append]
    norm_num [reachesSize, numJoined]
  have hempty : {ω : SiteConfig (Site d) |
      ∃ (occ : Finset (trivialSetup d q).Index) (rep : (trivialSetup d q).Index → Site d),
        1 ≤ occ.card ∧ (∀ m ∈ occ, rep m ∈ (∅ : Set (Site d))) ∧
          (∀ m ∈ occ, rep m ∈ siteCluster G ω x)} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    rintro occ rep ⟨hcard, hcell, -⟩
    obtain ⟨m, hm⟩ := Finset.card_pos.1 hcard
    exact hcell m hm
  have h1 := hT 1
  simp only [id_eq, hreach, hempty, measureReal_empty] at h1
  linarith

end KNAll.Site

end

section AxiomCheck
open KNAll.Site
#print axioms KNAll.Site.le_pinnedProb_inter_of_forall_extend
#print axioms KNAll.Site.pinnedProb_split
#print axioms KNAll.Site.SiteWalk.walkProb_le_prob_run
#print axioms KNAll.Site.SiteWalk.bernoulliReachProb_le_prob_run
#print axioms KNAll.Site.SiteWalk.thetaSiteOn_pos
#print axioms KNAll.Site.SiteWalk.siteWalkOfInjection_transfer
#print axioms KNAll.Site.not_reachTransfer
end AxiomCheck
