import Hypergraph.HyperFibre
import Hypergraph.ProdBernoulliFKG

/-!
# The stopped exploration record, its locality, and decision-tree Harris in the hyperedge model

The bond development formalises the exploration of the open cluster of a vertex set as a decision
tree (`Percolation/Literature/SetClusterExploration.lean`), and the correlation inequality that
holds along it (`Percolation/Continuity/LowerTail/TreeHarrisReal.lean`, Gladkov 2024, Thm. 3.2).
This module is the hyperedge port.

## The record

The bond exploration stops in a state `⟨vis, rev⟩`: the vertices reached and the edges revealed.
What the later steps consume is not `vis` alone but the pair, split according to the answers
received: `rev ∩ K` are the edges queried and found open, `rev \ K` those queried and found closed.
`ExplorationRecord` is that data for a hypergraph, and `recordAt H S ω` is the record the
exploration of the cluster of `S` leaves behind in the configuration `ω`.  Its queried set is
`labelsMeeting H (hyperClusterSet H ω S)`, every label incident to the cluster, which is what
`mem_revealedAt_iff` proves for the bond exploration.

The reached set alone is a strictly coarser record, and
`exists_recordAt_ne_of_hyperClusterSet_eq` exhibits two configurations with the same cluster and
different records.  `KN/HyperTrace.lean` records the parallel loss for vertex traces of label sets;
here the loss is the states of the queried labels.

* `ExplorationRecord`, `ExplorationRecord.queried`, `recordAt`, `recordEvent`;
* `queried_recordAt`, `recordEvent_subset_clusterEvent`, `inter_queried_eq_openLabels`.

## Locality

* `recordAt_congr`, `determinedBy_recordEvent` — the record is determined by the labels it queried,
  in the sense of `DeterminedBy`.  The cluster half of this is `determinedBy_clusterEvent` of
  `KN/HyperImplA.lean`; the states of the queried labels are read off the trace directly.
* `measurableSet_recordEvent` — over a finite label type the queried set is finite, so
  `DeterminedBy.measurableSet_of_finset` applies, as in `measurableSet_clusterEvent`.
* `recordEvent_eq_cylinder` — a record event that occurs at all is exactly the cylinder fixing the
  states of the queried labels.  This is the hyperedge form of self-determination of the revealed
  set (`selfDetermined_revealedAt` in the bond file).

## The correlation statement

`spliceRecord r ω` is the bond splice `C₁ →_{S} C₂` at the record `r`: the recorded labels keep
their recorded states, the rest are read off `ω`.  `condRecord H r Y` is the resulting conditional
probability of `Y`, written as an ordinary integral against the product measure, so no conditioning
event has to have positive probability.

* `real_recordEvent_inter` — the exact factorization
  `P(record = r, Y) = P(record = r) · condRecord r Y`, valid for every event `Y`.  This is the bond
  `cE` identity, and being an identity of finite weighted sums it carries no denominator.
* `condRecord_eq_real_of_determinedBy`, `real_recordEvent_inter_residual` — for an event determined
  by the labels the exploration did not query the residual probability is the unconditioned one, and
  equally the one in the model with the queried labels closed (`deleteHyper`).
* `integral_fibreMean_mul_real_le` — Harris for the cluster functional `fibreMean` of
  `KN/HyperFibre.lean`, which is defined on every record and not only on the feasible ones, against
  an increasing event.
* `treeHarris_hyper` — the hyperedge decision-tree Harris inequality: for `F` increasing and `Y`
  increasing, and a family `A` of residual events with `A K` determined by the labels the
  exploration did not query when the cluster is `K`,
  `E[F(C)] · P(Y) ≤ ∑_K F(K) · P(C = K) · P_{H_K}(A K)`, the right side being the bond
  `E[f · E[1_Y | ℱ]]` with the conditional expectation computed by `clusterFactorization`.

A functional of the cluster is measurable for the exploration, so the bond right side
`E[f · E[1_Y | ℱ]]` collapses to `E[f · 1_Y]`; that collapse is `real_recordEvent_inter` summed over
records, and it is why the inequality here needs Harris only, and not the induction over the tree
that the bond statement needs for a general increasing `f`.

The family `A` cannot be replaced by a single event: an event determined by the labels avoiding `K`
for *every* `K` is determined by the labels incident to nothing.  `residualConn` and
`clusterEvent_inter_hyperConn` supply the family in the case the gluing argument uses, a connection
between vertices outside the explored cluster.

## References

* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), Def. 2.4,
  Example 2.5, Lemma 3.1, Theorem 3.2.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation
  and related processes*, Random Struct. Alg. 29 (2006), eq. (6).
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## The exploration record -/

/-- **Target 1.**  What the exploration of the cluster of a vertex set leaves behind when it stops:
the vertices it reached, the labels it queried and found open, and the labels it queried and found
closed.  The bond template is the stopped state `⟨vis, rev⟩` of
`Percolation.Literature.SetClusterExploration`, with `rev` split by the answers received. -/
structure ExplorationRecord (V E : Type*) where
  /-- The vertices the exploration reached. -/
  reached : Set V
  /-- The labels the exploration queried and found open. -/
  openLabels : Set E
  /-- The labels the exploration queried and found closed. -/
  closedLabels : Set E

namespace ExplorationRecord

/-- The labels the exploration queried, whatever the answer. -/
def queried (r : ExplorationRecord V E) : Set E := r.openLabels ∪ r.closedLabels

theorem openLabels_subset_queried (r : ExplorationRecord V E) : r.openLabels ⊆ r.queried :=
  Set.subset_union_left

theorem closedLabels_subset_queried (r : ExplorationRecord V E) : r.closedLabels ⊆ r.queried :=
  Set.subset_union_right

/-- Records agreeing in all three fields are equal. -/
theorem ext' {r r' : ExplorationRecord V E} (h1 : r.reached = r'.reached)
    (h2 : r.openLabels = r'.openLabels) (h3 : r.closedLabels = r'.closedLabels) : r = r' := by
  cases r
  cases r'
  simp only [ExplorationRecord.mk.injEq]
  exact ⟨h1, h2, h3⟩

end ExplorationRecord

/-- The record the exploration of the cluster of `S` leaves behind in the configuration `ω`: it
reaches the cluster, and it has queried exactly the labels incident to the cluster, finding open
those that lie in `ω`.  For the bond exploration that description of the revealed set is
`mem_revealedAt_iff`; here it is the definition, and `determinedBy_recordEvent` is what makes it a
legitimate one. -/
def recordAt (H : Hypergraph V E) (S : Set V) (ω : Set E) : ExplorationRecord V E where
  reached := hyperClusterSet H ω S
  openLabels := ω ∩ labelsMeeting H (hyperClusterSet H ω S)
  closedLabels := labelsMeeting H (hyperClusterSet H ω S) \ ω

@[simp] theorem recordAt_reached (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    (recordAt H S ω).reached = hyperClusterSet H ω S := rfl

@[simp] theorem recordAt_openLabels (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    (recordAt H S ω).openLabels = ω ∩ labelsMeeting H (hyperClusterSet H ω S) := rfl

@[simp] theorem recordAt_closedLabels (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    (recordAt H S ω).closedLabels = labelsMeeting H (hyperClusterSet H ω S) \ ω := rfl

/-- **The queried set of the stopped record** is every label incident to the cluster: the open ones
and the closed ones exhaust it.  Bond template: `mem_revealedAt_iff`. -/
theorem queried_recordAt (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    (recordAt H S ω).queried = labelsMeeting H (hyperClusterSet H ω S) := by
  ext e
  simp only [ExplorationRecord.queried, recordAt_openLabels, recordAt_closedLabels,
    Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
  tauto

/-- The two answers are exclusive. -/
theorem disjoint_openLabels_closedLabels (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    Disjoint (recordAt H S ω).openLabels (recordAt H S ω).closedLabels :=
  Set.disjoint_left.2 fun _ he he' => he'.2 he.1

/-- The event that the exploration of the cluster of `S` stops with the record `r`. -/
def recordEvent (H : Hypergraph V E) (S : Set V) (r : ExplorationRecord V E) : Set (Set E) :=
  {ω | recordAt H S ω = r}

@[simp] theorem mem_recordEvent (H : Hypergraph V E) (S : Set V) (r : ExplorationRecord V E)
    (ω : Set E) : ω ∈ recordEvent H S r ↔ recordAt H S ω = r := Iff.rfl

theorem mem_recordEvent_self (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    ω ∈ recordEvent H S (recordAt H S ω) := rfl

/-- The record refines the cluster: it names the cluster among its data. -/
theorem recordEvent_subset_clusterEvent (H : Hypergraph V E) (S : Set V)
    (r : ExplorationRecord V E) : recordEvent H S r ⊆ clusterEvent H S r.reached := by
  intro ω hω
  have h : recordAt H S ω = r := hω
  show hyperClusterSet H ω S = r.reached
  rw [← h]
  rfl

/-- On its own event a record's queried set is the set of labels incident to its reached set. -/
theorem queried_eq_labelsMeeting_of_mem (H : Hypergraph V E) (S : Set V)
    {r : ExplorationRecord V E} {ω : Set E} (hω : ω ∈ recordEvent H S r) :
    r.queried = labelsMeeting H r.reached := by
  have h : recordAt H S ω = r := hω
  rw [← h, queried_recordAt, recordAt_reached]

/-- On its own event a record's open labels are the trace of the configuration on its queried
set. -/
theorem inter_queried_eq_openLabels (H : Hypergraph V E) (S : Set V)
    {r : ExplorationRecord V E} {ω : Set E} (hω : ω ∈ recordEvent H S r) :
    ω ∩ r.queried = r.openLabels := by
  have h : recordAt H S ω = r := hω
  rw [← h, queried_recordAt]
  rfl

/-! ### The reached set is not the record

The record is strictly finer than the cluster it names: the states of the queried labels are extra
information.  A hypergraph with one vertex and one label already separates them, and this is the
reason the exploration has to carry the answers and not only the vertices it reached. -/

/-- The model with one vertex and one label, whose single label is incident to that vertex. -/
private def unitHyper : Hypergraph Unit Unit where
  incidence := fun _ => Set.univ
  prob := fun _ => 0

/-- In the one-vertex model the cluster is everything, whatever the configuration. -/
private theorem hyperClusterSet_unitHyper (ω : Set Unit) :
    hyperClusterSet unitHyper ω (Set.univ : Set Unit) = Set.univ :=
  Set.eq_univ_of_forall fun y => mem_hyperClusterSet_self unitHyper ω (Set.mem_univ y)

/-- **Two configurations with the same cluster and different records.**  In the model with one
vertex and one label the cluster is the whole vertex set in every configuration, while the record
reports whether the label was found open. -/
theorem exists_recordAt_ne_of_hyperClusterSet_eq :
    ∃ (H : Hypergraph Unit Unit) (S : Set Unit) (ω ω' : Set Unit),
      hyperClusterSet H ω S = hyperClusterSet H ω' S ∧ recordAt H S ω ≠ recordAt H S ω' := by
  refine ⟨unitHyper, Set.univ, ∅, Set.univ, ?_, ?_⟩
  · rw [hyperClusterSet_unitHyper, hyperClusterSet_unitHyper]
  · intro hEq
    have hlab : () ∈ labelsMeeting unitHyper
        (hyperClusterSet unitHyper (Set.univ : Set Unit) (Set.univ : Set Unit)) := by
      rw [hyperClusterSet_unitHyper]
      exact Set.not_disjoint_iff.2 ⟨(), Set.mem_univ _, Set.mem_univ _⟩
    have h2 : () ∈ (recordAt unitHyper (Set.univ : Set Unit) (Set.univ : Set Unit)).openLabels := by
      show () ∈ (Set.univ : Set Unit) ∩ labelsMeeting unitHyper
        (hyperClusterSet unitHyper (Set.univ : Set Unit) (Set.univ : Set Unit))
      exact ⟨Set.mem_univ _, hlab⟩
    rw [← hEq] at h2
    have h3 : () ∈ (∅ : Set Unit) ∩ labelsMeeting unitHyper
        (hyperClusterSet unitHyper (∅ : Set Unit) (Set.univ : Set Unit)) := h2
    exact h3.1

/-! ## Target 2: locality of the record -/

/-- **The record is read off the labels it queried.**  Two configurations with the same trace on the
labels incident to the cluster have the same cluster, by `determinedBy_clusterEvent`, hence the same
queried set, hence the same answers.  Bond template: `run_congr` and `fin_congr`. -/
theorem recordAt_congr (H : Hypergraph V E) (S : Set V) {ω ω' : Set E}
    (h : ω ∩ labelsMeeting H (hyperClusterSet H ω S)
        = ω' ∩ labelsMeeting H (hyperClusterSet H ω S)) :
    recordAt H S ω' = recordAt H S ω := by
  have hcl : hyperClusterSet H ω' S = hyperClusterSet H ω S := by
    have hmem : ω ∈ clusterEvent H S (hyperClusterSet H ω S) := rfl
    exact ((determinedBy_iff _ _).1 (determinedBy_clusterEvent H S (hyperClusterSet H ω S))
      ω ω' h).1 hmem
  have hstate : ∀ e ∈ labelsMeeting H (hyperClusterSet H ω S), (e ∈ ω ↔ e ∈ ω') := by
    intro e he
    constructor
    · intro heω
      have hm : e ∈ ω ∩ labelsMeeting H (hyperClusterSet H ω S) := ⟨heω, he⟩
      rw [h] at hm
      exact hm.1
    · intro heω'
      have hm : e ∈ ω' ∩ labelsMeeting H (hyperClusterSet H ω S) := ⟨heω', he⟩
      rw [← h] at hm
      exact hm.1
  refine ExplorationRecord.ext' ?_ ?_ ?_
  · exact hcl
  · show ω' ∩ labelsMeeting H (hyperClusterSet H ω' S)
      = ω ∩ labelsMeeting H (hyperClusterSet H ω S)
    rw [hcl]
    exact h.symm
  · show labelsMeeting H (hyperClusterSet H ω' S) \ ω'
      = labelsMeeting H (hyperClusterSet H ω S) \ ω
    rw [hcl]
    ext e
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨he, heω'⟩
      exact ⟨he, fun heω => heω' ((hstate e he).1 heω)⟩
    · rintro ⟨he, heω⟩
      exact ⟨he, fun heω' => heω ((hstate e he).2 heω')⟩

/-- **Target 2.**  The stopped record is determined by the labels it queried. -/
theorem determinedBy_recordEvent (H : Hypergraph V E) (S : Set V) (r : ExplorationRecord V E) :
    DeterminedBy (recordEvent H S r) r.queried := by
  rw [determinedBy_iff]
  have key : ∀ a b : Set E, a ∩ r.queried = b ∩ r.queried →
      a ∈ recordEvent H S r → b ∈ recordEvent H S r := by
    intro a b hab ha
    have hra : recordAt H S a = r := ha
    have hq : r.queried = labelsMeeting H (hyperClusterSet H a S) := by
      rw [← hra, queried_recordAt]
    have h2 : a ∩ labelsMeeting H (hyperClusterSet H a S)
        = b ∩ labelsMeeting H (hyperClusterSet H a S) := by
      rw [← hq]; exact hab
    show recordAt H S b = r
    rw [recordAt_congr H S h2, hra]
  exact fun ω ω' hinter => ⟨key ω ω' hinter, key ω' ω hinter.symm⟩

/-- **Target 2, measurability.**  Over a finite label type the queried set of a record is finite, so
the record event is a finite union of cylinders.  Same route as `measurableSet_clusterEvent`. -/
theorem measurableSet_recordEvent [Fintype E] (H : Hypergraph V E) (S : Set V)
    (r : ExplorationRecord V E) : MeasurableSet (recordEvent H S r) := by
  classical
  have hfin : (r.queried).Finite := Set.toFinite _
  have h : DeterminedBy (recordEvent H S r) (↑hfin.toFinset : Set E) := by
    rw [hfin.coe_toFinset]
    exact determinedBy_recordEvent H S r
  exact h.measurableSet_of_finset

/-- **A record event that occurs is a cylinder.**  It is exactly the set of configurations whose
trace on the queried labels is the recorded one: the cluster, hence the queried set itself, is
already determined by that trace.  Bond template: `selfDetermined_revealedAt`. -/
theorem recordEvent_eq_cylinder (H : Hypergraph V E) (S : Set V) {r : ExplorationRecord V E}
    {ω₀ : Set E} (hω₀ : ω₀ ∈ recordEvent H S r) :
    recordEvent H S r = {ω : Set E | ω ∩ r.queried = r.openLabels} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hω
    exact inter_queried_eq_openLabels H S hω
  · intro hω
    have h1 : ω₀ ∩ r.queried = ω ∩ r.queried := by
      rw [inter_queried_eq_openLabels H S hω₀, hω]
    exact ((determinedBy_iff _ _).1 (determinedBy_recordEvent H S r) ω₀ ω h1).1 hω₀

/-! ## Target 3: the splice at a record and the residual probability -/

/-- **The bond splice `C₁ →_S C₂` at a record.**  The labels the exploration queried keep their
recorded states; the labels it did not query are read off `ω`. -/
def spliceRecord (r : ExplorationRecord V E) (ω : Set E) : Set E :=
  r.openLabels ∪ (ω \ r.queried)

/-- The event that the splice at `r` lands in `Y`.  This is the event `Y` "seen from the record
`r`". -/
def residualEvent (r : ExplorationRecord V E) (Y : Set (Set E)) : Set (Set E) :=
  {ω | spliceRecord r ω ∈ Y}

/-- **The conditional probability of `Y` given the record `r`**, written as an ordinary probability
of the residual event and not as a quotient: the record event is not required to have positive
probability, nor even to be nonempty.  Bond template: `TreeHarris.cE`. -/
def condRecord (H : Hypergraph V E) (r : ExplorationRecord V E) (Y : Set (Set E)) : ℝ :=
  (prodBernoulli H.prob).real (residualEvent r Y)

theorem spliceRecord_congr (r : ExplorationRecord V E) {ω ω' : Set E}
    (h : ω ∩ (r.queried)ᶜ = ω' ∩ (r.queried)ᶜ) : spliceRecord r ω = spliceRecord r ω' := by
  unfold spliceRecord
  rw [Set.sdiff_eq, Set.sdiff_eq, h]

/-- The residual event depends only on the labels the exploration did not query. -/
theorem determinedBy_residualEvent (r : ExplorationRecord V E) (Y : Set (Set E)) :
    DeterminedBy (residualEvent r Y) (r.queried)ᶜ := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [residualEvent, Set.mem_setOf_eq, spliceRecord_congr r h]

/-- On its own event the splice is the identity: the recorded states are the ones the configuration
already has.  Bond template: `fin_splice`. -/
theorem spliceRecord_eq_self (H : Hypergraph V E) (S : Set V) {r : ExplorationRecord V E}
    {ω : Set E} (hω : ω ∈ recordEvent H S r) : spliceRecord r ω = ω := by
  unfold spliceRecord
  rw [← inter_queried_eq_openLabels H S hω]
  exact Set.inter_union_sdiff ω r.queried

/-- On the record event, `Y` and the residual event agree. -/
theorem recordEvent_inter (H : Hypergraph V E) (S : Set V) (r : ExplorationRecord V E)
    (Y : Set (Set E)) :
    recordEvent H S r ∩ Y = recordEvent H S r ∩ residualEvent r Y := by
  ext ω
  simp only [Set.mem_inter_iff, residualEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hω, hY⟩
    exact ⟨hω, by rw [spliceRecord_eq_self H S hω]; exact hY⟩
  · rintro ⟨hω, hY⟩
    rw [spliceRecord_eq_self H S hω] at hY
    exact ⟨hω, hY⟩

/-- **The exact conditional expectation identity.**  The probability of `Y` on the event that the
exploration stops with the record `r` is the probability of that event times the residual
probability of `Y`, for *every* event `Y`.  This is the bond `cE` identity, and it is denominator
free: both sides are finite weighted sums, and a record event of probability zero contributes
zero to both. -/
theorem real_recordEvent_inter [Fintype E] (H : Hypergraph V E) (S : Set V)
    (r : ExplorationRecord V E) (Y : Set (Set E)) :
    (prodBernoulli H.prob).real (recordEvent H S r ∩ Y)
      = (prodBernoulli H.prob).real (recordEvent H S r) * condRecord H r Y := by
  classical
  have hfin : (r.queried).Finite := Set.toFinite _
  have hcoe : (↑hfin.toFinset : Set E) = r.queried := hfin.coe_toFinset
  have hdet : DeterminedBy (recordEvent H S r) (↑hfin.toFinset : Set E) := by
    rw [hcoe]
    exact determinedBy_recordEvent H S r
  have hres : DeterminedBy (residualEvent r Y) (↑hfin.toFinset : Set E)ᶜ := by
    rw [hcoe]
    exact determinedBy_residualEvent r Y
  rw [recordEvent_inter H S r Y,
    prodBernoulli_real_inter_of_determinedBy H.prob hfin.toFinset hdet hres
      (measurableSet_recordEvent H S r) (measurableSet_of_fintype _)]
  rfl

/-- For an event determined by the labels the exploration did not query, the residual probability is
the unconditioned one: the record carries no information about it. -/
theorem condRecord_eq_real_of_determinedBy (H : Hypergraph V E) (r : ExplorationRecord V E)
    {Y : Set (Set E)} (hY : DeterminedBy Y (r.queried)ᶜ) :
    condRecord H r Y = (prodBernoulli H.prob).real Y := by
  have h : residualEvent r Y = Y := by
    ext ω
    simp only [residualEvent, Set.mem_setOf_eq]
    refine (determinedBy_iff Y (r.queried)ᶜ).1 hY _ _ ?_
    ext e
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, spliceRecord, Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1
      · exact absurd (ExplorationRecord.openLabels_subset_queried r h1) h2
      · exact h1.1
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr ⟨h1, h2⟩, h2⟩
  rw [condRecord, h]

/-- **The exact residual model at a record.**  For an event determined by the labels the exploration
did not query, the conditional law is the model with every queried label closed.  This is
`clusterFactorization` at the level of the record; the labels meeting the reached set are exactly
the queried ones, by `queried_eq_labelsMeeting_of_mem`. -/
theorem real_recordEvent_inter_residual [Fintype E] (H : Hypergraph V E) (S : Set V)
    (r : ExplorationRecord V E) {A : Set (Set E)}
    (hA : DeterminedBy A (labelsMeeting H r.reached)ᶜ) :
    (prodBernoulli H.prob).real (recordEvent H S r ∩ A)
      = (prodBernoulli H.prob).real (recordEvent H S r)
        * (prodBernoulli (deleteHyper H r.reached).prob).real A := by
  by_cases hne : (recordEvent H S r).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hne
    have hq : r.queried = labelsMeeting H r.reached := queried_eq_labelsMeeting_of_mem H S hω₀
    have hA' : DeterminedBy A (r.queried)ᶜ := by
      rw [hq]; exact hA
    rw [real_recordEvent_inter H S r A, condRecord_eq_real_of_determinedBy H r hA',
      prodBernoulli_deleteHyper_real_eq H r.reached hA]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.empty_inter]
    simp

/-! ## Target 3: Harris along the exploration -/

/-- The indicator of an increasing event is an increasing function.  Companion of
`antitone_ind_of_isLowerSet` in `KN/HyperAvoid.lean`. -/
theorem monotone_ind_of_isUpperSet {ι : Type*} {Y : Set (Set ι)} (hY : IsUpperSet Y) :
    Monotone fun ω : Set ι => DecisionTree.ind Y ω := by
  intro a b hab
  show DecisionTree.ind Y a ≤ DecisionTree.ind Y b
  by_cases ha : a ∈ Y
  · rw [DecisionTree.ind_of_mem ha, DecisionTree.ind_of_mem (hY hab ha)]
  · rw [DecisionTree.ind_of_not_mem ha]
    exact DecisionTree.ind_nonneg _ _

/-- **Harris for a cluster functional against an increasing event.**  `fibreMean H S F` is defined on
every set of labels, not only on the feasible records, and it is increasing when `F` is
(`fibreMean_mono`), so it may be handed to `prodBernoulli_integral_mul_le` directly.  No sign
hypothesis on `F` is needed. -/
theorem integral_fibreMean_mul_real_le [Fintype E] (H : Hypergraph V E) (S : Set V)
    {F : Set V → ℝ} (hF : Monotone F) {Y : Set (Set E)} (hY : IsUpperSet Y) :
    (∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) * (prodBernoulli H.prob).real Y
      ≤ ∫ ω in Y, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob) := by
  have hYm : MeasurableSet Y := measurableSet_of_fintype Y
  have key := prodBernoulli_integral_mul_le H.prob (f := fibreMean H S F)
    (g := fun ω => DecisionTree.ind Y ω) (fibreMean_mono H S hF) (monotone_ind_of_isUpperSet hY)
  have hindint : (∫ ω, DecisionTree.ind Y ω ∂(prodBernoulli H.prob))
      = (prodBernoulli H.prob).real Y := by
    have hfun : (fun ω : Set E => DecisionTree.ind Y ω) = Y.indicator (1 : Set E → ℝ) := by
      funext ω
      simp only [DecisionTree.indicator_eq_mul_ind, Pi.one_apply, one_mul]
    rw [hfun, integral_indicator_one hYm]
  have hprodint : (∫ ω, fibreMean H S F ω * DecisionTree.ind Y ω ∂(prodBernoulli H.prob))
      = ∫ ω in Y, fibreMean H S F ω ∂(prodBernoulli H.prob) := by
    have hfun : (fun ω : Set E => fibreMean H S F ω * DecisionTree.ind Y ω)
        = Y.indicator fun ω => fibreMean H S F ω := by
      funext ω
      simp only [DecisionTree.indicator_eq_mul_ind]
    rw [hfun, integral_indicator hYm]
  rw [hindint, hprodint] at key
  simpa only [fibreMean_eq] using key

/-- **Target 3, the hyperedge decision-tree Harris inequality.**  For an increasing `F` and an
increasing event `Y`, and a family `A` presenting `Y` on each cluster event by an event determined
by the labels the exploration did not query,

  `E[F(C)] · P(Y) ≤ ∑_K F(K) · P(C = K) · P_{H_K}(A K)`,

where `H_K` is the model with the labels meeting `K` closed.  The right-hand side is the bond
`E[f · E[1_Y | ℱ]]` with the conditional expectation computed exactly by `clusterFactorization`,
and the whole statement is an inequality between finite weighted sums, with no conditioning on an
event of positive probability. -/
theorem treeHarris_hyper [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    {F : Set V → ℝ} (hF : Monotone F) {Y : Set (Set E)} (hY : IsUpperSet Y)
    (A : Finset V → Set (Set E))
    (hAdet : ∀ K : Finset V, DeterminedBy (A K) (labelsMeeting H (↑K : Set V))ᶜ)
    (hAY : ∀ K : Finset V,
      clusterEvent H S (↑K : Set V) ∩ Y = clusterEvent H S (↑K : Set V) ∩ A K) :
    (∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) * (prodBernoulli H.prob).real Y
      ≤ ∑ K : Finset V, F (↑K : Set V) *
          ((prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V)) *
            (prodBernoulli (deleteHyper H (↑K : Set V)).prob).real (A K)) := by
  refine le_trans (integral_fibreMean_mul_real_le H S hF hY) (le_of_eq ?_)
  rw [setIntegral_fibreMean_eq_sum H S F (measurableSet_of_fintype Y)]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [hAY K, clusterFactorization H S (↑K : Set V) (hAdet K) (measurableSet_of_fintype _)]

/-! ## A family of residual events

The family `A` of `treeHarris_hyper` cannot be replaced by one event: an event determined by the
labels avoiding `K` for every `K` is determined by the labels incident to no vertex at all.  The
family the gluing argument supplies is the one below: a connection between vertices outside the
explored cluster, read in the configuration with the queried labels discarded.  It is the
`clusterEventAvoiding` device of `KN/HyperExchange.lean` for connection events. -/

/-- The event that `x` reaches `y` through labels avoiding `K`. -/
def residualConn (H : Hypergraph V E) (K : Set V) (x y : V) : Set (Set E) :=
  {ω | (openHyperGraph H (ω ∩ (labelsMeeting H K)ᶜ)).Reachable x y}

/-- The residual connection event depends only on the labels avoiding `K`. -/
theorem determinedBy_residualConn (H : Hypergraph V E) (K : Set V) (x y : V) :
    DeterminedBy (residualConn H K x y) (labelsMeeting H K)ᶜ := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [residualConn, Set.mem_setOf_eq, h]

/-- A walk out of a vertex outside `K` never enters `K` and never uses a label meeting `K`, on the
event that the cluster of `S` is exactly `K`: an open label meeting `K` has all of its vertices
inside `K` (`incidence_subset_of_clusterEvent`), so it cannot be traversed from outside. -/
private theorem walk_avoid (H : Hypergraph V E) (S K : Set V) {ω : Set E}
    (hω : ω ∈ clusterEvent H S K) {x y : V} (w : (openHyperGraph H ω).Walk x y) :
    x ∉ K → y ∉ K ∧ (openHyperGraph H (ω ∩ (labelsMeeting H K)ᶜ)).Reachable x y := by
  induction w with
  | nil => exact fun hx => ⟨hx, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hadj p ih =>
      intro ha
      obtain ⟨hne, e, heω, hae, hbe⟩ := (openHyperGraph_adj_iff H ω a b).1 hadj
      have hnotmeet : e ∉ labelsMeeting H K := fun hm =>
        ha (incidence_subset_of_clusterEvent H S K hω heω hm hae)
      have hb : b ∉ K := fun hbK =>
        hnotmeet (Set.not_disjoint_iff.2 ⟨b, hbe, hbK⟩)
      obtain ⟨hc, hr⟩ := ih hb
      have hadj' : (openHyperGraph H (ω ∩ (labelsMeeting H K)ᶜ)).Adj a b :=
        (openHyperGraph_adj_iff H _ a b).2 ⟨hne, e, ⟨heω, hnotmeet⟩, hae, hbe⟩
      exact ⟨hc, hadj'.reachable.trans hr⟩

/-- **The family, verified.**  On the event that the cluster of `S` is exactly `K`, a connection out
of a vertex outside `K` is a connection through labels avoiding `K`.  So `residualConn H K x y` is
an admissible `A K` in `treeHarris_hyper` whenever `x ∉ K`. -/
theorem clusterEvent_inter_hyperConn (H : Hypergraph V E) (S K : Set V) {x : V} (hx : x ∉ K)
    (y : V) :
    clusterEvent H S K ∩ hyperConn H x y = clusterEvent H S K ∩ residualConn H K x y := by
  ext ω
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hω, hconn⟩
    obtain ⟨w⟩ := hconn
    exact ⟨hω, (walk_avoid H S K hω w hx).2⟩
  · rintro ⟨hω, hres⟩
    exact ⟨hω, hres.mono (openHyperGraph_le_of_subset H Set.inter_subset_left)⟩

end KNAll.Site

end
