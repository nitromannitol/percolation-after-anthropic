import Hypergraph.HyperCTBase
import Percolation.Continuity.LowerTail.TreeHarrisReal

/-!
# The hyperedge cluster exploration as a decision tree, and Gladkov's Theorem 3.2 along it

`KN/HyperDecisionTree.lean` defines the exploration record directly and proves the correlation
inequality that holds along it only for functionals READ OFF THE RECORD (`treeHarris_hyper`,
`CTBase.treeHarris_real_recordDetermined`).  A function of the record is its own conditional
expectation, so for it the statement collapses to Harris' inequality and no induction is needed.
For an arbitrary increasing event the collapse fails, and the obstruction recorded in
`KN/HyperCTBase.lean` is concrete: `ω ↦ condRecord H (recordAt H S ω) Y` is not a monotone function
of `ω`, because a larger configuration queries labels the smaller one did not and those labels are
resampled rather than found open.  Gladkov's proof of Theorem 3.2 does not go through that map; it
inducts over the decision tree that builds the revealed set, pruning one deepest node at a time.
This module builds that tree for a hypergraph and transports Theorem 3.2 along it.

## The exploration

`ExplState`, `queryable`, `hstep`, `hinit`, `hrun`, `hfin`, `reachedBy`, `revealedBy` — the
exploration of the `C`-open cluster of the vertex set `S` among all labels: query, one at a time, an
unqueried label incident to a reached vertex; a label found open makes ALL of its vertices reached.
`ExplInv`, `inv_hfin`, `queryable_hfin` — the invariant and termination after `#E + 1` steps.

`reachedBy_eq` — the reached set is `hyperClusterSet H C S`; `mem_revealedBy_iff` and
`coe_revealed_clusterTree` — the queried set is `labelsMeeting H (hyperClusterSet H C S)`, which is
`(recordAt H S C).queried` of `KN/HyperDecisionTree.lean`.

The hyperedge exploration differs from the bond one (`SetClusterExploration.lean`) in its
`queryable` predicate.  A bond exploration may query the edges joining the reached set to its
complement; a hyperedge joining two unreached vertices while a third of its vertices is reached
would then be missed, and the queried set would not be `labelsMeeting H` of the reached set.  So
`queryable` filters on incidence with the reached set, internal labels included — the shape the
bond file already takes for a vertex SET source.

## The tree

`htree`, `clusterTree` — the exploration as a `Percolation.Literature.DTree E`;
`rev_iterate_hstep`, `revealedBy_eq_revealed` — the set the tree builds on `C` is the set the
exploration queries; `coe_splice_eq_spliceRecord` — Gladkov's hybrid `C₁ →_{S(C₁)} C₂` is the
`spliceRecord` of `KN/HyperDecisionTree.lean`.

**The tree induction survives arbitrary incidence sets.**  Gladkov's Theorem 3.2
(`DecisionTree.PrW_mul_PrW_le_Pr2W_treeHK`) is a statement about an abstract decision tree over an
arbitrary coordinate type; it knows nothing about the geometry the tree explores.  What the
hypergraph has to supply is a tree whose revealed set is the queried set of the record, and the
exploration above supplies it.  The loss recorded in `KN/HyperTrace.lean`
(`exists_traceOutside_not_injective`: a label is not determined by the vertices it touches) does
not enter, because the tree queries labels and not vertex pairs.  What that loss does forbid is
recovering the queried set from the reached set alone; the queried set is recovered here from the
INCIDENCE relation with the reached set, which is available, and that is `mem_revealedBy_iff`.

## The transport

`finEvent`, `sum_set_eq_sum_finset`, `wtW_univ_eq_weight`, `integral_eq_sum_wtW`,
`PrW_univ_eq_real`, `cE_bridge`, `integral_ind_mul_cE_eq_Pr2W` — the finitary weighted calculus of
`Percolation/Literature/DecisionTreeWeighted.lean`, whose configurations are finsets of open
coordinates, against the product measure of the measure layer, whose configurations are sets of open
labels.  Over a finite label type the coercion `Finset E → Set E` is a bijection carrying `wtW` to
`BHK2006.weight`, and `integral_prodBernoulli_eq_sum` turns every integral into a sum.

## The results

* **`real_mul_real_le_integral_ind_mul_cE`**, `real_mul_real_le_integral_ind_mul_condRecord` — the
  two-event inequality: for increasing `X` and `Y`,
  `P(X) · P(Y) ≤ E[1_X · P(Y ∣ ℱ_S)]`, with `X` an ARBITRARY increasing event.
* `integral_mul_cE_ind_ge`, **`treeHarris_real_general`** — the same for a monotone `f ≥ 0` in place
  of `1_X`, by the layer-cake lemma `CTBase.sum_mul_nonneg_of_upperSet` and the symmetry
  `CTBase.integral_mul_cE_comm`.  Bond templates: `TreeHarris.ED_mul_PrW_le_ED_mul_cE_ind` and
  `TreeHarris.treeHarris_real`.
* `treeHK_otherCluster` — the shape the gluing argument needs and the record-determined inequality
  does not cover: the exploration runs from `S` while the increasing event is a functional of the
  cluster of a different vertex.  `treeHK_conn` is the same for two connection events.
* `harris_of_treeHK`, `cE_empty_source` — the two ends of the range of the source: the full vertex
  set gives Harris' inequality `P(X) P(Y) ≤ P(X ∩ Y)`, the empty set gives the identity
  `P(X) P(Y) = P(X) P(Y)`.

## References

* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), Def. 2.4,
  Example 2.5, Lemma 3.1, Theorem 3.2.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
-/

noncomputable section

namespace KNAll.Site.TreeHK

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {V E : Type*}

/-! ## The exploration -/

/-- A state of the exploration: the vertices reached so far and the labels queried so far. -/
structure ExplState (V E : Type*) where
  /-- The vertices reached from the source by open queried labels. -/
  vis : Set V
  /-- The labels queried, whatever the answer. -/
  rev : Finset E

/-- A choice of an element of a finite set of labels, if any. -/
def pickLabel [DecidableEq E] (s : Finset E) : Option E :=
  if h : s.Nonempty then some h.choose else none

theorem mem_of_pickLabel_eq_some [DecidableEq E] {s : Finset E} {e : E}
    (h : pickLabel s = some e) : e ∈ s := by
  unfold pickLabel at h
  split_ifs at h with hs
  rw [Option.some.injEq] at h
  exact h ▸ hs.choose_spec

theorem pickLabel_eq_none_iff [DecidableEq E] {s : Finset E} : pickLabel s = none ↔ s = ∅ := by
  constructor
  · intro h
    by_contra hne
    have hs : s.Nonempty := Finset.nonempty_iff_ne_empty.2 hne
    unfold pickLabel at h
    rw [dif_pos hs] at h
    exact Option.some_ne_none _ h
  · intro h
    unfold pickLabel
    rw [dif_neg (Finset.not_nonempty_iff_eq_empty.2 h)]

open Classical in
/-- The labels the exploration may still query: not yet queried, and incident to a reached vertex.
Every label meeting the reached set is queryable, not only those joining it to an unreached
vertex; a hyperedge can meet the reached set and still have unreached vertices, and the bond
template `SetClusterExploration.bnd` already takes this shape. -/
def queryable [Fintype E] (H : Hypergraph V E) (σ : ExplState V E) : Finset E :=
  Finset.univ.filter fun e => e ∉ σ.rev ∧ ¬ Disjoint (H.incidence e) σ.vis

theorem mem_queryable [Fintype E] {H : Hypergraph V E} {σ : ExplState V E} {e : E} :
    e ∈ queryable H σ ↔ e ∉ σ.rev ∧ ¬ Disjoint (H.incidence e) σ.vis := by
  classical
  simp [queryable]

section Defs

variable [Fintype E] [DecidableEq E]

/-- One step of the exploration on the configuration `C`: query a queryable label; if it is open,
reach every vertex it is incident to. -/
def hstep (H : Hypergraph V E) (C : Finset E) (σ : ExplState V E) : ExplState V E :=
  match pickLabel (queryable H σ) with
  | none => σ
  | some e =>
      if e ∈ C then ⟨σ.vis ∪ H.incidence e, insert e σ.rev⟩ else ⟨σ.vis, insert e σ.rev⟩

/-- The initial state: the source reached, nothing queried. -/
def hinit (S : Set V) : ExplState V E := ⟨S, ∅⟩

/-- The state after `k` steps. -/
def hrun (H : Hypergraph V E) (S : Set V) (C : Finset E) : ℕ → ExplState V E
  | 0 => hinit S
  | k + 1 => hstep H C (hrun H S C k)

/-- The final state.  The fuel `#E + 1` is enough by `queryable_hfin`. -/
def hfin (H : Hypergraph V E) (S : Set V) (C : Finset E) : ExplState V E :=
  hrun H S C (Fintype.card E + 1)

/-- The vertices the exploration reaches. -/
def reachedBy (H : Hypergraph V E) (S : Set V) (C : Finset E) : Set V := (hfin H S C).vis

/-- The labels the exploration queries. -/
def revealedBy (H : Hypergraph V E) (S : Set V) (C : Finset E) : Finset E := (hfin H S C).rev

end Defs

/-! ## One step -/

section Basic

variable [Fintype E] [DecidableEq E] {H : Hypergraph V E} {S : Set V} {C : Finset E}

theorem hstep_of_queryable_eq_empty {σ : ExplState V E} (h : queryable H σ = ∅) :
    hstep H C σ = σ := by
  unfold hstep
  rw [pickLabel_eq_none_iff.2 h]

theorem hstep_of_queryable_ne_empty {σ : ExplState V E} (h : queryable H σ ≠ ∅) :
    ∃ e ∈ queryable H σ, pickLabel (queryable H σ) = some e ∧
      hstep H C σ =
        (if e ∈ C then ⟨σ.vis ∪ H.incidence e, insert e σ.rev⟩
          else ⟨σ.vis, insert e σ.rev⟩) := by
  unfold hstep
  cases hp : pickLabel (queryable H σ) with
  | none => exact absurd (pickLabel_eq_none_iff.1 hp) h
  | some e => exact ⟨e, mem_of_pickLabel_eq_some hp, rfl, rfl⟩

theorem rev_subset_hstep (C : Finset E) (σ : ExplState V E) : σ.rev ⊆ (hstep H C σ).rev := by
  by_cases h : queryable H σ = ∅
  · rw [hstep_of_queryable_eq_empty h]
  · obtain ⟨e, -, -, hs⟩ := hstep_of_queryable_ne_empty (C := C) h
    rw [hs]
    split_ifs <;> exact Finset.subset_insert e σ.rev

theorem card_rev_hstep {σ : ExplState V E} (h : queryable H σ ≠ ∅) :
    σ.rev.card + 1 ≤ (hstep H C σ).rev.card := by
  obtain ⟨e, he, -, hs⟩ := hstep_of_queryable_ne_empty (C := C) h
  have hno : e ∉ σ.rev := (mem_queryable.1 he).1
  rw [hs]
  split_ifs <;> simp [Finset.card_insert_of_notMem hno]

theorem hrun_succ (H : Hypergraph V E) (S : Set V) (C : Finset E) (k : ℕ) :
    hrun H S C (k + 1) = hstep H C (hrun H S C k) := rfl

end Basic

/-! ## The invariant -/

/-- The invariant of the exploration of the `C`-open cluster of `S`. -/
structure ExplInv [DecidableEq E] (H : Hypergraph V E) (S : Set V) (C : Finset E)
    (σ : ExplState V E) : Prop where
  /-- the source is reached -/
  root : S ⊆ σ.vis
  /-- every queried label meets the reached set -/
  touch : ∀ e ∈ σ.rev, ¬ Disjoint (H.incidence e) σ.vis
  /-- a queried label found open has all of its vertices reached -/
  open_vis : ∀ e ∈ σ.rev, e ∈ C → H.incidence e ⊆ σ.vis
  /-- every reached vertex is joined to the source by queried open labels -/
  reach : ∀ v ∈ σ.vis, ∃ s ∈ S,
    (openHyperGraph H (↑(σ.rev ∩ C) : Set E)).Reachable s v

section Invariant

variable [Fintype E] [DecidableEq E] {H : Hypergraph V E} {S : Set V} {C : Finset E}

omit [Fintype E] in
theorem inv_hinit : ExplInv H S C (hinit S) where
  root := le_rfl
  touch := by simp [hinit]
  open_vis := by simp [hinit]
  reach := fun v hv => ⟨v, hv, SimpleGraph.Reachable.refl _⟩

/-- **The invariant is preserved by a step.** -/
theorem inv_hstep {σ : ExplState V E} (hσ : ExplInv H S C σ) : ExplInv H S C (hstep H C σ) := by
  by_cases h : queryable H σ = ∅
  · rw [hstep_of_queryable_eq_empty h]; exact hσ
  obtain ⟨e, he, -, hs⟩ := hstep_of_queryable_ne_empty (C := C) h
  obtain ⟨herev, hmeet⟩ := mem_queryable.1 he
  obtain ⟨u, hue, huv⟩ := Set.not_disjoint_iff.1 hmeet
  have hmono : openHyperGraph H (↑(σ.rev ∩ C) : Set E) ≤
      openHyperGraph H (↑(insert e σ.rev ∩ C) : Set E) :=
    openHyperGraph_le_of_subset H
      (Finset.coe_subset.2 (Finset.inter_subset_inter (Finset.subset_insert _ _) subset_rfl))
  rw [hs]
  split_ifs with hC
  · -- the queried label is open: all of its vertices are reached
    refine ⟨hσ.root.trans Set.subset_union_left, ?_, ?_, ?_⟩
    · intro e' he'
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact Set.not_disjoint_iff.2 ⟨u, hue, Or.inl huv⟩
      · obtain ⟨w, hw1, hw2⟩ := Set.not_disjoint_iff.1 (hσ.touch e' he')
        exact Set.not_disjoint_iff.2 ⟨w, hw1, Or.inl hw2⟩
    · intro e' he' he'C x hx
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact Or.inr hx
      · exact Or.inl (hσ.open_vis e' he' he'C hx)
    · intro x hx
      rcases hx with hx | hx
      · obtain ⟨s, hsS, hsx⟩ := hσ.reach x hx
        exact ⟨s, hsS, hsx.mono hmono⟩
      · obtain ⟨s, hsS, hsu⟩ := hσ.reach u huv
        refine ⟨s, hsS, (hsu.mono hmono).trans ?_⟩
        by_cases hux : u = x
        · subst hux; exact SimpleGraph.Reachable.refl _
        · have hadj : (openHyperGraph H (↑(insert e σ.rev ∩ C) : Set E)).Adj u x :=
            (openHyperGraph_adj_iff H _ u x).2
              ⟨hux, e, Finset.mem_coe.2 (Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _, hC⟩),
                hue, hx⟩
          exact hadj.reachable
  · -- the queried label is closed
    refine ⟨hσ.root, ?_, ?_, ?_⟩
    · intro e' he'
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact hmeet
      · exact hσ.touch e' he'
    · intro e' he' he'C x hx
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact absurd he'C hC
      · exact hσ.open_vis e' he' he'C hx
    · intro x hx
      obtain ⟨s, hsS, hsx⟩ := hσ.reach x hx
      exact ⟨s, hsS, hsx.mono hmono⟩

theorem inv_hrun (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    ∀ k, ExplInv H S C (hrun H S C k)
  | 0 => inv_hinit
  | k + 1 => inv_hstep (inv_hrun H S C k)

theorem inv_hfin (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    ExplInv H S C (hfin H S C) := inv_hrun H S C _

/-! ## Termination -/

theorem queryable_empty_or_le_card (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    ∀ k, queryable H (hrun H S C k) = ∅ ∨ k ≤ (hrun H S C k).rev.card
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
      by_cases h : queryable H (hrun H S C k) = ∅
      · left; rw [hrun_succ, hstep_of_queryable_eq_empty h]; exact h
      · rcases queryable_empty_or_le_card H S C k with h' | h'
        · exact absurd h' h
        · exact Or.inr (le_trans (Nat.add_le_add_right h' 1) (card_rev_hstep h))

/-- **The exploration is complete when it stops**: no label meeting the reached set is left
unqueried. -/
theorem queryable_hfin (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    queryable H (hfin H S C) = ∅ := by
  rcases queryable_empty_or_le_card H S C (Fintype.card E + 1) with h | h
  · exact h
  · have hle : (hfin H S C).rev.card ≤ Fintype.card E := Finset.card_le_univ _
    exact absurd (lt_of_lt_of_le (Nat.lt_of_succ_le h) hle) (lt_irrefl _)

end Invariant

/-! ## What the exploration reaches and queries -/

section Correct

variable [Fintype E] [DecidableEq E] {H : Hypergraph V E} {S : Set V} {C : Finset E}

/-- A set containing the start of a walk and closed under adjacency along the walk's graph
contains its end. -/
private theorem mem_of_walk_closed {G : SimpleGraph V} {A : Set V}
    (hA : ∀ a b, G.Adj a b → a ∈ A → b ∈ A) {u v : V} (p : G.Walk u v) (hu : u ∈ A) : v ∈ A := by
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hA _ _ hadj hu)

/-- **The exploration reaches exactly the open cluster of the source.** -/
theorem reachedBy_eq (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    reachedBy H S C = hyperClusterSet H (↑C : Set E) S := by
  have hI := inv_hfin H S C
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨s, hsS, hsv⟩ := hI.reach v hv
    have hsub : (↑((hfin H S C).rev ∩ C) : Set E) ⊆ (↑C : Set E) :=
      Finset.coe_subset.2 Finset.inter_subset_right
    exact ⟨s, hsS, hsv.mono (openHyperGraph_le_of_subset H hsub)⟩
  · rintro v ⟨s, hsS, hsv⟩
    obtain ⟨p⟩ := hsv
    have hclosed : ∀ a b, (openHyperGraph H (↑C : Set E)).Adj a b →
        a ∈ reachedBy H S C → b ∈ reachedBy H S C := by
      intro a b hab ha
      obtain ⟨-, e, heC, hae, hbe⟩ := (openHyperGraph_adj_iff H _ a b).1 hab
      have hmeet : ¬ Disjoint (H.incidence e) (hfin H S C).vis :=
        Set.not_disjoint_iff.2 ⟨a, hae, ha⟩
      by_cases hrev : e ∈ (hfin H S C).rev
      · exact hI.open_vis e hrev (Finset.mem_coe.1 heC) hbe
      · have : e ∈ queryable H (hfin H S C) := mem_queryable.2 ⟨hrev, hmeet⟩
        rw [queryable_hfin] at this
        exact absurd this (Finset.notMem_empty e)
    exact mem_of_walk_closed hclosed p (hI.root hsS)

/-- **The exploration queries exactly the labels incident to the cluster it reaches.**  A label
joining two unreached vertices while a third of its vertices is reached is queried too; this is
the point at which the hyperedge exploration differs from the bond one, and it is the reason
`queryable` filters on incidence with the reached set rather than on joining it to its
complement. -/
theorem mem_revealedBy_iff (H : Hypergraph V E) (S : Set V) (C : Finset E) {e : E} :
    e ∈ revealedBy H S C ↔ ¬ Disjoint (H.incidence e) (reachedBy H S C) := by
  have hI := inv_hfin H S C
  constructor
  · exact fun he => hI.touch e he
  · intro hmeet
    by_contra hrev
    have : e ∈ queryable H (hfin H S C) := mem_queryable.2 ⟨hrev, hmeet⟩
    rw [queryable_hfin] at this
    exact absurd this (Finset.notMem_empty e)

/-- **The queried set is the queried set of the record** of `KN/HyperDecisionTree.lean`. -/
theorem coe_revealedBy (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    (↑(revealedBy H S C) : Set E) = labelsMeeting H (hyperClusterSet H (↑C : Set E) S) := by
  ext e
  rw [Finset.mem_coe, mem_revealedBy_iff, reachedBy_eq]
  rfl

end Correct


/-! ## The exploration as a decision tree -/

section Tree

variable [Fintype E] [DecidableEq E]

/-- **The exploration as a decision tree over the labels.**  At a state with a queryable label the
tree queries the label the exploration would query and branches on the answer; the `yes` child
continues from the state with all of the label's vertices reached, the `no` child from the state
with the label recorded closed.  This is the carrier the induction of Gladkov's Theorem 3.2 runs
over, and it is what `KN/HyperDecisionTree.lean` does not build. -/
def htree (H : Hypergraph V E) : ℕ → ExplState V E → DTree E
  | 0, _ => .leaf
  | n + 1, σ =>
      match pickLabel (queryable H σ) with
      | none => .leaf
      | some e =>
          .node e (htree H n ⟨σ.vis ∪ H.incidence e, insert e σ.rev⟩)
            (htree H n ⟨σ.vis, insert e σ.rev⟩)

variable {H : Hypergraph V E}

/-- **The tree queries what the exploration queries.** -/
theorem rev_iterate_hstep (C : Finset E) :
    ∀ (n : ℕ) (σ : ExplState V E),
      ((hstep H C)^[n] σ).rev = σ.rev ∪ DecisionTree.revealed (htree H n σ) C
  | 0, σ => by simp [htree, DecisionTree.revealed]
  | n + 1, σ => by
      rw [Function.iterate_succ_apply]
      by_cases h : queryable H σ = ∅
      · rw [hstep_of_queryable_eq_empty h,
          Function.iterate_fixed (hstep_of_queryable_eq_empty h)]
        simp [htree, pickLabel_eq_none_iff.2 h, DecisionTree.revealed]
      · obtain ⟨e, -, hpick, hs⟩ := hstep_of_queryable_ne_empty (C := C) h
        have htr : htree H (n + 1) σ =
            .node e (htree H n ⟨σ.vis ∪ H.incidence e, insert e σ.rev⟩)
              (htree H n ⟨σ.vis, insert e σ.rev⟩) := by
          simp only [htree, hpick]
        rw [hs, htr]
        by_cases hC : e ∈ C
        · rw [if_pos hC, rev_iterate_hstep C n]
          simp only [DecisionTree.revealed, if_pos hC, Finset.insert_union, Finset.union_insert]
        · rw [if_neg hC, rev_iterate_hstep C n]
          simp only [DecisionTree.revealed, if_neg hC, Finset.insert_union, Finset.union_insert]

private theorem hrun_eq_iterate (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    ∀ k : ℕ, hrun H S C k = (hstep H C)^[k] (hinit S)
  | 0 => rfl
  | k + 1 => by rw [hrun_succ, Function.iterate_succ_apply', hrun_eq_iterate H S C k]

/-- The decision tree of the exploration of the cluster of `S`. -/
def clusterTree (H : Hypergraph V E) (S : Set V) : DTree E :=
  htree H (Fintype.card E + 1) (hinit S)

/-- **The set the tree builds is the set the exploration queries.** -/
theorem revealedBy_eq_revealed (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    revealedBy H S C = DecisionTree.revealed (clusterTree H S) C := by
  rw [revealedBy, hfin, hrun_eq_iterate, rev_iterate_hstep, clusterTree]
  simp [hinit]

/-- **The set the tree builds is the queried set of the exploration record** of
`KN/HyperDecisionTree.lean`: every label incident to the explored cluster. -/
theorem coe_revealed_clusterTree (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    (↑(DecisionTree.revealed (clusterTree H S) C) : Set E)
      = labelsMeeting H (hyperClusterSet H (↑C : Set E) S) := by
  rw [← revealedBy_eq_revealed, coe_revealedBy]

theorem coe_revealed_clusterTree_eq_queried (H : Hypergraph V E) (S : Set V) (C : Finset E) :
    (↑(DecisionTree.revealed (clusterTree H S) C) : Set E)
      = (recordAt H S (↑C : Set E)).queried := by
  rw [coe_revealed_clusterTree, queried_recordAt]

/-- **The tree splice is the record splice.**  Gladkov's hybrid `C₁ →_{S(C₁)} C₂` and the
`spliceRecord` of `KN/HyperDecisionTree.lean` are the same configuration. -/
theorem coe_splice_eq_spliceRecord (H : Hypergraph V E) (S : Set V) (C₁ C₂ : Finset E) :
    (↑(DecisionTree.splice (DecisionTree.revealed (clusterTree H S) C₁) C₁ C₂) : Set E)
      = spliceRecord (recordAt H S (↑C₁ : Set E)) (↑C₂ : Set E) := by
  have hq := coe_revealed_clusterTree H S C₁
  ext e
  simp only [Finset.mem_coe, DecisionTree.mem_splice, spliceRecord, Set.mem_union, Set.mem_sdiff,
    recordAt_openLabels, Set.mem_inter_iff, queried_recordAt]
  rw [show (e ∈ DecisionTree.revealed (clusterTree H S) C₁)
      ↔ e ∈ labelsMeeting H (hyperClusterSet H (↑C₁ : Set E) S) from
    (Set.ext_iff.1 hq e)]
  tauto

end Tree


/-! ## From the finitary weighted calculus to the product measure -/

section Bridge

variable [Fintype E] [DecidableEq E]

/-- An event of configurations, read as an event of the finitary weighted calculus, whose
configurations are finsets of open labels. -/
def finEvent (X : Set (Set E)) : Set (Finset E) := {T : Finset E | (↑T : Set E) ∈ X}

omit [Fintype E] [DecidableEq E] in
theorem ind_coe (X : Set (Set E)) (T : Finset E) :
    DecisionTree.ind (finEvent X) T = DecisionTree.ind X (↑T : Set E) := by
  by_cases h : (↑T : Set E) ∈ X
  · rw [DecisionTree.ind_of_mem (show T ∈ finEvent X from h), DecisionTree.ind_of_mem h]
  · rw [DecisionTree.ind_of_not_mem (show T ∉ finEvent X from h), DecisionTree.ind_of_not_mem h]

omit [Fintype E] [DecidableEq E] in
theorem isUpperSet_finEvent {X : Set (Set E)} (hX : IsUpperSet X) : IsUpperSet (finEvent X) :=
  fun _ _ hTT hT => hX (Finset.coe_subset.2 hTT) hT

omit [DecidableEq E] in
/-- Summing over configurations is summing over the finsets of open labels. -/
theorem sum_set_eq_sum_finset (g : Set E → ℝ) :
    ∑ ω : Set E, g ω = ∑ T : Finset E, g (↑T : Set E) :=
  (Fintype.sum_bijective (fun T : Finset E => (↑T : Set E))
    ⟨Finset.coe_injective,
      fun ω => ⟨(Set.toFinite ω).toFinset, (Set.toFinite ω).coe_toFinset⟩⟩ _ _ fun _ => rfl).symm

/-- The Bernoulli weight of the bond calculus is the product weight of the measure layer. -/
theorem wtW_univ_eq_weight (q : E → ℝ) (T : Finset E) :
    DecisionTree.wtW (Finset.univ : Finset E) q T = BHK2006.weight q (↑T : Set E) := by
  unfold DecisionTree.wtW BHK2006.weight
  exact Finset.prod_congr rfl fun i _ => by by_cases h : i ∈ T <;> simp [h]

/-- The integral against `prodBernoulli` as a finitary weighted sum. -/
theorem integral_eq_sum_wtW (H : Hypergraph V E) (g : Set E → ℝ) :
    (∫ ω, g ω ∂(prodBernoulli H.prob))
      = ∑ T : Finset E, DecisionTree.wtW (Finset.univ : Finset E)
          (fun e => (H.prob e : ℝ)) T * g (↑T : Set E) := by
  rw [BHK2006.integral_prodBernoulli_eq_sum, sum_set_eq_sum_finset
    (fun ω => BHK2006.weight (fun e => (H.prob e : ℝ)) ω * g ω)]
  exact Finset.sum_congr rfl fun T _ => by rw [wtW_univ_eq_weight]

/-- The probability of the bond calculus is the probability of the measure layer. -/
theorem PrW_univ_eq_real (H : Hypergraph V E) (X : Set (Set E)) :
    DecisionTree.PrW (Finset.univ : Finset E) (fun e => (H.prob e : ℝ)) (finEvent X)
      = (prodBernoulli H.prob).real X := by
  rw [DecisionTree.PrW_eq_sum_ind, Finset.powerset_univ,
    ← CTBase.integral_ind_eq_real (prodBernoulli H.prob) X,
    integral_eq_sum_wtW H (fun ω => DecisionTree.ind X ω)]
  exact Finset.sum_congr rfl fun T _ => by rw [ind_coe]

/-- **The conditional expectation of the bond calculus at the exploration tree is the conditional
expectation of `KN/HyperCTBase.lean` at the exploration record.**  Gladkov's hybrid resamples the
labels the tree did not query; `spliceRecord` resamples the labels the record did not query, and
`coe_revealed_clusterTree` says those are the same labels. -/
theorem cE_bridge (H : Hypergraph V E) (S : Set V) (Y : Set (Set E)) (C : Finset E) :
    Percolation.Continuity.TreeHarris.cE (Finset.univ : Finset E) (fun e => (H.prob e : ℝ))
        (DecisionTree.revealed (clusterTree H S)) (DecisionTree.ind (finEvent Y)) C
      = CTBase.cE H S (fun ν => DecisionTree.ind Y ν) (↑C : Set E) := by
  rw [CTBase.cE_eq, CTBase.condRecordFun,
    integral_eq_sum_wtW H (fun η => DecisionTree.ind Y (spliceRecord (recordAt H S ↑C) η))]
  unfold Percolation.Continuity.TreeHarris.cE
  rw [Finset.powerset_univ]
  exact Finset.sum_congr rfl fun T₂ _ => by rw [ind_coe, coe_splice_eq_spliceRecord]

/-- **The two-configuration event of Theorem 3.2 is the mean of the record conditional
probability.** -/
theorem integral_ind_mul_cE_eq_Pr2W (H : Hypergraph V E) (S : Set V) (X Y : Set (Set E)) :
    (∫ ω, DecisionTree.ind X ω * CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω
        ∂(prodBernoulli H.prob))
      = DecisionTree.Pr2W (Finset.univ : Finset E) (fun e => (H.prob e : ℝ))
          (DecisionTree.treeHK ∅ (clusterTree H S) (finEvent X) (finEvent Y)) := by
  rw [Percolation.Continuity.TreeHarris.Pr2W_treeHK_eq_ED]
  simp only [DecisionTree.ED, Finset.powerset_univ]
  rw [integral_eq_sum_wtW H]
  exact Finset.sum_congr rfl fun T _ => by rw [ind_coe, cE_bridge]

end Bridge


/-! ## Gladkov's Theorem 3.2 for the hyperedge exploration -/

section Main

variable [Fintype E]

/-- **Gladkov 2024, Theorem 3.2, for the hyperedge cluster exploration.**  For increasing events
`X` and `Y` of the configuration,

  `P(X) · P(Y) ≤ E[1_X · P(Y ∣ ℱ_S)]`,

where `P(Y ∣ ℱ_S)` is the probability of `Y` after the labels the exploration of the cluster of `S`
did not query are resampled.  `X` is an arbitrary increasing event, not one read off the
exploration record: this is the statement `KN/HyperDecisionTree.lean` leaves open, and the reason
it does is that this file builds the decision tree the induction of Theorem 3.2 runs over.  -/
theorem real_mul_real_le_integral_ind_mul_cE (H : Hypergraph V E) (S : Set V)
    {X Y : Set (Set E)} (hX : IsUpperSet X) (hY : IsUpperSet Y) :
    (prodBernoulli H.prob).real X * (prodBernoulli H.prob).real Y
      ≤ ∫ ω, DecisionTree.ind X ω * CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω
          ∂(prodBernoulli H.prob) := by
  classical
  have h := DecisionTree.PrW_mul_PrW_le_Pr2W_treeHK (Finset.univ : Finset E)
    (fun e => unitInterval.nonneg (H.prob e)) (fun e => unitInterval.le_one (H.prob e))
    (clusterTree H S) (isUpperSet_finEvent hX) (isUpperSet_finEvent hY)
  rwa [PrW_univ_eq_real, PrW_univ_eq_real, ← integral_ind_mul_cE_eq_Pr2W] at h

/-- The same inequality with the residual probability written as `condRecord`. -/
theorem real_mul_real_le_integral_ind_mul_condRecord (H : Hypergraph V E) (S : Set V)
    {X Y : Set (Set E)} (hX : IsUpperSet X) (hY : IsUpperSet Y) :
    (prodBernoulli H.prob).real X * (prodBernoulli H.prob).real Y
      ≤ ∫ ω, DecisionTree.ind X ω * condRecord H (recordAt H S ω) Y ∂(prodBernoulli H.prob) := by
  have h := real_mul_real_le_integral_ind_mul_cE H S hX hY
  simpa only [CTBase.cE_ind_eq_condRecord] using h

/-- **The layer-cake extension**: the two-event inequality for a real monotone `f ≥ 0` in place of
the increasing event `X`.  Bond template: `TreeHarris.ED_mul_PrW_le_ED_mul_cE_ind`. -/
theorem integral_mul_cE_ind_ge (H : Hypergraph V E) (S : Set V) {f : Set E → ℝ}
    (hf : Monotone f) (hf0 : ∀ ω : Set E, 0 ≤ f ω) {Y : Set (Set E)} (hY : IsUpperSet Y) :
    (∫ ω, f ω ∂(prodBernoulli H.prob)) * (prodBernoulli H.prob).real Y
      ≤ ∫ ω, f ω * CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω ∂(prodBernoulli H.prob) := by
  classical
  have hnn : ∀ U : Set (Set E), IsUpperSet U →
      0 ≤ ∑ ω : Set E, (BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
        (CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω
          - (prodBernoulli H.prob).real Y)) * DecisionTree.ind U ω := by
    intro U hU
    have h2 := real_mul_real_le_integral_ind_mul_cE H S hU hY
    have hIU : (prodBernoulli H.prob).real U
        = ∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω * DecisionTree.ind U ω := by
      rw [← CTBase.integral_ind_eq_real (prodBernoulli H.prob) U,
        BHK2006.integral_prodBernoulli_eq_sum]
    have hIp : (∫ ω, DecisionTree.ind U ω *
          CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω ∂(prodBernoulli H.prob))
        = ∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
            (DecisionTree.ind U ω * CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω) :=
      BHK2006.integral_prodBernoulli_eq_sum _ _
    have hexp : ∑ ω : Set E, (BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
          (CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω
            - (prodBernoulli H.prob).real Y)) * DecisionTree.ind U ω
        = (∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
              (DecisionTree.ind U ω * CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω))
          - (∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω * DecisionTree.ind U ω) *
              (prodBernoulli H.prob).real Y := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ω _ => by ring
    rw [hexp, ← hIp, ← hIU]
    linarith
  have key := CTBase.sum_mul_nonneg_of_upperSet (Finset.univ : Finset (Set E))
    (fun ω => BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
      (CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω - (prodBernoulli H.prob).real Y))
    hnn f hf hf0
  have hIf : (∫ ω, f ω ∂(prodBernoulli H.prob))
      = ∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω * f ω :=
    BHK2006.integral_prodBernoulli_eq_sum _ _
  have hIfg : (∫ ω, f ω * CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω
        ∂(prodBernoulli H.prob))
      = ∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
          (f ω * CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω) :=
    BHK2006.integral_prodBernoulli_eq_sum _ _
  have hexp2 : ∑ ω : Set E, (BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
        (CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω
          - (prodBernoulli H.prob).real Y)) * f ω
      = (∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
            (f ω * CTBase.cE H S (fun ν => DecisionTree.ind Y ν) ω))
        - (∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω * f ω) *
            (prodBernoulli H.prob).real Y := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [hexp2, ← hIfg, ← hIf] at key
  linarith

/-- **Lemma TH for the hyperedge exploration, in full generality**: for a monotone `f ≥ 0` of the
configuration — not required to be read off the exploration record — and an increasing event `Y`,
`E[f] · P(Y) ≤ E[E[f ∣ ℱ_S] · 1_Y]`.  Bond template: `TreeHarris.treeHarris_real`. -/
theorem treeHarris_real_general (H : Hypergraph V E) (S : Set V) {f : Set E → ℝ}
    (hf : Monotone f) (hf0 : ∀ ω : Set E, 0 ≤ f ω) {Y : Set (Set E)} (hY : IsUpperSet Y) :
    (∫ ω, f ω ∂(prodBernoulli H.prob)) * (prodBernoulli H.prob).real Y
      ≤ ∫ ω, CTBase.cE H S f ω * DecisionTree.ind Y ω ∂(prodBernoulli H.prob) := by
  rw [← CTBase.integral_mul_cE_comm H S f (fun ν => DecisionTree.ind Y ν)]
  exact integral_mul_cE_ind_ge H S hf hf0 hY

end Main

/-! ## Two instantiations -/

section Instances

variable [Fintype E]

omit [Fintype E] in
/-- The event that the cluster of `s` lies in an up-set of vertex sets is increasing. -/
theorem isUpperSet_clusterMem (H : Hypergraph V E) (s : V) {U : Set (Set V)} (hU : IsUpperSet U) :
    IsUpperSet {ω : Set E | hyperClusterSet H ω ({s} : Set V) ∈ U} :=
  fun _ _ hsub hω => hU (hyperClusterSet_mono H ({s} : Set V) hsub) hω

/-- **The instantiation the gluing argument needs**, and the one the record-determined inequality
of `KN/HyperCTBase.lean` does not cover: the exploration is run from the source `S`, while the
increasing event on the left is a functional of the cluster of a different vertex `s`.  This is the
shape of the bond call `MarkerDominancePv.sum_condSumW_ge` at
`Percolation/Continuity/HullPort/TACE.lean:150`. -/
theorem treeHK_otherCluster (H : Hypergraph V E) (S : Set V) (s : V) {U : Set (Set V)}
    (hU : IsUpperSet U) {Y : Set (Set E)} (hY : IsUpperSet Y) :
    (prodBernoulli H.prob).real {ω : Set E | hyperClusterSet H ω ({s} : Set V) ∈ U} *
        (prodBernoulli H.prob).real Y
      ≤ ∫ ω, DecisionTree.ind {ω : Set E | hyperClusterSet H ω ({s} : Set V) ∈ U} ω *
          condRecord H (recordAt H S ω) Y ∂(prodBernoulli H.prob) :=
  real_mul_real_le_integral_ind_mul_condRecord H S (isUpperSet_clusterMem H s hU) hY

/-- The two-event inequality at a pair of connection events. -/
theorem treeHK_conn (H : Hypergraph V E) (S : Set V) (x y u v : V) :
    (prodBernoulli H.prob).real (hyperConn H x y) *
        (prodBernoulli H.prob).real (hyperConn H u v)
      ≤ ∫ ω, DecisionTree.ind (hyperConn H x y) ω *
          condRecord H (recordAt H S ω) (hyperConn H u v) ∂(prodBernoulli H.prob) :=
  real_mul_real_le_integral_ind_mul_condRecord H S (isUpperSet_hyperConn H x y)
    (isUpperSet_hyperConn H u v)

/-! ### The inequality has not collapsed

Run from the whole vertex set the exploration queries every label, so the residual probability is
the indicator itself and the inequality reads `P(X) P(Y) ≤ P(X ∩ Y)`: Harris' inequality, which
`prodBernoulli_harris_upper` of `KN/HyperUpper.lean` proves independently.  A statement that had
degenerated could not deliver it. -/

omit [Fintype E] in
/-- With every label incident to some vertex, the exploration from the whole vertex set queries
every label, so its splice is the identity. -/
theorem spliceRecord_univ (H : Hypergraph V E) (hinc : ∀ e : E, (H.incidence e).Nonempty)
    (ω η : Set E) : spliceRecord (recordAt H (Set.univ : Set V) ω) η = ω := by
  have hcl : hyperClusterSet H ω (Set.univ : Set V) = Set.univ :=
    Set.eq_univ_of_forall fun y => mem_hyperClusterSet_self H ω (Set.mem_univ y)
  have hlab : labelsMeeting H (hyperClusterSet H ω (Set.univ : Set V)) = Set.univ := by
    rw [hcl]
    refine Set.eq_univ_of_forall fun e => ?_
    obtain ⟨v, hv⟩ := hinc e
    exact Set.not_disjoint_iff.2 ⟨v, hv, Set.mem_univ v⟩
  have hq : (recordAt H (Set.univ : Set V) ω).queried = Set.univ := by
    rw [queried_recordAt, hlab]
  show (recordAt H (Set.univ : Set V) ω).openLabels ∪
    (η \ (recordAt H (Set.univ : Set V) ω).queried) = ω
  rw [hq, recordAt_openLabels, hlab]
  simp

/-- **Non-vacuity.**  The two-event inequality, run from the whole vertex set, is Harris'
inequality `P(X) P(Y) ≤ P(X ∩ Y)` for two increasing events. -/
theorem harris_of_treeHK (H : Hypergraph V E) (hinc : ∀ e : E, (H.incidence e).Nonempty)
    {X Y : Set (Set E)} (hX : IsUpperSet X) (hY : IsUpperSet Y) :
    (prodBernoulli H.prob).real X * (prodBernoulli H.prob).real Y
      ≤ (prodBernoulli H.prob).real (X ∩ Y) := by
  have h := real_mul_real_le_integral_ind_mul_cE H (Set.univ : Set V) hX hY
  have hcE : ∀ ω : Set E, CTBase.cE H (Set.univ : Set V) (fun ν => DecisionTree.ind Y ν) ω
      = DecisionTree.ind Y ω := by
    intro ω
    show (∫ η, DecisionTree.ind Y (spliceRecord (recordAt H (Set.univ : Set V) ω) η)
      ∂(prodBernoulli H.prob)) = _
    simp only [spliceRecord_univ H hinc ω]
    simp
  simp only [hcE] at h
  rwa [show (fun ω : Set E => DecisionTree.ind X ω * DecisionTree.ind Y ω)
      = fun ω : Set E => DecisionTree.ind (X ∩ Y) ω from
    funext fun ω => (BHK2006.ind_inter X Y ω).symm,
    CTBase.integral_ind_eq_real] at h


omit [Fintype E] in
/-- At the empty source the exploration queries nothing, so its splice resamples everything. -/
theorem spliceRecord_empty (H : Hypergraph V E) (ω η : Set E) :
    spliceRecord (recordAt H (∅ : Set V) ω) η = η := by
  have hcl : hyperClusterSet H ω (∅ : Set V) = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun _ hy => hy.choose_spec.1
  have hlab : labelsMeeting H (hyperClusterSet H ω (∅ : Set V)) = ∅ := by
    rw [hcl]
    exact Set.eq_empty_iff_forall_notMem.2 fun e he => he (by simp)
  have hq : (recordAt H (∅ : Set V) ω).queried = ∅ := by rw [queried_recordAt, hlab]
  show (recordAt H (∅ : Set V) ω).openLabels ∪
    (η \ (recordAt H (∅ : Set V) ω).queried) = η
  rw [hq, recordAt_openLabels, hlab]
  simp

/-- **The other end of the range.**  At the empty source the conditional probability is the
unconditioned one, so the inequality reads `P(X) P(Y) ≤ P(X) P(Y)`.  With `harris_of_treeHK`,
which is its value at the full source, this locates the statement between the two ends of Harris'
inequality: it is neither the trivial identity nor a restatement of Harris, and the conditional
probability genuinely depends on the source of the exploration. -/
theorem cE_empty_source (H : Hypergraph V E) (Y : Set (Set E)) (ω : Set E) :
    CTBase.cE H (∅ : Set V) (fun ν => DecisionTree.ind Y ν) ω
      = (prodBernoulli H.prob).real Y := by
  show (∫ η, DecisionTree.ind Y (spliceRecord (recordAt H (∅ : Set V) ω) η)
    ∂(prodBernoulli H.prob)) = _
  simp only [spliceRecord_empty H ω]
  exact CTBase.integral_ind_eq_real _ Y

end Instances

end KNAll.Site.TreeHK

end
