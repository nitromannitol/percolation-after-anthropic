import Hypergraph.HyperAvoid
import Hypergraph.HyperTrace

/-!
# The one-cluster inequality with the intersection on the right

`KN/HyperAvoid.lean` proves `avoidIntegral_mul_le`, the case `X ∩ Y = ∅` of van den
Berg–Häggström–Kahn's Theorem 1.1 for the hyperedge model:

  `avoidIntegral X f · avoidIntegral Y g ≤ avoidIntegral ∅ (f · g) · P(avoid (X ∪ Y))`.

The gluing induction needs `X ∩ Y` where that statement has `∅`.  Avoiding a smaller set is easier,
so the proved statement is the weaker one, and this module closes the gap:

* `avoidIntegral_mul_le_inter` — the same inequality with `avoidIntegral (X ∩ Y) (f · g)` on the
  right.

The proof is BHK's, by induction on the vertex set.  Percolation on the model with a vertex set `Z`
deleted is realised inside the fixed configuration space `Set E` with the fixed product weight, by
computing connectivity through the labels lying inside the current vertex set only: `labelsIn`,
`rCluster`, `rAvoid`.  With `Z := X ∩ Y` empty the inequality is `avoidIntegral_mul_le`; otherwise
one conditions on the labels incident to `Z` and applies the Ahlswede–Daykin four functions theorem
together with the induction hypothesis for the model with `Z` deleted.

The record kept of the exposed labels is `rTrace`: the vertices outside `Z` reached by an *open*
label which lies inside the current vertex set and meets `Z`.  `KN/HyperTrace.lean` warns that the
vertex record is strictly coarser than the label record, and that intersections survive it only as
an inclusion (`traceOutside_inter_subset`, `exists_traceOutside_inter_ssubset`).  The induction
below never needs more: the four functions hypothesis is proved by applying the induction
hypothesis with the *larger* avoided sets `(X ∖ Z) ∪ rTrace a` and `(Y ∖ Z) ∪ rTrace b` and then
shrinking them, and shrinking an avoided set only enlarges the avoidance event.  The two inclusions
actually used are `rTrace (a ∩ b) ⊆ rTrace a ∩ rTrace b` and `rTrace (a ∪ b) ⊆ rTrace a ∪ rTrace b`,
and both point the right way.

Two places do need the labels rather than their vertex record, and both are handled by putting the
label condition *inside* the definition of `rTrace`:

* a label of the model on `U` incident to a vertex of `Z` need not be a label of the model on
  `U ∖ Z` even when both of the vertices it joins lie outside `Z`, because a third incident vertex
  may lie in `Z`; the exploration therefore records the vertices outside `Z` of every open label
  meeting `Z`, not only those of the labels joining `Z` to its complement;
* a hyperedge, unlike an edge, is not determined by two of its vertices, so a label reaching a
  vertex of `Z` from outside need not lie inside the current vertex set; `rTrace` records only the
  labels that do.

The finite-sum apparatus is the one built for the graph case in
`Percolation/Literature/ConditionalPositiveAssociationProofs.lean` and is used verbatim:
`BHK2006.weight`, `BHK2006.blockFubini`, the three Harris inequalities, and Mathlib's
`four_functions_theorem_univ`.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006), Thm. 1.1.
* R. Ahlswede, D. E. Daykin, *An inequality for the weights of two families of sets, their unions
  and intersections*, Z. Wahrsch. Verw. Gebiete 43 (1978), 183–185.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Literature.BHK2006 (weight weight_nonneg blockFubini harris harris_mono_anti
  harris_anti_anti sum_ind_mono sum_ind_nonneg ind_le_one ind_inter weight_inter_mul_union)
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V E : Type*}

/-! ## The model restricted to a vertex set

Deleting a set of vertices is realised inside the fixed configuration space by computing
connectivity through the labels all of whose incident vertices survive.
-/

/-- The labels all of whose incident vertices lie in `U`.  These are the labels of the model
induced on `U`. -/
def labelsIn (H : Hypergraph V E) (U : Finset V) : Set E :=
  {e | ∀ v ∈ H.incidence e, v ∈ U}

/-- The cluster of `S` in the model induced on `U`. -/
def rCluster (H : Hypergraph V E) (U : Finset V) (S : Set V) (ω : Set E) : Set V :=
  hyperClusterSet H (ω ∩ labelsIn H U) S

/-- The event that the cluster of `S` in the model induced on `U` avoids `X`. -/
def rAvoid (H : Hypergraph V E) (U : Finset V) (S X : Set V) : Set (Set E) :=
  {ω | ∀ x ∈ X, x ∉ rCluster H U S ω}

/-- The vertices outside `Z` reached by an open label which lies inside `U` and meets `Z`.  This is
BHK's random set `S`; the condition that the label lie inside `U` is part of the definition because
a hyperedge, unlike an edge, is not determined by two of its vertices. -/
def rTrace (H : Hypergraph V E) (U Z : Finset V) (ω : Set E) : Set V :=
  traceOutside H (↑Z) (ω ∩ labelsIn H U ∩ labelsMeeting H (↑Z))

/-! ## Elementary properties -/

@[simp] theorem mem_labelsIn (H : Hypergraph V E) (U : Finset V) (e : E) :
    e ∈ labelsIn H U ↔ ∀ v ∈ H.incidence e, v ∈ U := Iff.rfl

/-- The labels of a larger vertex set are more numerous. -/
theorem labelsIn_mono (H : Hypergraph V E) {U U' : Finset V} (h : U' ⊆ U) :
    labelsIn H U' ⊆ labelsIn H U := fun _ he v hv => h (he v hv)

/-- Over a finite vertex type every label lies inside the whole vertex set. -/
theorem labelsIn_univ [Fintype V] (H : Hypergraph V E) :
    labelsIn H (Finset.univ : Finset V) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ => Finset.mem_univ _

/-- The restricted cluster grows when more labels are opened. -/
theorem rCluster_mono (H : Hypergraph V E) (U : Finset V) (S : Set V) :
    Monotone (rCluster H U S) := fun _ _ h =>
  hyperClusterSet_mono H S (Set.inter_subset_inter_left _ h)

/-- Enlarging the vertex set enlarges the cluster. -/
theorem rCluster_mono_vertex (H : Hypergraph V E) {U U' : Finset V} (h : U' ⊆ U) (S : Set V)
    (ω : Set E) : rCluster H U' S ω ⊆ rCluster H U S ω :=
  hyperClusterSet_mono H S (Set.inter_subset_inter_right _ (labelsIn_mono H h))

/-- The source lies in its own cluster. -/
theorem subset_rCluster (H : Hypergraph V E) (U : Finset V) (S : Set V) (ω : Set E) :
    S ⊆ rCluster H U S ω := subset_hyperClusterSet H _ S

@[simp] theorem mem_rAvoid (H : Hypergraph V E) (U : Finset V) (S X : Set V) (ω : Set E) :
    ω ∈ rAvoid H U S X ↔ ∀ x ∈ X, x ∉ rCluster H U S ω := Iff.rfl

/-- Avoiding a larger set is harder. -/
theorem rAvoid_antitone (H : Hypergraph V E) (U : Finset V) (S : Set V) {X X' : Set V}
    (h : X ⊆ X') : rAvoid H U S X' ⊆ rAvoid H U S X := fun _ hω x hx => hω x (h hx)

/-- Avoidance is a decreasing event. -/
theorem rAvoid_lower (H : Hypergraph V E) (U : Finset V) (S X : Set V) {ω ω' : Set E}
    (h : ω ⊆ ω') (h' : ω' ∈ rAvoid H U S X) : ω ∈ rAvoid H U S X :=
  fun x hx hc => h' x hx (rCluster_mono H U S h hc)

/-- The indicator of the avoidance event is a decreasing function. -/
theorem ind_rAvoid_antitone (H : Hypergraph V E) (U : Finset V) (S X : Set V) :
    Antitone (ind (rAvoid H U S X)) := by
  intro ω ω' h
  by_cases h' : ω' ∈ rAvoid H U S X
  · rw [ind_of_mem h', ind_of_mem (rAvoid_lower H U S X h h')]
  · rw [ind_of_not_mem h']; exact ind_nonneg _ _

/-- Avoiding a union is avoiding each of the two sets. -/
theorem rAvoid_union (H : Hypergraph V E) (U : Finset V) (S X Y : Set V) :
    rAvoid H U S (X ∪ Y) = rAvoid H U S X ∩ rAvoid H U S Y := by
  ext ω
  simp only [rAvoid, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, or_imp, forall_and]

/-- A source vertex that has to be avoided makes the avoidance event empty. -/
theorem rAvoid_eq_empty (H : Hypergraph V E) (U : Finset V) {S X : Set V} {x : V}
    (hxS : x ∈ S) (hxX : x ∈ X) : rAvoid H U S X = ∅ :=
  Set.eq_empty_of_forall_notMem fun ω hω => hω x hxX (subset_rCluster H U S ω hxS)

/-! ## The exposed labels and their vertex record -/

/-- The record of the exposed labels lies outside `Z` and inside `U`. -/
theorem rTrace_subset (H : Hypergraph V E) (U Z : Finset V) (ω : Set E) :
    rTrace H U Z ω ⊆ (↑(U \ Z) : Set V) := by
  intro x hx
  obtain ⟨e, he, hxe, hxZ⟩ := (mem_traceOutside_iff H (↑Z) _ x).1 hx
  refine Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨he.1.2 x hxe, fun hz => hxZ ?_⟩)
  exact Finset.mem_coe.2 hz

/-- The record of an intersection is contained in the intersection of the records. -/
theorem rTrace_inter_subset (H : Hypergraph V E) (U Z : Finset V) (a b : Set E) :
    rTrace H U Z (a ∩ b) ⊆ rTrace H U Z a ∩ rTrace H U Z b := by
  refine Set.subset_inter (traceOutside_mono H _ ?_) (traceOutside_mono H _ ?_) <;>
    rintro e ⟨⟨he, hL⟩, hM⟩
  · exact ⟨⟨he.1, hL⟩, hM⟩
  · exact ⟨⟨he.2, hL⟩, hM⟩

/-- The record of a union is the union of the records. -/
theorem rTrace_union (H : Hypergraph V E) (U Z : Finset V) (a b : Set E) :
    rTrace H U Z (a ∪ b) = rTrace H U Z a ∪ rTrace H U Z b := by
  have hsplit : (a ∪ b) ∩ labelsIn H U ∩ labelsMeeting H (↑Z : Set V)
      = (a ∩ labelsIn H U ∩ labelsMeeting H (↑Z : Set V))
        ∪ (b ∩ labelsIn H U ∩ labelsMeeting H (↑Z : Set V)) := by
    ext e
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  simp only [rTrace, hsplit, traceOutside_union]

/-- The record depends only on the open labels meeting `Z`. -/
theorem rTrace_inter_meeting (H : Hypergraph V E) (U Z : Finset V) (ω : Set E) :
    rTrace H U Z (ω ∩ labelsMeeting H (↑Z : Set V)) = rTrace H U Z ω := by
  have hsplit : (ω ∩ labelsMeeting H (↑Z : Set V)) ∩ labelsIn H U ∩ labelsMeeting H (↑Z : Set V)
      = ω ∩ labelsIn H U ∩ labelsMeeting H (↑Z : Set V) := by
    ext e
    simp only [Set.mem_inter_iff]
    tauto
  simp only [rTrace, hsplit]

/-- A label lying inside `U ∖ Z` does not meet `Z`. -/
theorem notMem_labelsMeeting_of_labelsIn_sdiff (H : Hypergraph V E) (U Z : Finset V) {e : E}
    (he : e ∈ labelsIn H (U \ Z)) : e ∉ labelsMeeting H (↑Z : Set V) := by
  intro hmeet
  obtain ⟨z, hz1, hz2⟩ := Set.not_disjoint_iff.1 hmeet
  exact (Finset.mem_sdiff.1 (he z hz1)).2 (Finset.mem_coe.1 hz2)

/-- Closing the labels that meet `Z` does not change the configuration inside `U ∖ Z`. -/
theorem sdiff_meeting_inter_labelsIn (H : Hypergraph V E) (U Z : Finset V) (ω : Set E) :
    (ω \ labelsMeeting H (↑Z : Set V)) ∩ labelsIn H (U \ Z) = ω ∩ labelsIn H (U \ Z) := by
  ext e
  constructor
  · rintro ⟨⟨hω, -⟩, hU⟩
    exact ⟨hω, hU⟩
  · rintro ⟨hω, hU⟩
    exact ⟨⟨hω, notMem_labelsMeeting_of_labelsIn_sdiff H U Z hU⟩, hU⟩

/-- The cluster in the model on `U ∖ Z` does not depend on the labels meeting `Z`. -/
theorem rCluster_sdiff_meeting (H : Hypergraph V E) (U Z : Finset V) (S : Set V) (ω : Set E) :
    rCluster H (U \ Z) S (ω \ labelsMeeting H (↑Z : Set V)) = rCluster H (U \ Z) S ω := by
  simp only [rCluster, sdiff_meeting_inter_labelsIn]

/-- The avoidance events of the model on `U ∖ Z` do not depend on the labels meeting `Z`. -/
theorem mem_rAvoid_sdiff_meeting (H : Hypergraph V E) (U Z : Finset V) (S T : Set V) (ω : Set E) :
    ω \ labelsMeeting H (↑Z : Set V) ∈ rAvoid H (U \ Z) S T ↔ ω ∈ rAvoid H (U \ Z) S T := by
  simp only [rAvoid, Set.mem_setOf_eq, rCluster_sdiff_meeting]

/-! ## The exploration step -/

/-- **The heart of BHK's identity (6).**  If, in the model on `U ∖ Z`, the cluster of `S` reaches no
vertex of the record `rTrace`, then every vertex of the cluster of `S` in the model on `U` lies
outside `Z` and already lies in the cluster of `S` in the model on `U ∖ Z`.

The step of the walk is where hyperedges differ from edges: the label crossed may be incident to a
vertex of `Z` other than the two it joins, and then it is not a label of the model on `U ∖ Z`.  It
cannot occur, because such a label is exposed and puts the vertex already reached into the record.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem rCluster_restrict_step {H : Hypergraph V E} {U Z : Finset V} {S : Set V}
    (hSZ : ∀ x ∈ S, x ∉ (↑Z : Set V)) {ω : Set E}
    (hS : ∀ n ∈ rTrace H U Z ω, n ∉ rCluster H (U \ Z) S ω) {v : V}
    (hv : v ∈ rCluster H U S ω) :
    v ∉ (↑Z : Set V) ∧ v ∈ rCluster H (U \ Z) S ω := by
  obtain ⟨x, hx, hr⟩ := hv
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => exact ⟨hSZ x hx, mem_hyperClusterSet_self H _ hx⟩
  | tail _ hbc ih =>
    obtain ⟨hbZ, hb⟩ := ih
    rw [openHyperGraph_adj_iff] at hbc
    obtain ⟨hne, e, heω, hbe, hce⟩ := hbc
    have hnotmeet : e ∉ labelsMeeting H (↑Z : Set V) := by
      intro hmeet
      exact hS _ ((mem_traceOutside_iff H (↑Z) _ _).2 ⟨e, ⟨heω, hmeet⟩, hbe, hbZ⟩) hb
    have hdisj : Disjoint (H.incidence e) (↑Z : Set V) := by
      by_contra hcon
      exact hnotmeet hcon
    have heUZ : e ∈ labelsIn H (U \ Z) := fun v hv =>
      Finset.mem_sdiff.2 ⟨heω.2 v hv, fun hvZ =>
        Set.disjoint_left.1 hdisj hv (Finset.mem_coe.2 hvZ)⟩
    refine ⟨fun hcZ => Set.disjoint_left.1 hdisj hce hcZ,
      hyperClusterSet_mem_of_adj H _ S hb ?_⟩
    rw [openHyperGraph_adj_iff]
    exact ⟨hne, e, ⟨heω.1, heUZ⟩, hbe, hce⟩

/-- On the event of `rCluster_restrict_step`, the cluster of `S` in the model on `U` is its cluster
in the model on `U ∖ Z`. [cite: VandenbergHaggstromKahn2005, §1 p. 4] -/
theorem rCluster_restrict {H : Hypergraph V E} {U Z : Finset V} {S : Set V}
    (hSZ : ∀ x ∈ S, x ∉ (↑Z : Set V)) {ω : Set E}
    (hS : ∀ n ∈ rTrace H U Z ω, n ∉ rCluster H (U \ Z) S ω) :
    rCluster H U S ω = rCluster H (U \ Z) S ω :=
  Set.Subset.antisymm (fun _ hv => (rCluster_restrict_step hSZ hS hv).2)
    (rCluster_mono_vertex H Finset.sdiff_subset S ω)

/-- **BHK's identity (6)**, pointwise: for `Z ⊆ W`, the event that the cluster of `S` in the model
on `U` avoids `W` is the event that its cluster in the model on `U ∖ Z` avoids
`(W ∖ Z) ∪ rTrace ω`. [cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem mem_rAvoid_iff_restrict {H : Hypergraph V E} {U Z : Finset V} {S : Set V}
    (hSZ : ∀ x ∈ S, x ∉ (↑Z : Set V)) {W : Set V} (hZW : (↑Z : Set V) ⊆ W) (ω : Set E) :
    ω ∈ rAvoid H U S W ↔ ω ∈ rAvoid H (U \ Z) S ((W \ ↑Z) ∪ rTrace H U Z ω) := by
  constructor
  · intro h x hx hmem
    have hmem' : x ∈ rCluster H U S ω :=
      rCluster_mono_vertex H Finset.sdiff_subset S ω hmem
    rcases hx with ⟨hxW, -⟩ | hxT
    · exact h x hxW hmem'
    · obtain ⟨e, ⟨heω, hmeet⟩, hxe, hxZ⟩ := (mem_traceOutside_iff H (↑Z) _ x).1 hxT
      obtain ⟨z, hz1, hz2⟩ := Set.not_disjoint_iff.1 hmeet
      refine h z (hZW hz2) (hyperClusterSet_mem_of_adj H _ S hmem' ?_)
      rw [openHyperGraph_adj_iff]
      refine ⟨fun hxz => hxZ ?_, e, heω, hxe, hz1⟩
      rw [hxz]
      exact hz2
  · intro h x hxW hmem
    have hS : ∀ n ∈ rTrace H U Z ω, n ∉ rCluster H (U \ Z) S ω := fun n hn => h n (Or.inr hn)
    obtain ⟨hxZ, hmem'⟩ := rCluster_restrict_step hSZ hS hmem
    exact h x (Or.inl ⟨hxW, hxZ⟩) hmem'

/-! ## Conditioning on the exposed labels -/

section Reduced

variable [Fintype E]

/-- The block expectation `T ↦ E[F(cluster on U) · 1{cluster avoids B ∪ T}]`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4] -/
def blockAvoidE (w : E → ℝ) (H : Hypergraph V E) (U : Finset V) (S : Set V)
    (F : Set V → ℝ) (B T : Set V) : ℝ :=
  ∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * ind (rAvoid H U S (B ∪ T)) ω)

/-- Block expectations of nonnegative integrands are nonnegative. -/
theorem blockAvoidE_nonneg {w : E → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (H : Hypergraph V E) (U : Finset V) (S : Set V) {F : Set V → ℝ} (hF : ∀ K, 0 ≤ F K)
    (B T : Set V) : 0 ≤ blockAvoidE w H U S F B T :=
  sum_ind_nonneg hw0 hw1 (fun _ => hF _) _

/-- **BHK's (6), summed**: conditioning on the open labels that meet `Z` writes the avoidance
expectation on `U` as the expectation, over those labels, of the avoidance expectation on `U ∖ Z`
with the record of the exposed labels added to the avoided set.
[cite: VandenbergHaggstromKahn2005, §1 p. 4] -/
theorem avoid_step_sum {H : Hypergraph V E} {U Z : Finset V} {S : Set V}
    (hSZ : ∀ x ∈ S, x ∉ (↑Z : Set V)) {W : Set V} (hZW : (↑Z : Set V) ⊆ W)
    (w : E → ℝ) (hm : ∑ ω : Set E, weight w ω = 1) (F : Set V → ℝ) :
    ∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * ind (rAvoid H U S W) ω) =
      ∑ ω : Set E, weight w ω * blockAvoidE w H (U \ Z) S F (W \ ↑Z) (rTrace H U Z ω) := by
  set A := labelsMeeting H (↑Z : Set V) with hA
  set Φ : Set E → Set E → ℝ := fun ζ η =>
    F (rCluster H (U \ Z) S η) *
      ind (rAvoid H (U \ Z) S ((W \ ↑Z) ∪ rTrace H U Z ζ)) η with hΦ
  have h1 : ∀ ω : Set E,
      F (rCluster H U S ω) * ind (rAvoid H U S W) ω = Φ (ω ∩ A) (ω \ A) := by
    intro ω
    simp only [hΦ, hA, rTrace_inter_meeting, rCluster_sdiff_meeting]
    by_cases hω : ω ∈ rAvoid H U S W
    · have hω' := (mem_rAvoid_iff_restrict hSZ hZW ω).1 hω
      rw [ind_of_mem hω, ind_of_mem ((mem_rAvoid_sdiff_meeting H U Z S _ ω).2 hω'),
        rCluster_restrict hSZ fun n hn => hω' n (Or.inr hn)]
    · have hω' : ω \ labelsMeeting H (↑Z : Set V)
          ∉ rAvoid H (U \ Z) S ((W \ ↑Z) ∪ rTrace H U Z ω) := fun h =>
        hω ((mem_rAvoid_iff_restrict hSZ hZW ω).2
          ((mem_rAvoid_sdiff_meeting H U Z S _ ω).1 h))
      rw [ind_of_not_mem hω, ind_of_not_mem hω', mul_zero, mul_zero]
  have h2 : ∀ ω ω' : Set E, Φ (ω ∩ A) (ω' \ A) =
      F (rCluster H (U \ Z) S ω') *
        ind (rAvoid H (U \ Z) S ((W \ ↑Z) ∪ rTrace H U Z ω)) ω' := by
    intro ω ω'
    simp only [hΦ, hA, rTrace_inter_meeting, rCluster_sdiff_meeting]
    by_cases hω' : ω' ∈ rAvoid H (U \ Z) S ((W \ ↑Z) ∪ rTrace H U Z ω)
    · rw [ind_of_mem hω', ind_of_mem ((mem_rAvoid_sdiff_meeting H U Z S _ ω').2 hω')]
    · rw [ind_of_not_mem hω',
        ind_of_not_mem fun h => hω' ((mem_rAvoid_sdiff_meeting H U Z S _ ω').1 h)]
  calc ∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * ind (rAvoid H U S W) ω)
      = (∑ ω : Set E, weight w ω) * ∑ ω : Set E, weight w ω * Φ (ω ∩ A) (ω \ A) := by
        rw [hm, one_mul]; simp_rw [h1]
    _ = ∑ ω : Set E, weight w ω * ∑ ω' : Set E, weight w ω' * Φ (ω ∩ A) (ω' \ A) :=
        blockFubini w A Φ
    _ = ∑ ω : Set E, weight w ω * blockAvoidE w H (U \ Z) S F (W \ ↑Z) (rTrace H U Z ω) := by
        simp_rw [h2]; rfl

/-! ## The induction -/

/-- **BHK's Theorem 1.1 for the hyperedge model**, in functional form, for the model induced on the
vertex set `U`: for increasing nonnegative `F` and `G`,

  `E[F(C) 1{C avoids X}] · E[G(C) 1{C avoids Y}]
     ≤ E[F(C) G(C) 1{C avoids X ∩ Y}] · P(C avoids X ∪ Y)`.

Induction on `U`.  With `X ∩ Y = ∅` the inequality is four applications of Harris' inequality;
otherwise the labels incident to `Z := X ∩ Y` are exposed, `avoid_step_sum` rewrites all four sums
as expectations over those labels, and the four functions theorem reduces the inequality to the
induction hypothesis for `U ∖ Z`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5)] -/
theorem avoidCore (H : Hypergraph V E) (w : E → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω : Set E, weight w ω = 1) (U : Finset V) :
    ∀ S X Y : Set V, X ⊆ (↑U : Set V) → Y ⊆ (↑U : Set V) →
    ∀ F G : Set V → ℝ, Monotone F → Monotone G → (∀ K, 0 ≤ F K) → (∀ K, 0 ≤ G K) →
    (∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * ind (rAvoid H U S X) ω)) *
        (∑ ω : Set E, weight w ω * (G (rCluster H U S ω) * ind (rAvoid H U S Y) ω)) ≤
      (∑ ω : Set E, weight w ω *
          (F (rCluster H U S ω) * G (rCluster H U S ω) * ind (rAvoid H U S (X ∩ Y)) ω)) *
        (∑ ω : Set E, weight w ω * ind (rAvoid H U S (X ∪ Y)) ω) := by
  induction U using Finset.strongInduction with
  | H U ih =>
  intro S X Y hXU hYU F G hF hG hF0 hG0
  have hRHS : 0 ≤ (∑ ω : Set E, weight w ω *
      (F (rCluster H U S ω) * G (rCluster H U S ω) * ind (rAvoid H U S (X ∩ Y)) ω)) *
      (∑ ω : Set E, weight w ω * ind (rAvoid H U S (X ∪ Y)) ω) :=
    mul_nonneg
      (Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω)
        (mul_nonneg (mul_nonneg (hF0 _) (hG0 _)) (ind_nonneg _ _)))
      (Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _))
  -- the trivial cases in which the source itself has to be avoided
  by_cases hsX : ∃ x ∈ S, x ∈ X
  · obtain ⟨x, hxS, hxX⟩ := hsX
    have h0 : ∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * ind (rAvoid H U S X) ω) = 0 :=
      Finset.sum_eq_zero fun ω _ => by
        rw [rAvoid_eq_empty H U hxS hxX, ind_of_not_mem (Set.notMem_empty ω)]; ring
    rw [h0, zero_mul]
    exact hRHS
  by_cases hsY : ∃ x ∈ S, x ∈ Y
  · obtain ⟨x, hxS, hxY⟩ := hsY
    have h0 : ∑ ω : Set E, weight w ω * (G (rCluster H U S ω) * ind (rAvoid H U S Y) ω) = 0 :=
      Finset.sum_eq_zero fun ω _ => by
        rw [rAvoid_eq_empty H U hxS hxY, ind_of_not_mem (Set.notMem_empty ω)]; ring
    rw [h0, mul_zero]
    exact hRHS
  replace hsX : ∀ x ∈ S, x ∉ X := fun x hxS hxX => hsX ⟨x, hxS, hxX⟩
  -- `Z := X ∩ Y`
  set Z : Finset V := U.filter fun v => v ∈ X ∧ v ∈ Y with hZ
  have hZU : Z ⊆ U := Finset.filter_subset _ _
  have hmemZ : ∀ v, v ∈ Z ↔ v ∈ X ∧ v ∈ Y := fun v => by
    simp only [hZ, Finset.mem_filter, and_iff_right_iff_imp]
    exact fun h => hXU h.1
  have hSZ : ∀ x ∈ S, x ∉ (↑Z : Set V) := fun x hx hxZ =>
    hsX x hx ((hmemZ x).1 (Finset.mem_coe.1 hxZ)).1
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · /- `X ∩ Y = ∅`: four applications of Harris' inequality (BHK display (4)). -/
    have hXY : ∀ ω : Set E, ind (rAvoid H U S (X ∩ Y)) ω = 1 := fun ω =>
      ind_of_mem fun x hx => by
        have hxZ : x ∈ Z := (hmemZ x).2 hx
        rw [hZe] at hxZ
        exact absurd hxZ (Finset.notMem_empty x)
    have hXuY : ∀ ω : Set E, ind (rAvoid H U S (X ∪ Y)) ω
        = ind (rAvoid H U S X) ω * ind (rAvoid H U S Y) ω := fun ω => by
      rw [rAvoid_union, ind_inter]
    simp_rw [hXY, mul_one, hXuY]
    have hFm : Monotone fun ω : Set E => F (rCluster H U S ω) :=
      fun _ _ hab => hF (rCluster_mono H U S hab)
    have hGm : Monotone fun ω : Set E => G (rCluster H U S ω) :=
      fun _ _ hab => hG (rCluster_mono H U S hab)
    have h1 : ∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * ind (rAvoid H U S X) ω) ≤
        (∑ ω : Set E, weight w ω * F (rCluster H U S ω)) *
          ∑ ω : Set E, weight w ω * ind (rAvoid H U S X) ω :=
      harris_mono_anti hw0 hw1 hm (fun _ => hF0 _) hFm
        (ind_rAvoid_antitone H U S X) (fun _ => ind_le_one _ _)
    have h2 : ∑ ω : Set E, weight w ω * (G (rCluster H U S ω) * ind (rAvoid H U S Y) ω) ≤
        (∑ ω : Set E, weight w ω * G (rCluster H U S ω)) *
          ∑ ω : Set E, weight w ω * ind (rAvoid H U S Y) ω :=
      harris_mono_anti hw0 hw1 hm (fun _ => hG0 _) hGm
        (ind_rAvoid_antitone H U S Y) (fun _ => ind_le_one _ _)
    have h3 : (∑ ω : Set E, weight w ω * F (rCluster H U S ω)) *
        (∑ ω : Set E, weight w ω * G (rCluster H U S ω)) ≤
        ∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * G (rCluster H U S ω)) := by
      have hh := harris hw0 hw1 (fun _ => hF0 _) (fun _ => hG0 _) hFm hGm
      rwa [hm, one_mul] at hh
    have h4 : (∑ ω : Set E, weight w ω * ind (rAvoid H U S X) ω) *
        (∑ ω : Set E, weight w ω * ind (rAvoid H U S Y) ω) ≤
        ∑ ω : Set E, weight w ω * (ind (rAvoid H U S X) ω * ind (rAvoid H U S Y) ω) :=
      harris_anti_anti hw0 hw1 hm (ind_rAvoid_antitone H U S X) (ind_rAvoid_antitone H U S Y)
        (fun _ => ind_le_one _ _) (fun _ => ind_le_one _ _)
    have hFn : 0 ≤ ∑ ω : Set E, weight w ω * F (rCluster H U S ω) :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (hF0 _)
    have hGn : 0 ≤ ∑ ω : Set E, weight w ω * G (rCluster H U S ω) :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (hG0 _)
    have hXn : 0 ≤ ∑ ω : Set E, weight w ω * ind (rAvoid H U S X) ω :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)
    have hYn : 0 ≤ ∑ ω : Set E, weight w ω * ind (rAvoid H U S Y) ω :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)
    calc (∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * ind (rAvoid H U S X) ω)) *
          (∑ ω : Set E, weight w ω * (G (rCluster H U S ω) * ind (rAvoid H U S Y) ω))
        ≤ ((∑ ω : Set E, weight w ω * F (rCluster H U S ω)) *
              ∑ ω : Set E, weight w ω * ind (rAvoid H U S X) ω) *
            ((∑ ω : Set E, weight w ω * G (rCluster H U S ω)) *
              ∑ ω : Set E, weight w ω * ind (rAvoid H U S Y) ω) :=
          mul_le_mul h1 h2 (sum_ind_nonneg hw0 hw1 (fun _ => hG0 _) _) (mul_nonneg hFn hXn)
      _ = ((∑ ω : Set E, weight w ω * F (rCluster H U S ω)) *
              ∑ ω : Set E, weight w ω * G (rCluster H U S ω)) *
            ((∑ ω : Set E, weight w ω * ind (rAvoid H U S X) ω) *
              ∑ ω : Set E, weight w ω * ind (rAvoid H U S Y) ω) := by ring
      _ ≤ (∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * G (rCluster H U S ω))) *
            ∑ ω : Set E, weight w ω * (ind (rAvoid H U S X) ω * ind (rAvoid H U S Y) ω) :=
          mul_le_mul h3 h4 (mul_nonneg hXn hYn)
            (Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω)
              (mul_nonneg (hF0 _) (hG0 _)))
  · /- `X ∩ Y ≠ ∅`: expose the labels incident to `Z` and apply the four functions theorem with the
    induction hypothesis for `U ∖ Z` (BHK pp. 4–5). -/
    have hss : U \ Z ⊂ U := Finset.sdiff_ssubset hZU hZne
    have hZX : (↑Z : Set V) ⊆ X := fun v hv => ((hmemZ v).1 (Finset.mem_coe.1 hv)).1
    have hZY : (↑Z : Set V) ⊆ Y := fun v hv => ((hmemZ v).1 (Finset.mem_coe.1 hv)).2
    have hZXY : (↑Z : Set V) ⊆ X ∩ Y := fun v hv => (hmemZ v).1 (Finset.mem_coe.1 hv)
    have hZXuY : (↑Z : Set V) ⊆ X ∪ Y := fun v hv =>
      Or.inl ((hmemZ v).1 (Finset.mem_coe.1 hv)).1
    have hFG : Monotone fun K => F K * G K := fun a b hab =>
      mul_le_mul (hF hab) (hG hab) (hG0 _) (hF0 _)
    have e1 := avoid_step_sum hSZ hZX w hm F (H := H) (U := U)
    have e2 := avoid_step_sum hSZ hZY w hm G (H := H) (U := U)
    have e3 : ∑ ω : Set E, weight w ω * (F (rCluster H U S ω) * G (rCluster H U S ω) *
          ind (rAvoid H U S (X ∩ Y)) ω) =
        ∑ ω : Set E, weight w ω *
          blockAvoidE w H (U \ Z) S (fun K => F K * G K) ((X ∩ Y) \ ↑Z) (rTrace H U Z ω) :=
      avoid_step_sum hSZ hZXY w hm (fun K => F K * G K) (H := H) (U := U)
    have e4 : ∑ ω : Set E, weight w ω * ind (rAvoid H U S (X ∪ Y)) ω =
        ∑ ω : Set E, weight w ω *
          blockAvoidE w H (U \ Z) S (fun _ => 1) ((X ∪ Y) \ ↑Z) (rTrace H U Z ω) := by
      have hh := avoid_step_sum hSZ hZXuY w hm (fun _ => (1 : ℝ)) (H := H) (U := U)
      simpa only [one_mul] using hh
    rw [e1, e2, e3, e4]
    refine four_functions_theorem_univ
      (fun ω => weight w ω * blockAvoidE w H (U \ Z) S F (X \ ↑Z) (rTrace H U Z ω))
      (fun ω => weight w ω * blockAvoidE w H (U \ Z) S G (Y \ ↑Z) (rTrace H U Z ω))
      (fun ω => weight w ω *
        blockAvoidE w H (U \ Z) S (fun K => F K * G K) ((X ∩ Y) \ ↑Z) (rTrace H U Z ω))
      (fun ω => weight w ω *
        blockAvoidE w H (U \ Z) S (fun _ => 1) ((X ∪ Y) \ ↑Z) (rTrace H U Z ω))
      (fun ω => mul_nonneg (weight_nonneg hw0 hw1 ω)
        (blockAvoidE_nonneg hw0 hw1 H _ _ hF0 _ _))
      (fun ω => mul_nonneg (weight_nonneg hw0 hw1 ω)
        (blockAvoidE_nonneg hw0 hw1 H _ _ hG0 _ _))
      (fun ω => mul_nonneg (weight_nonneg hw0 hw1 ω)
        (blockAvoidE_nonneg hw0 hw1 H _ _ (fun K => mul_nonneg (hF0 K) (hG0 K)) _ _))
      (fun ω => mul_nonneg (weight_nonneg hw0 hw1 ω)
        (blockAvoidE_nonneg hw0 hw1 H _ _ (fun _ => zero_le_one) _ _))
      fun a b => ?_
    -- the Ahlswede–Daykin hypothesis: the weight lattice identity times the induction hypothesis
    set Ta := rTrace H U Z a with hTa
    set Tb := rTrace H U Z b with hTb
    have hX1 : X \ ↑Z ∪ Ta ⊆ (↑(U \ Z) : Set V) := Set.union_subset
      (fun v hv => by
        rw [Finset.coe_sdiff]
        exact ⟨hXU hv.1, hv.2⟩)
      (rTrace_subset H U Z a)
    have hY1 : Y \ ↑Z ∪ Tb ⊆ (↑(U \ Z) : Set V) := Set.union_subset
      (fun v hv => by
        rw [Finset.coe_sdiff]
        exact ⟨hYU hv.1, hv.2⟩)
      (rTrace_subset H U Z b)
    have IH := ih (U \ Z) hss S (X \ ↑Z ∪ Ta) (Y \ ↑Z ∪ Tb) hX1 hY1 F G hF hG hF0 hG0
    have hsub3 : (X ∩ Y) \ ↑Z ∪ rTrace H U Z (a ∩ b)
        ⊆ (X \ ↑Z ∪ Ta) ∩ (Y \ ↑Z ∪ Tb) := by
      refine Set.union_subset (fun v hv => ⟨Or.inl ⟨hv.1.1, hv.2⟩, Or.inl ⟨hv.1.2, hv.2⟩⟩) ?_
      intro v hv
      exact ⟨Or.inr (rTrace_inter_subset H U Z a b hv).1,
        Or.inr (rTrace_inter_subset H U Z a b hv).2⟩
    have hsub4 : (X ∪ Y) \ ↑Z ∪ rTrace H U Z (a ∪ b)
        ⊆ (X \ ↑Z ∪ Ta) ∪ (Y \ ↑Z ∪ Tb) := by
      rw [rTrace_union]
      rintro v (⟨hXY | hXY, hvZ⟩ | hT | hT)
      · exact Or.inl (Or.inl ⟨hXY, hvZ⟩)
      · exact Or.inr (Or.inl ⟨hXY, hvZ⟩)
      · exact Or.inl (Or.inr hT)
      · exact Or.inr (Or.inr hT)
    have h3 : ∑ ω : Set E, weight w ω * (F (rCluster H (U \ Z) S ω) * G (rCluster H (U \ Z) S ω) *
        ind (rAvoid H (U \ Z) S ((X \ ↑Z ∪ Ta) ∩ (Y \ ↑Z ∪ Tb))) ω) ≤
        blockAvoidE w H (U \ Z) S (fun K => F K * G K) ((X ∩ Y) \ ↑Z)
          (rTrace H U Z (a ∩ b)) :=
      sum_ind_mono hw0 hw1 (fun _ => mul_nonneg (hF0 _) (hG0 _)) (rAvoid_antitone H _ S hsub3)
    have h4 : ∑ ω : Set E, weight w ω *
        ind (rAvoid H (U \ Z) S ((X \ ↑Z ∪ Ta) ∪ (Y \ ↑Z ∪ Tb))) ω ≤
        blockAvoidE w H (U \ Z) S (fun _ => 1) ((X ∪ Y) \ ↑Z) (rTrace H U Z (a ∪ b)) := by
      have hh := sum_ind_mono (w := w) hw0 hw1 (h := fun _ : Set E => (1 : ℝ))
        (fun _ => zero_le_one) (rAvoid_antitone H (U \ Z) S hsub4)
      simp only [one_mul] at hh
      simpa only [blockAvoidE, one_mul] using hh
    have hIH' : blockAvoidE w H (U \ Z) S F (X \ ↑Z) Ta *
        blockAvoidE w H (U \ Z) S G (Y \ ↑Z) Tb ≤
        blockAvoidE w H (U \ Z) S (fun K => F K * G K) ((X ∩ Y) \ ↑Z) (rTrace H U Z (a ∩ b)) *
          blockAvoidE w H (U \ Z) S (fun _ => 1) ((X ∪ Y) \ ↑Z) (rTrace H U Z (a ∪ b)) :=
      IH.trans (mul_le_mul h3 h4
        (Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _))
        (blockAvoidE_nonneg hw0 hw1 H _ _ (fun K => mul_nonneg (hF0 K) (hG0 K)) _ _))
    have hwab := weight_inter_mul_union w a b
    show weight w a * blockAvoidE w H (U \ Z) S F (X \ ↑Z) Ta *
        (weight w b * blockAvoidE w H (U \ Z) S G (Y \ ↑Z) Tb) ≤
      weight w (a ∩ b) *
          blockAvoidE w H (U \ Z) S (fun K => F K * G K) ((X ∩ Y) \ ↑Z)
            (rTrace H U Z (a ∩ b)) *
        (weight w (a ∪ b) *
          blockAvoidE w H (U \ Z) S (fun _ => 1) ((X ∪ Y) \ ↑Z) (rTrace H U Z (a ∪ b)))
    calc weight w a * blockAvoidE w H (U \ Z) S F (X \ ↑Z) Ta *
          (weight w b * blockAvoidE w H (U \ Z) S G (Y \ ↑Z) Tb)
        = (weight w a * weight w b) *
            (blockAvoidE w H (U \ Z) S F (X \ ↑Z) Ta *
              blockAvoidE w H (U \ Z) S G (Y \ ↑Z) Tb) := by ring
      _ ≤ (weight w (a ∩ b) * weight w (a ∪ b)) *
            (blockAvoidE w H (U \ Z) S (fun K => F K * G K) ((X ∩ Y) \ ↑Z)
                (rTrace H U Z (a ∩ b)) *
              blockAvoidE w H (U \ Z) S (fun _ => 1) ((X ∪ Y) \ ↑Z)
                (rTrace H U Z (a ∪ b))) := by
          rw [hwab]
          exact mul_le_mul_of_nonneg_left hIH'
            (mul_nonneg (weight_nonneg hw0 hw1 _) (weight_nonneg hw0 hw1 _))
      _ = _ := by ring

end Reduced

/-! ## The target -/

/-- The cluster of the model induced on the whole vertex set is the cluster. -/
theorem rCluster_univ [Fintype V] (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    rCluster H (Finset.univ : Finset V) S ω = hyperClusterSet H ω S := by
  simp only [rCluster, labelsIn_univ, Set.inter_univ]

/-- The avoidance event of the model induced on the whole vertex set is the avoidance event. -/
theorem rAvoid_univ [Fintype V] (H : Hypergraph V E) (S X : Set V) :
    rAvoid H (Finset.univ : Finset V) S X = avoidEvent H S X := by
  ext ω
  show (∀ x ∈ X, x ∉ rCluster H (Finset.univ : Finset V) S ω) ↔
    Disjoint (hyperClusterSet H ω S) X
  rw [Set.disjoint_right]
  simp only [rCluster_univ]

/-- **The one-cluster inequality with the intersection on the right.**  For increasing nonnegative
`f` and `g`,

  `avoidIntegral X f · avoidIntegral Y g
     ≤ avoidIntegral (X ∩ Y) (f · g) · P(avoidEvent (X ∪ Y))`.

This is van den Berg–Häggström–Kahn's Theorem 1.1 for the hyperedge model.  It strengthens
`avoidIntegral_mul_le`, which carries `∅` where this carries `X ∩ Y`: avoiding a smaller set is
easier, so `avoidIntegral (X ∩ Y) (f · g) ≤ avoidIntegral ∅ (f · g)`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5)] -/
theorem avoidIntegral_mul_le_inter [Fintype V] [Fintype E] (H : Hypergraph V E) (S X Y : Set V)
    {f g : Set V → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) :
    avoidIntegral H S X f * avoidIntegral H S Y g
      ≤ avoidIntegral H S (X ∩ Y) (fun K => f K * g K) *
          (prodBernoulli H.prob).real (avoidEvent H S (X ∪ Y)) := by
  have hXU : X ⊆ (↑(Finset.univ : Finset V) : Set V) := by
    rw [Finset.coe_univ]; exact Set.subset_univ X
  have hYU : Y ⊆ (↑(Finset.univ : Finset V) : Set V) := by
    rw [Finset.coe_univ]; exact Set.subset_univ Y
  have key := avoidCore H (fun e => (H.prob e : ℝ)) (fun e => unitInterval.nonneg (H.prob e))
    (fun e => unitInterval.le_one (H.prob e)) (sum_weight_eq_one H.prob) Finset.univ
    S X Y hXU hYU f g hf hg hf0 hg0
  simp only [rCluster_univ, rAvoid_univ] at key
  rw [avoidIntegral_eq_sum H S X f, avoidIntegral_eq_sum H S Y g,
    avoidIntegral_eq_sum H S (X ∩ Y) (fun K => f K * g K),
    prodBernoulli_real_eq_sum H.prob (avoidEvent H S (X ∪ Y))]
  exact key

end KNAll.Site

end
