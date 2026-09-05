import Hypergraph.HyperCore

/-!
# Outside traces, and why the exploration must record labels

The bond exploration exposes the edges incident to a set `Z` and records only which vertices outside
`Z` those edges reach.  For a graph that record is faithful: an edge is a pair of vertices, so the
outside vertices it reaches, together with `Z`, determine the edge.  For a hypergraph the same record
is lossy, because two distinct labels can reach the same outside vertices.

This module measures the loss.  Write `traceOutside H Z I` for the set of vertices outside `Z`
reached by the labels in `I`.  Then

* `traceOutside_mono` — the trace is monotone in the label set;
* `traceOutside_union` — the trace turns unions of label sets into unions of vertex sets, exactly;
* `traceOutside_inter_subset` — for intersections only one inclusion survives;
* `exists_traceOutside_inter_ssubset` — and the other inclusion is false, already for a hypergraph
  with one vertex and two labels;
* `exists_traceOutside_not_injective` — the mechanism behind that failure: distinct label sets can
  have equal traces, so the trace cannot be inverted.

The last two are the reason every later step carries label sets rather than their traces.  A label
set is its own record, so for label sets the intersection is preserved on the nose, and the
exploration keeps the information that `traceOutside` throws away.
-/

noncomputable section

namespace KNAll.Site

variable {V E : Type*}

/-! ## The trace -/

/-- The set of vertices outside `Z` reached by the labels in `I`. -/
def traceOutside (H : Hypergraph V E) (Z : Set V) (I : Set E) : Set V :=
  ⋃ e ∈ I, (H.incidence e \ Z)

/-- Membership in the trace, unfolded: a vertex is traced when some label of `I` is incident to it
and it lies outside `Z`. -/
theorem mem_traceOutside_iff (H : Hypergraph V E) (Z : Set V) (I : Set E) (x : V) :
    x ∈ traceOutside H Z I ↔ ∃ e ∈ I, x ∈ H.incidence e ∧ x ∉ Z := by
  constructor
  · intro hx
    have hx' : x ∈ ⋃ e ∈ I, (H.incidence e \ Z) := hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hx'
    exact ⟨e, he, hxe.1, hxe.2⟩
  · rintro ⟨e, he, hx, hZ⟩
    exact Set.mem_biUnion he (Set.mem_sdiff_of_mem hx hZ)

/-! ## What the trace preserves -/

/-- **The trace is monotone.**  Exposing more labels can only reach more outside vertices. -/
theorem traceOutside_mono (H : Hypergraph V E) (Z : Set V) {I J : Set E} (hIJ : I ⊆ J) :
    traceOutside H Z I ⊆ traceOutside H Z J := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := (mem_traceOutside_iff H Z I x).1 hx
  exact (mem_traceOutside_iff H Z J x).2 ⟨e, hIJ he, hxe⟩

/-- **Unions are preserved exactly.**  A vertex is reached by `I ∪ J` precisely when some single
label of `I`, or some single label of `J`, reaches it. -/
theorem traceOutside_union (H : Hypergraph V E) (Z : Set V) (I J : Set E) :
    traceOutside H Z (I ∪ J) = traceOutside H Z I ∪ traceOutside H Z J := by
  ext x
  simp only [Set.mem_union, mem_traceOutside_iff]
  constructor
  · rintro ⟨e, he | he, hxe⟩
    · exact Or.inl ⟨e, he, hxe⟩
    · exact Or.inr ⟨e, he, hxe⟩
  · rintro (⟨e, he, hxe⟩ | ⟨e, he, hxe⟩)
    · exact ⟨e, Or.inl he, hxe⟩
    · exact ⟨e, Or.inr he, hxe⟩

/-- **Intersections survive only one way.**  A vertex reached by a label common to `I` and `J` is of
course reached by `I` and by `J`.  The converse is the content of
`exists_traceOutside_inter_ssubset`, and it fails. -/
theorem traceOutside_inter_subset (H : Hypergraph V E) (Z : Set V) (I J : Set E) :
    traceOutside H Z (I ∩ J) ⊆ traceOutside H Z I ∩ traceOutside H Z J :=
  Set.subset_inter (traceOutside_mono H Z Set.inter_subset_left)
    (traceOutside_mono H Z Set.inter_subset_right)

/-! ## What the trace destroys

The witness is the smallest hypergraph in which two labels are indistinguishable from outside: one
vertex, two labels, both incident to that vertex, and nothing withheld from the outside.  The two
singleton label sets are disjoint, yet each traces to the whole vertex set.
-/

/-- One vertex and two labels, each incident to that vertex.  The opening probabilities are
irrelevant here, so both are `0`. -/
def twoLabelHypergraph : Hypergraph Unit Bool where
  incidence := fun _ => Set.univ
  prob := fun _ => 0

/-- Both labels of `twoLabelHypergraph` trace, on their own, to the whole vertex set. -/
theorem mem_traceOutside_twoLabelHypergraph (b : Bool) (x : Unit) :
    x ∈ traceOutside twoLabelHypergraph ∅ {b} :=
  (mem_traceOutside_iff twoLabelHypergraph ∅ {b} x).2
    ⟨b, rfl, Set.mem_univ x, by simp⟩

/-- **The reverse inclusion of `traceOutside_inter_subset` is false.**  In `twoLabelHypergraph` with
`Z = ∅`, the label sets `{true}` and `{false}` are disjoint, so the trace of their intersection is
empty, while each of them traces to the whole vertex set.  Hence the outside record of an exposed
label set does not determine which labels the set shares with another, and an exploration that keeps
only traces cannot run the induction behind the gluing inequality. -/
theorem exists_traceOutside_inter_ssubset :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (H : Hypergraph V E) (Z : Set V)
      (I J : Set E),
      ¬ (traceOutside H Z I ∩ traceOutside H Z J ⊆ traceOutside H Z (I ∩ J)) := by
  refine ⟨Unit, Bool, inferInstance, inferInstance, twoLabelHypergraph, ∅, {true}, {false}, ?_⟩
  intro hsub
  have hmem := hsub ⟨mem_traceOutside_twoLabelHypergraph true (),
    mem_traceOutside_twoLabelHypergraph false ()⟩
  obtain ⟨e, he, -⟩ :=
    (mem_traceOutside_iff twoLabelHypergraph ∅ ({true} ∩ {false}) ()).1 hmem
  have h1 : e = true := he.1
  have h2 : e = false := he.2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- **The trace is not injective on label sets.**  This is the mechanism behind
`exists_traceOutside_inter_ssubset`: the two disjoint label sets `{true}` and `{false}` have the same
trace, so no map from traces back to label sets can exist, and any record built from traces alone is
strictly coarser than the record built from labels. -/
theorem exists_traceOutside_not_injective :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (H : Hypergraph V E) (Z : Set V)
      (I J : Set E),
      I ≠ J ∧ traceOutside H Z I = traceOutside H Z J := by
  refine ⟨Unit, Bool, inferInstance, inferInstance, twoLabelHypergraph, ∅, {true}, {false},
    ?_, ?_⟩
  · intro h
    have ht : (true : Bool) ∈ ({true} : Set Bool) := rfl
    rw [h] at ht
    exact Bool.noConfusion (ht : (true : Bool) = false)
  · ext x
    exact ⟨fun _ => mem_traceOutside_twoLabelHypergraph false x,
      fun _ => mem_traceOutside_twoLabelHypergraph true x⟩

end KNAll.Site

end
