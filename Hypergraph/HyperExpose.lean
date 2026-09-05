import Hypergraph.HyperExchange

/-!
# Exposing the labels incident to a set, and the reduced model

The induction behind the hyperedge inequality fixes a set `Z` of vertices, exposes the labels
incident to `Z`, and continues in a smaller model.  The four functions theorem is applied to
quantities indexed by the set of exposed labels found open, so the bookkeeping has to send unions to
unions and intersections to intersections exactly.

`KN/HyperTrace.lean` shows that recording the *vertices* those labels reach does not do this:
`traceOutside_union` is an equality but `traceOutside_inter_subset` is only an inclusion, and
`exists_traceOutside_inter_ssubset` exhibits a hypergraph with one vertex and two labels where the
reverse inclusion fails.  The mechanism is `exists_traceOutside_not_injective`: two distinct labels
can reach the same outside vertices, so the record forgets which labels a set contains.

This module keeps the labels themselves.  The reduced label type is the tagged disjoint union

    reducedLabel H Z = {e // e ∉ labelsMeeting H Z} ⊕ {e // e ∈ labelsMeeting H Z}

of the labels that survive and the labels that were exposed, and every label of the reduced model
carries its own name, so two exposed labels stay distinct even when their incidence sets minus `Z`
coincide.  The contents:

* `originalLabel_injective`, `originalLabel_surjective` — the reduced label type is a relabelling of
  `E`, not an enlargement of it;
* `record_union`, `record_inter` — the record of a set of exposed labels preserves both operations
  **exactly**, the point of the whole construction;
* `record_eq_iff` — and the record is injective on the exposed labels, in contrast with
  `exists_traceOutside_not_injective`;
* `reduceConfig_eq_survivorPart_union_record` — a configuration of the original model splits in the
  reduced model into the surviving open labels and the record of the exposed open labels;
* `openHyperGraph_reducedHyper_survivorPart` — the reduced model on the surviving open labels is,
  as a graph, exactly the original model on the open labels avoiding `Z`;
* `openHyperGraph_reducedHyper_reduceConfig` — the same holds for the full reduced configuration
  once every open exposed label has all its vertices in `Z`, which is what the exploration supplies,
  and `exists_reachable_reducedHyper_of_exposed` shows that hypothesis cannot be dropped;
* `prodBernoulli_map_reduceConfig` — the product measure on the reduced label type is the product
  measure on `E` transported along the relabelling, so probabilities transfer.

## Why the tagging is `survivors ⊕ exposed` and not `E ⊕ exposed`

Tagging the whole of `E` on the left and the exposed labels again on the right would list every
exposed label twice, and under a product measure the two copies would carry independent states.  The
reduced model would then not be a reduction of the original one, and `prodBernoulli_map_reduceConfig`
would be false.  Splitting `E` along `labelsMeeting H Z` keeps the essential feature, that an exposed
label is a *named* object and not its incidence set, while leaving the relabelling
`originalLabel` a bijection.  Both summands carry the incidence set with `Z` removed, as the
exploration requires.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## The reduced label type -/

/-- A label that survives the exposure of `Z`: one whose incidence set misses `Z`. -/
abbrev survivorLabel (H : Hypergraph V E) (Z : Set V) : Type _ :=
  {e : E // e ∉ labelsMeeting H Z}

/-- A label exposed by `Z`: one incident to at least one vertex of `Z`. -/
abbrev exposedLabel (H : Hypergraph V E) (Z : Set V) : Type _ :=
  {e : E // e ∈ labelsMeeting H Z}

/-- The label type of the reduced model: the tagged disjoint union of the labels that survive and
the labels that were exposed.  Each label keeps its own name, so two exposed labels remain distinct
however their incidence sets compare. -/
abbrev reducedLabel (H : Hypergraph V E) (Z : Set V) : Type _ :=
  survivorLabel H Z ⊕ exposedLabel H Z

/-- The label of the original model that a reduced label names. -/
def originalLabel (H : Hypergraph V E) (Z : Set V) : reducedLabel H Z → E :=
  Sum.elim Subtype.val Subtype.val

@[simp] theorem originalLabel_inl (H : Hypergraph V E) (Z : Set V) (e : survivorLabel H Z) :
    originalLabel H Z (Sum.inl e) = (e : E) := rfl

@[simp] theorem originalLabel_inr (H : Hypergraph V E) (Z : Set V) (e : exposedLabel H Z) :
    originalLabel H Z (Sum.inr e) = (e : E) := rfl

/-- **No label is duplicated.**  Two reduced labels naming the same original label are equal: within
a summand because the tag carries the name, across summands because a label cannot both meet `Z` and
miss it. -/
theorem originalLabel_injective (H : Hypergraph V E) (Z : Set V) :
    Function.Injective (originalLabel H Z) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Subtype.ext h)
  · have h' : (a : E) = (b : E) := h
    exact absurd (h' ▸ b.2 : (a : E) ∈ labelsMeeting H Z) a.2
  · have h' : (a : E) = (b : E) := h
    exact absurd (h' ▸ a.2 : (b : E) ∈ labelsMeeting H Z) b.2
  · exact congrArg Sum.inr (Subtype.ext h)

/-- **No label is lost.**  Every label of the original model is named by a reduced label, according
as it misses `Z` or meets it. -/
theorem originalLabel_surjective (H : Hypergraph V E) (Z : Set V) :
    Function.Surjective (originalLabel H Z) := by
  intro e
  by_cases h : e ∈ labelsMeeting H Z
  · exact ⟨Sum.inr ⟨e, h⟩, rfl⟩
  · exact ⟨Sum.inl ⟨e, h⟩, rfl⟩

/-! ## The reduced model -/

/-- The hypergraph on `V` obtained by exposing `Z`: the labels are the reduced labels, and each of
them keeps its incidence set with `Z` removed.  The opening probabilities are inherited from the
label that the reduced label names. -/
def reducedHyper (H : Hypergraph V E) (Z : Set V) : Hypergraph V (reducedLabel H Z) where
  incidence := fun l => H.incidence (originalLabel H Z l) \ Z
  prob := fun l => H.prob (originalLabel H Z l)

@[simp] theorem reducedHyper_incidence (H : Hypergraph V E) (Z : Set V) (l : reducedLabel H Z) :
    (reducedHyper H Z).incidence l = H.incidence (originalLabel H Z l) \ Z := rfl

@[simp] theorem reducedHyper_prob (H : Hypergraph V E) (Z : Set V) (l : reducedLabel H Z) :
    (reducedHyper H Z).prob l = H.prob (originalLabel H Z l) := rfl

/-- An exposed label keeps its incidence set with `Z` removed. -/
theorem reducedHyper_incidence_inr (H : Hypergraph V E) (Z : Set V) (e : exposedLabel H Z) :
    (reducedHyper H Z).incidence (Sum.inr e) = H.incidence (e : E) \ Z := rfl

/-- A surviving label keeps its incidence set unchanged: it misses `Z` already. -/
theorem reducedHyper_incidence_inl (H : Hypergraph V E) (Z : Set V) (e : survivorLabel H Z) :
    (reducedHyper H Z).incidence (Sum.inl e) = H.incidence (e : E) := by
  have hd : Disjoint (H.incidence (e : E)) Z := by
    by_contra hcon
    exact e.2 hcon
  refine Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, fun hz => ?_⟩⟩
  exact Set.disjoint_left.1 hd hx hz

/-! ## The record of the exposed labels

`record H Z I` is the tagged image of `I` in the reduced label type: the right-tagged labels whose
name lies in `I`.  Unlike `traceOutside`, it is a homomorphism of Boolean operations on the nose. -/

/-- The tagged image of a set of labels: the exposed labels of `I`, tagged on the right. -/
def record (H : Hypergraph V E) (Z : Set V) (I : Set E) : Set (reducedLabel H Z) :=
  {l | Sum.elim (fun _ : survivorLabel H Z => False)
        (fun e : exposedLabel H Z => (e : E) ∈ I) l}

@[simp] theorem mem_record_inl (H : Hypergraph V E) (Z : Set V) (I : Set E)
    (e : survivorLabel H Z) : Sum.inl e ∈ record H Z I ↔ False := Iff.rfl

@[simp] theorem mem_record_inr (H : Hypergraph V E) (Z : Set V) (I : Set E)
    (e : exposedLabel H Z) : Sum.inr e ∈ record H Z I ↔ (e : E) ∈ I := Iff.rfl

/-- The record is literally the image of `I` under the right tag, which is why it is exact. -/
theorem record_eq_image (H : Hypergraph V E) (Z : Set V) (I : Set E) :
    record H Z I = Sum.inr '' {e : exposedLabel H Z | (e : E) ∈ I} := by
  ext l
  cases l with
  | inl e => simp
  | inr e => simp

@[simp] theorem record_empty (H : Hypergraph V E) (Z : Set V) :
    record H Z (∅ : Set E) = ∅ := by
  ext l
  cases l with
  | inl e => simp
  | inr e => simp

theorem record_mono (H : Hypergraph V E) (Z : Set V) {I J : Set E} (hIJ : I ⊆ J) :
    record H Z I ⊆ record H Z J := by
  rintro (e | e) hl
  · exact hl
  · exact hIJ hl

/-- **Unions are preserved exactly**, as they already were for `traceOutside`. -/
theorem record_union (H : Hypergraph V E) (Z : Set V) (I J : Set E) :
    record H Z (I ∪ J) = record H Z I ∪ record H Z J := by
  ext l
  cases l with
  | inl e => simp
  | inr e => simp

/-- **Intersections are preserved exactly.**  This is the whole point of the module.  The vertex
record of `KN/HyperTrace.lean` gives only the inclusion `traceOutside_inter_subset`, and
`exists_traceOutside_inter_ssubset` shows the reverse inclusion is false already for a hypergraph
with one vertex and two labels: there the label sets `{true}` and `{false}` are disjoint while each
traces to the whole vertex set.  Keeping the label itself as its own record removes the ambiguity,
because `Sum.inr` is injective, and the equality below holds for arbitrary `I` and `J`. -/
theorem record_inter (H : Hypergraph V E) (Z : Set V) (I J : Set E) :
    record H Z (I ∩ J) = record H Z I ∩ record H Z J := by
  ext l
  cases l with
  | inl e => simp
  | inr e => simp

/-- Differences are preserved exactly as well: the record is a homomorphism for the whole Boolean
structure, not merely for unions. -/
theorem record_diff (H : Hypergraph V E) (Z : Set V) (I J : Set E) :
    record H Z (I \ J) = record H Z I \ record H Z J := by
  ext l
  cases l with
  | inl e => simp
  | inr e => simp

/-- **The record is injective on the exposed labels.**  Two label sets have the same record exactly
when they contain the same exposed labels.  Compare `exists_traceOutside_not_injective`, where two
disjoint label sets have the same vertex trace. -/
theorem record_eq_iff (H : Hypergraph V E) (Z : Set V) (I J : Set E) :
    record H Z I = record H Z J ↔ I ∩ labelsMeeting H Z = J ∩ labelsMeeting H Z := by
  constructor
  · intro h
    ext e
    constructor
    · rintro ⟨heI, heM⟩
      have hmem : Sum.inr (⟨e, heM⟩ : exposedLabel H Z) ∈ record H Z I := heI
      rw [h] at hmem
      exact ⟨hmem, heM⟩
    · rintro ⟨heJ, heM⟩
      have hmem : Sum.inr (⟨e, heM⟩ : exposedLabel H Z) ∈ record H Z J := heJ
      rw [← h] at hmem
      exact ⟨hmem, heM⟩
  · intro h
    ext l
    cases l with
    | inl e => simp
    | inr e =>
        simp only [mem_record_inr]
        constructor
        · intro he
          exact (Set.ext_iff.1 h (e : E)).1 ⟨he, e.2⟩ |>.1
        · intro he
          exact (Set.ext_iff.1 h (e : E)).2 ⟨he, e.2⟩ |>.1

/-- In particular the record determines a set of exposed labels. -/
theorem record_injective_of_exposed (H : Hypergraph V E) (Z : Set V) {I J : Set E}
    (hI : I ⊆ labelsMeeting H Z) (hJ : J ⊆ labelsMeeting H Z)
    (h : record H Z I = record H Z J) : I = J := by
  have hIJ := (record_eq_iff H Z I J).1 h
  rw [Set.inter_eq_self_of_subset_left hI, Set.inter_eq_self_of_subset_left hJ] at hIJ
  exact hIJ

/-! ## Configurations in the reduced model -/

/-- A configuration of the original model, read in the reduced model: a reduced label is open when
the label it names is open. -/
def reduceConfig (H : Hypergraph V E) (Z : Set V) (ω : Set E) : Set (reducedLabel H Z) :=
  restrictSite (originalLabel H Z) ω

@[simp] theorem mem_reduceConfig (H : Hypergraph V E) (Z : Set V) (ω : Set E)
    (l : reducedLabel H Z) : l ∈ reduceConfig H Z ω ↔ originalLabel H Z l ∈ ω := Iff.rfl

theorem measurable_reduceConfig (H : Hypergraph V E) (Z : Set V) :
    Measurable (reduceConfig H Z) := measurable_restrictSite (originalLabel H Z)

/-- The surviving open labels of a configuration, tagged on the left.  This is the part of the
configuration that the exploration carries forward; the exposed part is held in `record`. -/
def survivorPart (H : Hypergraph V E) (Z : Set V) (ω : Set E) : Set (reducedLabel H Z) :=
  {l | Sum.elim (fun e : survivorLabel H Z => (e : E) ∈ ω)
        (fun _ : exposedLabel H Z => False) l}

@[simp] theorem mem_survivorPart_inl (H : Hypergraph V E) (Z : Set V) (ω : Set E)
    (e : survivorLabel H Z) : Sum.inl e ∈ survivorPart H Z ω ↔ (e : E) ∈ ω := Iff.rfl

@[simp] theorem mem_survivorPart_inr (H : Hypergraph V E) (Z : Set V) (ω : Set E)
    (e : exposedLabel H Z) : Sum.inr e ∈ survivorPart H Z ω ↔ False := Iff.rfl

theorem survivorPart_subset_reduceConfig (H : Hypergraph V E) (Z : Set V) (ω : Set E) :
    survivorPart H Z ω ⊆ reduceConfig H Z ω := by
  rintro (e | e) hl
  · exact hl
  · exact hl.elim

/-- **The exploration's bookkeeping, in one line.**  A configuration read in the reduced model is
the disjoint union of the surviving open labels and the record of the exposed open labels. -/
theorem reduceConfig_eq_survivorPart_union_record (H : Hypergraph V E) (Z : Set V) (ω : Set E) :
    reduceConfig H Z ω = survivorPart H Z ω ∪ record H Z ω := by
  ext l
  cases l with
  | inl e => simp
  | inr e => simp

theorem disjoint_survivorPart_record (H : Hypergraph V E) (Z : Set V) (ω : Set E) (I : Set E) :
    Disjoint (survivorPart H Z ω) (record H Z I) := by
  rw [Set.disjoint_left]
  rintro (e | e) hl hr
  · exact hr
  · exact hl

/-- The surviving part is the left summand of the reduced configuration. -/
theorem survivorPart_eq_inter_range (H : Hypergraph V E) (Z : Set V) (ω : Set E) :
    survivorPart H Z ω
      = reduceConfig H Z ω ∩ Set.range (Sum.inl : survivorLabel H Z → reducedLabel H Z) := by
  ext l
  cases l with
  | inl e => simp
  | inr e => simp

/-! ## Connectivity outside `Z`

The reduced model computes the connections of the original model that avoid `Z`.  The statement is
an equality of graphs, so it holds for every pair of vertices; vertices of `Z` are isolated on both
sides, which is why no hypothesis `x ∉ Z` is needed. -/

/-- **The reduced model on the surviving labels is the original model on the labels avoiding `Z`.**
A surviving label misses `Z`, so removing `Z` from its incidence set changes nothing, and the two
adjacency relations have the same witnesses. -/
theorem openHyperGraph_reducedHyper_survivorPart (H : Hypergraph V E) (Z : Set V) (ω : Set E) :
    openHyperGraph (reducedHyper H Z) (survivorPart H Z ω)
      = openHyperGraph H (ω ∩ (labelsMeeting H Z)ᶜ) := by
  ext x y
  rw [openHyperGraph_adj_iff, openHyperGraph_adj_iff]
  constructor
  · rintro ⟨hne, l, hl, hx, hy⟩
    cases l with
    | inl e =>
        rw [reducedHyper_incidence_inl] at hx hy
        exact ⟨hne, (e : E), ⟨hl, e.2⟩, hx, hy⟩
    | inr e => exact hl.elim
  · rintro ⟨hne, e, ⟨heω, heM⟩, hx, hy⟩
    refine ⟨hne, Sum.inl ⟨e, heM⟩, heω, ?_, ?_⟩
    · rw [reducedHyper_incidence_inl]; exact hx
    · rw [reducedHyper_incidence_inl]; exact hy

/-- **Target 3.**  Two vertices are joined in the reduced model by a chain of open labels exactly
when they are joined in `H` by a chain of open labels none of which meets `Z`, provided every open
exposed label has all of its vertices in `Z`.

That proviso is what the exploration supplies: it conditions on the cluster of the source being
exactly `Z`, and `incidence_subset_of_clusterEvent` says that on that event an open label meeting
`Z` lies inside `Z`.  It cannot be dropped, by `exists_reachable_reducedHyper_of_exposed`: an open
exposed label with two vertices outside `Z` joins them in the reduced model while `H` may have no
chain avoiding `Z` between them. -/
theorem openHyperGraph_reducedHyper_reduceConfig (H : Hypergraph V E) (Z : Set V) (ω : Set E)
    (hZ : ∀ e ∈ ω, e ∈ labelsMeeting H Z → H.incidence e ⊆ Z) :
    openHyperGraph (reducedHyper H Z) (reduceConfig H Z ω)
      = openHyperGraph H (ω ∩ (labelsMeeting H Z)ᶜ) := by
  rw [← openHyperGraph_reducedHyper_survivorPart H Z ω]
  ext x y
  rw [openHyperGraph_adj_iff, openHyperGraph_adj_iff]
  constructor
  · rintro ⟨hne, l, hl, hx, hy⟩
    cases l with
    | inl e => exact ⟨hne, Sum.inl e, hl, hx, hy⟩
    | inr e =>
        have hlω : (e : E) ∈ ω := hl
        have hx' : x ∈ H.incidence (e : E) \ Z := hx
        exact absurd (hZ (e : E) hlω e.2 hx'.1) hx'.2
  · rintro ⟨hne, l, hl, hx, hy⟩
    exact ⟨hne, l, survivorPart_subset_reduceConfig H Z ω hl, hx, hy⟩

/-- Reachability form of `openHyperGraph_reducedHyper_survivorPart`. -/
theorem reachable_reducedHyper_survivorPart_iff (H : Hypergraph V E) (Z : Set V) (ω : Set E)
    (x y : V) :
    (openHyperGraph (reducedHyper H Z) (survivorPart H Z ω)).Reachable x y
      ↔ (openHyperGraph H (ω ∩ (labelsMeeting H Z)ᶜ)).Reachable x y := by
  rw [openHyperGraph_reducedHyper_survivorPart]

/-- Reachability form of `openHyperGraph_reducedHyper_reduceConfig`, the statement the induction
step consumes. -/
theorem reachable_reducedHyper_reduceConfig_iff (H : Hypergraph V E) (Z : Set V) (ω : Set E)
    (hZ : ∀ e ∈ ω, e ∈ labelsMeeting H Z → H.incidence e ⊆ Z) (x y : V) :
    (openHyperGraph (reducedHyper H Z) (reduceConfig H Z ω)).Reachable x y
      ↔ (openHyperGraph H (ω ∩ (labelsMeeting H Z)ᶜ)).Reachable x y := by
  rw [openHyperGraph_reducedHyper_reduceConfig H Z ω hZ]

/-- Clusters transfer: the cluster of `S` in the reduced model on the surviving labels is the
cluster of `S` in `H` computed off the labels meeting `Z`. -/
theorem hyperClusterSet_reducedHyper_survivorPart (H : Hypergraph V E) (Z : Set V) (ω : Set E)
    (S : Set V) :
    hyperClusterSet (reducedHyper H Z) (survivorPart H Z ω) S
      = hyperClusterSet H (ω ∩ (labelsMeeting H Z)ᶜ) S := by
  simp only [hyperClusterSet, openHyperGraph_reducedHyper_survivorPart]

/-- The avoiding cluster event of `KN/HyperExchange.lean` is the pull-back of the corresponding
event of the reduced model.  This is the form in which the induction step changes model. -/
theorem clusterEventAvoiding_eq_preimage (H : Hypergraph V E) (Z T L : Set V) :
    clusterEventAvoiding H Z T L
      = reduceConfig H Z ⁻¹'
          {σ : Set (reducedLabel H Z) |
            hyperClusterSet (reducedHyper H Z)
              (σ ∩ Set.range (Sum.inl : survivorLabel H Z → reducedLabel H Z)) T = L} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, ← survivorPart_eq_inter_range,
    hyperClusterSet_reducedHyper_survivorPart]
  rfl

/-! ### The hypothesis of target 3 is necessary

One vertex inside `Z`, two vertices outside it, and a single label incident to all three.  The label
meets `Z`, so it is exposed; in the reduced model it keeps its two outside vertices and joins them,
while in the original model there is no open label avoiding `Z` at all. -/

/-- One label incident to every vertex of `Option Bool`. -/
def crossingHypergraph : Hypergraph (Option Bool) Unit where
  incidence := fun _ => Set.univ
  prob := fun _ => 0

theorem labelsMeeting_crossingHypergraph :
    labelsMeeting crossingHypergraph ({none} : Set (Option Bool)) = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.not_disjoint_iff.2 ⟨none, Set.mem_univ _, rfl⟩

/-- With no open label, reachability is equality. -/
private theorem eq_of_reachable_empty (H : Hypergraph V E) {x y : V}
    (h : (openHyperGraph H (∅ : Set E)).Reachable x y) : x = y := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj p =>
      obtain ⟨-, e, he, -, -⟩ := (openHyperGraph_adj_iff H ∅ _ _).1 hadj
      simp at he

/-- **The proviso of `openHyperGraph_reducedHyper_reduceConfig` cannot be dropped.**  An open
exposed label whose incidence set leaves `Z` creates, in the reduced model, a connection between two
vertices outside `Z` that the original model does not have off `Z`. -/
theorem exists_reachable_reducedHyper_of_exposed :
    ∃ (W L : Type) (H : Hypergraph W L) (Z : Set W) (ω : Set L) (x y : W),
      x ∉ Z ∧ y ∉ Z ∧
      (openHyperGraph (reducedHyper H Z) (reduceConfig H Z ω)).Reachable x y ∧
      ¬ (openHyperGraph H (ω ∩ (labelsMeeting H Z)ᶜ)).Reachable x y := by
  refine ⟨Option Bool, Unit, crossingHypergraph, {none}, Set.univ, some true, some false,
    by simp, by simp, ?_, ?_⟩
  · have hme : () ∈ labelsMeeting crossingHypergraph ({none} : Set (Option Bool)) := by
      rw [labelsMeeting_crossingHypergraph]; exact Set.mem_univ _
    refine SimpleGraph.Adj.reachable ?_
    rw [openHyperGraph_adj_iff]
    refine ⟨by simp, Sum.inr ⟨(), hme⟩, trivial, ⟨Set.mem_univ _, by simp⟩,
      ⟨Set.mem_univ _, by simp⟩⟩
  · intro hr
    have hemp : (Set.univ : Set Unit)
        ∩ (labelsMeeting crossingHypergraph ({none} : Set (Option Bool)))ᶜ = ∅ := by
      rw [labelsMeeting_crossingHypergraph]
      simp
    rw [hemp] at hr
    have hxy := eq_of_reachable_empty crossingHypergraph hr
    simp at hxy

/-! ## The measure of the reduced model

`originalLabel` is injective, so restricting a configuration along it pushes the product measure on
`Set E` forward to the product measure on the reduced label type with the inherited parameters.  The
proof is the one `siteBernoulli_map_restrictSite` gives in `KN/SiteStatements.lean` for site
percolation, written for arbitrary parameters. -/

section Measure

variable {ι κ : Type*}

/-- **The relabelling coupling.**  For injective `f`, restricting a configuration along `f` pushes
the product Bernoulli measure with parameters `p` forward to the product Bernoulli measure with
parameters `p ∘ f`. -/
theorem prodBernoulli_map_restrictSite (p : ι → unitInterval) {f : κ → ι}
    (hf : Function.Injective f) :
    (prodBernoulli p).map (restrictSite f) = prodBernoulli (p ∘ f) := by
  have hSV : Measurable fun q : ι → Prop => {i | q i} := measurable_setOf
  have hSW : Measurable fun q : κ → Prop => {i | q i} := measurable_setOf
  rw [prodBernoulli_eq_map, prodBernoulli_eq_map,
    Measure.map_map (measurable_restrictSite f) hSV]
  have hcomp : (restrictSite (V := ι) f ∘ fun q : ι → Prop => {i | q i}) =
      (fun q : κ → Prop => {i | q i}) ∘ fun (q : ι → Prop) (a : κ) => q (f a) := rfl
  rw [hcomp, ← Measure.map_map hSW (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj hf]
  rfl

end Measure

/-- **Target 4.**  The product measure on the reduced label type is the product measure on `E`
transported along the relabelling: reading a configuration of `H` in the reduced model produces a
sample of the reduced model. -/
theorem prodBernoulli_map_reduceConfig (H : Hypergraph V E) (Z : Set V) :
    (prodBernoulli H.prob).map (reduceConfig H Z) = prodBernoulli (reducedHyper H Z).prob :=
  prodBernoulli_map_restrictSite H.prob (originalLabel_injective H Z)

/-- Probabilities transfer: an event of the reduced model has the same probability there as its
pull-back has in the original model. -/
theorem prodBernoulli_reducedHyper_real (H : Hypergraph V E) (Z : Set V)
    {A : Set (Set (reducedLabel H Z))} (hA : MeasurableSet A) :
    (prodBernoulli (reducedHyper H Z).prob).real A
      = (prodBernoulli H.prob).real (reduceConfig H Z ⁻¹' A) := by
  rw [← prodBernoulli_map_reduceConfig H Z,
    map_measureReal_apply (measurable_reduceConfig H Z) hA]

/-- The avoiding cluster event has the same probability as the corresponding cluster event of the
reduced model.  Targets 3 and 4 together: the identification of the events is
`clusterEventAvoiding_eq_preimage`, the identification of the measures is
`prodBernoulli_map_reduceConfig`. -/
theorem prodBernoulli_clusterEventAvoiding_reduced (H : Hypergraph V E) (Z T L : Set V)
    (hA : MeasurableSet {σ : Set (reducedLabel H Z) |
      hyperClusterSet (reducedHyper H Z)
        (σ ∩ Set.range (Sum.inl : survivorLabel H Z → reducedLabel H Z)) T = L}) :
    (prodBernoulli H.prob).real (clusterEventAvoiding H Z T L)
      = (prodBernoulli (reducedHyper H Z).prob).real
          {σ : Set (reducedLabel H Z) |
            hyperClusterSet (reducedHyper H Z)
              (σ ∩ Set.range (Sum.inl : survivorLabel H Z → reducedLabel H Z)) T = L} := by
  rw [prodBernoulli_reducedHyper_real H Z hA, clusterEventAvoiding_eq_preimage H Z T L]

end KNAll.Site

end
