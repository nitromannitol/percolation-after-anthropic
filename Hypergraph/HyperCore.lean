import Hypergraph.SiteStatements
import Percolation.Literature.PercolationEvents
import Percolation.Literature.LatticeModels.ProdBernoulliIndependence
import Percolation.Literature.LatticeModels.ProdBernoulliClusterLocality

/-!
# The finite hypergraph layer

Phase 1 of the site percolation formalization.  The measure layer of the development is already
stated for an arbitrary index type, so nothing is needed there: labels are just another index.  What
has to be built is the connectivity layer, which in the bond development is hard-wired to `Sym2 V`.

The results here are the ones every later step uses:

* `determinedBy_clusterEvent` — the event that the cluster of `S` is exactly `K` depends only on the
  labels that meet `K`;
* `incidence_subset_of_clusterEvent` — on that event, an open label meeting `K` lies inside `K`;
* `measurableSet_clusterEvent` — the event is measurable;
* `clusterFactorization` — it is independent of every event determined by the labels avoiding `K`;
* `prodBernoulli_deleteHyper_real_eq` — closing the labels that meet `K` does not change the
  probability of an event determined by the labels avoiding `K`.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## Definitions -/

/-- The labels incident to at least one vertex of `K`. -/
def labelsMeeting (H : Hypergraph V E) (K : Set V) : Set E :=
  {e | ¬ Disjoint (H.incidence e) K}

open Classical in
/-- The hypergraph with every label meeting `K` closed.  The incidence structure, hence the open
graph, is unchanged; only the parameters move. -/
def deleteHyper (H : Hypergraph V E) (K : Set V) : Hypergraph V E where
  incidence := H.incidence
  prob := fun e => if e ∈ labelsMeeting H K then 0 else H.prob e

/-- The set of vertices joined to `S` by a chain of open labels. -/
def hyperClusterSet (H : Hypergraph V E) (ω : Set E) (S : Set V) : Set V :=
  {y | ∃ x ∈ S, (openHyperGraph H ω).Reachable x y}

/-- The event that the cluster of `S` is exactly `K`. -/
def clusterEvent (H : Hypergraph V E) (S K : Set V) : Set (Set E) :=
  {ω | hyperClusterSet H ω S = K}

/-! ## Elementary facts, proved -/

@[simp] theorem mem_labelsMeeting (H : Hypergraph V E) (K : Set V) (e : E) :
    e ∈ labelsMeeting H K ↔ ¬ Disjoint (H.incidence e) K := Iff.rfl

@[simp] theorem deleteHyper_incidence (H : Hypergraph V E) (K : Set V) :
    (deleteHyper H K).incidence = H.incidence := rfl

/-- Deleting labels does not change the open graph, only the measure. -/
@[simp] theorem openHyperGraph_deleteHyper (H : Hypergraph V E) (K : Set V) (ω : Set E) :
    openHyperGraph (deleteHyper H K) ω = openHyperGraph H ω := rfl

theorem mem_hyperClusterSet_self (H : Hypergraph V E) (ω : Set E) {S : Set V} {x : V}
    (hx : x ∈ S) : x ∈ hyperClusterSet H ω S :=
  ⟨x, hx, SimpleGraph.Reachable.refl x⟩

theorem subset_hyperClusterSet (H : Hypergraph V E) (ω : Set E) (S : Set V) :
    S ⊆ hyperClusterSet H ω S := fun _ hx => mem_hyperClusterSet_self H ω hx

/-- Adjacency in the open graph, unfolded. -/
theorem openHyperGraph_adj_iff (H : Hypergraph V E) (ω : Set E) (x y : V) :
    (openHyperGraph H ω).Adj x y ↔
      x ≠ y ∧ ∃ e ∈ ω, x ∈ H.incidence e ∧ y ∈ H.incidence e := by
  constructor
  · rintro ⟨hne, hor⟩
    rcases hor with ⟨e, he, hx, hy⟩ | ⟨e, he, hy, hx⟩
    · exact ⟨hne, e, he, hx, hy⟩
    · exact ⟨hne, e, he, hx, hy⟩
  · rintro ⟨hne, e, he, hx, hy⟩
    exact ⟨hne, Or.inl ⟨e, he, hx, hy⟩⟩

/-- The cluster is closed under following an open label out of it. -/
theorem hyperClusterSet_mem_of_adj (H : Hypergraph V E) (ω : Set E) (S : Set V) {x y : V}
    (hx : x ∈ hyperClusterSet H ω S) (hxy : (openHyperGraph H ω).Adj x y) :
    y ∈ hyperClusterSet H ω S := by
  obtain ⟨s, hs, hr⟩ := hx
  exact ⟨s, hs, hr.trans hxy.reachable⟩

/-! ## The Phase 1 targets

The five results this module's definitions exist for are proved in `KN/HyperImplA.lean`
(locality of an open label on the cluster event, and determinedness of that event),
`KN/HyperImplB.lean` (measurability, and invariance of the probability under deletion of the labels
meeting the cluster) and `KN/HyperImplC.lean` (the cluster factorization, and the finite Lipschitz
estimate for product Bernoulli measures).
-/

end KNAll.Site

end
