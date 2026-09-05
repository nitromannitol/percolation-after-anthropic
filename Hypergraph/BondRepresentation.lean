import Hypergraph.SiteStatements

/-!
# Bond percolation is a hyperedge model

Bond percolation on the vertex type `V` with edge parameters `w : Sym2 V → [0,1]` is the hyperedge
model whose labels are the elements of `Sym2 V`, the label `e` being incident to its own endpoints
and open with probability `w e`.  Nothing has to be built: the configuration space is
`Set (Sym2 V)` on both sides, the label parameters are `w` on both sides, and so the two models
carry literally the same measure.

The one thing to check is the adjacency.  A label incident to two distinct vertices `x` and `y` is
forced to be `s(x, y)`, so a common open label of `x` and `y` is an open edge between them and
conversely.  The diagonal labels `s(z, z)` are incident to the single vertex `z`, so they never
join two distinct vertices, and they do not disturb the identification.

Consequently the connection events agree as sets of configurations, and the finite hyperedge
inequality `KNAll.Site.HyperedgeGluing` gives `KNAll.Conjecture1` after discarding the event
`{o ↔ A}` from the right-hand side, which only makes that side smaller.
-/

noncomputable section

namespace KNAll.Bond

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels KNAll.Site

variable {V : Type*}

/-! ## The representation -/

/-- Bond percolation as a hyperedge model: the labels are the elements of `Sym2 V`, the label `e`
is incident to the endpoints of `e`, and the parameters are those of the bond model. -/
def bondHypergraph (w : Sym2 V → unitInterval) : Hypergraph V (Sym2 V) where
  incidence := fun e => {x | x ∈ e}
  prob := w

@[simp] theorem bondHypergraph_incidence (w : Sym2 V → unitInterval) (e : Sym2 V) :
    (bondHypergraph w).incidence e = {x | x ∈ e} := rfl

@[simp] theorem bondHypergraph_prob (w : Sym2 V → unitInterval) :
    (bondHypergraph w).prob = w := rfl

/-- The two models carry the same measure on the same configuration space. -/
theorem prodBernoulli_bondHypergraph (w : Sym2 V → unitInterval) :
    prodBernoulli (bondHypergraph w).prob = prodBernoulli w := rfl

/-! ## The diagonal labels -/

/-- A diagonal label is incident to a single vertex. -/
theorem incidence_diag (w : Sym2 V → unitInterval) (z : V) :
    (bondHypergraph w).incidence s(z, z) = {z} := by
  ext x
  simp only [bondHypergraph_incidence, Set.mem_setOf_eq, Sym2.mem_iff, Set.mem_singleton_iff,
    or_self]

/-- **The diagonal labels create no adjacency.**  Being incident to the single vertex `z`, a label
`s(z, z)` is never incident to two distinct vertices, whether or not it is open. -/
theorem diag_not_incident_two (w : Sym2 V → unitInterval) {x y z : V} (hxy : x ≠ y)
    (hx : x ∈ (bondHypergraph w).incidence s(z, z)) :
    y ∉ (bondHypergraph w).incidence s(z, z) := by
  rw [incidence_diag] at hx ⊢
  simp only [Set.mem_singleton_iff] at hx ⊢
  intro hy
  exact hxy (hx.trans hy.symm)

/-! ## The adjacency identification -/

/-- **The adjacency identification.**  Two vertices share an open label of the bond hypergraph
exactly when they are distinct and the edge between them is open.  A label incident to both of two
distinct vertices has to be the edge joining them; in particular a diagonal label, incident to one
vertex only, never qualifies. -/
theorem openHyperGraph_adj_iff (w : Sym2 V → unitInterval) (ω : Set (Sym2 V)) (x y : V) :
    (openHyperGraph (bondHypergraph w) ω).Adj x y ↔ (openGraph ω).Adj x y := by
  simp only [openHyperGraph, SimpleGraph.fromRel_adj, openGraph_adj, bondHypergraph_incidence,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hne, hor⟩
    refine ⟨?_, hne⟩
    rcases hor with ⟨e, he, hx, hy⟩ | ⟨e, he, hy, hx⟩
    · have hE : e = s(x, y) := (Sym2.mem_and_mem_iff hne).1 ⟨hx, hy⟩
      rwa [hE] at he
    · have hE : e = s(x, y) := (Sym2.mem_and_mem_iff hne).1 ⟨hx, hy⟩
      rwa [hE] at he
  · rintro ⟨he, hne⟩
    exact ⟨hne, Or.inl ⟨s(x, y), he, Sym2.mem_mk_left x y, Sym2.mem_mk_right x y⟩⟩

/-- The open hypergraph of the bond representation **is** the open bond graph. -/
theorem openHyperGraph_eq (w : Sym2 V → unitInterval) (ω : Set (Sym2 V)) :
    openHyperGraph (bondHypergraph w) ω = openGraph ω :=
  SimpleGraph.ext (funext fun x => funext fun y => propext (openHyperGraph_adj_iff w ω x y))

/-- **The event identity.**  The two models have the same connection events, as subsets of the
common configuration space `Set (Sym2 V)`. -/
theorem hyperConn_eq_openConn (w : Sym2 V → unitInterval) (x y : V) :
    hyperConn (bondHypergraph w) x y = openConn x y := by
  ext ω
  simp only [hyperConn, openConn, Set.mem_setOf_eq, openHyperGraph_eq]

/-! ## The transfer -/

/-- **The transfer.**  The finite hyperedge inequality gives Conjecture 1 for bond percolation.
The hypergraph form concludes with the intersection `{o ↔ b} ∩ {o ↔ A}`, which is contained in
`{o ↔ b}`, so the bond form follows by monotonicity of the measure. -/
theorem conjecture1_of_hyperedgeGluing (h : HyperedgeGluing) : KNAll.Conjecture1 := by
  intro n w A hA o b
  have key := h (Fin n) (Sym2 (Fin n)) (bondHypergraph w) A hA o b
  simp only [hyperConn_eq_openConn, bondHypergraph_prob] at key
  exact key.trans (measureReal_mono Set.inter_subset_left (measure_ne_top _ _))

end KNAll.Bond

end
