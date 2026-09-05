import Hypergraph.SiteStatements

/-!
# Site percolation is a hyperedge model

For a graph `G` with independent site probabilities, put one hypergraph vertex for each site and one
for each edge of `G`, called a port, and one label for each site.  The label of `v` is incident to
`v` itself and to the port of every edge at `v`, and it is open exactly when the site `v` is open.

Two facts make the representation exact.  Adjacency in the open hypergraph never joins two sites
directly: it joins a site to a port at that site, or two ports at a common site, and in either case
the common label is open.  So a chain of open labels between two distinct sites is an open site path,
and conversely.  Since the labels *are* the sites, the two models carry literally the same measure,
and the connection events are equal as sets of configurations.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V : Type*}

/-- The vertices of the port hypergraph: the sites of `G`, and one port for each edge. -/
abbrev PortVertex (V : Type*) : Type _ := V ⊕ Sym2 V

/-- The label of the site `v` is incident to `v` and to the port of every edge at `v`. -/
def portIncidence (G : SimpleGraph V) (v : V) : Set (PortVertex V) :=
  {Sum.inl v} ∪ {q | ∃ u, G.Adj v u ∧ q = Sum.inr s(v, u)}

/-- The port hypergraph of a graph with site probabilities.  Its labels are the sites, so its
configuration space and its measure are those of site percolation. -/
def portHypergraph (G : SimpleGraph V) (w : V → unitInterval) : Hypergraph (PortVertex V) V where
  incidence := portIncidence G
  prob := w

@[simp] theorem portHypergraph_prob (G : SimpleGraph V) (w : V → unitInterval) :
    (portHypergraph G w).prob = w := rfl

/-- The measure of the port hypergraph is the site percolation measure. -/
theorem prodBernoulli_portHypergraph (G : SimpleGraph V) (w : V → unitInterval) :
    prodBernoulli (portHypergraph G w).prob = siteBernoulli w := rfl

theorem mem_portIncidence_inl {G : SimpleGraph V} {v x : V} :
    Sum.inl x ∈ portIncidence G v ↔ x = v := by
  simp only [portIncidence, mem_union, mem_singleton_iff, mem_setOf_eq]
  constructor
  · rintro (h | ⟨u, _, h⟩)
    · exact Sum.inl_injective h
    · exact absurd h (by simp)
  · rintro rfl; exact Or.inl rfl

theorem mem_portIncidence_inr {G : SimpleGraph V} {v : V} {e : Sym2 V} :
    Sum.inr e ∈ portIncidence G v ↔ ∃ u, G.Adj v u ∧ e = s(v, u) := by
  simp only [portIncidence, mem_union, mem_singleton_iff, mem_setOf_eq]
  constructor
  · rintro (h | ⟨u, hadj, h⟩)
    · exact absurd h (by simp)
    · exact ⟨u, hadj, Sum.inr_injective h⟩
  · rintro ⟨u, hadj, rfl⟩; exact Or.inr ⟨u, hadj, rfl⟩

/-- **No two sites are adjacent in the open hypergraph.**  A label incident to two distinct sites
would have to be both of them. -/
theorem not_adj_inl_inl (G : SimpleGraph V) (w : V → unitInterval) (ω : Set V) (x y : V) :
    ¬ (openHyperGraph (portHypergraph G w) ω).Adj (Sum.inl x) (Sum.inl y) := by
  rintro ⟨hne, hor⟩
  rcases hor with ⟨v, _, hx, hy⟩ | ⟨v, _, hy, hx⟩ <;>
    · rw [show (portHypergraph G w).incidence v = portIncidence G v from rfl,
        mem_portIncidence_inl] at hx hy
      exact hne (by rw [hx, hy])

/-- A site is adjacent to a port only through its own label, which must be open. -/
theorem adj_inl_inr_iff (G : SimpleGraph V) (w : V → unitInterval) (ω : Set V) (x : V)
    (e : Sym2 V) :
    (openHyperGraph (portHypergraph G w) ω).Adj (Sum.inl x) (Sum.inr e) ↔
      x ∈ ω ∧ ∃ u, G.Adj x u ∧ e = s(x, u) := by
  constructor
  · rintro ⟨-, hor⟩
    rcases hor with ⟨v, hv, hx, he⟩ | ⟨v, hv, he, hx⟩ <;>
      · rw [show (portHypergraph G w).incidence v = portIncidence G v from rfl,
          mem_portIncidence_inl] at hx
        subst hx
        rw [show (portHypergraph G w).incidence x = portIncidence G x from rfl,
          mem_portIncidence_inr] at he
        exact ⟨hv, he⟩
  · rintro ⟨hx, u, hadj, rfl⟩
    refine ⟨by simp, Or.inl ⟨x, hx, ?_, ?_⟩⟩
    · rw [show (portHypergraph G w).incidence x = portIncidence G x from rfl,
        mem_portIncidence_inl]
    · rw [show (portHypergraph G w).incidence x = portIncidence G x from rfl,
        mem_portIncidence_inr]
      exact ⟨u, hadj, rfl⟩

/-- Adjacency in the open site graph, from `KN.SiteStatements`. -/
theorem openSiteGraph_adj_iff (G : SimpleGraph V) (ω : Set V) (x y : V) :
    (openSiteGraph G ω).Adj x y ↔ G.Adj x y ∧ x ∈ ω ∧ y ∈ ω :=
  openSiteGraph_adj_iff' G ω x y

/-! ## From an open site path to a chain of open labels -/

/-- One site step becomes two hypergraph steps, through the port of the traversed edge. -/
theorem reachable_inl_of_adj (G : SimpleGraph V) (w : V → unitInterval) (ω : Set V) {a b : V}
    (h : (openSiteGraph G ω).Adj a b) :
    (openHyperGraph (portHypergraph G w) ω).Reachable (Sum.inl a) (Sum.inl b) := by
  rw [openSiteGraph_adj_iff] at h
  obtain ⟨hadj, ha, hb⟩ := h
  have h1 : (openHyperGraph (portHypergraph G w) ω).Adj (Sum.inl a) (Sum.inr s(a, b)) := by
    rw [adj_inl_inr_iff]; exact ⟨ha, b, hadj, rfl⟩
  have h2 : (openHyperGraph (portHypergraph G w) ω).Adj (Sum.inl b) (Sum.inr s(a, b)) := by
    rw [adj_inl_inr_iff]
    refine ⟨hb, a, hadj.symm, ?_⟩
    rw [Sym2.eq_swap]
  exact (h1.reachable).trans h2.reachable.symm

/-- A chain of open sites gives a chain of open labels. -/
theorem reachable_hyper_of_site (G : SimpleGraph V) (w : V → unitInterval) (ω : Set V) {x y : V}
    (h : (openSiteGraph G ω).Reachable x y) :
    (openHyperGraph (portHypergraph G w) ω).Reachable (Sum.inl x) (Sum.inl y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj q ih => exact (reachable_inl_of_adj G w ω hadj).trans ih

/-- Two adjacent open sites are joined in the open site graph. -/
theorem reachable_of_adj_site (G : SimpleGraph V) (ω : Set V) {a b : V} (hG : G.Adj a b)
    (ha : a ∈ ω) (hb : b ∈ ω) : (openSiteGraph G ω).Reachable a b :=
  (SimpleGraph.Adj.reachable ((openSiteGraph_adj_iff G ω a b).2 ⟨hG, ha, hb⟩))

/-! ## From a chain of open labels to an open site path -/

/-- The invariant carried along a chain of open labels started at the site `x`: a site reached is
joined to `x` by an open site path, and a port reached has an open endpoint that is. -/
def GoodFrom (G : SimpleGraph V) (ω : Set V) (x : V) : PortVertex V → Prop
  | Sum.inl z => (openSiteGraph G ω).Reachable x z
  | Sum.inr e => ∃ z ∈ e, z ∈ ω ∧ (openSiteGraph G ω).Reachable x z

theorem goodFrom_step (G : SimpleGraph V) (w : V → unitInterval) (ω : Set V) (x : V)
    {q q' : PortVertex V} (hq : GoodFrom G ω x q)
    (hadj : (openHyperGraph (portHypergraph G w) ω).Adj q q') :
    GoodFrom G ω x q' := by
  match q, q' with
  | Sum.inl a, Sum.inl b => exact absurd hadj (not_adj_inl_inl G w ω a b)
  | Sum.inl a, Sum.inr e =>
      rw [adj_inl_inr_iff] at hadj
      obtain ⟨ha, u, hGa, rfl⟩ := hadj
      exact ⟨a, Sym2.mem_mk_left a u, ha, hq⟩
  | Sum.inr e, Sum.inl b =>
      rw [SimpleGraph.adj_comm, adj_inl_inr_iff] at hadj
      obtain ⟨hb, u, hGb, rfl⟩ := hadj
      obtain ⟨z, hze, hzω, hzr⟩ := hq
      rcases Sym2.mem_iff.1 hze with rfl | rfl
      · exact hzr
      · exact hzr.trans (reachable_of_adj_site G ω hGb.symm hzω hb)
  | Sum.inr e, Sum.inr f =>
      obtain ⟨-, hor⟩ := hadj
      rcases hor with ⟨v, hv, he, hf⟩ | ⟨v, hv, hf, he⟩ <;>
        · rw [show (portHypergraph G w).incidence v = portIncidence G v from rfl,
            mem_portIncidence_inr] at he hf
          obtain ⟨u, hGu, rfl⟩ := he
          obtain ⟨u', hGu', rfl⟩ := hf
          obtain ⟨z, hze, hzω, hzr⟩ := hq
          refine ⟨v, Sym2.mem_mk_left v u', hv, ?_⟩
          rcases Sym2.mem_iff.1 hze with rfl | rfl
          · exact hzr
          · exact hzr.trans (reachable_of_adj_site G ω hGu.symm hzω hv)

theorem goodFrom_of_walk (G : SimpleGraph V) (w : V → unitInterval) (ω : Set V) (x : V) :
    ∀ {a q : PortVertex V}, (openHyperGraph (portHypergraph G w) ω).Walk a q →
      GoodFrom G ω x a → GoodFrom G ω x q := by
  intro a q p
  induction p with
  | nil => exact fun h => h
  | cons hadj q ih => exact fun h => ih (goodFrom_step G w ω x h hadj)

/-! ## The event identity -/

/-- If `x` reaches a different site, then `x` is open: the first step of the path says so. -/
theorem mem_of_reachable_ne (G : SimpleGraph V) (ω : Set V) {x y : V}
    (h : (openSiteGraph G ω).Reachable x y) (hxy : x ≠ y) : x ∈ ω := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hxy
  | cons hadj _ => exact ((openSiteGraph_adj_iff G ω _ _).1 hadj).2.1

/-- **The representation is exact on distinct terminals.**  For `x ≠ y` the event that a chain of
open labels joins the two sites is, as a set of configurations, the event that an open site path
joins them. -/
theorem hyperConn_eq_siteConn (G : SimpleGraph V) (w : V → unitInterval) {x y : V} (hxy : x ≠ y) :
    hyperConn (portHypergraph G w) (Sum.inl x) (Sum.inl y) = siteConn G x y := by
  ext ω
  constructor
  · rintro ⟨p⟩
    have hreach : (openSiteGraph G ω).Reachable x y :=
      goodFrom_of_walk G w ω x p (show GoodFrom G ω x (Sum.inl x) from SimpleGraph.Reachable.refl x)
    exact ⟨mem_of_reachable_ne G ω hreach hxy, hreach⟩
  · rintro ⟨-, hreach⟩
    exact reachable_hyper_of_site G w ω hreach

/-! ## The transfer -/

/-- **The transfer.**  The finite hyperedge inequality gives the site inequality, with no vertex
forced open, whenever the observer and the target are distinct and neither lies in `A`. -/
theorem siteGluingUnpinned_of_hyperedgeGluing (h : HyperedgeGluing) : SiteGluingUnpinned := by
  intro n G w A hA o b hob hoA hbA
  have hpairo : ∀ a ∈ A, hyperConn (portHypergraph G w) (Sum.inl o) (Sum.inl a) = siteConn G o a :=
    fun a ha => hyperConn_eq_siteConn G w (by rintro rfl; exact hoA ha)
  have hpairb : ∀ a ∈ A, hyperConn (portHypergraph G w) (Sum.inl a) (Sum.inl b) = siteConn G a b :=
    fun a ha => hyperConn_eq_siteConn G w (by rintro rfl; exact hbA ha)
  set e : Fin n ↪ PortVertex (Fin n) := ⟨Sum.inl, Sum.inl_injective⟩ with he
  have hA' : (A.map e).Nonempty := hA.map
  have key := h (PortVertex (Fin n)) (Fin n) (portHypergraph G w) (A.map e) hA'
    (Sum.inl o) (Sum.inl b)
  have hmeas : (prodBernoulli (portHypergraph G w).prob) = siteBernoulli w := rfl
  rw [hmeas] at key
  have hunion : (⋃ a ∈ A.map e, hyperConn (portHypergraph G w) (Sum.inl o) a)
      = siteConnSet G o ↑A := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_map, he, Function.Embedding.coeFn_mk, exists_prop,
      siteConnSet]
    constructor
    · rintro ⟨q, ⟨a, ha, rfl⟩, hq⟩
      exact ⟨a, ha, by rwa [hpairo a ha] at hq⟩
    · rintro ⟨a, ha, hq⟩
      exact ⟨Sum.inl a, ⟨a, ha, rfl⟩, by rwa [hpairo a ha]⟩
  have hinf : (A.map e).inf' hA'
      (fun a => (siteBernoulli w).real (hyperConn (portHypergraph G w) a (Sum.inl b)))
      = A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b)) := by
    rw [Finset.inf'_map]
    refine Finset.inf'_congr hA rfl fun a ha => ?_
    simp only [Function.comp_apply, he, Function.Embedding.coeFn_mk]
    rw [hpairb a ha]
  rw [hunion, hinf, hyperConn_eq_siteConn G w hob] at key
  exact key

end KNAll.Site

end