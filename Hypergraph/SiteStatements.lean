import KNConjectures.Conjectures
import Mathlib.Probability.Independence.InfinitePi

/-!
# Bernoulli site percolation: the model, the critical statement, and the finite input

This module states, in the vocabulary of the development, the two propositions that the manuscript
`site_percolation_criticality.tex` sets out to prove.  Nothing is proved here.

* `SiteCriticality d` is the assertion that nearest-neighbour Bernoulli **site** percolation on `ℤ^d`
  has no infinite open cluster at its critical parameter.  It is the site analogue of
  `Percolation.Literature.PercolationContinuity`, which the development proves for bond percolation.
* `HyperedgeGluing` is the finite input of the manuscript: in a finite model of independent
  hyperedges, `P(o ↔ b) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)`.  For hyperedges of size two this is the
  bond statement `KNAll.Conjecture1`, which is proved in `KN/Conjectures.lean`.
* `PinnedSiteGluing` is the same inequality for site percolation on a finite graph when the named
  vertices are open with probability one, the form used by the lattice argument.

A site configuration is the set of open vertices.  Two vertices are connected when they are joined by
a path all of whose vertices are open; in particular a closed vertex is connected to nothing, not even
to itself, so the open cluster of a closed vertex is empty.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Site percolation on a graph -/

/-- A site configuration: the set of open vertices. -/
abbrev SiteConfig (V : Type*) : Type _ := Set V

variable {V : Type*}

/-- The graph of open vertices: an edge of `G` survives when both of its endpoints are open. -/
def openSiteGraph (G : SimpleGraph V) (ω : SiteConfig V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => G.Adj x y ∧ x ∈ ω ∧ y ∈ ω

/-- The open cluster of `x`: empty when `x` is closed, and otherwise the set of vertices joined to
`x` by a path of open vertices. -/
def siteCluster (G : SimpleGraph V) (ω : SiteConfig V) (x : V) : Set V :=
  {y | x ∈ ω ∧ (openSiteGraph G ω).Reachable x y}

/-- The event that `x` and `y` are joined by a path of open vertices. -/
def siteConn (G : SimpleGraph V) (x y : V) : Set (SiteConfig V) :=
  {ω | x ∈ ω ∧ (openSiteGraph G ω).Reachable x y}

/-- The event that `x` is connected to some vertex of `A`. -/
def siteConnSet (G : SimpleGraph V) (x : V) (A : Set V) : Set (SiteConfig V) :=
  ⋃ a ∈ A, siteConn G x a

/-- Site percolation with vertex probabilities `w`: each vertex is open independently. -/
def siteBernoulli (w : V → unitInterval) : Measure (SiteConfig V) := prodBernoulli w

instance instIsProbabilityMeasureSiteBernoulli (w : V → unitInterval) :
    IsProbabilityMeasure (siteBernoulli w) :=
  instIsProbabilityMeasureProdBernoulli w

/-- Site percolation on an arbitrary graph: the probability that the open cluster of `x` is
infinite when every vertex is open with probability `p`. -/
def thetaSiteOn (G : SimpleGraph V) (x : V) (p : unitInterval) : ℝ :=
  (siteBernoulli (fun _ : V => p)).real {ω | (siteCluster G ω x).Infinite}

/-- Adjacency in the open site graph: an edge of `G` with both endpoints open. -/
theorem openSiteGraph_adj_iff' (G : SimpleGraph V) (ω : Set V) (x y : V) :
    (openSiteGraph G ω).Adj x y ↔ G.Adj x y ∧ x ∈ ω ∧ y ∈ ω := by
  constructor
  · rintro ⟨-, hor⟩
    rcases hor with ⟨h, hx, hy⟩ | ⟨h, hy, hx⟩
    · exact ⟨h, hx, hy⟩
    · exact ⟨h.symm, hx, hy⟩
  · rintro ⟨h, hx, hy⟩
    exact ⟨h.ne, Or.inl ⟨h, hx, hy⟩⟩

/-! ### Sanity checks on the conventions

These pin down the reading of the definitions, so that the statements below can be checked rather
than taken on trust. -/

/-- A closed vertex is connected to nothing, not even to itself. -/
theorem siteConn_self (G : SimpleGraph V) (x : V) : siteConn G x x = {ω | x ∈ ω} := by
  ext ω
  exact ⟨fun h => h.1, fun h => ⟨h, SimpleGraph.Reachable.refl x⟩⟩

/-- The open cluster of a closed vertex is empty. -/
theorem siteCluster_of_notMem (G : SimpleGraph V) (ω : Set V) {x : V} (hx : x ∉ ω) :
    siteCluster G ω x = ∅ := by
  ext y
  exact ⟨fun h => absurd h.1 hx, fun h => absurd h (Set.notMem_empty y)⟩

/-- A vertex of its own open cluster: an open vertex lies in its cluster. -/
theorem mem_siteCluster_self (G : SimpleGraph V) (ω : Set V) {x : V} (hx : x ∈ ω) :
    x ∈ siteCluster G ω x :=
  ⟨hx, SimpleGraph.Reachable.refl x⟩

/-- Every vertex of the open cluster of an open vertex is itself open. -/
theorem mem_of_mem_siteCluster (G : SimpleGraph V) (ω : Set V) {x y : V}
    (h : y ∈ siteCluster G ω x) : y ∈ ω := by
  obtain ⟨hx, hr⟩ := h
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hx
  | cons hadj q ih => exact ih ((openSiteGraph_adj_iff' G ω _ _).1 hadj).2.2

/-- Two adjacent open vertices are connected: the connection event is not empty when it should not
be. -/
theorem siteConn_of_adj (G : SimpleGraph V) {ω : Set V} {x y : V} (h : G.Adj x y)
    (hx : x ∈ ω) (hy : y ∈ ω) : ω ∈ siteConn G x y :=
  ⟨hx, SimpleGraph.Adj.reachable ((openSiteGraph_adj_iff' G ω x y).2 ⟨h, hx, hy⟩)⟩

/-- Connection requires both endpoints to be open. -/
theorem siteConn_subset (G : SimpleGraph V) (x y : V) :
    siteConn G x y ⊆ {ω | x ∈ ω ∧ y ∈ ω} := by
  rintro ω ⟨hx, hr⟩
  exact ⟨hx, mem_of_mem_siteCluster G ω ⟨hx, hr⟩⟩

/-! ## The critical statement on the integer lattices -/

/-- The percolation probability of site percolation on `ℤ^d` at parameter `p`: the probability that
the open cluster of the origin is infinite. -/
def thetaSite (d : ℕ) (p : unitInterval) : ℝ :=
  thetaSiteOn (zdGraph d) (0 : Site d) p

/-- The critical parameter of site percolation on `ℤ^d`, with the convention of
`Percolation.Literature.criticalProb`: the infimum is taken over the parameters at which the origin
percolates, together with `1`. -/
def criticalProbSite (d : ℕ) : ℝ :=
  sInf ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSite d ⟨p, h⟩} ∪ {1})

/-- The critical parameter lies in the unit interval.  The infimum is taken over a set that contains
`1` and consists of nonnegative numbers, exactly as for the bond critical parameter. -/
theorem criticalProbSite_nonneg_mem (d : ℕ) :
    ∀ p ∈ ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSite d ⟨p, h⟩} ∪ {1}), 0 ≤ p := by
  rintro p (⟨h, -⟩ | h)
  · exact h.1
  · rw [Set.mem_singleton_iff] at h
    rw [h]; exact zero_le_one

theorem criticalProbSite_mem_Icc (d : ℕ) : criticalProbSite d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_csInf ⟨1, Or.inr rfl⟩ (criticalProbSite_nonneg_mem d),
    csInf_le ⟨0, criticalProbSite_nonneg_mem d⟩ (Or.inr rfl)⟩

/-- The critical parameter is a lower bound for every parameter at which the origin percolates. -/
theorem criticalProbSite_le_of_pos (d : ℕ) (q : unitInterval) (hq : 0 < thetaSite d q) :
    criticalProbSite d ≤ (q : ℝ) :=
  csInf_le ⟨0, criticalProbSite_nonneg_mem d⟩ (Or.inl ⟨q.2, by simpa using hq⟩)

/-- The critical parameter as a point of the unit interval, so that it can be fed to `thetaSite`
without carrying a membership hypothesis.  This is what makes `SiteCriticality` a statement with no
vacuous reading. -/
def criticalProbSiteI (d : ℕ) : unitInterval :=
  ⟨criticalProbSite d, criticalProbSite_mem_Icc d⟩

@[simp] theorem coe_criticalProbSiteI (d : ℕ) :
    (criticalProbSiteI d : ℝ) = criticalProbSite d := rfl

/-- **The target of the manuscript**: at its critical parameter, site percolation on `ℤ^d` has no
infinite open cluster.  The site analogue of `Percolation.Literature.PercolationContinuity d`. -/
def SiteCriticality (d : ℕ) : Prop :=
  thetaSite d (criticalProbSiteI d) = 0

/-! ## The finite input -/

/-- A finite model of independent hyperedges: a label type `E`, an incidence map, and an opening
probability for each label.  A configuration is the set of open labels. -/
structure Hypergraph (V E : Type*) where
  /-- The vertices incident to a label. -/
  incidence : E → Set V
  /-- The probability that a label is open. -/
  prob : E → unitInterval

variable {E : Type*}

/-- Two vertices are adjacent when some open label is incident to both. -/
def openHyperGraph (H : Hypergraph V E) (ω : Set E) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => ∃ e ∈ ω, x ∈ H.incidence e ∧ y ∈ H.incidence e

/-- The event that a chain of open labels joins `x` to `y`.  Connectivity is reflexive here. -/
def hyperConn (H : Hypergraph V E) (x y : V) : Set (Set E) :=
  {ω | (openHyperGraph H ω).Reachable x y}

/-- **The finite input of the manuscript**, in its localized form: in every finite model of
independent hyperedges, `P(o ↔ b, o ↔ A) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)`.  Dropping the event
`{o ↔ A}` on the right gives the plain form, and for incidence sets of size two that is
`KNAll.Conjecture1`. -/
def HyperedgeGluing : Prop :=
  ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L) (A : Finset W) (hA : A.Nonempty)
      (o b : W),
    (prodBernoulli H.prob).real (⋃ a ∈ A, hyperConn H o a) *
        A.inf' hA (fun a => (prodBernoulli H.prob).real (hyperConn H a b)) ≤
      (prodBernoulli H.prob).real (hyperConn H o b ∩ ⋃ a ∈ A, hyperConn H o a)

/-- **The pinned site form** (its Corollary): the same inequality for site percolation on a finite
graph, when the observer, the target and every vertex of `A` are open with probability one. -/
def PinnedSiteGluing : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → unitInterval) (A : Finset (Fin n))
      (hA : A.Nonempty) (o b : Fin n),
    w o = 1 → w b = 1 → (∀ a ∈ A, w a = 1) →
    (siteBernoulli w).real (siteConnSet G o ↑A) *
        A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b)) ≤
      (siteBernoulli w).real (siteConn G o b)

/-- **The strengthened site form** (Theorem B of the revision): no vertex has to be forced open,
provided the observer and the target are distinct and neither lies in `A`. -/
def SiteGluingUnpinned : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → unitInterval) (A : Finset (Fin n))
      (hA : A.Nonempty) (o b : Fin n),
    o ≠ b → o ∉ A → b ∉ A →
    (siteBernoulli w).real (siteConnSet G o ↑A) *
        A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b)) ≤
      (siteBernoulli w).real (siteConn G o b ∩ siteConnSet G o ↑A)

/-! ## The external input of the lattice argument -/

/-- **The half-space input, stated as a hypothesis.**  The manuscript's final contradiction needs
this for site percolation: at the critical parameter of `ℤ^d`, site percolation in the half-space
`{x | 0 ≤ x 0}` has no infinite cluster.

This is not available from the development.  Its
`Percolation.Literature.BarskyGrimmettNewman1991` is the same statement for **bond** percolation,
cited to Grimmett 1999, Theorem (7.35), and the manuscript asserts the site case of that theorem
without proving it.  Carrying it as an explicit hypothesis is what keeps the Lean chain honest: any
proof of `SiteCriticality` that uses it will display it. -/
def SiteHalfSpaceCriticality (d : ℕ) [NeZero d] : Prop :=
  thetaSiteOn (halfSpaceGraph d) (halfSpaceOrigin d) (criticalProbSiteI d) = 0

/-- **The same-parameter slab reduction** of the manuscript, as a hypothesis: percolation on `ℤ^d`
at `p` forces percolation at the same `p` in a slab of some finite width. -/
def SiteSlabReduction (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, 0 < thetaSite d p →
    ∃ k : ℕ, 0 < thetaSiteOn (slabGraph d k) (slabOrigin d k) p

/-- **The weaker external input**: no slab percolates at the critical parameter of the full lattice.

This is all the endgame consumes.  Every slab is contained in the half-space, so
`SiteHalfSpaceCriticality` implies it, but not conversely: the half-space statement also carries the
equality of critical parameters.  Replacing the half-space input by this one is therefore a strict
weakening of what has to be supplied from outside, and it is the site analogue of the slab theorem of
Duminil-Copin, Sidoravicius and Tassion rather than of Barsky, Grimmett and Newman. -/
def SiteSlabCriticality (d : ℕ) [NeZero d] : Prop :=
  ∀ k : ℕ, thetaSiteOn (slabGraph d k) (slabOrigin d k) (criticalProbSiteI d) = 0

/-- The percolation probability is nonnegative, being the measure of an event. -/
theorem thetaSiteOn_nonneg (G : SimpleGraph V) (x : V) (p : unitInterval) :
    0 ≤ thetaSiteOn G x p :=
  measureReal_nonneg

/-- **The endgame, proved.**  The same-parameter slab reduction and the slab input give the critical
statement.  This is the step that the manuscript closes with the half-space theorem; it needs only
the weaker slab input, and the derivation itself is now machine-checked. -/
theorem siteCriticality_of_slabCriticality (d : ℕ) [NeZero d]
    (hred : SiteSlabReduction d) (hslab : SiteSlabCriticality d) :
    SiteCriticality d := by
  by_contra hne
  have hpos : 0 < thetaSite d (criticalProbSiteI d) :=
    lt_of_le_of_ne (thetaSiteOn_nonneg _ _ _) (Ne.symm hne)
  obtain ⟨k, hk⟩ := hred (criticalProbSiteI d) hpos
  exact absurd (hslab k) (ne_of_gt hk)

/-! ### Site percolation is monotone under inclusion of the underlying graph

`Percolation.Literature.theta_comap_le` is this statement for bond percolation.  The three steps
are the same for site percolation: the restriction of a configuration along an injection has the
right law, open paths of the restriction map to open paths, and the event that the open cluster is
infinite is measurable. -/

section Monotone

variable {W : Type*}

/-- The restriction of a site configuration along `f`: a vertex of `W` is open exactly when its
image is open. -/
def restrictSite (f : W → V) (ω : SiteConfig V) : SiteConfig W := f ⁻¹' ω

@[simp] theorem mem_restrictSite (f : W → V) (ω : SiteConfig V) (a : W) :
    a ∈ restrictSite f ω ↔ f a ∈ ω := Iff.rfl

theorem measurable_restrictSite (f : W → V) : Measurable (restrictSite (V := V) f) :=
  measurable_set_iff.2 fun a => measurable_set_mem (f a)

/-- **The restriction coupling has the right law**: for injective `f`, restricting a site
configuration pushes site percolation on `V` forward to site percolation on `W`. -/
theorem siteBernoulli_map_restrictSite {f : W → V} (hf : Function.Injective f) (p : unitInterval) :
    (siteBernoulli fun _ : V => p).map (restrictSite f) = siteBernoulli fun _ : W => p := by
  have hSV : Measurable fun q : V → Prop => {i | q i} := measurable_setOf
  have hSW : Measurable fun q : W → Prop => {i | q i} := measurable_setOf
  rw [siteBernoulli, siteBernoulli, prodBernoulli_eq_map, prodBernoulli_eq_map,
    Measure.map_map (measurable_restrictSite f) hSV]
  have hcomp : (restrictSite (V := V) f ∘ fun q : V → Prop => {i | q i}) =
      (fun q : W → Prop => {i | q i}) ∘ fun (q : V → Prop) (a : W) => q (f a) := rfl
  rw [hcomp, ← Measure.map_map hSW (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj hf]

/-- Open paths of the restricted configuration map to open paths. -/
theorem reachable_map_of_restrictSite (G : SimpleGraph V) {f : W → V}
    (ω : SiteConfig V) {x y : W}
    (h : (openSiteGraph (G.comap f) (restrictSite f ω)).Reachable x y) :
    (openSiteGraph G ω).Reachable (f x) (f y) := by
  refine h.map ⟨f, fun {a b} hab => ?_⟩
  rw [openSiteGraph_adj_iff'] at hab ⊢
  exact ⟨hab.1, hab.2.1, hab.2.2⟩

/-! #### Measurability of the infinite-cluster event -/

/-- An open walk is a chain of one-vertex cylinder events. -/
theorem measurableSet_isChain_openSiteGraph (G : SimpleGraph V) :
    ∀ (a : V) (l : List V),
      MeasurableSet {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (a :: l)} := by
  intro a l
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hset : {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (a :: b :: l)} =
        (({_ω : SiteConfig V | G.Adj a b} ∩ {ω : SiteConfig V | a ∈ ω}) ∩
            {ω : SiteConfig V | b ∈ ω}) ∩
          {ω | List.IsChain (openSiteGraph G ω).Adj (b :: l)} := by
      ext ω
      simp only [List.isChain_cons_cons, openSiteGraph_adj_iff', Set.mem_setOf_eq,
        Set.mem_inter_iff, and_assoc]
    rw [hset]
    exact (((MeasurableSet.const _).inter (measurableSet_mem _)).inter
      (measurableSet_mem _)).inter (ih b)

/-- `{x ↔ y}` as a countable union over the lists of vertices witnessing an open walk. -/
theorem siteConn_eq_iUnion (G : SimpleGraph V) (x y : V) :
    siteConn G x y = {ω : SiteConfig V | x ∈ ω} ∩
      ⋃ l : List V, {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (x :: l) ∧
        (x :: l).getLast (List.cons_ne_nil _ _) = y} := by
  ext ω
  simp only [siteConn, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion]
  rw [and_congr_right_iff]
  intro _
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · exact List.exists_isChain_cons_of_relationReflTransGen
  · rintro ⟨l, hl, hy⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hl hy

/-- The event that `x` and `y` are joined by an open path is measurable. -/
theorem measurableSet_siteConn [Countable V] (G : SimpleGraph V) (x y : V) :
    MeasurableSet (siteConn G x y) := by
  rw [siteConn_eq_iUnion]
  refine (measurableSet_mem _).inter (MeasurableSet.iUnion fun l => ?_)
  have hset : {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (x :: l) ∧
      (x :: l).getLast (List.cons_ne_nil _ _) = y} =
        {ω : SiteConfig V | List.IsChain (openSiteGraph G ω).Adj (x :: l)} ∩
          {_ω | (x :: l).getLast (List.cons_ne_nil _ _) = y} := by
    ext ω; simp
  rw [hset]
  exact (measurableSet_isChain_openSiteGraph G x l).inter (MeasurableSet.const _)

/-- The open cluster of `x` is infinite exactly when it leaves every finite set of vertices. -/
theorem siteInfinite_eq_iInter (G : SimpleGraph V) (x : V) :
    {ω : SiteConfig V | (siteCluster G ω x).Infinite} =
      ⋂ F : Finset V, ⋃ y ∈ (↑F : Set V)ᶜ, siteConn G x y := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff,
    Finset.mem_coe, exists_prop, siteCluster, siteConn]
  constructor
  · intro hinf F
    obtain ⟨y, hy, hyF⟩ := hinf.exists_notMem_finset F
    exact ⟨y, hyF, hy⟩
  · intro h hfin
    obtain ⟨y, hyF, hy⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.2 hy)

/-- The event that the open cluster of `x` is infinite is measurable. -/
theorem measurableSet_siteInfinite [Countable V] (G : SimpleGraph V) (x : V) :
    MeasurableSet {ω : SiteConfig V | (siteCluster G ω x).Infinite} := by
  rw [siteInfinite_eq_iInter]
  exact MeasurableSet.iInter fun F =>
    MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_siteConn G x y

/-! #### The coupling inequality -/

/-- `θ` of a subgraph, computed on the ambient configuration space. -/
theorem thetaSiteOn_comap_eq [Countable W] (G : SimpleGraph V) {f : W → V}
    (hf : Function.Injective f) (x : W) (p : unitInterval) :
    thetaSiteOn (G.comap f) x p = (siteBernoulli fun _ : V => p).real
      (restrictSite f ⁻¹' {ω : SiteConfig W | (siteCluster (G.comap f) ω x).Infinite}) := by
  rw [thetaSiteOn, ← siteBernoulli_map_restrictSite hf p,
    map_measureReal_apply (measurable_restrictSite f) (measurableSet_siteInfinite _ x)]

/-- **The coupling inequality**: for injective `f`, site percolation on the pullback graph is
dominated by site percolation on the ambient graph. -/
theorem thetaSiteOn_comap_le [Countable W] (G : SimpleGraph V) {f : W → V}
    (hf : Function.Injective f) (x : W) (p : unitInterval) :
    thetaSiteOn (G.comap f) x p ≤ thetaSiteOn G (f x) p := by
  rw [thetaSiteOn_comap_eq G hf, thetaSiteOn]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hω ⊢
  refine (hω.image hf.injOn).mono ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨hy.1, reachable_map_of_restrictSite G ω hy.2⟩

/-- Site percolation on an induced subgraph is monotone in the vertex set. -/
theorem thetaSiteOn_induce_mono [Countable V] (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T)
    (x : V)
    (hx : x ∈ S) (p : unitInterval) :
    thetaSiteOn (G.induce S) ⟨x, hx⟩ p ≤ thetaSiteOn (G.induce T) ⟨x, hST hx⟩ p := by
  have hG : G.induce S = (G.induce T).comap (Set.inclusion hST) := by ext a b; rfl
  rw [hG]
  exact thetaSiteOn_comap_le (G.induce T) (Set.inclusion_injective hST) ⟨x, hx⟩ p

end Monotone

/-- **Every slab lies in the half-space, so the half-space input implies the slab input.**  This is
the deduction that makes `SiteSlabCriticality` a consequence of the half-space theorem rather than a
separate assumption: `{x | 0 ≤ x 0 ≤ k}` is contained in `{x | 0 ≤ x 0}`, both graphs are induced
from `ℤ^d`, and site percolation is monotone in the vertex set of an induced subgraph. -/
theorem siteSlabCriticality_of_halfSpace (d : ℕ) [NeZero d]
    (hhalf : SiteHalfSpaceCriticality d) : SiteSlabCriticality d := by
  intro k
  refine le_antisymm ?_ (thetaSiteOn_nonneg _ _ _)
  have hsub : slab d k ⊆ halfSpace d := fun x hx => hx.1
  have hmono := thetaSiteOn_induce_mono (zdGraph d) hsub (0 : Site d) (zero_mem_slab d k)
    (criticalProbSiteI d)
  rw [← hhalf]
  exact hmono

/-- **The endgame from the half-space theorem.**  This is the whole lattice argument with its two
remaining inputs displayed: the site half-space theorem, and the same-parameter slab reduction of the
manuscript.  Nothing else is assumed. -/
theorem siteCriticality_of_halfSpace (d : ℕ) [NeZero d] (hhalf : SiteHalfSpaceCriticality d)
    (hred : SiteSlabReduction d) : SiteCriticality d :=
  siteCriticality_of_slabCriticality d hred (siteSlabCriticality_of_halfSpace d hhalf)

/-! ### The half-space input as the two published theorems

`SiteHalfSpaceCriticality` is not a single citation.  Barsky, Grimmett and Newman prove that the
percolation probability of the half-space vanishes at the **half-space** critical density, for bond
or site percolation; Grimmett and Marstrand prove, for site percolation on `ℤ^d` with `d ≥ 3`, that
the critical density of the half-space equals that of the whole lattice.  Stating both separately
keeps each import identifiable. -/

/-- The critical parameter of site percolation on a rooted graph, with the convention of
`criticalProbSite`. -/
def criticalProbSiteOn {V : Type*} (G : SimpleGraph V) (x : V) : ℝ :=
  sInf ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSiteOn G x ⟨p, h⟩} ∪ {1})

theorem criticalProbSiteOn_mem_Icc {V : Type*} (G : SimpleGraph V) (x : V) :
    criticalProbSiteOn G x ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : ∀ p ∈ ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSiteOn G x ⟨p, h⟩} ∪ {1}), 0 ≤ p := by
    rintro p (⟨h, -⟩ | h)
    · exact h.1
    · rw [Set.mem_singleton_iff] at h
      rw [h]; exact zero_le_one
  exact ⟨le_csInf ⟨1, Or.inr rfl⟩ h0, csInf_le ⟨0, h0⟩ (Or.inr rfl)⟩

/-- The same, as a point of the unit interval. -/
def criticalProbSiteOnI {V : Type*} (G : SimpleGraph V) (x : V) : unitInterval :=
  ⟨criticalProbSiteOn G x, criticalProbSiteOn_mem_Icc G x⟩

/-- **Barsky–Grimmett–Newman 1991**, in its site form: the percolation probability of the half-space
vanishes at the critical density *of the half-space*.  Their summary states the result for
independent nearest-neighbour bond or site percolation. -/
def SiteHalfSpaceOwnCriticality (d : ℕ) [NeZero d] : Prop :=
  thetaSiteOn (halfSpaceGraph d) (halfSpaceOrigin d)
    (criticalProbSiteOnI (halfSpaceGraph d) (halfSpaceOrigin d)) = 0

/-- **Grimmett–Marstrand 1990**: the critical density of the half-space equals that of `ℤ^d`.  That
paper works throughout with site percolation on `ℤ^d`. -/
def SiteHalfSpaceCriticalEqual (d : ℕ) [NeZero d] : Prop :=
  criticalProbSiteOn (halfSpaceGraph d) (halfSpaceOrigin d) = criticalProbSite d

/-- The half-space input is exactly the conjunction of the two published theorems. -/
theorem siteHalfSpaceCriticality_of_published (d : ℕ) [NeZero d]
    (hbgn : SiteHalfSpaceOwnCriticality d) (hgm : SiteHalfSpaceCriticalEqual d) :
    SiteHalfSpaceCriticality d := by
  have : criticalProbSiteOnI (halfSpaceGraph d) (halfSpaceOrigin d) = criticalProbSiteI d :=
    Subtype.ext hgm
  rw [SiteHalfSpaceCriticality, ← this]
  exact hbgn

/-! ### The endgame without any half-space or slab criticality theorem

If the reduction is strengthened so that percolation at `p` gives slab percolation at some parameter
strictly below `p`, the conclusion follows from the definition of the critical parameter alone.  No
theorem about percolation at a critical point is used. -/

/-- **The reduction with a strictly smaller parameter.**  Grimmett and Marstrand prove the version
with `p + γ` in place of `q < p`, and identify the passage to a parameter that is not larger as the
point where their sprinkling argument fails. -/
def SiteSlabReductionBelow (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → 0 < thetaSite d p →
    ∃ (k : ℕ) (q : unitInterval), (q : ℝ) < (p : ℝ) ∧
      0 < thetaSiteOn (slabGraph d k) (slabOrigin d k) q

/-- Percolation in a slab forces percolation on the whole lattice at the same parameter. -/
theorem thetaSiteOn_slab_le (d : ℕ) [NeZero d] (k : ℕ) (p : unitInterval) :
    thetaSiteOn (slabGraph d k) (slabOrigin d k) p ≤ thetaSite d p :=
  thetaSiteOn_comap_le (zdGraph d) Subtype.val_injective (slabOrigin d k) p

/-- **Criticality from the strengthened reduction.**  The only other inputs are that the critical
parameter is neither `0` nor `1`. -/
theorem siteCriticality_of_slabReductionBelow (d : ℕ) [NeZero d]
    (hpc0 : 0 < criticalProbSite d) (hpc1 : criticalProbSite d < 1)
    (hred : SiteSlabReductionBelow d) : SiteCriticality d := by
  by_contra hne
  have hpos : 0 < thetaSite d (criticalProbSiteI d) :=
    lt_of_le_of_ne (thetaSiteOn_nonneg _ _ _) (Ne.symm hne)
  obtain ⟨k, q, hq, hqpos⟩ := hred (criticalProbSiteI d) hpc0 hpc1 hpos
  exact absurd hq (not_lt.2 (criticalProbSite_le_of_pos d q
    (lt_of_lt_of_le hqpos (thetaSiteOn_slab_le d k q))))

/-! ### A note on the slab family

`slabGraph d k` is the induced graph on `{x | 0 ≤ x 0 ≤ k}`, which is thin in one coordinate.  The
manuscript produces a slab thin in `d - 2` coordinates, and that one is contained in a translate of
this one, so the reduction stated here is implied by the manuscript's.  Both `SiteSlabReduction` and
`SiteSlabCriticality` refer to the same family, which is what the endgame needs. -/

end KNAll.Site

end
