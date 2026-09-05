import Hypergraph.SiteFiniteEnergy
import Percolation.Literature.UniquenessInfiniteCluster

/-!
# Uniqueness of the infinite open cluster for site percolation on `ℤ^d`

Discharge of `KNAll.Site.SiteUniquenessInfiniteCluster` (`KN/SiteFiniteEnergy.lean`): for
nearest-neighbour Bernoulli **site** percolation on `ℤ^d`, every `d` and every `p`, almost surely
at most one open cluster is infinite.  The bond statement is
`Percolation.Literature.Grimmett1999_numInfiniteClusters_le_one_holds`
(`Percolation/Literature/UniquenessInfiniteCluster.lean`) and the argument here is its site form.

1. Translation-invariant events have probability `0` or `1`
   (`siteBernoulli_zero_one_of_relabel_shift`).  The abstract input is
   `Percolation.Literature.ergodic_coordShift_infinitePi` (`ZeroOneLaw.lean`), which is stated for
   an arbitrary index type; what is added is the identification of the translation of
   configurations with a coordinate shift (`semiconj_setOf_shift`) and the fact that a large
   multiple of a non-zero vector moves a finite set of sites off itself
   (`exists_iterate_shift_symm_notMem`).
2. `P(`exactly two infinite clusters`) = 0` (`siteBernoulli_exactlyTwoInfSiteClusters_eq_zero`):
   otherwise some box `Λ_n` meets both clusters with positive probability, and opening every
   vertex of `Λ_n` merges them (`openSites_mem_exactlyOneInfSiteCluster`), so
   `P(`exactly one`) > 0` by insertion tolerance (`real_pos_of_openSites`, built on
   `KNAll.Site.prod_mul_real_preimage_openSites_le`); both events are translation invariant, so
   both would have probability `1`.
3. `P(`at least three infinite clusters`) = 0` (`siteBernoulli_threeInfSiteClusters_eq_zero`):
   otherwise some `Λ_r` meets three of them with positive probability, and opening `Λ_r` produces
   a cut-ball (`IsSiteCutSet`, `siteCutBall`: every vertex of the ball is open, and deleting the
   ball leaves at least three infinite branches attached to it) with probability `a > 0`, at least
   `a` at every centre by translation invariance.  Placing `(2m+1)^d` disjoint translates of `Λ_r`
   in `Λ_n`, `n = (2r+2)m + r`, the expected number of cut-balls is at least `a (2m+1)^d`, while
   deterministically the number of cut-balls inside `Λ_n` is at most `|∂ⁱⁿΛ_{n+1}|`
   (`card_filter_siteCutBall_le`): each cut-ball is a hub of the open graph of `Λ_{n+1}` relative
   to `∂ⁱⁿΛ_{n+1}` (`IsSiteCutSet.isHub`), and
   `Percolation.Literature.card_add_two_le_card_of_isHub` applies.  For `m` large the two bounds
   contradict each other.

Deleting a set `K` of vertices is, for site percolation, simply a change of graph:
`withinGraph (openSiteGraph G ω) S = openSiteGraph (withinGraph G S) ω`
(`withinGraph_openSiteGraph`).  The constrained-cluster vocabulary of
`Percolation/Literature/ConstrainedClusters.lean`, which the bond proof needs for `ω - K`, is
therefore not required: the events "`x` is joined to `y` after deleting `K`" and "the cluster of
`x` after deleting `K` is infinite" are the events `siteReach` and `sitePerc` of the graph
`withinGraph G Kᶜ`, and inherit their measurability.  For the same reason no side condition
`ω ⊆ G.edgeSet` appears: every set of vertices is a site configuration.

Only the opening half of finite energy is used.  The single probabilistic input is
`KNAll.Site.prod_mul_real_preimage_openSites_le`,
`(∏_{i ∈ F} w i) · P({ω | ω ∪ F ∈ E}) ≤ P(E)`; the two-sided form `KNAll.Site.siteFiniteEnergy`
and the splitting identity `KNAll.Site.siteBernoulli_real_eq_pinned` are not needed.

Reused unchanged from the bond development: the counting lemma and the walk lemmas of
`BurtonKeaneCombinatorics.lean` (`IsHub`, `card_add_two_le_card_of_isHub`,
`exists_adj_reachable_withinGraph_of_walk`, `withinGraph_withinGraph`, `withinGraph_mono_left`),
which are stated for an arbitrary `SimpleGraph` and are applied here to
`withinGraph (openSiteGraph G ω) ↑Λ`; the lattice bookkeeping of
`UniquenessInfiniteCluster.lean` (`shiftedBox_reachable`, `disjoint_shiftedBox_of_ne`,
`shiftedBox_injective`, `mem_box_succ_of_adj`, `centres`, `card_centres`, `centres_subset_box`,
`box_withinGraph_reachable`, `single_ne_zero`), which speaks about `ℤ^d` alone; and
`card_innerBoundary_box_le`, `image_add_box_subset` (`SiteConnectionTools.lean`).

## References

* B. Bollobás, O. Riordan, *Percolation*, Cambridge Univ. Press (2006), Ch. 5, §5.1, Lemmas 1–3
  and Thm. 4, printed pp. 117–124 (there the model is site percolation).
  [cite: BollobasRiordanPercolation2006, Ch. 5 §5.1]
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2, Thm. (8.1), pp. 198–202.
  [cite: GrimmettPercolation1999, §8.2 Thm. (8.1) pp. 198-202]
* R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505. [cite: BurtonKeane1989]
* M. Aizenman, H. Kesten, C. M. Newman, Comm. Math. Phys. 111 (1987) 505–531, Prop. 1.1.
  [cite: AizenmanKestenNewmanCMP1987, Prop. 1.1]
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set SimpleGraph
open Percolation.Literature Percolation.Literature.LatticeModels

variable {V W : Type*}

/-- Deleting the vertices outside `S` from the open site graph is site percolation on the graph
`withinGraph G S`. -/
theorem withinGraph_openSiteGraph (G : SimpleGraph V) (ω : SiteConfig V) (S : Set V) :
    withinGraph (openSiteGraph G ω) S = openSiteGraph (withinGraph G S) ω := by
  ext x y
  simp only [withinGraph_adj, openSiteGraph_adj_iff']
  tauto

/-- The support of the component of `x`. -/
theorem supp_connectedComponentMk (G : SimpleGraph V) (x : V) :
    (G.connectedComponentMk x).supp = {y | G.Reachable x y} := by
  ext y
  simp only [ConnectedComponent.mem_supp_iff, Set.mem_setOf_eq]
  exact ⟨fun h => (ConnectedComponent.eq.1 h).symm, fun h => ConnectedComponent.eq.2 h.symm⟩

/-! ## Connection and percolation events -/

/-- The event that `x` is joined to `y` by a path of open vertices, including the trivial case
`x = y` (where no vertex has to be open). -/
def siteReach (G : SimpleGraph V) (x y : V) : Set (SiteConfig V) :=
  {ω | (openSiteGraph G ω).Reachable x y}

/-- For distinct endpoints, reachability is `siteConn`: a non-trivial open walk from `x` opens
`x`. -/
theorem siteReach_eq_of_ne (G : SimpleGraph V) {x y : V} (hxy : x ≠ y) :
    siteReach G x y = siteConn G x y := by
  ext ω
  simp only [siteReach, siteConn, Set.mem_setOf_eq]
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hxy
  | cons hadj q => exact ((openSiteGraph_adj_iff' G ω _ _).1 hadj).2.1

/-- The connection event is measurable. -/
theorem measurableSet_siteReach [Countable V] (G : SimpleGraph V) (x y : V) :
    MeasurableSet (siteReach G x y) := by
  by_cases hxy : x = y
  · subst hxy
    have h : siteReach G x x = Set.univ := by
      ext ω; simp [siteReach]
    rw [h]
    exact MeasurableSet.univ
  · rw [siteReach_eq_of_ne G hxy]
    exact measurableSet_siteConn G x y

/-- The event that the open cluster of `x`, in the sense of the component of `x` in the open site
graph, is infinite. -/
def sitePerc (G : SimpleGraph V) (x : V) : Set (SiteConfig V) :=
  {ω | ((openSiteGraph G ω).connectedComponentMk x).supp.Infinite}

/-- Membership in `sitePerc`, unfolded. -/
theorem mem_sitePerc_iff (G : SimpleGraph V) (ω : SiteConfig V) (x : V) :
    ω ∈ sitePerc G x ↔ {y | (openSiteGraph G ω).Reachable x y}.Infinite := by
  rw [sitePerc, Set.mem_setOf_eq, supp_connectedComponentMk]

/-- The cluster of `x` is infinite exactly when it leaves every finite set. -/
theorem sitePerc_eq_iInter (G : SimpleGraph V) (x : V) :
    sitePerc G x = ⋂ F : Finset V, ⋃ y ∈ (↑F : Set V)ᶜ, siteReach G x y := by
  ext ω
  rw [mem_sitePerc_iff]
  simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff, Finset.mem_coe, exists_prop,
    siteReach, Set.mem_setOf_eq]
  constructor
  · intro hinf F
    obtain ⟨y, hy, hyF⟩ := hinf.exists_notMem_finset F
    exact ⟨y, hyF, hy⟩
  · intro h hfin
    obtain ⟨y, hyF, hy⟩ := h hfin.toFinset
    exact hyF (hfin.mem_toFinset.2 hy)

/-- The infinite-cluster event is measurable. -/
theorem measurableSet_sitePerc [Countable V] (G : SimpleGraph V) (x : V) :
    MeasurableSet (sitePerc G x) := by
  rw [sitePerc_eq_iInter]
  exact MeasurableSet.iInter fun F =>
    MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_siteReach G x y

/-- `N ≤ 1` iff any two percolating vertices are joined. -/
theorem numInfiniteSiteClusters_le_one_iff (G : SimpleGraph V) (ω : SiteConfig V) :
    numInfiniteSiteClusters G ω ≤ 1 ↔
      ∀ x y, ω ∈ sitePerc G x → ω ∈ sitePerc G y → (openSiteGraph G ω).Reachable x y := by
  rw [numInfiniteSiteClusters, Set.encard_le_one_iff]
  constructor
  · intro h x y hx hy
    exact ConnectedComponent.exact (h _ _ hx hy)
  · intro h C D hC hD
    induction C using ConnectedComponent.ind with
    | h x =>
      induction D using ConnectedComponent.ind with
      | h y => exact ConnectedComponent.sound (h x y hC hD)

/-! ## The events "at least three", "exactly two", "exactly one" infinite open clusters -/

/-- At least three infinite open clusters. -/
def threeInfSiteClusters (G : SimpleGraph V) : Set (SiteConfig V) :=
  {ω | ∃ x y z, ω ∈ sitePerc G x ∧ ω ∈ sitePerc G y ∧ ω ∈ sitePerc G z ∧
    ¬ (openSiteGraph G ω).Reachable x y ∧ ¬ (openSiteGraph G ω).Reachable x z ∧
    ¬ (openSiteGraph G ω).Reachable y z}

/-- Exactly two infinite open clusters. -/
def exactlyTwoInfSiteClusters (G : SimpleGraph V) : Set (SiteConfig V) :=
  {ω | ∃ x y, ω ∈ sitePerc G x ∧ ω ∈ sitePerc G y ∧ ¬ (openSiteGraph G ω).Reachable x y ∧
    ∀ z, ω ∈ sitePerc G z →
      (openSiteGraph G ω).Reachable z x ∨ (openSiteGraph G ω).Reachable z y}

/-- Exactly one infinite open cluster. -/
def exactlyOneInfSiteCluster (G : SimpleGraph V) : Set (SiteConfig V) :=
  {ω | (∃ x, ω ∈ sitePerc G x) ∧
    ∀ x y, ω ∈ sitePerc G x → ω ∈ sitePerc G y → (openSiteGraph G ω).Reachable x y}

/-- If `N ≤ 1` fails there are exactly two or at least three infinite clusters. -/
theorem mem_union_of_not_numInfiniteSiteClusters_le_one {G : SimpleGraph V} {ω : SiteConfig V}
    (h : ¬ numInfiniteSiteClusters G ω ≤ 1) :
    ω ∈ exactlyTwoInfSiteClusters G ∪ threeInfSiteClusters G := by
  rw [numInfiniteSiteClusters_le_one_iff] at h
  push Not at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  by_cases h3 : ∃ z, ω ∈ sitePerc G z ∧ ¬ (openSiteGraph G ω).Reachable z x ∧
      ¬ (openSiteGraph G ω).Reachable z y
  · obtain ⟨z, hz, hzx, hzy⟩ := h3
    exact Or.inr ⟨x, y, z, hx, hy, hz, hxy, fun h => hzx h.symm, fun h => hzy h.symm⟩
  · push Not at h3
    refine Or.inl ⟨x, y, hx, hy, hxy, fun z hz => ?_⟩
    by_cases hzx : (openSiteGraph G ω).Reachable z x
    · exact Or.inl hzx
    · exact Or.inr (h3 z hz hzx)

/-- The events "exactly one" and "exactly two" are disjoint. -/
theorem disjoint_exactlyOne_exactlyTwo_site (G : SimpleGraph V) :
    Disjoint (exactlyOneInfSiteCluster G) (exactlyTwoInfSiteClusters G) := by
  rw [Set.disjoint_left]
  rintro ω ⟨-, h1⟩ ⟨x, y, hx, hy, hxy, -⟩
  exact hxy (h1 x y hx hy)

/-- Measurability of "at least three". -/
theorem measurableSet_threeInfSiteClusters [Countable V] (G : SimpleGraph V) :
    MeasurableSet (threeInfSiteClusters G) := by
  unfold threeInfSiteClusters
  simp only [Set.setOf_exists]
  refine MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun z => ?_
  simp only [Set.setOf_and]
  exact (measurableSet_sitePerc G x).inter ((measurableSet_sitePerc G y).inter
    ((measurableSet_sitePerc G z).inter ((measurableSet_siteReach G x y).compl.inter
    ((measurableSet_siteReach G x z).compl.inter (measurableSet_siteReach G y z).compl))))

/-- Measurability of "exactly two". -/
theorem measurableSet_exactlyTwoInfSiteClusters [Countable V] (G : SimpleGraph V) :
    MeasurableSet (exactlyTwoInfSiteClusters G) := by
  unfold exactlyTwoInfSiteClusters
  simp only [Set.setOf_exists]
  refine MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y => ?_
  simp only [Set.setOf_and, Set.setOf_forall, imp_iff_not_or, Set.setOf_or]
  exact (measurableSet_sitePerc G x).inter ((measurableSet_sitePerc G y).inter
    ((measurableSet_siteReach G x y).compl.inter (MeasurableSet.iInter fun z =>
      (measurableSet_sitePerc G z).compl.union
        ((measurableSet_siteReach G z x).union (measurableSet_siteReach G z y)))))

/-- Measurability of "exactly one". -/
theorem measurableSet_exactlyOneInfSiteCluster [Countable V] (G : SimpleGraph V) :
    MeasurableSet (exactlyOneInfSiteCluster G) := by
  unfold exactlyOneInfSiteCluster
  simp only [Set.setOf_and, Set.setOf_exists, Set.setOf_forall, imp_iff_not_or, Set.setOf_or]
  exact (MeasurableSet.iUnion fun x => measurableSet_sitePerc G x).inter
    (MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      (measurableSet_sitePerc G x).compl.union
        ((measurableSet_sitePerc G y).compl.union (measurableSet_siteReach G x y)))

/-! ## Transport of clusters along a graph isomorphism -/

section Relabel

variable {G : SimpleGraph V} {G' : SimpleGraph W}

/-- Adjacency is transported by relabelling along an adjacency-preserving bijection. -/
theorem openSiteGraph_relabel_adj_iff (e : V ≃ W) (he : ∀ a b, G'.Adj (e a) (e b) ↔ G.Adj a b)
    (ω : SiteConfig V) (a b : V) :
    (openSiteGraph G' (SiteConfig.relabel e ω)).Adj (e a) (e b) ↔ (openSiteGraph G ω).Adj a b := by
  have hmem : ∀ c : V, (e c ∈ SiteConfig.relabel e ω) ↔ c ∈ ω := by
    intro c
    rw [SiteConfig.mem_relabel_iff, Equiv.symm_apply_apply]
  rw [openSiteGraph_adj_iff', openSiteGraph_adj_iff', hmem, hmem, he]

/-- An adjacency-preserving bijection is an isomorphism of the open site graphs. -/
def openSiteGraphRelabelIso (e : V ≃ W) (he : ∀ a b, G'.Adj (e a) (e b) ↔ G.Adj a b)
    (ω : SiteConfig V) : openSiteGraph G ω ≃g openSiteGraph G' (SiteConfig.relabel e ω) where
  toEquiv := e
  map_rel_iff' := fun {a b} => openSiteGraph_relabel_adj_iff e he ω a b

/-- Open paths are transported by relabelling. -/
theorem siteReach_relabel_iff (e : V ≃ W) (he : ∀ a b, G'.Adj (e a) (e b) ↔ G.Adj a b)
    (ω : SiteConfig V) (x y : V) :
    (openSiteGraph G' (SiteConfig.relabel e ω)).Reachable (e x) (e y) ↔
      (openSiteGraph G ω).Reachable x y :=
  Iso.reachable_iff (φ := openSiteGraphRelabelIso e he ω)

/-- Infinite clusters are transported by relabelling. -/
theorem relabel_mem_sitePerc_iff (e : V ≃ W) (he : ∀ a b, G'.Adj (e a) (e b) ↔ G.Adj a b)
    (ω : SiteConfig V) (x : V) :
    SiteConfig.relabel e ω ∈ sitePerc G' (e x) ↔ ω ∈ sitePerc G x := by
  rw [mem_sitePerc_iff, mem_sitePerc_iff]
  have hset : {w | (openSiteGraph G' (SiteConfig.relabel e ω)).Reachable (e x) w} =
      e '' {y | (openSiteGraph G ω).Reachable x y} := by
    ext w
    constructor
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      rw [Set.mem_setOf_eq, ← siteReach_relabel_iff e he ω x (e.symm w), e.apply_symm_apply]
      exact hw
    · rintro ⟨y, hy, rfl⟩
      exact (siteReach_relabel_iff e he ω x y).2 hy
  rw [hset, Set.infinite_image_iff e.injective.injOn]

end Relabel

section Invariance

variable {G : SimpleGraph V} (e : V ≃ V) (he : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b)

include he

/-- "Exactly two" is invariant under a graph automorphism. -/
theorem preimage_relabel_exactlyTwoInfSiteClusters :
    SiteConfig.relabel e ⁻¹' exactlyTwoInfSiteClusters G = exactlyTwoInfSiteClusters G := by
  ext ω
  simp only [Set.mem_preimage, exactlyTwoInfSiteClusters, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, y, hx, hy, hxy, hall⟩
    refine ⟨e.symm x, e.symm y, ?_, ?_, ?_, fun z hz => ?_⟩
    · rw [← relabel_mem_sitePerc_iff e he, e.apply_symm_apply]; exact hx
    · rw [← relabel_mem_sitePerc_iff e he, e.apply_symm_apply]; exact hy
    · rw [← siteReach_relabel_iff e he, e.apply_symm_apply, e.apply_symm_apply]; exact hxy
    · have hz' : SiteConfig.relabel e ω ∈ sitePerc G (e z) :=
        (relabel_mem_sitePerc_iff e he ω z).2 hz
      rcases hall (e z) hz' with hh | hh
      · left
        rw [← siteReach_relabel_iff e he ω z (e.symm x), e.apply_symm_apply]; exact hh
      · right
        rw [← siteReach_relabel_iff e he ω z (e.symm y), e.apply_symm_apply]; exact hh
  · rintro ⟨x, y, hx, hy, hxy, hall⟩
    refine ⟨e x, e y, (relabel_mem_sitePerc_iff e he ω x).2 hx,
      (relabel_mem_sitePerc_iff e he ω y).2 hy, ?_, fun z hz => ?_⟩
    · rw [siteReach_relabel_iff e he]; exact hxy
    · have hz' : ω ∈ sitePerc G (e.symm z) := by
        rw [← relabel_mem_sitePerc_iff e he, e.apply_symm_apply]; exact hz
      rcases hall _ hz' with hh | hh
      · left
        have h := (siteReach_relabel_iff e he ω (e.symm z) x).2 hh
        rwa [e.apply_symm_apply] at h
      · right
        have h := (siteReach_relabel_iff e he ω (e.symm z) y).2 hh
        rwa [e.apply_symm_apply] at h

/-- "Exactly one" is invariant under a graph automorphism. -/
theorem preimage_relabel_exactlyOneInfSiteCluster :
    SiteConfig.relabel e ⁻¹' exactlyOneInfSiteCluster G = exactlyOneInfSiteCluster G := by
  ext ω
  simp only [Set.mem_preimage, exactlyOneInfSiteCluster, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨x, hx⟩, hall⟩
    refine ⟨⟨e.symm x, ?_⟩, fun a b ha hb => ?_⟩
    · rw [← relabel_mem_sitePerc_iff e he, e.apply_symm_apply]; exact hx
    · rw [← siteReach_relabel_iff e he]
      exact hall _ _ ((relabel_mem_sitePerc_iff e he ω a).2 ha)
        ((relabel_mem_sitePerc_iff e he ω b).2 hb)
  · rintro ⟨⟨x, hx⟩, hall⟩
    refine ⟨⟨e x, (relabel_mem_sitePerc_iff e he ω x).2 hx⟩, fun a b ha hb => ?_⟩
    have ha' : ω ∈ sitePerc G (e.symm a) := by
      rw [← relabel_mem_sitePerc_iff e he, e.apply_symm_apply]; exact ha
    have hb' : ω ∈ sitePerc G (e.symm b) := by
      rw [← relabel_mem_sitePerc_iff e he, e.apply_symm_apply]; exact hb
    have h := (siteReach_relabel_iff e he ω (e.symm a) (e.symm b)).2 (hall _ _ ha' hb')
    rwa [e.apply_symm_apply, e.apply_symm_apply] at h

end Invariance

/-! ## Opening a set of vertices -/

section Open

variable {G : SimpleGraph V}

/-- Opening more vertices keeps a vertex percolating. -/
theorem sitePerc_mono {ω ω' : SiteConfig V} (h : ω ⊆ ω') {x : V} (hx : ω ∈ sitePerc G x) :
    ω' ∈ sitePerc G x := by
  rw [mem_sitePerc_iff] at hx ⊢
  exact hx.mono fun y hy => hy.mono (openSiteGraph_mono G h)

/-- If `x` is joined in `ω ∪ F` to no vertex of `F`, then opening `F` does not change the
cluster of `x`. -/
theorem siteReach_openSites_iff {F : Set V} {ω : SiteConfig V} {x : V}
    (h : ∀ a ∈ F, ¬ (openSiteGraph G (openSites F ω)).Reachable x a) (y : V) :
    (openSiteGraph G (openSites F ω)).Reachable x y ↔ (openSiteGraph G ω).Reachable x y := by
  refine ⟨?_, fun hr => hr.mono (openSiteGraph_mono G Set.subset_union_left)⟩
  have key : ∀ (u y : V), (openSiteGraph G (openSites F ω)).Walk u y →
      (∀ a ∈ F, ¬ (openSiteGraph G (openSites F ω)).Reachable u a) →
      (openSiteGraph G ω).Reachable u y := by
    intro u y p
    induction p with
    | nil => intro _; exact Reachable.refl _
    | @cons a b c hadj q ih =>
      intro hu
      have hab := (openSiteGraph_adj_iff' G _ a b).1 hadj
      have ha : a ∈ ω := by
        rcases (mem_openSites F ω a).1 hab.2.1 with h1 | h1
        · exact h1
        · exact absurd (Reachable.refl a) (hu a h1)
      have hb : b ∈ ω := by
        rcases (mem_openSites F ω b).1 hab.2.2 with h1 | h1
        · exact h1
        · exact absurd (Adj.reachable hadj) (hu b h1)
      have hb' : ∀ z ∈ F, ¬ (openSiteGraph G (openSites F ω)).Reachable b z := fun z hz hr =>
        hu z hz ((Adj.reachable hadj).trans hr)
      exact (Adj.reachable ((openSiteGraph_adj_iff' G ω a b).2 ⟨hab.1, ha, hb⟩)).trans (ih hb')
  rintro ⟨p⟩
  exact key x y p h

/-- Under the same hypothesis, `x` percolates in `ω ∪ F` iff it percolates in `ω`. -/
theorem openSites_mem_sitePerc_iff {F : Set V} {ω : SiteConfig V} {x : V}
    (h : ∀ a ∈ F, ¬ (openSiteGraph G (openSites F ω)).Reachable x a) :
    openSites F ω ∈ sitePerc G x ↔ ω ∈ sitePerc G x := by
  rw [mem_sitePerc_iff, mem_sitePerc_iff]
  have hset : {y | (openSiteGraph G (openSites F ω)).Reachable x y} =
      {y | (openSiteGraph G ω).Reachable x y} := by
    ext y; exact siteReach_openSites_iff h y
  rw [hset]

/-- If every vertex of `B` is opened and `B` is connected in `G` through vertices of `B`, then
`B` is connected in the open site graph. -/
theorem reachable_openSites_of_connected {B : Finset V}
    (hB : ∀ x ∈ B, ∀ y ∈ B, (withinGraph G ↑B).Reachable x y) (ω : SiteConfig V) {x y : V}
    (hx : x ∈ B) (hy : y ∈ B) :
    (openSiteGraph G (openSites (↑B : Set V) ω)).Reachable x y := by
  refine (hB x hx y hy).mono ?_
  rintro a b ⟨hab, ha, hb⟩
  rw [openSiteGraph_adj_iff']
  exact ⟨hab, (mem_openSites _ ω a).2 (Or.inr ha), (mem_openSites _ ω b).2 (Or.inr hb)⟩

/-- **Merge lemma.**  If `ω` has an infinite open cluster and every infinite open cluster meets
the finite set `B`, connected in `G` through vertices of `B`, then opening every vertex of `B`
leaves exactly one infinite open cluster. -/
theorem openSites_mem_exactlyOneInfSiteCluster {B : Finset V}
    (hB : ∀ x ∈ B, ∀ y ∈ B, (withinGraph G ↑B).Reachable x y) {ω : SiteConfig V}
    (hex : ∃ x, ω ∈ sitePerc G x)
    (hall : ∀ x, ω ∈ sitePerc G x → ∃ b ∈ B, (openSiteGraph G ω).Reachable x b) :
    openSites (↑B : Set V) ω ∈ exactlyOneInfSiteCluster G := by
  set F : Set V := (↑B : Set V) with hF
  have hsub : ω ⊆ openSites F ω := Set.subset_union_left
  have key : ∀ x, openSites F ω ∈ sitePerc G x →
      ∃ b ∈ B, (openSiteGraph G (openSites F ω)).Reachable x b := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have h' : ∀ a ∈ F, ¬ (openSiteGraph G (openSites F ω)).Reachable x a := by
      intro a ha
      exact hcon a ha
    rw [openSites_mem_sitePerc_iff h'] at hx
    obtain ⟨b, hb, hxb⟩ := hall x hx
    exact hcon b hb (hxb.mono (openSiteGraph_mono G hsub))
  refine ⟨?_, fun x y hx hy => ?_⟩
  · obtain ⟨x, hx⟩ := hex
    exact ⟨x, sitePerc_mono hsub hx⟩
  · obtain ⟨a, ha, hxa⟩ := key x hx
    obtain ⟨b, hb, hyb⟩ := key y hy
    exact (hxa.trans (reachable_openSites_of_connected hB ω ha hb)).trans hyb.symm

end Open

/-! ## Deleting a set of vertices -/

section Delete

variable {G : SimpleGraph V}

/-- Deleting vertices only removes edges. -/
theorem openSiteGraph_withinGraph_le (S : Set V) (ω : SiteConfig V) :
    openSiteGraph (withinGraph G S) ω ≤ openSiteGraph G ω := by
  intro a b hab
  rw [openSiteGraph_adj_iff'] at hab ⊢
  exact ⟨(withinGraph_le G S) hab.1, hab.2.1, hab.2.2⟩

/-- Opening the vertices of `K` does not change the open graph with `K` deleted. -/
theorem openSiteGraph_withinGraph_openSites (K : Finset V) (ω : SiteConfig V) :
    openSiteGraph (withinGraph G (↑K : Set V)ᶜ) (openSites (↑K : Set V) ω)
      = openSiteGraph (withinGraph G (↑K : Set V)ᶜ) ω := by
  ext a b
  simp only [openSiteGraph_adj_iff', withinGraph_adj, mem_openSites, Set.mem_compl_iff,
    Finset.mem_coe]
  constructor
  · rintro ⟨⟨hab, ha', hb'⟩, ha, hb⟩
    refine ⟨⟨hab, ha', hb'⟩, ?_, ?_⟩
    · rcases ha with h | h
      · exact h
      · exact absurd h ha'
    · rcases hb with h | h
      · exact h
      · exact absurd h hb'
  · rintro ⟨h, ha, hb⟩
    exact ⟨h, Or.inl ha, Or.inl hb⟩

/-! ## Cut sets -/

/-- `K` is a **cut set** of the site configuration `ω`: every vertex of `K` is open, and there are
three vertices outside `K`, each joined to `K` by an open edge, lying in three distinct infinite
open clusters of the configuration with the vertices of `K` deleted. -/
structure IsSiteCutSet (G : SimpleGraph V) (K : Finset V) (ω : SiteConfig V) : Prop where
  /-- every vertex of `K` is open -/
  open_inside : (↑K : Set V) ⊆ ω
  /-- three open neighbours of `K` in distinct infinite clusters of `ω` with `K` deleted -/
  branches : ∃ w : Fin 3 → V, (∀ i, w i ∉ K) ∧
      (∀ i, ∃ k ∈ K, (openSiteGraph G ω).Adj k (w i)) ∧
      (∀ i j, (openSiteGraph (withinGraph G (↑K : Set V)ᶜ) ω).Reachable (w i) (w j) → i = j) ∧
      (∀ i, ω ∈ sitePerc (withinGraph G (↑K : Set V)ᶜ) (w i))

/-- An infinite open cluster meeting the finite set `K` contains, outside `K`, an infinite open
cluster of the configuration with `K` deleted, attached to `K` by an open edge. -/
theorem exists_branch_of_sitePerc [DecidableEq V] [G.LocallyFinite] (K : Finset V)
    {ω : SiteConfig V} {x : V} (hxK : x ∈ K) (hx : ω ∈ sitePerc G x) :
    ∃ a, a ∉ K ∧ (∃ k ∈ K, (openSiteGraph G ω).Adj k a) ∧ (openSiteGraph G ω).Reachable x a ∧
      ω ∈ sitePerc (withinGraph G (↑K : Set V)ᶜ) a := by
  classical
  set N : Finset V := (LatticeModels.outerBoundary G K).filter fun a =>
    (∃ k ∈ K, (openSiteGraph G ω).Adj k a) ∧ (openSiteGraph G ω).Reachable x a with hN
  have hcover : {y | (openSiteGraph G ω).Reachable x y} \ (↑K : Set V) ⊆
      ⋃ a ∈ N, {y | (openSiteGraph (withinGraph G (↑K : Set V)ᶜ) ω).Reachable a y} := by
    rintro u ⟨hu, huK⟩
    have hu' : (openSiteGraph G ω).Reachable x u := hu
    obtain ⟨q⟩ := hu'.symm
    obtain ⟨a, b, ha, hb, hab, -, hr⟩ := exists_adj_reachable_withinGraph_of_walk
      (openSiteGraph G ω) q (S := (↑K : Set V)ᶜ) huK ⟨x, q.end_mem_support, fun h => h hxK⟩
    have hb' : b ∈ K := by simpa using hb
    have haK : a ∉ K := by simpa using ha
    have hGab : G.Adj a b := ((openSiteGraph_adj_iff' G ω a b).1 hab).1
    have hxa : (openSiteGraph G ω).Reachable x a := hu'.trans (hr.mono (withinGraph_le _ _))
    refine Set.mem_biUnion (x := a) ?_ ?_
    · rw [hN, Finset.mem_coe, Finset.mem_filter, LatticeModels.mem_outerBoundary_iff]
      exact ⟨⟨haK, b, hb', hGab⟩, ⟨b, hb', hab.symm⟩, hxa⟩
    · rw [Set.mem_setOf_eq, ← withinGraph_openSiteGraph]
      exact hr.symm
  have hinf : ({y | (openSiteGraph G ω).Reachable x y} \ (↑K : Set V)).Infinite := by
    rw [mem_sitePerc_iff] at hx
    exact hx.sdiff K.finite_toSet
  by_contra hcon
  push Not at hcon
  refine hinf ((Set.Finite.biUnion N.finite_toSet fun a ha => ?_).subset hcover)
  rw [hN, Finset.mem_coe, Finset.mem_filter, LatticeModels.mem_outerBoundary_iff] at ha
  have hnot := hcon a ha.1.1 ha.2.1 ha.2.2
  rw [mem_sitePerc_iff] at hnot
  exact Set.not_infinite.1 hnot

/-- **Three clusters make a cut set.**  If three vertices of `K` lie in distinct infinite open
clusters of `ω`, then `K` is a cut set of the configuration with every vertex of `K` opened. -/
theorem isSiteCutSet_openSites_of_three [DecidableEq V] [G.LocallyFinite] {K : Finset V}
    {ω : SiteConfig V} {x : Fin 3 → V} (hxK : ∀ i, x i ∈ K) (hperc : ∀ i, ω ∈ sitePerc G (x i))
    (hdis : ∀ i j, (openSiteGraph G ω).Reachable (x i) (x j) → i = j) :
    IsSiteCutSet G K (openSites (↑K : Set V) ω) := by
  choose w hwK hwadj hxw hwperc using fun i => exists_branch_of_sitePerc K (hxK i) (hperc i)
  have hgraph := openSiteGraph_withinGraph_openSites (G := G) K ω
  have hmono : openSiteGraph G ω ≤ openSiteGraph G (openSites (↑K : Set V) ω) :=
    openSiteGraph_mono G Set.subset_union_left
  refine ⟨Set.subset_union_right, w, hwK, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · obtain ⟨k, hk, hadj⟩ := hwadj i
    exact ⟨k, hk, hmono hadj⟩
  · rw [hgraph] at hij
    have hij' : (openSiteGraph G ω).Reachable (w i) (w j) :=
      hij.mono (openSiteGraph_withinGraph_le _ ω)
    exact hdis i j (((hxw i).trans hij').trans (hxw j).symm)
  · rw [mem_sitePerc_iff, hgraph]
    exact (mem_sitePerc_iff _ ω (w i)).1 (hwperc i)

/-- **A cut set is a hub** of the open graph of `Λ` relative to the inner boundary `∂ⁱⁿΛ`. -/
theorem IsSiteCutSet.isHub [DecidableEq V] [G.LocallyFinite] {K Λ : Finset V} {ω : SiteConfig V}
    (hcut : IsSiteCutSet G K ω) (hKne : K.Nonempty) (hKΛ : K ⊆ Λ)
    (hnb : ∀ k ∈ K, ∀ v, G.Adj k v → v ∈ Λ)
    (hKconn : ∀ x ∈ K, ∀ y ∈ K, (withinGraph G ↑K).Reachable x y) :
    IsHub (withinGraph (openSiteGraph G ω) ↑Λ) (LatticeModels.innerBoundary G Λ) K := by
  obtain ⟨w, hwK, hwadj, hwdis, hwperc⟩ := hcut.branches
  have hGadj : ∀ {a b : V}, (openSiteGraph G ω).Adj a b → G.Adj a b := fun h =>
    ((openSiteGraph_adj_iff' G ω _ _).1 h).1
  have hwΛ : ∀ i, w i ∈ Λ := fun i => by
    obtain ⟨k, hk, hadj⟩ := hwadj i
    exact hnb k hk _ (hGadj hadj)
  refine ⟨hKne, ?_, ?_, w, hwK, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro k hk hkL
    rw [LatticeModels.mem_innerBoundary_iff] at hkL
    obtain ⟨-, y, hy, hky⟩ := hkL
    exact hy (hnb k hk y hky)
  · intro x hx y hy
    rw [withinGraph_withinGraph]
    refine (hKconn x hx y hy).mono ?_
    rintro a b ⟨hab, ha, hb⟩
    refine ⟨?_, ⟨hKΛ ha, ha⟩, ⟨hKΛ hb, hb⟩⟩
    rw [openSiteGraph_adj_iff']
    exact ⟨hab, hcut.open_inside ha, hcut.open_inside hb⟩
  · intro i
    obtain ⟨k, hk, hadj⟩ := hwadj i
    exact ⟨k, hk, hadj, hKΛ hk, hwΛ i⟩
  · intro i j hij
    refine hwdis i j ?_
    rw [← withinGraph_openSiteGraph]
    exact hij.mono (withinGraph_mono_left (withinGraph_le _ _) _)
  · intro i
    obtain ⟨u, hu, huΛ⟩ := ((mem_sitePerc_iff _ ω (w i)).1 (hwperc i)).exists_notMem_finset Λ
    have hu' : (withinGraph (openSiteGraph G ω) (↑K : Set V)ᶜ).Reachable (w i) u := by
      rw [withinGraph_openSiteGraph]
      exact hu
    obtain ⟨q⟩ := hu'
    obtain ⟨a, b, ha, hb, hab, -, hr⟩ := exists_adj_reachable_withinGraph_of_walk
      (withinGraph (openSiteGraph G ω) (↑K : Set V)ᶜ) q (S := (↑Λ : Set V)) (hwΛ i)
      ⟨u, q.end_mem_support, huΛ⟩
    refine ⟨a, ?_, ?_⟩
    · rw [LatticeModels.mem_innerBoundary_iff]
      exact ⟨ha, b, hb, hGadj hab.1⟩
    · rw [withinGraph_withinGraph] at hr ⊢
      rwa [Set.inter_comm]

end Delete

/-! ## Translations act ergodically on site percolation -/

section Ergodic

open ProbabilityTheory unitInterval

variable {d : ℕ}

/-- The coordinate encoding `q ↦ {i | q i}` carries the product of the one-vertex laws to
`siteBernoulli`. -/
theorem measurePreserving_setOf_siteBernoulli {ι : Type*} (w : ι → unitInterval) :
    MeasurePreserving (fun q : ι → Prop => {i | q i})
      (Measure.infinitePi fun i : ι =>
        toNNReal (w i) • Measure.dirac True + toNNReal (σ (w i)) • Measure.dirac False)
      (siteBernoulli w) :=
  ⟨measurable_setOf, by rw [siteBernoulli, prodBernoulli_eq_map]⟩

/-- The coordinate shift along `x ↦ x - v` is semiconjugate, through the coordinate encoding, to
the translation of configurations by `v`. -/
theorem semiconj_setOf_shift (v : LatticeModels.Site d) :
    Function.Semiconj (fun q : LatticeModels.Site d → Prop => {i | q i})
      (coordShift (X := Prop) ⇑(LatticeModels.Site.shift v).symm)
      (SiteConfig.relabel (LatticeModels.Site.shift v)) := by
  intro q
  ext x
  rw [SiteConfig.mem_relabel_iff]
  rfl

/-- Iterating the inverse translation. -/
theorem iterate_shift_symm (v : LatticeModels.Site d) (n : ℕ) (x : LatticeModels.Site d) :
    (⇑(LatticeModels.Site.shift v).symm)^[n] x = x - n • v := by
  induction n generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, LatticeModels.Site.shift_symm_apply, succ_nsmul]
    abel

/-- A large multiple of a non-zero vector moves every finite set of sites off itself. -/
theorem exists_iterate_shift_symm_notMem {v : LatticeModels.Site d} (hv : v ≠ 0)
    (s : Finset (LatticeModels.Site d)) :
    ∃ n : ℕ, ∀ x ∈ s, (⇑(LatticeModels.Site.shift v).symm)^[n] x ∉ s := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  set M : ℕ := s.sup fun x => (x k).natAbs with hM
  have hMbd : ∀ x ∈ s, |x k| ≤ (M : ℤ) := by
    intro x hx
    have h : (x k).natAbs ≤ M := Finset.le_sup (f := fun x => (x k).natAbs) hx
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  refine ⟨2 * M + 1, fun x hx hx' => ?_⟩
  rw [iterate_shift_symm] at hx'
  have h1 := hMbd x hx
  have h2 := hMbd _ hx'
  have hcoord : (x - ((2 * M + 1 : ℕ) • v)) k = x k - ((2 * M + 1 : ℕ) : ℤ) * v k := by
    simp [Pi.sub_apply, nsmul_eq_mul]
  rw [hcoord] at h2
  have hvk : 1 ≤ |v k| := Int.one_le_abs hk
  have h3 : |((2 * M + 1 : ℕ) : ℤ) * v k| ≤ 2 * M := by
    calc |((2 * M + 1 : ℕ) : ℤ) * v k|
        = |x k - (x k - ((2 * M + 1 : ℕ) : ℤ) * v k)| := by rw [sub_sub_cancel]
      _ ≤ |x k| + |x k - ((2 * M + 1 : ℕ) : ℤ) * v k| := abs_sub _ _
      _ ≤ (M : ℤ) + (M : ℤ) := add_le_add h1 h2
      _ = 2 * M := by ring
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((2 * M + 1 : ℕ) : ℤ))] at h3
  push_cast at h3
  nlinarith

/-- **Translations preserve site percolation.** -/
theorem measurePreserving_relabel_shift (p : unitInterval) (v : LatticeModels.Site d) :
    MeasurePreserving (SiteConfig.relabel (LatticeModels.Site.shift v))
      (siteBernoulli fun _ : LatticeModels.Site d => p)
      (siteBernoulli fun _ : LatticeModels.Site d => p) := by
  set μ : LatticeModels.Site d → Measure Prop := fun _ =>
    toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False with hμ
  have hsetOf := measurePreserving_setOf_siteBernoulli (fun _ : LatticeModels.Site d => p)
  have hshift : MeasurePreserving (coordShift (X := Prop) ⇑(LatticeModels.Site.shift v).symm)
      (Measure.infinitePi μ) (Measure.infinitePi μ) :=
    measurePreserving_coordShift μ (LatticeModels.Site.shift v).symm.injective fun _ => rfl
  refine ⟨(SiteConfig.relabel (LatticeModels.Site.shift v)).measurable, ?_⟩
  rw [← hsetOf.map_eq,
    Measure.map_map (SiteConfig.relabel (LatticeModels.Site.shift v)).measurable measurable_setOf,
    ← (semiconj_setOf_shift v).comp_eq,
    ← Measure.map_map measurable_setOf (measurable_coordShift _), hshift.map_eq]

/-- **Translations of `ℤ^d` act ergodically on site percolation.** -/
theorem ergodic_relabel_shift_siteBernoulli (p : unitInterval) {v : LatticeModels.Site d}
    (hv : v ≠ 0) :
    Ergodic (SiteConfig.relabel (LatticeModels.Site.shift v))
      (siteBernoulli fun _ : LatticeModels.Site d => p) := by
  set μ : LatticeModels.Site d → Measure Prop := fun _ =>
    toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False with hμ
  have herg : Ergodic (coordShift (X := Prop) ⇑(LatticeModels.Site.shift v).symm)
      (Measure.infinitePi μ) :=
    ergodic_coordShift_infinitePi μ (LatticeModels.Site.shift v).symm.injective (fun _ => rfl)
      fun s => exists_iterate_shift_symm_notMem hv s
  exact (measurePreserving_setOf_siteBernoulli (fun _ : LatticeModels.Site d => p)).ergodic_of_ergodic_semiconj
    herg (SiteConfig.relabel (LatticeModels.Site.shift v)).measurable (semiconj_setOf_shift v)

/-- **Zero-one law for translation-invariant events of site percolation on `ℤ^d`.** -/
theorem siteBernoulli_zero_one_of_relabel_shift (p : unitInterval) {v : LatticeModels.Site d}
    (hv : v ≠ 0) {A : Set (SiteConfig (LatticeModels.Site d))} (hA : MeasurableSet A)
    (hinv : SiteConfig.relabel (LatticeModels.Site.shift v) ⁻¹' A = A) :
    (siteBernoulli fun _ : LatticeModels.Site d => p) A = 0 ∨
      (siteBernoulli fun _ : LatticeModels.Site d => p) A = 1 :=
  (ergodic_relabel_shift_siteBernoulli p hv).toPreErgodic.prob_eq_zero_or_one hA hinv

end Ergodic

/-! ## Transport of cut sets, and measurability -/

section CutSetTransport

/-- Cut sets are transported by graph isomorphisms. -/
theorem IsSiteCutSet.map [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph W}
    (e : V ≃ W) (he : ∀ a b, G'.Adj (e a) (e b) ↔ G.Adj a b) {K : Finset V} {ω : SiteConfig V}
    (h : IsSiteCutSet G K ω) :
    IsSiteCutSet G' (K.image e) (SiteConfig.relabel e ω) := by
  obtain ⟨w, hwK, hwadj, hwdis, hwperc⟩ := h.branches
  have hK : ∀ a : V, (e a ∈ K.image e) ↔ a ∈ K := fun a =>
    Function.Injective.mem_finset_image e.injective
  have he' : ∀ a b, (withinGraph G' (↑(K.image e) : Set W)ᶜ).Adj (e a) (e b) ↔
      (withinGraph G (↑K : Set V)ᶜ).Adj a b := by
    intro a b
    simp only [withinGraph_adj, Set.mem_compl_iff, Finset.mem_coe, he, hK]
  refine ⟨?_, fun i => e (w i), fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [SiteConfig.mem_relabel_iff, Equiv.symm_apply_apply]
    exact h.open_inside hk
  · rw [hK]
    exact hwK i
  · obtain ⟨k, hk, hadj⟩ := hwadj i
    exact ⟨e k, Finset.mem_image_of_mem _ hk,
      (openSiteGraph_relabel_adj_iff e he ω k (w i)).2 hadj⟩
  · exact hwdis i j ((siteReach_relabel_iff e he' ω (w i) (w j)).1 hij)
  · exact (relabel_mem_sitePerc_iff e he' ω (w i)).2 (hwperc i)

/-- The event that a given open edge is present is measurable. -/
theorem measurableSet_setOf_openSiteGraph_adj (G : SimpleGraph V) (x y : V) :
    MeasurableSet {ω : SiteConfig V | (openSiteGraph G ω).Adj x y} := by
  have h : {ω : SiteConfig V | (openSiteGraph G ω).Adj x y} =
      {_ω : SiteConfig V | G.Adj x y} ∩
        ({ω : SiteConfig V | x ∈ ω} ∩ {ω : SiteConfig V | y ∈ ω}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, openSiteGraph_adj_iff']
  rw [h]
  exact (MeasurableSet.const _).inter ((measurableSet_mem x).inter (measurableSet_mem y))

/-- The event that every vertex of a finite set is open is measurable. -/
theorem measurableSet_setOf_finset_subset (K : Finset V) :
    MeasurableSet {ω : SiteConfig V | (↑K : Set V) ⊆ ω} := by
  have h : {ω : SiteConfig V | (↑K : Set V) ⊆ ω} =
      ⋂ x ∈ (↑K : Set V), {ω : SiteConfig V | x ∈ ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.subset_def]
  rw [h]
  exact MeasurableSet.biInter (Finset.countable_toSet K) fun x _ => measurableSet_mem x

/-- The cut-set event is measurable. -/
theorem measurableSet_isSiteCutSet [Countable V] (G : SimpleGraph V) (K : Finset V) :
    MeasurableSet {ω : SiteConfig V | IsSiteCutSet G K ω} := by
  classical
  set S : SimpleGraph V := withinGraph G (↑K : Set V)ᶜ with hS
  have heq : {ω : SiteConfig V | IsSiteCutSet G K ω} =
      {ω : SiteConfig V | (↑K : Set V) ⊆ ω} ∩
        ⋃ w : Fin 3 → V, ((⋂ i, {_ω : SiteConfig V | w i ∉ K}) ∩
          (⋂ i, ⋃ k ∈ K, {ω : SiteConfig V | (openSiteGraph G ω).Adj k (w i)}) ∩
          (⋂ i, ⋂ j, {_ω : SiteConfig V | i = j} ∪ (siteReach S (w i) (w j))ᶜ) ∩
          (⋂ i, sitePerc S (w i))) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff, siteReach, exists_prop]
    constructor
    · rintro ⟨h1, w, h2, h3, h4, h5⟩
      refine ⟨h1, w, ⟨⟨h2, h3⟩, fun i j => ?_⟩, h5⟩
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr fun h => hij (h4 i j h)
    · rintro ⟨h1, w, ⟨⟨h2, h3⟩, h4⟩, h5⟩
      refine ⟨h1, w, h2, h3, fun i j h => ?_, h5⟩
      rcases h4 i j with hij | hij
      · exact hij
      · exact absurd h hij
  rw [heq]
  refine (measurableSet_setOf_finset_subset K).inter (MeasurableSet.iUnion fun w => ?_)
  refine (((MeasurableSet.iInter fun i => MeasurableSet.const _).inter
    (MeasurableSet.iInter fun i => MeasurableSet.biUnion (Finset.countable_toSet K)
      fun k _ => measurableSet_setOf_openSiteGraph_adj G k (w i))).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => (MeasurableSet.const _).union
      (measurableSet_siteReach S (w i) (w j)).compl)).inter
    (MeasurableSet.iInter fun i => measurableSet_sitePerc S (w i))

end CutSetTransport

/-! ## The cut-ball event on `ℤ^d` -/

section Lattice

open scoped ENNReal

variable {d : ℕ}

/-- The **cut-ball event** `T_r(c)`: the box `Λ_r(c)` is a cut set of the configuration. -/
def siteCutBall (c : LatticeModels.Site d) (r : ℕ) : Set (SiteConfig (LatticeModels.Site d)) :=
  {ω | IsSiteCutSet (LatticeModels.zdGraph d) (shiftedBox c r) ω}

/-- The cut-ball event is measurable. -/
theorem measurableSet_siteCutBall (c : LatticeModels.Site d) (r : ℕ) :
    MeasurableSet (siteCutBall c r) :=
  measurableSet_isSiteCutSet _ _

/-- Translating a configuration by `v` carries the cut-ball event at `c` into the cut-ball event
at `c + v`. -/
theorem siteCutBall_subset_preimage_shift (c v : LatticeModels.Site d) (r : ℕ) :
    siteCutBall c r ⊆
      SiteConfig.relabel (LatticeModels.Site.shift v) ⁻¹' siteCutBall (c + v) r := by
  intro ω hω
  have h := IsSiteCutSet.map (LatticeModels.Site.shift v)
    (fun a b => LatticeModels.zdGraph_adj_shift_iff v a b) hω
  have hbox : (shiftedBox c r).image (LatticeModels.Site.shift v) = shiftedBox (c + v) r := by
    rw [← shiftedBox_image_add]
    rfl
  rw [hbox] at h
  exact h

/-- **Translation invariance of the cut-ball probability.** -/
theorem real_siteCutBall_zero_le (p : unitInterval) (c : LatticeModels.Site d) (r : ℕ) :
    (siteBernoulli fun _ : LatticeModels.Site d => p).real (siteCutBall 0 r) ≤
      (siteBernoulli fun _ : LatticeModels.Site d => p).real (siteCutBall c r) := by
  have hmp := measurePreserving_relabel_shift (d := d) p c
  have hpre : (siteBernoulli fun _ : LatticeModels.Site d => p)
      (SiteConfig.relabel (LatticeModels.Site.shift c) ⁻¹' siteCutBall c r)
      = (siteBernoulli fun _ : LatticeModels.Site d => p) (siteCutBall c r) :=
    hmp.measure_preimage (measurableSet_siteCutBall c r).nullMeasurableSet
  have hpre' : (siteBernoulli fun _ : LatticeModels.Site d => p).real
      (SiteConfig.relabel (LatticeModels.Site.shift c) ⁻¹' siteCutBall c r)
      = (siteBernoulli fun _ : LatticeModels.Site d => p).real (siteCutBall c r) := by
    rw [measureReal_def, measureReal_def, hpre]
  rw [← hpre']
  refine measureReal_mono ?_ (measure_ne_top _ _)
  have h := siteCutBall_subset_preimage_shift (0 : LatticeModels.Site d) c r
  simpa using h

open Classical in
/-- **Deterministic bound on the number of cut-balls.** -/
theorem card_filter_siteCutBall_le (r m : ℕ) (ω : SiteConfig (LatticeModels.Site d)) :
    ((centres r m).filter fun c => ω ∈ siteCutBall c r).card ≤
      (LatticeModels.innerBoundary (LatticeModels.zdGraph d)
        (LatticeModels.box d ((2 * r + 2) * m + r + 1))).card := by
  classical
  set n := (2 * r + 2) * m + r with hn
  set Wc := (centres r m).filter fun c => ω ∈ siteCutBall c r with hWc
  set 𝓚 : Finset (Finset (LatticeModels.Site d)) := Wc.image fun c => shiftedBox c r with h𝓚
  have hcard : 𝓚.card = Wc.card := Finset.card_image_of_injective _ (shiftedBox_injective r)
  rcases Wc.eq_empty_or_nonempty with hW | hW
  · rw [hW]; simp
  have hne : 𝓚.Nonempty := by rwa [h𝓚, Finset.image_nonempty]
  rw [← hcard]
  refine le_trans (Nat.le_add_right _ 2) (card_add_two_le_card_of_isHub
    (withinGraph (openSiteGraph (LatticeModels.zdGraph d) ω)
      ↑(LatticeModels.box d (n + 1))) _ 𝓚 hne ?_ ?_)
  · intro K hK K' hK' hKK'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hK'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hc).1
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hc').1
    exact disjoint_shiftedBox_of_ne fun h => hKK' (by rw [h])
  · intro K hK
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨hcW, hcut⟩ := Finset.mem_filter.1 hc
    have hcbox : c ∈ LatticeModels.box d ((2 * r + 2) * m) := centres_subset_box r m hcW
    have hKn : shiftedBox c r ⊆ LatticeModels.box d n := fun x hx =>
      image_add_box_subset hcbox
        (Finset.mem_image.2 ⟨x - c, mem_shiftedBox_iff.1 hx, sub_add_cancel x c⟩)
    refine IsSiteCutSet.isHub hcut ⟨c, self_mem_shiftedBox c r⟩
      (hKn.trans (LatticeModels.box_mono d (Nat.le_succ n))) (fun k hk v hkv => ?_)
      (fun x hx y hy => ?_)
    · exact mem_box_succ_of_adj (hKn hk) hkv
    · exact shiftedBox_reachable c r hx hy

/-- The expected number of cut-balls among the centres is at most `|∂ⁱⁿΛ_{n+1}|`. -/
theorem sum_measure_siteCutBall_le (p : unitInterval) (r m : ℕ) :
    ∑ c ∈ centres r m, (siteBernoulli fun _ : LatticeModels.Site d => p) (siteCutBall c r) ≤
      (LatticeModels.innerBoundary (LatticeModels.zdGraph d)
        (LatticeModels.box d ((2 * r + 2) * m + r + 1))).card := by
  classical
  set μ := siteBernoulli fun _ : LatticeModels.Site d => p with hμ
  set L := LatticeModels.innerBoundary (LatticeModels.zdGraph d)
    (LatticeModels.box d ((2 * r + 2) * m + r + 1)) with hL
  have h1 : ∑ c ∈ centres r m, μ (siteCutBall c r) =
      ∫⁻ ω, ∑ c ∈ centres r m, (siteCutBall c r).indicator 1 ω ∂μ := by
    rw [lintegral_finsetSum _ fun c _ => measurable_one.indicator (measurableSet_siteCutBall c r)]
    exact Finset.sum_congr rfl fun c _ =>
      (lintegral_indicator_one (measurableSet_siteCutBall c r)).symm
  calc ∑ c ∈ centres r m, μ (siteCutBall c r)
      = ∫⁻ ω, ∑ c ∈ centres r m, (siteCutBall c r).indicator 1 ω ∂μ := h1
    _ ≤ ∫⁻ _ω, (L.card : ℝ≥0∞) ∂μ := by
        refine lintegral_mono fun ω => ?_
        have hsum : ∑ c ∈ centres r m,
            (siteCutBall c r).indicator (1 : SiteConfig (LatticeModels.Site d) → ℝ≥0∞) ω =
              (((centres r m).filter fun c => ω ∈ siteCutBall c r).card : ℝ≥0∞) := by
          simp only [Set.indicator_apply, Pi.one_apply]
          rw [Finset.sum_boole]
        rw [hsum, hL]
        exact Nat.cast_le.2 (card_filter_siteCutBall_le r m ω)
    _ = L.card := by rw [lintegral_const, measure_univ, mul_one]

end Lattice

/-! ## Degenerate parameter and insertion tolerance -/

section Tools

/-- The empty configuration has no infinite cluster. -/
theorem empty_notMem_sitePerc (G : SimpleGraph V) (x : V) :
    (∅ : SiteConfig V) ∉ sitePerc G x := by
  rw [mem_sitePerc_iff]
  have hbot : openSiteGraph G (∅ : SiteConfig V) = ⊥ := by
    ext a b
    simp [openSiteGraph_adj_iff']
  rw [hbot]
  have hs : {y | (⊥ : SimpleGraph V).Reachable x y} = {x} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, reachable_bot]
    exact eq_comm
  rw [hs]
  exact Set.not_infinite.2 (Set.finite_singleton x)

/-- At `p = 0` the configuration is almost surely empty, so events avoiding `∅` are null. -/
theorem siteBernoulli_eq_zero_of_coe_eq_zero [Countable V] {p : unitInterval} (hp : (p : ℝ) = 0)
    {s : Set (SiteConfig V)} (hs : (∅ : SiteConfig V) ∉ s) :
    (siteBernoulli fun _ : V => p) s = 0 := by
  have hzero : ∀ x : V, (siteBernoulli fun _ : V => p) {ω : SiteConfig V | x ∈ ω} = 0 := by
    intro x
    have hr : (siteBernoulli fun _ : V => p).real {ω : SiteConfig V | x ∈ ω} = 0 := by
      rw [siteBernoulli, prodBernoulli_real_setOf_mem]
      exact hp
    rw [measureReal_def] at hr
    rcases (ENNReal.toReal_eq_zero_iff _).1 hr with h | h
    · exact h
    · exact absurd h (measure_ne_top _ _)
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hzero)
  have hne : ω ≠ (∅ : SiteConfig V) := fun h => hs (h ▸ hω)
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  exact Set.mem_iUnion.2 ⟨x, hx⟩

/-- **Insertion tolerance for a finite set of vertices.**  If `p > 0`, the event `A` has positive
probability and opening every vertex of `F` carries `A` into the measurable event `E`, then `E`
has positive probability. -/
theorem real_pos_of_openSites (p : unitInterval) (hp : 0 < (p : ℝ)) (F : Finset V)
    {A E : Set (SiteConfig V)} (hE : MeasurableSet E)
    (hA : 0 < (siteBernoulli fun _ : V => p).real A)
    (hAE : ∀ ω ∈ A, openSites (↑F : Set V) ω ∈ E) :
    0 < (siteBernoulli fun _ : V => p).real E := by
  have h1 : (siteBernoulli fun _ : V => p).real A ≤
      (siteBernoulli fun _ : V => p).real (openSites (↑F : Set V) ⁻¹' E) :=
    measureReal_mono (fun ω hω => hAE ω hω) (measure_ne_top _ _)
  have h2 := prod_mul_real_preimage_openSites_le (fun _ : V => p) F hE
  have h3 : (0 : ℝ) < ∏ _i ∈ F, ((p : ℝ)) := Finset.prod_pos fun _ _ => hp
  nlinarith

end Tools

/-! ## `P_p(at least three infinite clusters) = 0` -/

section Three

variable {d : ℕ}

/-- The event that `Λ_r` meets three distinct infinite open clusters. -/
def threeInSiteBox (r : ℕ) : Set (SiteConfig (LatticeModels.Site d)) :=
  {ω | ∃ x : Fin 3 → LatticeModels.Site d, (∀ i, x i ∈ LatticeModels.box d r) ∧
    (∀ i, ω ∈ sitePerc (LatticeModels.zdGraph d) (x i)) ∧
    ∀ i j, (openSiteGraph (LatticeModels.zdGraph d) ω).Reachable (x i) (x j) → i = j}

/-- Three infinite clusters meet some common box. -/
theorem threeInfSiteClusters_subset_iUnion :
    threeInfSiteClusters (LatticeModels.zdGraph d) ⊆ ⋃ r, threeInSiteBox (d := d) r := by
  have hcov : ∀ v : LatticeModels.Site d, ∃ n, v ∈ LatticeModels.box d n := fun v => by
    have hv : v ∈ ⋃ L : ℕ,
        ((LatticeModels.box d L : Finset (LatticeModels.Site d)) : Set (LatticeModels.Site d)) := by
      rw [LatticeModels.iUnion_coe_box]
      exact Set.mem_univ v
    simpa using hv
  rintro ω ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
  obtain ⟨n₁, h₁⟩ := hcov x
  obtain ⟨n₂, h₂⟩ := hcov y
  obtain ⟨n₃, h₃⟩ := hcov z
  set n := max n₁ (max n₂ n₃) with hn
  have h₁' : x ∈ LatticeModels.box d n := LatticeModels.box_mono d (le_max_left _ _) h₁
  have h₂' : y ∈ LatticeModels.box d n :=
    LatticeModels.box_mono d ((le_max_left _ _).trans (le_max_right _ _)) h₂
  have h₃' : z ∈ LatticeModels.box d n :=
    LatticeModels.box_mono d ((le_max_right _ _).trans (le_max_right _ _)) h₃
  refine Set.mem_iUnion.2 ⟨n, ![x, y, z], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢
    all_goals first
      | exact hxy h | exact hxy h.symm | exact hxz h | exact hxz h.symm | exact hyz h
      | exact hyz h.symm

/-- **`P_p(there are at least three infinite open clusters) = 0`** on `ℤ^d`, `d ≥ 1`. -/
theorem siteBernoulli_threeInfSiteClusters_eq_zero (hd : 1 ≤ d) (p : unitInterval) :
    (siteBernoulli fun _ : LatticeModels.Site d => p)
      (threeInfSiteClusters (LatticeModels.zdGraph d)) = 0 := by
  classical
  set μ := siteBernoulli fun _ : LatticeModels.Site d => p with hμ
  by_contra h3
  rcases eq_or_lt_of_le p.2.1 with hp0 | hp
  · refine h3 (siteBernoulli_eq_zero_of_coe_eq_zero hp0.symm ?_)
    rintro ⟨x, y, z, hx, -, -, -, -, -⟩
    exact empty_notMem_sitePerc _ x hx
  obtain ⟨r, hr⟩ : ∃ r, μ (threeInSiteBox (d := d) r) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h3 (measure_mono_null threeInfSiteClusters_subset_iUnion
      (measure_iUnion_null_iff.2 hall))
  have hA : 0 < μ.real (threeInSiteBox (d := d) r) := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.2 hr, measure_lt_top _ _⟩
  have hAT : ∀ ω ∈ threeInSiteBox (d := d) r,
      openSites (↑(LatticeModels.box d r) : Set (LatticeModels.Site d)) ω ∈
        siteCutBall (0 : LatticeModels.Site d) r := by
    rintro ω ⟨x, hxbox, hperc, hdis⟩
    show IsSiteCutSet (LatticeModels.zdGraph d) (shiftedBox 0 r) _
    rw [shiftedBox_zero]
    exact isSiteCutSet_openSites_of_three hxbox hperc hdis
  have ha : 0 < μ.real (siteCutBall (0 : LatticeModels.Site d) r) :=
    real_pos_of_openSites p hp (LatticeModels.box d r) (measurableSet_siteCutBall 0 r) hA hAT
  set a := μ.real (siteCutBall (0 : LatticeModels.Site d) r) with ha_def
  set C₀ : ℕ := 2 * d * (2 * r + 3) ^ (d - 1) with hC₀
  obtain ⟨m, hm⟩ := exists_nat_gt ((C₀ : ℝ) / a)
  have hm' : (C₀ : ℝ) < a * (2 * m + 1) := by
    rw [div_lt_iff₀ ha] at hm
    nlinarith
  set n := (2 * r + 2) * m + r with hn
  set L := LatticeModels.innerBoundary (LatticeModels.zdGraph d)
    (LatticeModels.box d (n + 1)) with hL
  have hlow : ((2 * m + 1 : ℝ)) ^ d * a ≤ ∑ c ∈ centres r m, μ.real (siteCutBall c r) := by
    calc ((2 * m + 1 : ℝ)) ^ d * a = ∑ _c ∈ centres (d := d) r m, a := by
          rw [Finset.sum_const, card_centres, nsmul_eq_mul]; push_cast; ring
      _ ≤ ∑ c ∈ centres r m, μ.real (siteCutBall c r) :=
          Finset.sum_le_sum fun c _ => real_siteCutBall_zero_le p c r
  have hup : ∑ c ∈ centres r m, μ.real (siteCutBall c r) ≤ (L.card : ℝ) := by
    have h := sum_measure_siteCutBall_le (d := d) p r m
    have hsum : ∑ c ∈ centres r m, μ.real (siteCutBall c r) =
        (∑ c ∈ centres r m, μ (siteCutBall c r)).toReal := by
      rw [ENNReal.toReal_sum fun c _ => measure_ne_top _ _]
      rfl
    rw [hsum]
    have hmono := ENNReal.toReal_mono (ENNReal.natCast_ne_top L.card) h
    simpa using hmono
  have hLcard : (L.card : ℝ) ≤ C₀ * (2 * m + 1 : ℝ) ^ (d - 1) := by
    have h1 := card_innerBoundary_box_le (d := d) (n + 1)
    have h2 : 2 * (n + 1) + 1 ≤ (2 * r + 3) * (2 * m + 1) := by
      have h3 : (2 * r + 3) * (2 * m + 1) = 2 * (n + 1) + 1 + 2 * m := by rw [hn]; ring
      omega
    calc (L.card : ℝ) ≤ ((2 * d * (2 * (n + 1) + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ((2 * d * ((2 * r + 3) * (2 * m + 1)) ^ (d - 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
      _ = C₀ * (2 * m + 1 : ℝ) ^ (d - 1) := by rw [hC₀]; push_cast; rw [mul_pow]; ring
  have hpow : (2 * m + 1 : ℝ) ^ d = (2 * m + 1) * (2 * m + 1) ^ (d - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
    ring
  have hchain := hlow.trans (hup.trans hLcard)
  rw [hpow] at hchain
  have hpos : (0 : ℝ) < (2 * m + 1) ^ (d - 1) := by positivity
  have key : (2 * m + 1 : ℝ) * a ≤ C₀ := by
    have h' : ((2 * m + 1 : ℝ) * a) * (2 * m + 1) ^ (d - 1) ≤
        (C₀ : ℝ) * (2 * m + 1) ^ (d - 1) := by linarith [hchain]
    exact le_of_mul_le_mul_right h' hpos
  linarith [key, hm']

end Three

/-! ## `P_p(exactly two infinite clusters) = 0` -/

section Two

variable {d : ℕ}

/-- The event `T_{n,2}`: exactly two infinite open clusters, both meeting `Λ_n`. -/
def twoInSiteBox (n : ℕ) : Set (SiteConfig (LatticeModels.Site d)) :=
  {ω | ∃ x y, x ∈ LatticeModels.box d n ∧ y ∈ LatticeModels.box d n ∧
    ω ∈ sitePerc (LatticeModels.zdGraph d) x ∧ ω ∈ sitePerc (LatticeModels.zdGraph d) y ∧
    ¬ (openSiteGraph (LatticeModels.zdGraph d) ω).Reachable x y ∧
    ∀ z, ω ∈ sitePerc (LatticeModels.zdGraph d) z →
      (openSiteGraph (LatticeModels.zdGraph d) ω).Reachable z x ∨
      (openSiteGraph (LatticeModels.zdGraph d) ω).Reachable z y}

/-- `I₂ = ⋃ₙ T_{n,2}`. -/
theorem exactlyTwoInfSiteClusters_subset_iUnion :
    exactlyTwoInfSiteClusters (LatticeModels.zdGraph d) ⊆ ⋃ n, twoInSiteBox (d := d) n := by
  have hcov : ∀ v : LatticeModels.Site d, ∃ n, v ∈ LatticeModels.box d n := fun v => by
    have hv : v ∈ ⋃ L : ℕ,
        ((LatticeModels.box d L : Finset (LatticeModels.Site d)) : Set (LatticeModels.Site d)) := by
      rw [LatticeModels.iUnion_coe_box]
      exact Set.mem_univ v
    simpa using hv
  rintro ω ⟨x, y, hx, hy, hxy, hall⟩
  obtain ⟨n₁, h₁⟩ := hcov x
  obtain ⟨n₂, h₂⟩ := hcov y
  exact Set.mem_iUnion.2 ⟨max n₁ n₂, x, y, LatticeModels.box_mono d (le_max_left _ _) h₁,
    LatticeModels.box_mono d (le_max_right _ _) h₂, hx, hy, hxy, hall⟩

/-- **`P_p(there are exactly two infinite open clusters) = 0`** on `ℤ^d`, `d ≥ 1`. -/
theorem siteBernoulli_exactlyTwoInfSiteClusters_eq_zero (hd : 1 ≤ d) (p : unitInterval) :
    (siteBernoulli fun _ : LatticeModels.Site d => p)
      (exactlyTwoInfSiteClusters (LatticeModels.zdGraph d)) = 0 := by
  classical
  set μ := siteBernoulli fun _ : LatticeModels.Site d => p with hμ
  by_contra h2
  rcases eq_or_lt_of_le p.2.1 with hp0 | hp
  · refine h2 (siteBernoulli_eq_zero_of_coe_eq_zero hp0.symm ?_)
    rintro ⟨x, y, hx, -, -, -⟩
    exact empty_notMem_sitePerc _ x hx
  obtain ⟨n, hn⟩ : ∃ n, μ (twoInSiteBox (d := d) n) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h2 (measure_mono_null exactlyTwoInfSiteClusters_subset_iUnion
      (measure_iUnion_null_iff.2 hall))
  have hA : 0 < μ.real (twoInSiteBox (d := d) n) := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.2 hn, measure_lt_top _ _⟩
  have hAT : ∀ ω ∈ twoInSiteBox (d := d) n,
      openSites (↑(LatticeModels.box d n) : Set (LatticeModels.Site d)) ω ∈
        exactlyOneInfSiteCluster (LatticeModels.zdGraph d) := by
    rintro ω ⟨x, y, hx, hy, hpx, hpy, -, hall⟩
    refine openSites_mem_exactlyOneInfSiteCluster
      (fun a ha b hb => box_withinGraph_reachable n ha hb) ⟨x, hpx⟩ fun z hz => ?_
    rcases hall z hz with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨y, hy, h⟩
  have h1 : 0 < μ.real (exactlyOneInfSiteCluster (LatticeModels.zdGraph d)) :=
    real_pos_of_openSites p hp (LatticeModels.box d n)
      (measurableSet_exactlyOneInfSiteCluster _) hA hAT
  have hv0 := single_ne_zero hd
  have hshift : ∀ a b : LatticeModels.Site d,
      (LatticeModels.zdGraph d).Adj
        (LatticeModels.Site.shift (Pi.single ⟨0, hd⟩ 1 : LatticeModels.Site d) a)
        (LatticeModels.Site.shift (Pi.single ⟨0, hd⟩ 1 : LatticeModels.Site d) b) ↔
      (LatticeModels.zdGraph d).Adj a b :=
    fun a b => LatticeModels.zdGraph_adj_shift_iff _ a b
  have hI1 : μ (exactlyOneInfSiteCluster (LatticeModels.zdGraph d)) = 1 := by
    rcases siteBernoulli_zero_one_of_relabel_shift p hv0
      (measurableSet_exactlyOneInfSiteCluster _)
      (preimage_relabel_exactlyOneInfSiteCluster _ hshift) with h | h
    · exfalso
      rw [measureReal_def, hμ, h] at h1
      simp at h1
    · exact h
  have hI2 : μ (exactlyTwoInfSiteClusters (LatticeModels.zdGraph d)) = 1 := by
    rcases siteBernoulli_zero_one_of_relabel_shift p hv0
      (measurableSet_exactlyTwoInfSiteClusters _)
      (preimage_relabel_exactlyTwoInfSiteClusters _ hshift) with h | h
    · exact absurd h h2
    · exact h
  have hunion : μ (exactlyOneInfSiteCluster (LatticeModels.zdGraph d) ∪
      exactlyTwoInfSiteClusters (LatticeModels.zdGraph d)) = 2 := by
    rw [measure_union (disjoint_exactlyOne_exactlyTwo_site _)
      (measurableSet_exactlyTwoInfSiteClusters _), hI1, hI2, one_add_one_eq_two]
  have hle := prob_le_one (μ := μ)
    (s := exactlyOneInfSiteCluster (LatticeModels.zdGraph d) ∪
      exactlyTwoInfSiteClusters (LatticeModels.zdGraph d))
  rw [hunion] at hle
  exact absurd hle (not_le.2 ENNReal.one_lt_two)

end Two

/-! ## Uniqueness of the infinite open cluster -/

/-- **Uniqueness of the infinite open cluster for Bernoulli site percolation on `ℤ^d`.** -/
theorem SiteUniquenessInfiniteCluster_holds : SiteUniquenessInfiniteCluster := by
  intro d p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [numInfiniteSiteClusters_le_one_iff]
    intro x y hx
    exact absurd ((mem_sitePerc_iff _ ω x).1 hx) (Set.not_infinite.2 (Set.toFinite _))
  · rw [ae_iff]
    refine measure_mono_null (fun ω hω => mem_union_of_not_numInfiniteSiteClusters_le_one hω) ?_
    exact measure_union_null (siteBernoulli_exactlyTwoInfSiteClusters_eq_zero hd p)
      (siteBernoulli_threeInfSiteClusters_eq_zero hd p)

end KNAll.Site





end
