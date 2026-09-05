import Hypergraph.HyperImplC

/-!
# The cluster exchange identity

The joint law of two disjoint clusters factorizes in either order.

The event `clusterEventAvoiding H K T L` computes the cluster of `T` after discarding every label
that meets `K`.  It is determined by the labels avoiding `K`, so `clusterFactorization` applies to
it, and:

* `clusterEvent_inter_avoiding` — on the event that the cluster of `S` is exactly `K`, and when `K`
  and `L` are disjoint, discarding the labels that meet `K` does not change the cluster of `T`.  An
  open label meeting the cluster of `T` cannot meet `K`, because an open label meeting `K` lies
  inside `K` and `K` misses `L`;
* `prodBernoulli_deleteHyper_avoiding` — under the deleted parameters the labels meeting `K` are
  almost surely closed, so discarding them changes nothing almost everywhere;
* `clusterExchange` — both products equal the probability of the intersection of the two cluster
  events.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## The avoiding cluster event -/

/-- The cluster of `T` computed using only the labels that avoid `K`. -/
def clusterEventAvoiding (H : Hypergraph V E) (K T L : Set V) : Set (Set E) :=
  {ω | hyperClusterSet H (ω ∩ (labelsMeeting H K)ᶜ) T = L}

/-! ## Target 1: the avoiding event avoids `K` -/

/-- **Target 1.**  The cluster of `T` computed off the labels meeting `K` depends only on the
labels avoiding `K`: the configuration enters the definition only through its trace there. -/
theorem determinedBy_clusterEventAvoiding (H : Hypergraph V E) (K T L : Set V) :
    DeterminedBy (clusterEventAvoiding H K T L) (labelsMeeting H K)ᶜ := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [clusterEventAvoiding, Set.mem_setOf_eq, h]

/-! ## Two elementary tools -/

/-- Opening more labels can only join more vertices. -/
private theorem openHyperGraph_le (H : Hypergraph V E) {α β : Set E} (hsub : α ⊆ β) :
    openHyperGraph H α ≤ openHyperGraph H β := by
  intro x y hxy
  obtain ⟨hne, e, he, hx, hy⟩ := (openHyperGraph_adj_iff H α x y).1 hxy
  exact (openHyperGraph_adj_iff H β x y).2 ⟨hne, e, hsub he, hx, hy⟩

/-- The cluster of a source is increasing in the set of open labels. -/
private theorem hyperClusterSet_subset (H : Hypergraph V E) {α β : Set E} (hsub : α ⊆ β)
    (S : Set V) : hyperClusterSet H α S ⊆ hyperClusterSet H β S := by
  rintro y ⟨x, hx, hr⟩
  exact ⟨x, hx, hr.mono (openHyperGraph_le H hsub)⟩

/-- A walk starting inside `M` and using only labels of `α` stays inside `M` and is available in
`β`, provided the labels of `α` that meet `M` lie in `β` and have all their vertices in `M`. -/
private theorem walk_confine (H : Hypergraph V E) (M : Set V) {α β : Set E}
    (hsub : ∀ e ∈ α, e ∈ labelsMeeting H M → e ∈ β)
    (hcl : ∀ e ∈ α, e ∈ labelsMeeting H M → H.incidence e ⊆ M)
    {x y : V} (w : (openHyperGraph H α).Walk x y) :
    x ∈ M → y ∈ M ∧ (openHyperGraph H β).Reachable x y := by
  induction w with
  | nil => exact fun hx => ⟨hx, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hadj p ih =>
      intro ha
      obtain ⟨hne, e, heα, hae, hbe⟩ := (openHyperGraph_adj_iff H α a b).1 hadj
      have hmeet : e ∈ labelsMeeting H M := by
        rw [mem_labelsMeeting]
        exact Set.not_disjoint_iff.2 ⟨a, hae, ha⟩
      have hb : b ∈ M := hcl e heα hmeet hbe
      obtain ⟨hcM, hr⟩ := ih hb
      have hadj' : (openHyperGraph H β).Adj a b :=
        (openHyperGraph_adj_iff H β a b).2 ⟨hne, e, hsub e heα hmeet, hae, hbe⟩
      exact ⟨hcM, hadj'.reachable.trans hr⟩

/-- On the event that the cluster of `S` is exactly `K`, an open label meeting a set disjoint from
`K` cannot meet `K`: an open label meeting `K` lies inside `K`. -/
private theorem notMem_labelsMeeting_of_meets (H : Hypergraph V E) {S K L : Set V}
    (hKL : Disjoint K L) {ω : Set E} (hωS : ω ∈ clusterEvent H S K) {e : E} (he : e ∈ ω)
    (hmL : e ∈ labelsMeeting H L) : e ∉ labelsMeeting H K := by
  intro hmK
  have hsubK : H.incidence e ⊆ K := incidence_subset_of_clusterEvent H S K hωS he hmK
  rw [mem_labelsMeeting] at hmL
  obtain ⟨a, hae, haL⟩ := Set.not_disjoint_iff.1 hmL
  exact Set.disjoint_left.1 hKL (hsubK hae) haL

/-! ## Target 2: the deletion is invisible on the event -/

/-- **Target 2.**  On the event that the cluster of `S` is exactly `K`, and for `K` and `L`
disjoint, the cluster of `T` is `L` exactly when the cluster of `T` computed off the labels meeting
`K` is `L`.  No inclusion between the sources and the clusters is needed: a source is contained in
its own cluster, which is all the argument uses. -/
theorem clusterEvent_inter_avoiding (H : Hypergraph V E) (S K T L : Set V)
    (hKL : Disjoint K L) :
    clusterEvent H S K ∩ clusterEvent H T L
      = clusterEvent H S K ∩ clusterEventAvoiding H K T L := by
  refine Set.ext fun ω => ?_
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hωS, hωT⟩
    refine ⟨hωS, ?_⟩
    have hL : hyperClusterSet H ω T = L := hωT
    have hTL : T ⊆ L := by rw [← hL]; exact subset_hyperClusterSet H ω T
    have hcl : ∀ e ∈ ω, e ∈ labelsMeeting H L → H.incidence e ⊆ L := fun e he hm =>
      incidence_subset_of_clusterEvent H T L hωT he hm
    have hsub : ∀ e ∈ ω, e ∈ labelsMeeting H L → e ∈ ω ∩ (labelsMeeting H K)ᶜ := fun e he hm =>
      ⟨he, notMem_labelsMeeting_of_meets H hKL hωS he hm⟩
    show hyperClusterSet H (ω ∩ (labelsMeeting H K)ᶜ) T = L
    refine Set.Subset.antisymm ?_ ?_
    · rw [← hL]
      exact hyperClusterSet_subset H Set.inter_subset_left T
    · intro y hy
      rw [← hL] at hy
      obtain ⟨x, hxT, hr⟩ := hy
      obtain ⟨w⟩ := hr
      exact ⟨x, hxT, (walk_confine H L hsub hcl w (hTL hxT)).2⟩
  · rintro ⟨hωS, hωA⟩
    refine ⟨hωS, ?_⟩
    have hL : hyperClusterSet H (ω ∩ (labelsMeeting H K)ᶜ) T = L := hωA
    have hmemA : (ω ∩ (labelsMeeting H K)ᶜ) ∈ clusterEvent H T L := hL
    have hTL : T ⊆ L := by
      rw [← hL]; exact subset_hyperClusterSet H (ω ∩ (labelsMeeting H K)ᶜ) T
    have hsub : ∀ e ∈ ω, e ∈ labelsMeeting H L → e ∈ ω ∩ (labelsMeeting H K)ᶜ := fun e he hm =>
      ⟨he, notMem_labelsMeeting_of_meets H hKL hωS he hm⟩
    have hcl : ∀ e ∈ ω, e ∈ labelsMeeting H L → H.incidence e ⊆ L := fun e he hm =>
      incidence_subset_of_clusterEvent H T L hmemA (hsub e he hm) hm
    show hyperClusterSet H ω T = L
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨x, hxT, hr⟩
      obtain ⟨w⟩ := hr
      exact (walk_confine H L hsub hcl w (hTL hxT)).1
    · rw [← hL]
      exact hyperClusterSet_subset H Set.inter_subset_left T

/-! ## Target 3: the deleted labels are almost surely absent -/

/-- Over a finite label type every event is measurable. -/
private theorem measurableSet_of_fintype {ι : Type*} [Fintype ι] (A : Set (Set ι)) :
    MeasurableSet A := by
  classical
  have h : DeterminedBy A (↑(Finset.univ : Finset ι)) := by
    rw [determinedBy_iff]
    intro ω ω' hω
    have hωω : ω = ω' := by simpa using hω
    rw [hωω]
  exact h.measurableSet_of_finset

/-- **Target 3.**  Under the parameters with the labels meeting `K` closed, those labels are almost
surely absent, so discarding them leaves the cluster of `T` unchanged almost everywhere. -/
theorem prodBernoulli_deleteHyper_avoiding (H : Hypergraph V E) [Fintype E] (K T L : Set V) :
    (prodBernoulli (deleteHyper H K).prob).real (clusterEventAvoiding H K T L)
      = (prodBernoulli (deleteHyper H K).prob).real (clusterEvent H T L) := by
  classical
  refine measureReal_congr ?_
  have hzero : ∀ e ∈ labelsMeeting H K, (deleteHyper H K).prob e = 0 := by
    intro e he
    simp only [deleteHyper, if_pos he]
  filter_upwards [prodBernoulli_ae_forall_notMem (deleteHyper H K).prob
    (Z := labelsMeeting H K) (Set.toFinite _).countable hzero] with ω hω
  have hint : ω ∩ (labelsMeeting H K)ᶜ = ω :=
    Set.inter_eq_left.2 fun e he hmem => hω e hmem he
  have hiff : ω ∈ clusterEventAvoiding H K T L ↔ ω ∈ clusterEvent H T L := by
    simp only [clusterEventAvoiding, clusterEvent, Set.mem_setOf_eq, hint]
  exact propext hiff

/-! ## Target 4: cluster exchange -/

/-- The probability of the intersection of two disjoint cluster events, factorized with the second
cluster read off the deleted hypergraph. -/
private theorem clusterEvent_inter_real (H : Hypergraph V E) [Fintype E] (S K T L : Set V)
    (hKL : Disjoint K L) :
    (prodBernoulli H.prob).real (clusterEvent H S K ∩ clusterEvent H T L)
      = (prodBernoulli H.prob).real (clusterEvent H S K) *
          (prodBernoulli (deleteHyper H K).prob).real (clusterEvent H T L) := by
  rw [clusterEvent_inter_avoiding H S K T L hKL,
    clusterFactorization H S K (determinedBy_clusterEventAvoiding H K T L)
      (measurableSet_of_fintype _),
    prodBernoulli_deleteHyper_avoiding H K T L]

/-- **Target 4, cluster exchange.**  For disjoint `K` and `L` the joint law of the two cluster
events factorizes in either order: both products are the probability of the intersection. -/
theorem clusterExchange (H : Hypergraph V E) [Fintype E] (S K T L : Set V)
    (hKL : Disjoint K L) :
    (prodBernoulli H.prob).real (clusterEvent H S K) *
        (prodBernoulli (deleteHyper H K).prob).real (clusterEvent H T L)
      = (prodBernoulli H.prob).real (clusterEvent H T L) *
        (prodBernoulli (deleteHyper H L).prob).real (clusterEvent H S K) := by
  rw [← clusterEvent_inter_real H S K T L hKL, ← clusterEvent_inter_real H T L S K hKL.symm,
    Set.inter_comm]

end KNAll.Site

end
