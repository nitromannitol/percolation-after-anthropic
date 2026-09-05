import Hypergraph.HyperImplC

/-!
# The cluster partition and the expansion over clusters

The exploration arguments downstream condition on the whole cluster of a source set.  That
conditioning is legitimate because the cluster events form a partition of the configuration space,
indexed by the possible cluster sets.

* `mem_clusterEvent_self` — a configuration lies in the cluster event indexed by its own cluster,
  which is the "at least one" half of the partition;
* `clusterEvent_disjoint` — two cluster events with different indices are disjoint, the "at most
  one" half;
* `iUnion_clusterEvent` — over a finite vertex type every cluster is the coercion of a finset, so
  the cluster events indexed by finsets already cover the configuration space;
* `real_eq_sum_clusterEvent` — the probability of a measurable event is the sum over finsets of its
  probability on each cluster event, by finite additivity over the disjoint cover;
* `sum_clusterEvent_eq_one` — the cluster events carry total mass one.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## The partition -/

/-- **Every configuration lies in a cluster event.**  The index is the cluster of `S` in that very
configuration. -/
theorem mem_clusterEvent_self (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    ω ∈ clusterEvent H S (hyperClusterSet H ω S) := rfl

/-- **Cluster events with different indices are disjoint.**  A configuration in both would have two
different clusters of `S`. -/
theorem clusterEvent_disjoint (H : Hypergraph V E) (S : Set V) {K L : Set V} (hKL : K ≠ L) :
    Disjoint (clusterEvent H S K) (clusterEvent H S L) := by
  rw [Set.disjoint_left]
  intro ω hK hL
  have h1 : hyperClusterSet H ω S = K := hK
  have h2 : hyperClusterSet H ω S = L := hL
  exact hKL (h1.symm.trans h2)

/-- **The cluster events indexed by finsets cover the configuration space.**  Over a finite vertex
type the cluster of `S` is a finite set, hence the coercion of a finset. -/
theorem iUnion_clusterEvent [Fintype V] (H : Hypergraph V E) (S : Set V) :
    (⋃ K : Finset V, clusterEvent H S (↑K : Set V)) = Set.univ := by
  refine Set.eq_univ_of_forall fun ω => ?_
  obtain ⟨F, hF⟩ : ∃ F : Finset V, (↑F : Set V) = hyperClusterSet H ω S :=
    (Set.toFinite (hyperClusterSet H ω S)).exists_finset_coe
  refine Set.mem_iUnion.2 ⟨F, ?_⟩
  rw [hF]
  exact mem_clusterEvent_self H S ω

/-! ## The expansion -/

/-- **The expansion over clusters.**  The probability of a measurable event is the sum of its
probabilities on the cluster events, which are finitely many, pairwise disjoint, measurable, and
cover the configuration space. -/
theorem real_eq_sum_clusterEvent [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (A : Set (Set E)) (hAm : MeasurableSet A) :
    (prodBernoulli H.prob).real A
      = ∑ K : Finset V, (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V) ∩ A) := by
  have hdisj :
      Pairwise (Function.onFun Disjoint fun K : Finset V =>
        clusterEvent H S (↑K : Set V) ∩ A) := by
    intro K L hKL
    have hne : (↑K : Set V) ≠ (↑L : Set V) := fun h => hKL (Finset.coe_injective h)
    show Disjoint (clusterEvent H S (↑K : Set V) ∩ A) (clusterEvent H S (↑L : Set V) ∩ A)
    exact (clusterEvent_disjoint H S hne).mono Set.inter_subset_left Set.inter_subset_left
  have hmeas : ∀ K : Finset V, MeasurableSet (clusterEvent H S (↑K : Set V) ∩ A) := fun K =>
    (measurableSet_clusterEvent H S (↑K : Set V)).inter hAm
  have hU : (⋃ K : Finset V, clusterEvent H S (↑K : Set V) ∩ A) = A := by
    rw [← Set.iUnion_inter, iUnion_clusterEvent H S, Set.univ_inter]
  calc (prodBernoulli H.prob).real A
      = (prodBernoulli H.prob).real (⋃ K : Finset V, clusterEvent H S (↑K : Set V) ∩ A) := by
        rw [hU]
    _ = ∑ K : Finset V, (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V) ∩ A) :=
        measureReal_iUnion_fintype hdisj hmeas fun _ => measure_ne_top _ _

/-- **The total mass of the cluster events is one.**  The expansion of the whole configuration
space. -/
theorem sum_clusterEvent_eq_one [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V) :
    ∑ K : Finset V, (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V)) = 1 := by
  have h := real_eq_sum_clusterEvent H S Set.univ MeasurableSet.univ
  simp only [Set.inter_univ] at h
  rw [← h, probReal_univ]

end KNAll.Site

end
