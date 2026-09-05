import Hypergraph.HyperCore

/-!
# Phase 1, targets 1 and 2

Two facts about the event that the cluster of `S` in the open hypergraph is exactly `K`.

* `incidence_subset_of_clusterEvent` — on that event an open label meeting `K` has all of its
  vertices inside `K`.  A vertex of the label lying in `K` is in the cluster, and every other vertex
  of the label is joined to it by that very label, hence is in the cluster too.
* `determinedBy_clusterEvent` — the event depends only on the labels meeting `K`.  Two
  configurations agreeing on those labels have the same cluster of `S`, because a walk leaving a
  vertex of `K` uses a label meeting `K`, on which the two configurations agree, and by the first
  fact such a label keeps the walk inside `K`.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Target 1 -/

/-- **Target 1.**  On the event that the cluster of `S` is exactly `K`, every open label that meets
`K` has all of its vertices inside `K`: an open label reaching out of `K` would enlarge the
cluster. -/
theorem incidence_subset_of_clusterEvent {V E : Type*} (H : Hypergraph V E) (S K : Set V)
    {ω : Set E} (hω : ω ∈ clusterEvent H S K) {e : E} (he : e ∈ ω)
    (hmeet : e ∈ labelsMeeting H K) : H.incidence e ⊆ K := by
  have hK : hyperClusterSet H ω S = K := hω
  rw [mem_labelsMeeting] at hmeet
  obtain ⟨v, hve, hvK⟩ := Set.not_disjoint_iff.1 hmeet
  intro y hy
  by_cases hvy : v = y
  · exact hvy ▸ hvK
  · have hv : v ∈ hyperClusterSet H ω S := by rw [hK]; exact hvK
    have hadj : (openHyperGraph H ω).Adj v y :=
      (openHyperGraph_adj_iff H ω v y).2 ⟨hvy, e, he, hve, hy⟩
    have hy' : y ∈ hyperClusterSet H ω S := hyperClusterSet_mem_of_adj H ω S hv hadj
    rw [hK] at hy'
    exact hy'

/-! ## Target 2 -/

/-- A walk starting inside `K` and using only labels of `α` stays inside `K` and is available in
`β`, provided the labels of `α` that meet `K` lie in `β` and have all their vertices in `K`. -/
private theorem walk_transfer {V E : Type*} (H : Hypergraph V E) (K : Set V) {α β : Set E}
    (hsub : ∀ e ∈ α, e ∈ labelsMeeting H K → e ∈ β)
    (hcl : ∀ e ∈ α, e ∈ labelsMeeting H K → H.incidence e ⊆ K)
    {x y : V} (w : (openHyperGraph H α).Walk x y) :
    x ∈ K → y ∈ K ∧ (openHyperGraph H β).Reachable x y := by
  induction w with
  | nil => exact fun hx => ⟨hx, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hadj p ih =>
      intro ha
      obtain ⟨hne, e, heα, hae, hbe⟩ := (openHyperGraph_adj_iff H α a b).1 hadj
      have hmeet : e ∈ labelsMeeting H K := by
        rw [mem_labelsMeeting]
        exact Set.not_disjoint_iff.2 ⟨a, hae, ha⟩
      have hb : b ∈ K := hcl e heα hmeet hbe
      obtain ⟨hcK, hr⟩ := ih hb
      have hadj' : (openHyperGraph H β).Adj a b :=
        (openHyperGraph_adj_iff H β a b).2 ⟨hne, e, hsub e heα hmeet, hae, hbe⟩
      exact ⟨hcK, hadj'.reachable.trans hr⟩

/-- Two configurations agreeing on the labels that meet `K` cannot disagree about the cluster of `S`
being `K`. -/
private theorem cluster_transfer {V E : Type*} (H : Hypergraph V E) (S K : Set V) {ω ω' : Set E}
    (hinter : ω ∩ labelsMeeting H K = ω' ∩ labelsMeeting H K)
    (hω : ω ∈ clusterEvent H S K) : ω' ∈ clusterEvent H S K := by
  have hK : hyperClusterSet H ω S = K := hω
  have hS : S ⊆ K := by rw [← hK]; exact subset_hyperClusterSet H ω S
  have hclω : ∀ e ∈ ω, e ∈ labelsMeeting H K → H.incidence e ⊆ K := fun e he hm =>
    incidence_subset_of_clusterEvent H S K hω he hm
  have hωω' : ∀ e ∈ ω, e ∈ labelsMeeting H K → e ∈ ω' := by
    intro e he hm
    have hmem : e ∈ ω ∩ labelsMeeting H K := ⟨he, hm⟩
    rw [hinter] at hmem
    exact hmem.1
  have hω'ω : ∀ e ∈ ω', e ∈ labelsMeeting H K → e ∈ ω := by
    intro e he hm
    have hmem : e ∈ ω' ∩ labelsMeeting H K := ⟨he, hm⟩
    rw [← hinter] at hmem
    exact hmem.1
  have hclω' : ∀ e ∈ ω', e ∈ labelsMeeting H K → H.incidence e ⊆ K := fun e he hm =>
    hclω e (hω'ω e he hm) hm
  show hyperClusterSet H ω' S = K
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨x, hxS, hr⟩
    obtain ⟨w⟩ := hr
    exact (walk_transfer H K hω'ω hclω' w (hS hxS)).1
  · intro y hy
    rw [← hK] at hy
    obtain ⟨x, hxS, hr⟩ := hy
    obtain ⟨w⟩ := hr
    exact ⟨x, hxS, (walk_transfer H K hωω' hclω w (hS hxS)).2⟩

/-- **Target 2.**  The event that the cluster of `S` is exactly `K` depends only on the labels that
meet `K`. -/
theorem determinedBy_clusterEvent {V E : Type*} (H : Hypergraph V E) (S K : Set V) :
    DeterminedBy (clusterEvent H S K) (labelsMeeting H K) := by
  rw [determinedBy_iff]
  intro ω ω' h
  exact ⟨fun hω => cluster_transfer H S K h hω, fun hω' => cluster_transfer H S K h.symm hω'⟩

end KNAll.Site

end
