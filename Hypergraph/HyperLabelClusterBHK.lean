import Hypergraph.HyperCSHTwoB

/-!
# Reading a member cluster from a labelled source cluster

The vertex cluster of a source set does not determine the cluster of one of its members in a
general hypergraph.  This file avoids that loss of information by adjoining one marker vertex for
each label.  The marker for `e` belongs only to the incidence set of `e`; consequently the marker
vertices in the augmented source cluster record exactly the open label cluster of the source.

Applying the already proved two-cluster negative-correlation theorem to this augmented hypergraph
gives the member-functional form of BHK 1.4 that is missing from `KN.HyperCSHThree`.
-/

noncomputable section

namespace KNAll.Site.LabelClusterBHK

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.CTOne
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem)
open scoped Classical

variable {V E : Type*}

/-- Add one private marker vertex for every label. -/
def markedIncidence (H : Hypergraph V E) (e : E) : Set (V ⊕ E) :=
  Sum.inl '' H.incidence e ∪ {Sum.inr e}

/-- The marked hypergraph has the same independent labels and probabilities as `H`. -/
def markedHypergraph (H : Hypergraph V E) : Hypergraph (V ⊕ E) E where
  incidence := markedIncidence H
  prob := H.prob

@[simp] theorem markedHypergraph_prob (H : Hypergraph V E) :
    (markedHypergraph H).prob = H.prob := rfl

@[simp] theorem inl_mem_markedIncidence (H : Hypergraph V E) (e : E) (x : V) :
    Sum.inl x ∈ markedIncidence H e ↔ x ∈ H.incidence e := by
  simp [markedIncidence]

@[simp] theorem inr_mem_markedIncidence (H : Hypergraph V E) (e f : E) :
    Sum.inr f ∈ markedIncidence H e ↔ f = e := by
  simp [markedIncidence]

/-- The open labels incident to the open vertex cluster of `S`. -/
def labelCluster (H : Hypergraph V E) (S : Set V) (omega : Set E) : Set E :=
  omega ∩ labelsMeeting H (hyperClusterSet H omega S)

theorem labelCluster_subset (H : Hypergraph V E) (S : Set V) (omega : Set E) :
    labelCluster H S omega ⊆ omega := Set.inter_subset_left

/-- The invariant carried by a walk in the marked hypergraph that starts at `inl x`. -/
def GoodFrom (H : Hypergraph V E) (omega : Set E) (x : V) : V ⊕ E → Prop
  | Sum.inl y => (openHyperGraph H omega).Reachable x y
  | Sum.inr e => e ∈ omega ∧ ∃ y ∈ H.incidence e, (openHyperGraph H omega).Reachable x y

theorem goodFrom_step (H : Hypergraph V E) (omega : Set E) (x : V) {a b : V ⊕ E}
    (ha : GoodFrom H omega x a)
    (hab : (openHyperGraph (markedHypergraph H) omega).Adj a b) :
    GoodFrom H omega x b := by
  obtain ⟨hne, e, he, hae, hbe⟩ := (openHyperGraph_adj_iff (markedHypergraph H) omega a b).1 hab
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hae' : a ∈ H.incidence e := (inl_mem_markedIncidence H e a).1 hae
          have hbe' : b ∈ H.incidence e := (inl_mem_markedIncidence H e b).1 hbe
          have hab' : (openHyperGraph H omega).Adj a b :=
            (openHyperGraph_adj_iff H omega a b).2
              ⟨fun h => hne (congrArg Sum.inl h), e, he, hae', hbe'⟩
          exact ha.trans hab'.reachable
      | inr f =>
          have hae' : a ∈ H.incidence e := (inl_mem_markedIncidence H e a).1 hae
          have hfe : f = e := (inr_mem_markedIncidence H e f).1 hbe
          subst f
          exact ⟨he, a, hae', ha⟩
  | inr f =>
      cases b with
      | inl b =>
          obtain ⟨hf, y, hy, hxy⟩ := ha
          have hfe : f = e := (inr_mem_markedIncidence H e f).1 hae
          subst e
          have hb : b ∈ H.incidence f := (inl_mem_markedIncidence H f b).1 hbe
          by_cases hyb : y = b
          · exact hyb ▸ hxy
          · exact hxy.trans ((openHyperGraph_adj_iff H omega y b).2
              ⟨hyb, f, hf, hy, hb⟩).reachable
      | inr g =>
          have hfe : f = e := (inr_mem_markedIncidence H e f).1 hae
          have hge : g = e := (inr_mem_markedIncidence H e g).1 hbe
          exact absurd (hfe.trans hge.symm) (fun h => hne (congrArg Sum.inr h))

theorem goodFrom_of_walk (H : Hypergraph V E) (omega : Set E) (x : V) :
    ∀ {a b : V ⊕ E}, (openHyperGraph (markedHypergraph H) omega).Walk a b →
      GoodFrom H omega x a → GoodFrom H omega x b := by
  intro a b p
  induction p with
  | nil => exact fun h => h
  | cons hab p ih => exact fun h => ih (goodFrom_step H omega x h hab)

theorem marked_reachable_of_reachable (H : Hypergraph V E) (omega : Set E) {x y : V}
    (h : (openHyperGraph H omega).Reachable x y) :
    (openHyperGraph (markedHypergraph H) omega).Reachable (Sum.inl x) (Sum.inl y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
      obtain ⟨hne, e, he, hae, hbe⟩ := (openHyperGraph_adj_iff H omega a b).1 hab
      have hab' : (openHyperGraph (markedHypergraph H) omega).Adj (Sum.inl a) (Sum.inl b) :=
        (openHyperGraph_adj_iff (markedHypergraph H) omega _ _).2
          ⟨fun h => hne (Sum.inl_injective h), e, he,
            (inl_mem_markedIncidence H e a).2 hae,
            (inl_mem_markedIncidence H e b).2 hbe⟩
      exact hab'.reachable.trans ih

theorem reachable_of_marked_reachable (H : Hypergraph V E) (omega : Set E) {x y : V}
    (h : (openHyperGraph (markedHypergraph H) omega).Reachable (Sum.inl x) (Sum.inl y)) :
    (openHyperGraph H omega).Reachable x y := by
  obtain ⟨p⟩ := h
  exact goodFrom_of_walk H omega x p (SimpleGraph.Reachable.refl x)

theorem marked_reachable_inl_iff (H : Hypergraph V E) (omega : Set E) (x y : V) :
    (openHyperGraph (markedHypergraph H) omega).Reachable (Sum.inl x) (Sum.inl y) ↔
      (openHyperGraph H omega).Reachable x y :=
  ⟨reachable_of_marked_reachable H omega, marked_reachable_of_reachable H omega⟩

theorem inl_mem_marked_cluster_iff (H : Hypergraph V E) (omega : Set E) (S : Set V) (y : V) :
    Sum.inl y ∈ hyperClusterSet (markedHypergraph H) omega (Sum.inl '' S) ↔
      y ∈ hyperClusterSet H omega S := by
  simp only [hyperClusterSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, hxy⟩
    exact ⟨x, hx, (marked_reachable_inl_iff H omega x y).1 hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨Sum.inl x, ⟨x, hx, rfl⟩, (marked_reachable_inl_iff H omega x y).2 hxy⟩

theorem inr_mem_marked_cluster_iff (H : Hypergraph V E) (omega : Set E) (S : Set V) (e : E) :
    Sum.inr e ∈ hyperClusterSet (markedHypergraph H) omega (Sum.inl '' S) ↔
      e ∈ labelCluster H S omega := by
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, hxe⟩
    have hgood : GoodFrom H omega x (Sum.inr e) := by
      rcases hxe with ⟨p⟩
      exact goodFrom_of_walk H omega x p (SimpleGraph.Reachable.refl x)
    obtain ⟨he, y, hye, hxy⟩ := hgood
    exact ⟨he, Set.not_disjoint_iff.2 ⟨y, hye, ⟨x, hx, hxy⟩⟩⟩
  · rintro ⟨he, hmeet⟩
    obtain ⟨y, hye, x, hx, hxy⟩ := Set.not_disjoint_iff.1 hmeet
    have hxy' := marked_reachable_of_reachable H omega hxy
    have hye' : (openHyperGraph (markedHypergraph H) omega).Adj (Sum.inl y) (Sum.inr e) :=
      (openHyperGraph_adj_iff (markedHypergraph H) omega _ _).2
        ⟨by simp, e, he, (inl_mem_markedIncidence H e y).2 hye,
          (inr_mem_markedIncidence H e e).2 rfl⟩
    exact ⟨Sum.inl x, ⟨x, hx, rfl⟩, hxy'.trans hye'.reachable⟩

theorem hyperClusterSet_labelCluster (H : Hypergraph V E) {S : Set V} {x : V} (hx : x ∈ S)
    (omega : Set E) :
    hyperClusterSet H (labelCluster H S omega) ({x} : Set V) =
      hyperClusterSet H omega ({x} : Set V) := by
  refine Set.Subset.antisymm
    (hyperClusterSet_mono H _ (labelCluster_subset H S omega)) ?_
  intro u hu
  rw [mem_hyperClusterSet_singleton] at hu ⊢
  rw [SimpleGraph.reachable_iff_reflTransGen] at hu ⊢
  induction hu with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
      obtain ⟨hne, e, he, hbe, hce⟩ := (openHyperGraph_adj_iff H omega b c).1 hbc
      have hbC : b ∈ hyperClusterSet H omega S :=
        ⟨x, hx, (SimpleGraph.reachable_iff_reflTransGen _ _).2 hab⟩
      have hmeet : e ∈ labelsMeeting H (hyperClusterSet H omega S) :=
        Set.not_disjoint_iff.2 ⟨b, hbe, hbC⟩
      exact ih.tail ((openHyperGraph_adj_iff H _ b c).2
        ⟨hne, e, ⟨he, hmeet⟩, hbe, hce⟩)

/-- Pull the marker part out of a marked vertex set. -/
def markerPart (K : Set (V ⊕ E)) : Set E := {e | Sum.inr e ∈ K}

theorem markerPart_mono : Monotone (markerPart : Set (V ⊕ E) → Set E) :=
  fun _ _ h _ he => h he

/-- Lift an owner-cluster functional to the marked source cluster. -/
def ownerLift (H : Hypergraph V E) (x : V) (Psi : Set V → ℝ) (K : Set (V ⊕ E)) : ℝ :=
  Psi (hyperClusterSet H (markerPart K) ({x} : Set V))

theorem ownerLift_mono (H : Hypergraph V E) (x : V) {Psi : Set V → ℝ}
    (hPsi : Monotone Psi) : Monotone (ownerLift H x Psi) :=
  fun _ _ h => hPsi (hyperClusterSet_mono H _ (markerPart_mono h))

theorem ownerLift_marked_cluster (H : Hypergraph V E) {S : Set V} {x : V} (hx : x ∈ S)
    (Psi : Set V → ℝ) (omega : Set E) :
    ownerLift H x Psi (hyperClusterSet (markedHypergraph H) omega (Sum.inl '' S)) =
      Psi (hyperClusterSet H omega ({x} : Set V)) := by
  unfold ownerLift
  have hpart : markerPart (hyperClusterSet (markedHypergraph H) omega (Sum.inl '' S)) =
      labelCluster H S omega := by
    ext e
    exact inr_mem_marked_cluster_iff H omega S e
  rw [hpart, hyperClusterSet_labelCluster H hx omega]

/-- The marker-cluster functional that reads whether it contains a vertex of `N`. -/
def reachLift (N : Set V) (K : Set (V ⊕ E)) : ℝ :=
  if ∃ n ∈ N, Sum.inl n ∈ K then 1 else 0

theorem reachLift_mono (N : Set V) : Monotone (reachLift N : Set (V ⊕ E) → ℝ) := by
  intro K K' hKK'
  by_cases h : ∃ n ∈ N, Sum.inl n ∈ K
  · have h' : ∃ n ∈ N, Sum.inl n ∈ K' :=
      h.imp fun n hn => ⟨hn.1, hKK' hn.2⟩
    simp only [reachLift, if_pos h, if_pos h']
    exact le_rfl
  · simp only [reachLift, if_neg h]
    split_ifs <;> norm_num

theorem reachLift_marked_cluster (H : Hypergraph V E) (N : Set V) (v : V) (omega : Set E) :
    reachLift N (hyperClusterSet (markedHypergraph H) omega ({Sum.inl v} : Set (V ⊕ E))) =
      KNAll.Site.CSHTwoB.nr H N v omega := by
  have hiff : (∃ n ∈ N,
      Sum.inl n ∈ hyperClusterSet (markedHypergraph H) omega ({Sum.inl v} : Set (V ⊕ E))) ↔
      ∃ n ∈ N, (openHyperGraph H omega).Reachable n v := by
    constructor
    · rintro ⟨n, hn, q, hq, hqn⟩
      rw [Set.mem_singleton_iff] at hq
      subst q
      exact ⟨n, hn, ((marked_reachable_inl_iff H omega v n).1 hqn).symm⟩
    · rintro ⟨n, hn, hnv⟩
      exact ⟨n, hn, Sum.inl v, rfl,
        (marked_reachable_inl_iff H omega v n).2 hnv.symm⟩
  unfold reachLift KNAll.Site.CSHTwoB.nr
  by_cases h : ∃ n ∈ N, (openHyperGraph H omega).Reachable n v
  · rw [if_pos (hiff.2 h), ind_of_mem
      (show omega ∈ {eta : Set E | ∃ n ∈ N, (openHyperGraph H eta).Reachable n v} from h)]
  · rw [if_neg (fun hm => h (hiff.1 hm)), ind_of_not_mem
      (show omega ∉ {eta : Set E | ∃ n ∈ N, (openHyperGraph H eta).Reachable n v} from h)]

theorem marked_avoidEvent (H : Hypergraph V E) (S T : Set V) :
    avoidEvent (markedHypergraph H) (Sum.inl '' S) (Sum.inl '' T) = avoidEvent H S T := by
  ext omega
  simp only [mem_avoidEvent, Set.disjoint_left, Set.mem_image]
  constructor
  · intro h y hyC hyT
    exact h ((inl_mem_marked_cluster_iff H omega S y).2 hyC) ⟨y, hyT, rfl⟩
  · rintro h q hqC ⟨y, hyT, rfl⟩
    exact h ((inl_mem_marked_cluster_iff H omega S y).1 hqC) hyT

/--
The missing member-functional form of BHK 1.4 for independent hyperedges.

Conditionally on the cluster of `S` avoiding `v`, an increasing functional of the cluster of a
specified member `x ∈ S` and the event that `v` reaches `N` are negatively correlated.
-/
theorem bhk14_memberFunctional [Fintype V] [Fintype E] (H : Hypergraph V E)
    (S : Set V) (x v : V) (hx : x ∈ S) (N : Set V) {Psi : Set V → ℝ}
    (hPsi : Monotone Psi) :
    (prodBernoulli H.prob).real (avoidEvent H S ({v} : Set V)) *
        (∫ omega in avoidEvent H S ({v} : Set V),
          Psi (hyperClusterSet H omega ({x} : Set V)) * KNAll.Site.CSHTwoB.nr H N v omega
            ∂(prodBernoulli H.prob))
      ≤ (∫ omega in avoidEvent H S ({v} : Set V),
            Psi (hyperClusterSet H omega ({x} : Set V)) ∂(prodBernoulli H.prob)) *
          ∫ omega in avoidEvent H S ({v} : Set V),
            KNAll.Site.CSHTwoB.nr H N v omega ∂(prodBernoulli H.prob) := by
  let Sin : Set (V ⊕ E) := Sum.inl '' S
  let vv : V ⊕ E := Sum.inl v
  have hT : ({vv} : Set (V ⊕ E)) ⊆ ({vv} : Set (V ⊕ E)) := Set.Subset.rfl
  have key := avoid_cluster_sub_negCorrelation (markedHypergraph H)
    Sin ({vv} : Set (V ⊕ E)) ({vv} : Set (V ⊕ E)) hT
    (F := ownerLift H x Psi) (G := reachLift N)
    (ownerLift_mono H x hPsi) (reachLift_mono N)
  have hav : avoidEvent (markedHypergraph H) Sin ({vv} : Set (V ⊕ E)) =
      avoidEvent H S ({v} : Set V) := by
    simpa [Sin, vv] using marked_avoidEvent H S ({v} : Set V)
  simp only [markedHypergraph_prob, hav, Sin, vv,
    ownerLift_marked_cluster H hx Psi, reachLift_marked_cluster H N v] at key
  exact key

end KNAll.Site.LabelClusterBHK

end

#print axioms KNAll.Site.LabelClusterBHK.bhk14_memberFunctional
