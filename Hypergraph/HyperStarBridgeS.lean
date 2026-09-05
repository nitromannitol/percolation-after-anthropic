import Hypergraph.HyperStarH

/-!
# Probability form of the labelled one-source estimate

`HyperStarH.starH_integral` is the proved hyperedge analogue of the bond
estimate `(star^H)`.  This file performs only the finite indicator algebra
needed by its next consumer: the two integrals of complementary reachability
indicators are the corresponding avoidance probabilities.

No covariance hierarchy or marker-dominance statement is assumed here.
-/

noncomputable section

namespace KNAll.Site.HyperStarBridgeS

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.AGBase KNAll.Site.CSHTwoB KNAll.Site.CSHThree
open KNAll.Site.HyperStarH
open Percolation.Literature.DecisionTree (ind)
open scoped Classical

variable {V E : Type*}

/-- The complementary reachability integral is the avoidance probability. -/
theorem integral_one_sub_nr_eq_real_avoid [Fintype E]
    (H : Hypergraph V E) (S : Set V) (v : V) :
    (∫ omega, 1 - nr H S v omega ∂(prodBernoulli H.prob)) =
      (prodBernoulli H.prob).real (avoidEvent H S ({v} : Set V)) := by
  rw [← AGBase.integral_ind (μ := prodBernoulli H.prob)
    (avoidEvent H S ({v} : Set V))]
  exact integral_congr_of_forall _ fun omega =>
    (ind_avoid_singleton_eq_one_sub_nr H S v omega).symm

/-- Avoiding both `S` and `N` is the product of their two complementary
reachability indicators. -/
theorem integral_two_one_sub_nr_eq_real_avoid_union [Fintype E]
    (H : Hypergraph V E) (S N : Set V) (v : V) :
    (∫ omega, (1 - nr H S v omega) * (1 - nr H N v omega)
        ∂(prodBernoulli H.prob)) =
      (prodBernoulli H.prob).real (avoidEvent H (S ∪ N) ({v} : Set V)) := by
  rw [← integral_one_sub_nr_eq_real_avoid H (S ∪ N) v]
  apply integral_congr_of_forall _
  intro omega
  rw [CSHThree.nr_union_eq H S N v omega]
  ring

/--
The labelled one-source estimate in avoidance-probability form.  This is the
exact input called `(star^H)` by the subsequent `META-A2` induction.
-/
theorem starH_probability [Fintype V] [Fintype E]
    (H : Hypergraph V E) (N S : Set V) (x v : V) (hvS : v ∉ S)
    (Psi : Set V → ℝ) (hxS : x ∈ S) (hPsi : Monotone Psi)
    (hPsi0 : ∀ C, 0 ≤ Psi C) :
    CSHThree.yH H Psi x S v N *
        (prodBernoulli H.prob).real (avoidEvent H S ({v} : Set V))
      ≤ (prodBernoulli H.prob).real
            (avoidEvent H (S ∪ N) ({v} : Set V)) *
          CSHThree.covH H Psi x S v (∅ : Set V) := by
  simpa only [integral_one_sub_nr_eq_real_avoid,
    integral_two_one_sub_nr_eq_real_avoid_union] using
      HyperStarH.starH_integral H N S x v hvS Psi hxS hPsi hPsi0

end KNAll.Site.HyperStarBridgeS

end

#print axioms KNAll.Site.HyperStarBridgeS.integral_one_sub_nr_eq_real_avoid
#print axioms KNAll.Site.HyperStarBridgeS.integral_two_one_sub_nr_eq_real_avoid_union
#print axioms KNAll.Site.HyperStarBridgeS.starH_probability
