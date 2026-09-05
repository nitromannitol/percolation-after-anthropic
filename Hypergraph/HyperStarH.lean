import Hypergraph.HyperCSHThree
import Hypergraph.HyperLabelClusterBHK

/-!
# The labelled one-source estimate

This file is the first consumer of `LabelClusterBHK.bhk14_memberFunctional`.  It ports the
one-source estimate `(star^H)` from the bond proof after the missing member-functional form of
BHK 1.4 has been recovered by marker augmentation.
-/

noncomputable section

namespace KNAll.Site.HyperStarH

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.AGBase KNAll.Site.CTBase KNAll.Site.CTOne
open KNAll.Site.CSHTwoA KNAll.Site.CSHTwoB KNAll.Site.CSHThree
open KNAll.Site.LabelClusterBHK
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem)
open scoped Classical

variable {V E : Type*}

/-- Avoiding the singleton marker `v` is the complement of reaching `v` from `S`. -/
theorem ind_avoid_singleton_eq_one_sub_nr (H : Hypergraph V E) (S : Set V) (v : V)
    (omega : Set E) :
    ind (avoidEvent H S ({v} : Set V)) omega = 1 - nr H S v omega := by
  have hav : omega ∈ avoidEvent H S ({v} : Set V) ↔
      ¬ ∃ s ∈ S, (openHyperGraph H omega).Reachable s v := by
    simp only [mem_avoidEvent, Set.disjoint_singleton_right, hyperClusterSet,
      Set.mem_setOf_eq]
  by_cases h : ∃ s ∈ S, (openHyperGraph H omega).Reachable s v
  · rw [ind_of_not_mem (fun ha => (hav.1 ha) h), nr,
      ind_of_mem (show omega ∈ {eta : Set E |
        ∃ s ∈ S, (openHyperGraph H eta).Reachable s v} from h)]
    norm_num
  · rw [ind_of_mem (hav.2 h), nr,
      ind_of_not_mem (show omega ∉ {eta : Set E |
        ∃ s ∈ S, (openHyperGraph H eta).Reachable s v} from h)]
    norm_num

/-- BHK 1.4 in the whole-space integral form used by the `(star^H)` algebra. -/
theorem bhk14_memberFunctional_integral [Fintype V] [Fintype E]
    (H : Hypergraph V E) (S : Set V) (x v : V) (hx : x ∈ S) (N : Set V)
    {Psi : Set V → ℝ} (hPsi : Monotone Psi) :
    (∫ omega, (1 - nr H S v omega) ∂(prodBernoulli H.prob)) *
        (∫ omega, Psi (hyperClusterSet H omega ({x} : Set V)) *
          ((1 - nr H S v omega) * nr H N v omega) ∂(prodBernoulli H.prob))
      ≤ (∫ omega, Psi (hyperClusterSet H omega ({x} : Set V)) *
            (1 - nr H S v omega) ∂(prodBernoulli H.prob)) *
          ∫ omega, (1 - nr H S v omega) * nr H N v omega
            ∂(prodBernoulli H.prob) := by
  have key := bhk14_memberFunctional H S x v hx N hPsi
  have hind : ∀ omega : Set E,
      ind (avoidEvent H S ({v} : Set V)) omega = 1 - nr H S v omega :=
    ind_avoid_singleton_eq_one_sub_nr H S v
  have hP : (∫ omega, (1 - nr H S v omega) ∂(prodBernoulli H.prob)) =
      (prodBernoulli H.prob).real (avoidEvent H S ({v} : Set V)) := by
    rw [← AGBase.integral_ind (μ := prodBernoulli H.prob)
      (avoidEvent H S ({v} : Set V))]
    exact integral_congr_of_forall _ fun omega => (hind omega).symm
  have hFN : (∫ omega, Psi (hyperClusterSet H omega ({x} : Set V)) *
        ((1 - nr H S v omega) * nr H N v omega) ∂(prodBernoulli H.prob)) =
      ∫ omega in avoidEvent H S ({v} : Set V),
        Psi (hyperClusterSet H omega ({x} : Set V)) * nr H N v omega
          ∂(prodBernoulli H.prob) := by
    rw [← AGBase.integral_mul_ind (μ := prodBernoulli H.prob)
      (avoidEvent H S ({v} : Set V))
      (fun omega => Psi (hyperClusterSet H omega ({x} : Set V)) * nr H N v omega)]
    apply integral_congr_of_forall _
    intro omega
    rw [hind]
    ring
  have hF : (∫ omega, Psi (hyperClusterSet H omega ({x} : Set V)) *
        (1 - nr H S v omega) ∂(prodBernoulli H.prob)) =
      ∫ omega in avoidEvent H S ({v} : Set V),
        Psi (hyperClusterSet H omega ({x} : Set V)) ∂(prodBernoulli H.prob) := by
    rw [← AGBase.integral_mul_ind (μ := prodBernoulli H.prob)
      (avoidEvent H S ({v} : Set V))
      (fun omega => Psi (hyperClusterSet H omega ({x} : Set V)))]
    exact integral_congr_of_forall _ fun omega => congrArg _ (hind omega).symm
  have hN : (∫ omega, (1 - nr H S v omega) * nr H N v omega
        ∂(prodBernoulli H.prob)) =
      ∫ omega in avoidEvent H S ({v} : Set V), nr H N v omega
        ∂(prodBernoulli H.prob) := by
    rw [← AGBase.integral_mul_ind (μ := prodBernoulli H.prob)
      (avoidEvent H S ({v} : Set V)) (fun omega => nr H N v omega)]
    apply integral_congr_of_forall _
    intro omega
    rw [hind]
    ring
  rw [hP, hFN, hF, hN]
  exact key

/-- Law of total covariance along the stopped exploration of `C_N`. -/
theorem yH_totalCovariance [Fintype V] [Fintype E]
    (H : Hypergraph V E) (N S : Set V) (x v : V) (hvS : v ∉ S)
    (Psi : Set V → ℝ) :
    CSHThree.yH H Psi x S v N =
      (∫ omega, Psi (hyperClusterSet H omega ({x} : Set V)) * nr H S v omega
          ∂(prodBernoulli H.prob)) -
        ∫ omega,
          CTBase.cE H N
              (fun eta => Psi (hyperClusterSet H eta ({x} : Set V))) omega *
            CTBase.cE H N (nr H S v) omega ∂(prodBernoulli H.prob) := by
  let f : Set E → ℝ := fun omega => Psi (hyperClusterSet H omega ({x} : Set V))
  let h : Set E → ℝ := fun omega => nr H S v omega
  change CSHThree.yH H Psi x S v N =
    (∫ omega, f omega * h omega ∂(prodBernoulli H.prob)) -
      ∫ omega, CTBase.cE H N f omega * CTBase.cE H N h omega
        ∂(prodBernoulli H.prob)
  rw [CSHThree.yH,
    ← CTBase.integral_cE H N (fun omega => f omega * h omega),
    ← integral_sub_of_fintype (prodBernoulli H.prob)
      (CTBase.cE H N (fun omega => f omega * h omega))
      (fun omega => CTBase.cE H N f omega * CTBase.cE H N h omega)]
  apply integral_congr_of_forall _
  intro omega
  have hM := fun eta => CSHThree.starH_markov H N S x v hvS Psi omega eta
  by_cases hx : x ∈ hyperClusterSet H omega N
  · rw [ind_of_not_mem (fun ha =>
        ((mem_avoidEvent_iff_not_mem H x N omega).1 ha) hx), zero_mul]
    have e1 : CTBase.cE H N (fun eta => f eta * h eta) omega =
        f omega * CTBase.cE H N h omega := by
      refine cE_mul_of_splice_invariant H N (f := h) ?_
      intro eta
      exact (hM eta).1 hx
    have e2 : CTBase.cE H N f omega = f omega :=
      cE_clusterFun_of_mem H N Psi omega hx
    rw [e1, e2]
    ring
  · rw [ind_of_mem ((mem_avoidEvent_iff_not_mem H x N omega).2 hx), one_mul]
    have e2 : CTBase.cE H N f omega =
        ∫ eta, Psi (hyperClusterSet H
            (off H (hyperClusterSet H omega N) eta) ({x} : Set V))
          ∂(prodBernoulli H.prob) := by
      show (∫ eta, f (spliceRecord (recordAt H N omega) eta)
          ∂(prodBernoulli H.prob)) = _
      apply integral_congr_of_forall _
      intro eta
      exact (hM eta).2.1 hx
    by_cases hv : v ∈ hyperClusterSet H omega N
    · have e1 : CTBase.cE H N (fun eta => f eta * h eta) omega =
          h omega * ∫ eta, Psi (hyperClusterSet H
              (off H (hyperClusterSet H omega N) eta) ({x} : Set V))
            ∂(prodBernoulli H.prob) := by
        show (∫ eta, f (spliceRecord (recordAt H N omega) eta) *
            h (spliceRecord (recordAt H N omega) eta)
              ∂(prodBernoulli H.prob)) = _
        rw [← integral_const_mul]
        apply integral_congr_of_forall _
        intro eta
        simp only [f, h]
        rw [(hM eta).2.1 hx, (hM eta).2.2.1 hv]
        ring
      have e3 : CTBase.cE H N h omega = h omega := by
        show (∫ eta, h (spliceRecord (recordAt H N omega) eta)
            ∂(prodBernoulli H.prob)) = h omega
        have hh : ∀ eta : Set E,
            h (spliceRecord (recordAt H N omega) eta) = h omega := by
          intro eta
          exact (hM eta).2.2.1 hv
        simp only [hh]
        simp
      have e4 : CSHThree.covH H Psi x S v (hyperClusterSet H omega N) = 0 := by
        unfold CSHThree.covH
        have z1 : (∫ eta, Psi (hyperClusterSet H
                (off H (hyperClusterSet H omega N) eta) ({x} : Set V)) *
              nr H S v (off H (hyperClusterSet H omega N) eta)
                ∂(prodBernoulli H.prob)) = 0 := by
          have hz : ∀ eta : Set E,
              Psi (hyperClusterSet H
                  (off H (hyperClusterSet H omega N) eta) ({x} : Set V)) *
                nr H S v (off H (hyperClusterSet H omega N) eta) = 0 := by
            intro eta
            rw [(hM eta).2.2.2.2 hv, mul_zero]
          simp only [hz]
          simp
        have z2 : (∫ eta, nr H S v (off H (hyperClusterSet H omega N) eta)
            ∂(prodBernoulli H.prob)) = 0 := by
          have hz : ∀ eta : Set E,
              nr H S v (off H (hyperClusterSet H omega N) eta) = 0 := by
            intro eta
            exact (hM eta).2.2.2.2 hv
          simp only [hz]
          simp
        rw [z1, z2]
        ring
      rw [e1, e2, e3, e4]
      ring
    · have e1 : CTBase.cE H N (fun eta => f eta * h eta) omega =
          ∫ eta, Psi (hyperClusterSet H
              (off H (hyperClusterSet H omega N) eta) ({x} : Set V)) *
            nr H S v (off H (hyperClusterSet H omega N) eta)
              ∂(prodBernoulli H.prob) := by
        show (∫ eta, f (spliceRecord (recordAt H N omega) eta) *
            h (spliceRecord (recordAt H N omega) eta)
              ∂(prodBernoulli H.prob)) = _
        apply integral_congr_of_forall _
        intro eta
        simp only [f, h]
        rw [(hM eta).2.1 hx, (hM eta).2.2.2.1 hv]
      have e3 : CTBase.cE H N h omega =
          ∫ eta, nr H S v (off H (hyperClusterSet H omega N) eta)
            ∂(prodBernoulli H.prob) := by
        show (∫ eta, h (spliceRecord (recordAt H N omega) eta)
            ∂(prodBernoulli H.prob)) = _
        apply integral_congr_of_forall _
        intro eta
        exact (hM eta).2.2.2.1 hv
      rw [e1, e2, e3]
      rfl

/-- The decision-tree companion of `(star^H)`: `Y^H(N) ≤ H(∅)`. -/
theorem yH_le_covH_integral [Fintype V] [Fintype E]
    (H : Hypergraph V E) (N S : Set V) (x v : V) (hvS : v ∉ S)
    (Psi : Set V → ℝ) (hPsi : Monotone Psi) (hPsi0 : ∀ C, 0 ≤ Psi C) :
    CSHThree.yH H Psi x S v N ≤ CSHThree.covH H Psi x S v (∅ : Set V) := by
  let f : Set E → ℝ := fun omega => Psi (hyperClusterSet H omega ({x} : Set V))
  let h : Set E → ℝ := fun omega => nr H S v omega
  have hY := yH_totalCovariance H N S x v hvS Psi
  change CSHThree.yH H Psi x S v N =
    (∫ omega, f omega * h omega ∂(prodBernoulli H.prob)) -
      ∫ omega, CTBase.cE H N f omega * CTBase.cE H N h omega
        ∂(prodBernoulli H.prob) at hY
  have hC : (∫ omega, CTBase.cE H N f omega * CTBase.cE H N h omega
        ∂(prodBernoulli H.prob)) =
      ∫ omega, CTBase.cE H N f omega * h omega ∂(prodBernoulli H.prob) := by
    have key := CTBase.integral_mul_cE_comm H N (CTBase.cE H N f) h
    simpa only [cE_cE] using key
  have hB0 : CSHThree.covH H Psi x S v (∅ : Set V) =
      (∫ omega, f omega * h omega ∂(prodBernoulli H.prob)) -
        (∫ omega, f omega ∂(prodBernoulli H.prob)) *
          ∫ omega, h omega ∂(prodBernoulli H.prob) := by
    simpa only [f, h] using CSHThree.covH_empty H Psi x S v
  let U : Set (Set E) := {omega | ∃ s ∈ S, (openHyperGraph H omega).Reachable s v}
  have hU : IsUpperSet U := by
    intro omega omega' homega
    rintro ⟨s, hs, hsv⟩
    exact ⟨s, hs, hsv.mono (openHyperGraph_le_of_subset H homega)⟩
  have hfmono : Monotone f :=
    fun _ _ homega => hPsi (hyperClusterSet_mono H ({x} : Set V) homega)
  have hf0 : ∀ omega, 0 ≤ f omega := fun omega => hPsi0 _
  have hTH := TreeHK.treeHarris_real_general H N hfmono hf0 hU
  have hUind : ∀ omega : Set E, ind U omega = h omega := fun _ => rfl
  rw [← AGBase.integral_ind (μ := prodBernoulli H.prob) U] at hTH
  simp only [hUind] at hTH
  rw [hY, hC, hB0]
  linarith

/--
The one-source estimate `(star^H)` for an independent hyperedge model.

The exploration is from `N`; the owner `x` belongs to the marker set `S`, while `v` does not.
The proof is the law-of-total-covariance/decision-tree argument of the bond development, with the
member-functional BHK inequality supplied by `bhk14_memberFunctional_integral`.
-/
theorem starH_integral [Fintype V] [Fintype E]
    (H : Hypergraph V E) (N S : Set V) (x v : V) (hvS : v ∉ S)
    (Psi : Set V → ℝ) (hxS : x ∈ S) (hPsi : Monotone Psi)
    (hPsi0 : ∀ C, 0 ≤ Psi C) :
    CSHThree.yH H Psi x S v N *
        (∫ omega, 1 - nr H S v omega ∂(prodBernoulli H.prob))
      ≤ (∫ omega, (1 - nr H S v omega) * (1 - nr H N v omega)
            ∂(prodBernoulli H.prob)) *
          CSHThree.covH H Psi x S v (∅ : Set V) := by
  let f : Set E → ℝ := fun omega => Psi (hyperClusterSet H omega ({x} : Set V))
  let h : Set E → ℝ := fun omega => nr H S v omega
  let n : Set E → ℝ := fun omega => nr H N v omega
  change CSHThree.yH H Psi x S v N * (∫ omega, 1 - h omega ∂(prodBernoulli H.prob)) ≤
    (∫ omega, (1 - h omega) * (1 - n omega) ∂(prodBernoulli H.prob)) *
      CSHThree.covH H Psi x S v (∅ : Set V)

  /- Law of total covariance along the exploration of `C_N`. -/
  have hY : CSHThree.yH H Psi x S v N =
      (∫ omega, f omega * h omega ∂(prodBernoulli H.prob)) -
        ∫ omega, CTBase.cE H N f omega * CTBase.cE H N h omega
          ∂(prodBernoulli H.prob) := by
    rw [CSHThree.yH,
      ← CTBase.integral_cE H N (fun omega => f omega * h omega),
      ← integral_sub_of_fintype (prodBernoulli H.prob)
        (CTBase.cE H N (fun omega => f omega * h omega))
        (fun omega => CTBase.cE H N f omega * CTBase.cE H N h omega)]
    apply integral_congr_of_forall _
    intro omega
    have hM := fun eta => CSHThree.starH_markov H N S x v hvS Psi omega eta
    by_cases hx : x ∈ hyperClusterSet H omega N
    · rw [ind_of_not_mem (fun ha =>
          ((mem_avoidEvent_iff_not_mem H x N omega).1 ha) hx), zero_mul]
      have e1 : CTBase.cE H N (fun eta => f eta * h eta) omega =
          f omega * CTBase.cE H N h omega := by
        refine cE_mul_of_splice_invariant H N (f := h) ?_
        intro eta
        exact (hM eta).1 hx
      have e2 : CTBase.cE H N f omega = f omega := by
        exact cE_clusterFun_of_mem H N Psi omega hx
      rw [e1, e2]
      ring
    · rw [ind_of_mem ((mem_avoidEvent_iff_not_mem H x N omega).2 hx), one_mul]
      have e2 : CTBase.cE H N f omega =
          ∫ eta, Psi (hyperClusterSet H
              (off H (hyperClusterSet H omega N) eta) ({x} : Set V))
            ∂(prodBernoulli H.prob) := by
        show (∫ eta, f (spliceRecord (recordAt H N omega) eta)
            ∂(prodBernoulli H.prob)) = _
        apply integral_congr_of_forall _
        intro eta
        exact (hM eta).2.1 hx
      by_cases hv : v ∈ hyperClusterSet H omega N
      · have e1 : CTBase.cE H N (fun eta => f eta * h eta) omega =
            h omega * ∫ eta, Psi (hyperClusterSet H
                (off H (hyperClusterSet H omega N) eta) ({x} : Set V))
              ∂(prodBernoulli H.prob) := by
          show (∫ eta, f (spliceRecord (recordAt H N omega) eta) *
              h (spliceRecord (recordAt H N omega) eta)
                ∂(prodBernoulli H.prob)) = _
          rw [← integral_const_mul]
          apply integral_congr_of_forall _
          intro eta
          simp only [f, h]
          rw [(hM eta).2.1 hx, (hM eta).2.2.1 hv]
          ring
        have e3 : CTBase.cE H N h omega = h omega := by
          show (∫ eta, h (spliceRecord (recordAt H N omega) eta)
              ∂(prodBernoulli H.prob)) = h omega
          have hh : ∀ eta : Set E,
              h (spliceRecord (recordAt H N omega) eta) = h omega := by
            intro eta
            exact (hM eta).2.2.1 hv
          simp only [hh]
          simp
        have e4 : CSHThree.covH H Psi x S v (hyperClusterSet H omega N) = 0 := by
          unfold CSHThree.covH
          have z1 : (∫ eta, Psi (hyperClusterSet H
                  (off H (hyperClusterSet H omega N) eta) ({x} : Set V)) *
                nr H S v (off H (hyperClusterSet H omega N) eta)
                  ∂(prodBernoulli H.prob)) = 0 := by
            have hz : ∀ eta : Set E,
                Psi (hyperClusterSet H
                    (off H (hyperClusterSet H omega N) eta) ({x} : Set V)) *
                  nr H S v (off H (hyperClusterSet H omega N) eta) = 0 := by
              intro eta
              rw [(hM eta).2.2.2.2 hv, mul_zero]
            simp only [hz]
            simp
          have z2 : (∫ eta, nr H S v (off H (hyperClusterSet H omega N) eta)
              ∂(prodBernoulli H.prob)) = 0 := by
            have hz : ∀ eta : Set E,
                nr H S v (off H (hyperClusterSet H omega N) eta) = 0 := by
              intro eta
              exact (hM eta).2.2.2.2 hv
            simp only [hz]
            simp
          rw [z1, z2]
          ring
        rw [e1, e2, e3, e4]
        ring
      · have e1 : CTBase.cE H N (fun eta => f eta * h eta) omega =
            ∫ eta, Psi (hyperClusterSet H
                (off H (hyperClusterSet H omega N) eta) ({x} : Set V)) *
              nr H S v (off H (hyperClusterSet H omega N) eta)
                ∂(prodBernoulli H.prob) := by
          show (∫ eta, f (spliceRecord (recordAt H N omega) eta) *
              h (spliceRecord (recordAt H N omega) eta)
                ∂(prodBernoulli H.prob)) = _
          apply integral_congr_of_forall _
          intro eta
          simp only [f, h]
          rw [(hM eta).2.1 hx, (hM eta).2.2.2.1 hv]
        have e3 : CTBase.cE H N h omega =
            ∫ eta, nr H S v (off H (hyperClusterSet H omega N) eta)
              ∂(prodBernoulli H.prob) := by
          show (∫ eta, h (spliceRecord (recordAt H N omega) eta)
              ∂(prodBernoulli H.prob)) = _
          apply integral_congr_of_forall _
          intro eta
          exact (hM eta).2.2.2.1 hv
        rw [e1, e2, e3]
        rfl

  /- Move the second conditional expectation across the integral. -/
  have hC : (∫ omega, CTBase.cE H N f omega * CTBase.cE H N h omega
        ∂(prodBernoulli H.prob)) =
      ∫ omega, CTBase.cE H N f omega * h omega ∂(prodBernoulli H.prob) := by
    have key := CTBase.integral_mul_cE_comm H N (CTBase.cE H N f) h
    simpa only [cE_cE] using key

  have hB0 : CSHThree.covH H Psi x S v (∅ : Set V) =
      (∫ omega, f omega * h omega ∂(prodBernoulli H.prob)) -
        (∫ omega, f omega ∂(prodBernoulli H.prob)) *
          ∫ omega, h omega ∂(prodBernoulli H.prob) := by
    simpa only [f, h] using CSHThree.covH_empty H Psi x S v

  /- Gladkov's decision-tree Harris inequality against `{v ↔ S ∪ N}`. -/
  let U : Set (Set E) :=
    {omega | ∃ s ∈ S ∪ N, (openHyperGraph H omega).Reachable s v}
  have hU : IsUpperSet U := by
    intro omega omega' homega
    rintro ⟨s, hs, hsv⟩
    exact ⟨s, hs, hsv.mono (openHyperGraph_le_of_subset H homega)⟩
  have hfmono : Monotone f :=
    fun _ _ homega => hPsi (hyperClusterSet_mono H ({x} : Set V) homega)
  have hf0 : ∀ omega, 0 ≤ f omega := fun omega => hPsi0 _
  have hTH0 := TreeHK.treeHarris_real_general H N hfmono hf0 hU
  have hUind : ∀ omega : Set E, ind U omega = nr H (S ∪ N) v omega := fun _ => rfl
  rw [← AGBase.integral_ind (μ := prodBernoulli H.prob) U] at hTH0
  simp only [hUind] at hTH0
  have hUnion : (∫ omega, nr H (S ∪ N) v omega ∂(prodBernoulli H.prob)) =
      (∫ omega, h omega ∂(prodBernoulli H.prob)) +
        ∫ omega, (1 - h omega) * n omega ∂(prodBernoulli H.prob) := by
    rw [← integral_add (integrable_of_fintype _) (integrable_of_fintype _)]
    apply integral_congr_of_forall _
    intro omega
    simpa only [h, n] using CSHThree.nr_union_eq H S N v omega
  have hUnionR : (∫ omega, CTBase.cE H N f omega * nr H (S ∪ N) v omega
        ∂(prodBernoulli H.prob)) =
      (∫ omega, CTBase.cE H N f omega * h omega ∂(prodBernoulli H.prob)) +
        ∫ omega, CTBase.cE H N f omega * ((1 - h omega) * n omega)
          ∂(prodBernoulli H.prob) := by
    rw [← integral_add (integrable_of_fintype _) (integrable_of_fintype _)]
    apply integral_congr_of_forall _
    intro omega
    rw [CSHThree.nr_union_eq H S N v omega]
    simp only [h, n]
    ring
  rw [hUnion, hUnionR] at hTH0
  have hTH := hTH0

  /- The local factor `(1-h)n` is fixed by the exploration of `N`. -/
  let Z : Set E → ℝ := fun omega => (1 - h omega) * n omega
  have hZlocal : ∀ omega : Set E, CTBase.cE H N Z omega = Z omega := by
    intro omega
    have hM := fun eta => CSHThree.starH_markov H N S x v hvS Psi omega eta
    have hn : ∀ eta : Set E,
        n (spliceRecord (recordAt H N omega) eta) = n omega := by
      intro eta
      have hrec := spliceRecord_mem_recordEvent H N omega eta
      have hcl : hyperClusterSet H (spliceRecord (recordAt H N omega) eta) N =
          hyperClusterSet H omega N := by
        have hr := congrArg ExplorationRecord.reached
          (show recordAt H N (spliceRecord (recordAt H N omega) eta) = recordAt H N omega
            from hrec)
        simpa using hr
      simp only [n, nr_eq_indMem, hcl]
    have hZ : ∀ eta : Set E, Z (spliceRecord (recordAt H N omega) eta) = Z omega := by
      intro eta
      by_cases hv : v ∈ hyperClusterSet H omega N
      · simp only [Z, hn eta]
        simp only [h]
        rw [(hM eta).2.2.1 hv]
      · have hn0 : n omega = 0 := by
          simp only [n, nr_eq_indMem, AGBase.indMem, if_neg hv]
        simp only [Z, hn eta, hn0, mul_zero]
    show (∫ eta, Z (spliceRecord (recordAt H N omega) eta)
        ∂(prodBernoulli H.prob)) = Z omega
    simp only [hZ]
    simp
  have hEZ : (∫ omega, CTBase.cE H N f omega * Z omega
        ∂(prodBernoulli H.prob)) =
      ∫ omega, f omega * Z omega ∂(prodBernoulli H.prob) := by
    have key := CTBase.integral_mul_cE_comm H N f Z
    simp only [hZlocal] at key
    exact key.symm

  /- BHK 1.4, now in exactly the member-functional form needed here. -/
  have hG := bhk14_memberFunctional_integral H S x v hxS N hPsi
  change (∫ omega, 1 - h omega ∂(prodBernoulli H.prob)) *
      (∫ omega, f omega * ((1 - h omega) * n omega)
        ∂(prodBernoulli H.prob)) ≤
    (∫ omega, f omega * (1 - h omega) ∂(prodBernoulli H.prob)) *
      ∫ omega, (1 - h omega) * n omega ∂(prodBernoulli H.prob) at hG

  have hP : (∫ omega, 1 - h omega ∂(prodBernoulli H.prob)) =
      1 - ∫ omega, h omega ∂(prodBernoulli H.prob) := by
    rw [integral_sub_of_fintype]
    simp
  have hQ : (∫ omega, (1 - h omega) * (1 - n omega)
        ∂(prodBernoulli H.prob)) =
      (∫ omega, 1 - h omega ∂(prodBernoulli H.prob)) -
        ∫ omega, (1 - h omega) * n omega ∂(prodBernoulli H.prob) := by
    rw [← integral_sub_of_fintype]
    apply integral_congr_of_forall _
    intro omega
    ring
  have hFh : (∫ omega, f omega * (1 - h omega) ∂(prodBernoulli H.prob)) =
      (∫ omega, f omega ∂(prodBernoulli H.prob)) -
        ∫ omega, f omega * h omega ∂(prodBernoulli H.prob) := by
    rw [← integral_sub_of_fintype]
    apply integral_congr_of_forall _
    intro omega
    ring
  have hP0 : 0 ≤ ∫ omega, 1 - h omega ∂(prodBernoulli H.prob) := by
    apply integral_nonneg
    intro omega
    change (0 : ℝ) ≤ 1 - nr H S v omega
    linarith [(nr_nonneg_le_one H S v omega).2]

  set Efh := ∫ omega, f omega * h omega ∂(prodBernoulli H.prob) with hEfh
  set Ef := ∫ omega, f omega ∂(prodBernoulli H.prob) with hEf
  set Eh := ∫ omega, h omega ∂(prodBernoulli H.prob) with hEh
  set Cgh := ∫ omega, CTBase.cE H N f omega * h omega
    ∂(prodBernoulli H.prob) with hCgh
  set EZ := ∫ omega, (1 - h omega) * n omega ∂(prodBernoulli H.prob) with hEZdef
  set EfZ := ∫ omega, f omega * ((1 - h omega) * n omega)
    ∂(prodBernoulli H.prob) with hEfZ
  have hEZ' : (∫ omega, CTBase.cE H N f omega * ((1 - h omega) * n omega)
      ∂(prodBernoulli H.prob)) = EfZ := by
    simpa only [Z] using hEZ
  rw [hEZ'] at hTH
  rw [hP, hFh] at hG
  rw [hY, hC, hQ, hP, hB0]
  have h1 : (1 - Eh) * (Ef * EZ - EfZ) ≤ (1 - Eh) * (Cgh - Ef * Eh) := by
    have hP0' : 0 ≤ 1 - Eh := by
      rw [← hP]
      exact hP0
    exact mul_le_mul_of_nonneg_left (by linarith) hP0'
  have key : (1 - Eh - EZ) * (Efh - Ef * Eh) - (Efh - Cgh) * (1 - Eh) =
      ((1 - Eh) * (Cgh - Ef * Eh) - (1 - Eh) * (Ef * EZ - EfZ)) +
        (EZ * (Ef - Efh) - (1 - Eh) * EfZ) := by ring
  nlinarith [h1, hG, key]

end KNAll.Site.HyperStarH

end

#print axioms KNAll.Site.HyperStarH.bhk14_memberFunctional_integral
#print axioms KNAll.Site.HyperStarH.yH_totalCovariance
#print axioms KNAll.Site.HyperStarH.yH_le_covH_integral
#print axioms KNAll.Site.HyperStarH.starH_integral
