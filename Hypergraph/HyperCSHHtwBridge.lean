import Hypergraph.HyperA2H

/-!
# The hyperedge Htw bridge

This file translates the labelled finite-world diagonal proved in
`KN.HyperA2H` into the covariance language used by the conditioned slack
hierarchy.  Configurations remain sets of labels throughout.
-/

noncomputable section

namespace KNAll.Site.HyperCSHHtw

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.AGBase KNAll.Site.CTOne KNAll.Site.CSHTwoA
open KNAll.Site.CSHTwoB KNAll.Site.CSHThree KNAll.Site.HyperMetaA2
open KNAll.Site.HyperA2H
open Percolation.Literature.BHK2006 (weight)
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem)
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The event that `u` is connected to at least one member of `S`. -/
def connTo (H : Hypergraph V E) (u : V) (S : Set V) : Set (Set E) :=
  {omega | ∃ s ∈ S, (openHyperGraph H omega).Reachable u s}

theorem connTo_eq_compl_avoid (H : Hypergraph V E) (u : V) (S : Set V) :
    connTo H u S = (avoidEvent H ({u} : Set V) S)ᶜ := by
  ext omega
  simp only [connTo, Set.mem_setOf_eq, Set.mem_compl_iff,
    mem_avoidEvent_singleton_iff]
  push_neg
  rfl

theorem connTo_comm (H : Hypergraph V E) (u : V) (S : Set V) :
    connTo H u S = {omega | ∃ s ∈ S,
      (openHyperGraph H omega).Reachable s u} := by
  ext omega
  simp only [connTo, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h.symm⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, h.symm⟩

@[simp] theorem connTo_singleton (H : Hypergraph V E) (u s : V) :
    connTo H u ({s} : Set V) = hyperConn H u s := by
  ext omega
  simp only [connTo, Set.mem_setOf_eq, Set.mem_singleton_iff, exists_eq_left,
    mem_hyperConn]

theorem ind_connTo_eq_nr (H : Hypergraph V E) (u : V) (S : Set V)
    (omega : Set E) : ind (connTo H u S) omega = nr H S u omega := by
  unfold nr
  rw [← connTo_comm]

theorem connTo_isUpper (H : Hypergraph V E) (u : V) (S : Set V) :
    IsUpperSet (connTo H u S) := by
  intro a b hab
  rintro ⟨s, hs, hreach⟩
  exact ⟨s, hs, hreach.mono (openHyperGraph_le_of_subset H hab)⟩

/-- Avoiding a singleton from a set is the same disconnection event as the
singleton avoiding the set. -/
theorem avoidEvent_set_singleton_comm (H : Hypergraph V E) (S : Set V)
    (u : V) :
    avoidEvent H S ({u} : Set V) = avoidEvent H ({u} : Set V) S := by
  ext omega
  constructor
  · intro h
    refine (mem_avoidEvent_singleton_iff H S u omega).2 fun s hs hus => ?_
    exact Set.disjoint_left.1 ((mem_avoidEvent H S ({u} : Set V) omega).1 h)
      ⟨s, hs, hus.symm⟩ (Set.mem_singleton u)
  · intro h
    refine (mem_avoidEvent H S ({u} : Set V) omega).2
      (Set.disjoint_left.2 fun z hzC hzu => ?_)
    rw [Set.mem_singleton_iff] at hzu
    subst z
    obtain ⟨s, hs, hsu⟩ := hzC
    exact (mem_avoidEvent_singleton_iff H S u omega).1 h s hs hsu.symm

/-- `BfS` on the whole vertex set is the usual covariance with the marker-set
connection event. -/
theorem BfS_univ_eq (H : Hypergraph V E) (x u : V) (S : Set V)
    (Psi : Set V → ℝ) :
    BfS H (fun e => (H.prob e : ℝ)) Finset.univ x S u Psi =
      (∫ omega in connTo H u S,
          Psi (hyperClusterSet H omega ({x} : Set V))
          ∂(prodBernoulli H.prob)) -
        (∫ omega, Psi (hyperClusterSet H omega ({x} : Set V))
          ∂(prodBernoulli H.prob)) *
          (prodBernoulli H.prob).real (connTo H u S) := by
  unfold BfS cfS
  have hprod : (∫ omega in connTo H u S,
      Psi (hyperClusterSet H omega ({x} : Set V))
      ∂(prodBernoulli H.prob)) =
      ∑ omega : Set E, weight (fun e => (H.prob e : ℝ)) omega *
        (Psi (hyperClusterSet H omega ({x} : Set V)) * nr H S u omega) := by
    rw [← AGBase.integral_mul_ind (μ := prodBernoulli H.prob)
      (connTo H u S),
      Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun omega _ => ?_
    rw [ind_connTo_eq_nr]
  have hmean : (∫ omega, Psi (hyperClusterSet H omega ({x} : Set V))
      ∂(prodBernoulli H.prob)) =
      ∑ omega : Set E, weight (fun e => (H.prob e : ℝ)) omega *
        Psi (hyperClusterSet H omega ({x} : Set V)) := by
    rw [Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  have hreal : (prodBernoulli H.prob).real (connTo H u S) =
      ∑ omega : Set E, weight (fun e => (H.prob e : ℝ)) omega * nr H S u omega := by
    rw [← AGBase.integral_ind (μ := prodBernoulli H.prob),
      Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun omega _ => ?_
    rw [ind_connTo_eq_nr]
  simp only [rCluster_univ, labelsIn_univ, Set.inter_univ]
  rw [hprod, hmean, hreal]

/-- The global avoided observer mass in probability notation. -/
theorem Eav_univ_eq (H : Hypergraph V E) (S : Set V) (o v : V)
    (Y : Set V) :
    Eav H (fun e => (H.prob e : ℝ)) Finset.univ S o v Y =
      (prodBernoulli H.prob).real
        (avoidEvent H ({v} : Set V) (S ∪ Y) ∩ hyperConn H o v) := by
  unfold Eav
  rw [← AGBase.integral_ind (μ := prodBernoulli H.prob),
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun omega _ => ?_
  rw [rCluster_univ, rAvoid_univ, indMem_hyperClusterSet, mul_comm,
    ← Percolation.Literature.BHK2006.ind_inter]
  rw [Set.inter_comm (hyperConn H o v)]
  ring

/-- The global avoidance mass in probability notation. -/
theorem Mav_univ_eq (H : Hypergraph V E) (S : Set V) (v : V)
    (Y : Set V) :
    Mav H (fun e => (H.prob e : ℝ)) Finset.univ S v Y =
      (prodBernoulli H.prob).real
        (avoidEvent H ({v} : Set V) (S ∪ Y)) := by
  unfold Mav
  rw [← AGBase.integral_ind (μ := prodBernoulli H.prob),
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun omega _ => ?_
  rw [rAvoid_univ]

/-- Restricting a fresh label record to the world left after exploring `Y`
is exactly deletion of all labels meeting the explored vertex cluster. -/
theorem inter_labelsIn_rest_univ (H : Hypergraph V E) (Y : Set V)
    (omega eta : Set E) :
    eta ∩ labelsIn H (rest H Finset.univ Y omega) =
      off H (hyperClusterSet H omega Y) eta := by
  ext e
  simp only [rest, rCluster_univ, labelsIn, Set.mem_inter_iff, Set.mem_setOf_eq,
    Finset.mem_filter, Finset.mem_univ, true_and, off, Set.mem_sdiff,
    mem_labelsMeeting, not_not]
  constructor
  · rintro ⟨he, hinc⟩
    exact ⟨he, Set.disjoint_left.2 fun v hv hvC => hinc v hv hvC⟩
  · rintro ⟨he, hdisj⟩
    exact ⟨he, fun v hv => Set.disjoint_left.1 hdisj hv⟩

/-- The induced-world covariance is the deleted-world covariance. -/
theorem BfS_rest_univ_eq_covH (H : Hypergraph V E) (Y : Set V)
    (omega : Set E) (x u : V) (S : Set V) (Psi : Set V → ℝ) :
    BfS H (fun e => (H.prob e : ℝ)) (rest H Finset.univ Y omega)
        x S u Psi =
      CSHThree.covH H Psi x S u (hyperClusterSet H omega Y) := by
  unfold BfS cfS CSHThree.covH rCluster
  rw [Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum,
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum,
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  simp only [inter_labelsIn_rest_univ]

theorem BfS_univ_eq_covH (H : Hypergraph V E) (x u : V) (S : Set V)
    (Psi : Set V → ℝ) :
    BfS H (fun e => (H.prob e : ℝ)) Finset.univ x S u Psi =
      CSHThree.covH H Psi x S u ∅ := by
  simpa only [rest_empty, CSHDefs.hyperClusterSet_empty_source] using
    BfS_rest_univ_eq_covH H (∅ : Set V) (∅ : Set E) x u S Psi

/-- The stopped pure-world functional is the average of the deleted-world
covariance over the owner's avoidance event. -/
theorem Yw_BfS_univ_eq (H : Hypergraph V E) (x u : V) (S Y : Set V)
    (Psi : Set V → ℝ) :
    Yw H (fun e => (H.prob e : ℝ)) Finset.univ x
        (fun U' => BfS H (fun e => (H.prob e : ℝ)) U' x S u Psi) Y =
      ∫ omega in avoidEvent H ({x} : Set V) Y,
        CSHThree.covH H Psi x S u (hyperClusterSet H omega Y)
        ∂(prodBernoulli H.prob) := by
  unfold Yw
  rw [← AGBase.integral_mul_ind (μ := prodBernoulli H.prob)
      (avoidEvent H ({x} : Set V) Y),
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun omega _ => ?_
  dsimp only
  rw [BfS_rest_univ_eq_covH, rAvoid_univ]

/-- The stopped tilted-world functional is the same average with the local
conditional observer factor. -/
theorem Xw_BfS_univ_eq (H : Hypergraph V E) (x o u : V) (S Y : Set V)
    (Psi : Set V → ℝ) :
    Xw H (fun e => (H.prob e : ℝ)) Finset.univ x S o u
        (fun U' => BfS H (fun e => (H.prob e : ℝ)) U' x S u Psi) Y =
      ∫ omega in avoidEvent H ({x} : Set V) Y,
        qav H (fun e => (H.prob e : ℝ)) (rest H Finset.univ Y omega)
            S o u *
          CSHThree.covH H Psi x S u (hyperClusterSet H omega Y)
        ∂(prodBernoulli H.prob) := by
  unfold Xw
  rw [← AGBase.integral_mul_ind (μ := prodBernoulli H.prob)
      (avoidEvent H ({x} : Set V) Y),
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun omega _ => ?_
  dsimp only
  rw [BfS_rest_univ_eq_covH, rAvoid_univ]

/-- `(Htw)` in the deleted-world covariance vocabulary. -/
theorem htw_world (H : Hypergraph V E) {x u : V} {S : Set V}
    (hxS : x ∈ S) (huS : u ∉ S) (o : V) {Psi : Set V → ℝ}
    (hPsi : Monotone Psi) (hPsi0 : ∀ C, 0 ≤ Psi C) (Y : Set V) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({u} : Set V) (S ∪ Y) ∩ hyperConn H o u) *
        (∫ omega in avoidEvent H ({x} : Set V) Y,
          CSHThree.covH H Psi x S u (hyperClusterSet H omega Y)
          ∂(prodBernoulli H.prob)) ≤
      (prodBernoulli H.prob).real
          (avoidEvent H ({u} : Set V) (S ∪ Y)) *
        (∫ omega in avoidEvent H ({x} : Set V) Y,
          qav H (fun e => (H.prob e : ℝ)) (rest H Finset.univ Y omega)
              S o u *
            CSHThree.covH H Psi x S u (hyperClusterSet H omega Y)
          ∂(prodBernoulli H.prob)) := by
  have key := HyperA2H.p1H_univ H (fun e => (H.prob e : ℝ))
    (fun e => unitInterval.nonneg (H.prob e))
    (fun e => unitInterval.le_one (H.prob e)) (sum_weight_eq_one H.prob)
    hxS huS o hPsi hPsi0 Y
  rw [Eav_univ_eq, Mav_univ_eq, Yw_BfS_univ_eq,
    Xw_BfS_univ_eq] at key
  exact key

/-! ## The worldwise set-relay transfer -/

/-- Hyperedge form of the set four-point transfer (K6).  Its sole
non-Harris input is `bhk14_memberFunctional`, so the owner functional is read
from the exact open-label cluster rather than from a non-injective vertex
trace. -/
theorem covTransfer_relaySet (H : Hypergraph V E) (S : Set V)
    (o v x : V) (hxS : x ∈ S) (Psi : Set V → ℝ)
    (hPsi : Monotone Psi) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) S ∩ hyperConn H o v) *
        CSHThree.covH H Psi x S v ∅ ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) S) *
        CSHThree.covH H Psi x S o ∅ := by
  set mu := prodBernoulli H.prob with hmu
  set f : Set E → ℝ := fun omega =>
    Psi (hyperClusterSet H omega ({x} : Set V)) with hf
  set m : ℝ := ∫ omega, f omega ∂mu with hm
  set D : Set (Set E) := avoidEvent H ({v} : Set V) S with hD
  set OT : Set (Set E) := connTo H o S with hOT
  set Ov : Set (Set E) := hyperConn H o v with hOv
  set Q : Set (Set E) := connTo H v S with hQ
  set U : Set (Set E) := OT ∪ Ov with hU
  have hmeas : ∀ T : Set (Set E), MeasurableSet T :=
    fun _ => measurableSet_of_fintype _
  have hint : ∀ (T : Set (Set E)), IntegrableOn f T mu :=
    fun _ => (Integrable.of_finite).integrableOn
  have hn := fun (T : Set (Set E)) =>
    (measureReal_nonneg : 0 ≤ mu.real T)

  rw [← BfS_univ_eq_covH H x v S Psi,
    ← BfS_univ_eq_covH H x o S Psi]
  rw [BfS_univ_eq, BfS_univ_eq]
  change mu.real (D ∩ Ov) *
      ((∫ omega in Q, f omega ∂mu) - m * mu.real Q) ≤
    mu.real D * ((∫ omega in OT, f omega ∂mu) - m * mu.real OT)

  have hHarris : mu.real U * m ≤ ∫ omega in U, f omega ∂mu := by
    simpa only [hmu, hf, hm] using
      setIntegral_clusterFun_ge H ({x} : Set V) Psi hPsi U
        ((connTo_isUpper H o S).union (isUpperSet_hyperConn H o v))

  have hBHK := KNAll.Site.LabelClusterBHK.bhk14_memberFunctional
    H S x v hxS ({o} : Set V) hPsi
  rw [avoidEvent_set_singleton_comm H S v] at hBHK
  have hnr : ∀ omega : Set E, nr H ({o} : Set V) v omega = ind Ov omega := by
    intro omega
    rw [← ind_connTo_eq_nr H v ({o} : Set V), connTo_singleton,
      hyperConn_comm H v o]
  simp only [hnr] at hBHK
  rw [AGBase.setIntegral_mul_ind, AGBase.setIntegral_ind] at hBHK
  change mu.real D * (∫ omega in D ∩ Ov, f omega ∂mu) ≤
    (∫ omega in D, f omega ∂mu) * mu.real (D ∩ Ov) at hBHK

  have hUdiff : U \ OT = D ∩ Ov := by
    ext omega
    simp only [hU, hOT, hOv, hD, Set.mem_sdiff, Set.mem_union,
      Set.mem_inter_iff, connTo, Set.mem_setOf_eq, mem_avoidEvent_singleton_iff,
      mem_hyperConn, not_exists, not_and]
    constructor
    · rintro ⟨h | h, hno⟩
      · obtain ⟨t, ht, hot⟩ := h
        exact absurd hot (hno t ht)
      · exact ⟨fun t ht hvt => hno t ht (h.trans hvt), h⟩
    · rintro ⟨hd, hov⟩
      exact ⟨Or.inr hov, fun t ht hot => hd t ht (hov.symm.trans hot)⟩
  have hUint : (∫ omega in U, f omega ∂mu) =
      (∫ omega in OT, f omega ∂mu) +
        ∫ omega in D ∩ Ov, f omega ∂mu := by
    rw [← integral_inter_add_sdiff (hmeas OT) (hint U),
      inter_eq_right.2 subset_union_left, hUdiff]
  have hUmu : mu.real U = mu.real OT + mu.real (D ∩ Ov) := by
    rw [← measureReal_inter_add_sdiff (s := U) (h := measure_ne_top _ _)
      (hmeas OT), inter_eq_right.2 subset_union_left, hUdiff]
  have hDQ : D = Qᶜ := by
    rw [hD, hQ]
    simpa only [compl_compl] using
      (congrArg (fun T : Set (Set E) => Tᶜ)
        (connTo_eq_compl_avoid H v S)).symm
  have hDint : (∫ omega in D, f omega ∂mu) =
      m - ∫ omega in Q, f omega ∂mu := by
    have h := integral_add_compl (hmeas Q)
      (Integrable.of_finite (f := f) (μ := mu))
    rw [← hDQ, ← hm] at h
    linarith
  have hDmu : mu.real D = 1 - mu.real Q := by
    have h := measureReal_add_measureReal_compl (μ := mu) (hmeas Q)
    rw [← hDQ, probReal_univ] at h
    linarith
  have hA : (∫ omega in OT, f omega ∂mu) - mu.real OT * m ≥
      mu.real (D ∩ Ov) * m - ∫ omega in D ∩ Ov, f omega ∂mu := by
    rw [hUint, hUmu] at hHarris
    linarith
  have hB : mu.real D *
        (mu.real (D ∩ Ov) * m - ∫ omega in D ∩ Ov, f omega ∂mu) ≥
      mu.real D * (mu.real (D ∩ Ov) * m) -
        mu.real (D ∩ Ov) * ∫ omega in D, f omega ∂mu := by
    rw [mul_sub]
    nlinarith [hBHK]
  have hC := mul_le_mul_of_nonneg_left hA (hn D)
  rw [hDint, hDmu] at hB
  rw [hDmu] at hC ⊢
  nlinarith [hB, hC, hn (D ∩ Ov), hn Q]

/-! ## The induced/deleted-world dictionary -/

/-- Avoidance in the induced world left after an exploration is avoidance in
the full incidence structure after deleting every label meeting the explored
cluster. -/
theorem mem_rAvoid_rest_univ_iff (H : Hypergraph V E) (Y : Set V)
    (omega eta : Set E) (S : Set V) (u : V) :
    eta ∈ rAvoid H (rest H Finset.univ Y omega) ({u} : Set V) S ↔
      off H (hyperClusterSet H omega Y) eta ∈
        avoidEvent H ({u} : Set V) S := by
  rw [mem_rAvoid, mem_avoidEvent_singleton_iff]
  simp only [rCluster, inter_labelsIn_rest_univ H Y omega eta,
    hyperClusterSet, Set.mem_setOf_eq, Set.mem_singleton_iff, exists_eq_left]

/-- In a world left after exploring `Y`, `Eav` is exactly the corresponding
probability in the hypergraph with all labels meeting the explored cluster
closed. -/
theorem Eav_rest_univ_eq_deleteHyper (H : Hypergraph V E) (Y : Set V)
    (omega : Set E) (S : Set V) (o u : V) :
    Eav H (fun e => (H.prob e : ℝ)) (rest H Finset.univ Y omega) S o u ∅ =
      (prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob).real
        (avoidEvent H ({u} : Set V) S ∩ hyperConn H o u) := by
  let C := hyperClusterSet H omega Y
  let A : Set (Set E) := avoidEvent H ({u} : Set V) S ∩ hyperConn H o u
  have hfun : ∀ eta : Set E,
      AGBase.indMem o
          (rCluster H (rest H Finset.univ Y omega) ({u} : Set V) eta) *
          ind (rAvoid H (rest H Finset.univ Y omega) ({u} : Set V)
            (S ∪ (∅ : Set V))) eta =
        ind A (off H C eta) := by
    intro eta
    rw [Set.union_empty]
    rw [AGBase.ind_congr
      (mem_rAvoid_rest_univ_iff H Y omega eta S u)]
    rw [rCluster, inter_labelsIn_rest_univ H Y omega eta,
      indMem_hyperClusterSet]
    rw [mul_comm, ← Percolation.Literature.BHK2006.ind_inter]
  unfold Eav
  rw [← Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  simp_rw [hfun]
  simp only [off]
  rw [CTOne.integral_comp_sdiff_prodBernoulli H.prob (labelsMeeting H C)]
  change (∫ eta, ind A eta
      ∂(prodBernoulli (deleteHyper H C).prob)) = _
  rw [AGBase.integral_ind]

/-- In a world left after exploring `Y`, `Mav` is exactly the corresponding
avoidance probability in the deleted hypergraph. -/
theorem Mav_rest_univ_eq_deleteHyper (H : Hypergraph V E) (Y : Set V)
    (omega : Set E) (S : Set V) (u : V) :
    Mav H (fun e => (H.prob e : ℝ)) (rest H Finset.univ Y omega) S u ∅ =
      (prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob).real
        (avoidEvent H ({u} : Set V) S) := by
  let C := hyperClusterSet H omega Y
  let A : Set (Set E) := avoidEvent H ({u} : Set V) S
  have hfun : ∀ eta : Set E,
      ind (rAvoid H (rest H Finset.univ Y omega) ({u} : Set V)
        (S ∪ (∅ : Set V))) eta = ind A (off H C eta) := by
    intro eta
    rw [Set.union_empty]
    exact AGBase.ind_congr
      (mem_rAvoid_rest_univ_iff H Y omega eta S u)
  unfold Mav
  rw [← Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  simp_rw [hfun]
  simp only [off]
  rw [CTOne.integral_comp_sdiff_prodBernoulli H.prob (labelsMeeting H C)]
  change (∫ eta, ind A eta
      ∂(prodBernoulli (deleteHyper H C).prob)) = _
  rw [AGBase.integral_ind]

/-- Consequently the induced observer ratio `qav` is the ordinary observer
constant in the deleted hypergraph. -/
theorem qav_rest_univ_eq_deleteHyper_obsConst (H : Hypergraph V E)
    (Y : Set V) (omega : Set E) (S : Set V) (o u : V) :
    qav H (fun e => (H.prob e : ℝ)) (rest H Finset.univ Y omega) S o u =
      obsConst (deleteHyper H (hyperClusterSet H omega Y)) o u S := by
  unfold qav obsConst
  rw [Eav_rest_univ_eq_deleteHyper, Mav_rest_univ_eq_deleteHyper]
  rw [hyperConn_deleteHyper]
  rfl

/-- Covariance in the deleted hypergraph, with no further deletion, is the
same quantity as `covH` in the original hypergraph at that deleted set. -/
theorem covH_deleteHyper_empty_eq (H : Hypergraph V E) (C : Set V)
    (Psi : Set V → ℝ) (x : V) (S : Set V) (u : V) :
    CSHThree.covH (deleteHyper H C) Psi x S u ∅ =
      CSHThree.covH H Psi x S u C := by
  unfold CSHThree.covH
  simp only [off_empty, hyperClusterSet_deleteHyper]
  have hnr : nr (deleteHyper H C) S u = nr H S u := rfl
  rw [hnr]
  change
    (∫ eta, Psi (hyperClusterSet H eta ({x} : Set V)) * nr H S u eta
        ∂(prodBernoulli (fun e => if e ∈ labelsMeeting H C then 0 else H.prob e))) -
      (∫ eta, Psi (hyperClusterSet H eta ({x} : Set V))
        ∂(prodBernoulli (fun e => if e ∈ labelsMeeting H C then 0 else H.prob e))) *
        ∫ eta, nr H S u eta
          ∂(prodBernoulli (fun e => if e ∈ labelsMeeting H C then 0 else H.prob e)) = _
  rw [← CTOne.integral_comp_sdiff_prodBernoulli H.prob
      (labelsMeeting H C)
      (fun eta => Psi (hyperClusterSet H eta ({x} : Set V)) * nr H S u eta),
    ← CTOne.integral_comp_sdiff_prodBernoulli H.prob
      (labelsMeeting H C)
      (fun eta => Psi (hyperClusterSet H eta ({x} : Set V))),
    ← CTOne.integral_comp_sdiff_prodBernoulli H.prob
      (labelsMeeting H C) (nr H S u)]
  simp only [off]

/-- An event containing the empty label configuration has positive product
probability when no coordinate has probability one.  Unlike the usual
full-support lemma, this permits the zero coordinates created by deletion. -/
theorem prodBernoulli_real_pos_of_empty_mem (p : E → unitInterval)
    (hp : ∀ e, p e < 1) {A : Set (Set E)} (hA : (∅ : Set E) ∈ A) :
    0 < (prodBernoulli p).real A := by
  have hcyl := prodBernoulli_real_setOf_forall_iff p Finset.univ
    (· ∈ (∅ : Set E))
  have hpos : 0 < (prodBernoulli p).real
      {eta : Set E | ∀ e ∈ (Finset.univ : Finset E),
        (e ∈ eta ↔ e ∈ (∅ : Set E))} := by
    rw [hcyl]
    refine Finset.prod_pos fun e _ => ?_
    rw [if_neg (Set.notMem_empty e)]
    exact sub_pos.2 (unitInterval.coe_lt_one.2 (hp e))
  have hsub : {eta : Set E | ∀ e ∈ (Finset.univ : Finset E),
      (e ∈ eta ↔ e ∈ (∅ : Set E))} ⊆ A := by
    intro eta heta
    have heq : eta = ∅ := Set.ext fun e => heta e (Finset.mem_univ e)
    rw [heq]
    exact hA
  exact hpos.trans_le (measureReal_mono hsub)

/-- The H-part of the conditioned-slack unfolding is nonnegative.  The proof
combines the worldwise relay transfer with `htw_world`; all divisions are by
explicitly positive empty-configuration probabilities. -/
theorem hpart_nonneg (H : Hypergraph V E)
    (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1)
    {x u : V} {S : Set V} (hxS : x ∈ S) (huS : u ∉ S)
    (o : V) {Psi : Set V → ℝ} (hPsi : Monotone Psi)
    (hPsi0 : ∀ C, 0 ≤ Psi C) (Y : Set V) (huY : u ∉ Y) :
    0 ≤ ∫ omega in avoidEvent H ({x} : Set V) Y,
      (CSHThree.covH H Psi x S o (hyperClusterSet H omega Y) -
        obsConst H o u (S ∪ Y) *
          CSHThree.covH H Psi x S u (hyperClusterSet H omega Y))
      ∂(prodBernoulli H.prob) := by
  let mu := prodBernoulli H.prob
  let Dset : Set (Set E) := avoidEvent H ({x} : Set V) Y
  let CovO : Set E → ℝ := fun omega =>
    CSHThree.covH H Psi x S o (hyperClusterSet H omega Y)
  let CovU : Set E → ℝ := fun omega =>
    CSHThree.covH H Psi x S u (hyperClusterSet H omega Y)
  let pW : Set E → ℝ := fun omega =>
    qav H (fun e => (H.prob e : ℝ)) (rest H Finset.univ Y omega) S o u
  let M : ℝ := mu.real (avoidEvent H ({u} : Set V) (S ∪ Y))
  let A : ℝ := mu.real
    (avoidEvent H ({u} : Set V) (S ∪ Y) ∩ hyperConn H o u)
  change 0 ≤ ∫ omega in Dset,
    (CovO omega - obsConst H o u (S ∪ Y) * CovU omega) ∂mu
  have hmeas : ∀ T : Set (Set E), MeasurableSet T :=
    fun _ => measurableSet_of_fintype _
  have hint : ∀ (f : Set E → ℝ) (T : Set (Set E)), IntegrableOn f T mu :=
    fun _ _ => (Integrable.of_finite).integrableOn
  have hMpos : 0 < M := by
    apply prodBernoulli_real_pos_of_nonempty hp
    refine ⟨∅, empty_mem_avoidEvent_singleton H ?_⟩
    simpa only [Set.mem_union, not_or] using And.intro huS huY
  have hobs : obsConst H o u (S ∪ Y) = A / M := by
    unfold obsConst A M mu
    rfl
  have hworld : ∀ omega : Set E, pW omega * CovU omega ≤ CovO omega := by
    intro omega
    let C := hyperClusterSet H omega Y
    let HW := deleteHyper H C
    have hK6 := covTransfer_relaySet HW S o u x hxS Psi hPsi
    have hlt : ∀ e, HW.prob e < 1 := by
      intro e
      simp only [HW, deleteHyper]
      split_ifs
      · exact zero_lt_one
      · exact (hp e).2
    have hMWpos : 0 < (prodBernoulli HW.prob).real
        (avoidEvent HW ({u} : Set V) S) := by
      refine prodBernoulli_real_pos_of_empty_mem HW.prob hlt ?_
      exact empty_mem_avoidEvent_singleton HW huS
    let MW : ℝ := (prodBernoulli HW.prob).real
      (avoidEvent HW ({u} : Set V) S)
    let EW : ℝ := (prodBernoulli HW.prob).real
      (avoidEvent HW ({u} : Set V) S ∩ hyperConn HW o u)
    change EW * CSHThree.covH HW Psi x S u ∅ ≤
      MW * CSHThree.covH HW Psi x S o ∅ at hK6
    have hpW : pW omega = EW / MW := by
      unfold pW EW MW HW C
      rw [qav_rest_univ_eq_deleteHyper_obsConst]
      rfl
    have hCovU : CovU omega = CSHThree.covH HW Psi x S u ∅ := by
      unfold CovU HW C
      rw [covH_deleteHyper_empty_eq]
    have hCovO : CovO omega = CSHThree.covH HW Psi x S o ∅ := by
      unfold CovO HW C
      rw [covH_deleteHyper_empty_eq]
    rw [hpW, hCovU, hCovO, div_mul_eq_mul_div,
      div_le_iff₀ hMWpos]
    simpa only [mul_comm] using hK6
  have hI1 : ∫ omega in Dset, pW omega * CovU omega ∂mu ≤
      ∫ omega in Dset, CovO omega ∂mu :=
    setIntegral_mono_on (hint _ _) (hint _ _) (hmeas Dset)
      (fun omega _ => hworld omega)
  have hHtw := htw_world H hxS huS o hPsi hPsi0 Y
  change A * ∫ omega in Dset, CovU omega ∂mu ≤
    M * ∫ omega in Dset, pW omega * CovU omega ∂mu at hHtw
  have hI2 : A / M * ∫ omega in Dset, CovU omega ∂mu ≤
      ∫ omega in Dset, pW omega * CovU omega ∂mu := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hMpos]
    simpa only [mul_comm] using hHtw
  rw [integral_sub (hint _ _) (hint _ _), integral_const_mul, hobs]
  linarith

end KNAll.Site.HyperCSHHtw

end

#print axioms KNAll.Site.HyperCSHHtw.BfS_univ_eq
#print axioms KNAll.Site.HyperCSHHtw.htw_world
#print axioms KNAll.Site.HyperCSHHtw.covTransfer_relaySet
#print axioms KNAll.Site.HyperCSHHtw.hpart_nonneg
