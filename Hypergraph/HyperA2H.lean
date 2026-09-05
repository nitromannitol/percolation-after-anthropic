import Hypergraph.HyperMetaA2

/-!
# The hyperedge two-source diagonal

This is the labelled-hyperedge analogue of `CovTau/A2H.lean`.  The world
functional is the covariance, in the model induced on `U`, of an increasing
function of the owner's vertex cluster with the event that the marker `v`
reaches the marker set `S`.  The proof deliberately keeps configurations as
sets of *labels*.  In particular, it never replaces an intersection of label
records by an intersection of their vertex traces.
-/

noncomputable section

namespace KNAll.Site.HyperA2H

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.AGBase KNAll.Site.CTOne KNAll.Site.CSHTwoB
open KNAll.Site.CSHTwoA KNAll.Site.CSHThree KNAll.Site.HyperMetaA2
open Percolation.Literature.BHK2006 (weight weight_nonneg harris)
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-!
This executable-sized regression records the obstruction that the META-A2
allocation must respect.  The two different Boolean labels have the same
one-vertex outside trace, although their intersection has empty trace.
-/
theorem noninjective_trace_inter_regression :
    traceOutside twoLabelHypergraph (∅ : Set Unit)
          (({true} : Set Bool) ∩ ({false} : Set Bool)) ≠
      traceOutside twoLabelHypergraph (∅ : Set Unit) ({true} : Set Bool) ∩
        traceOutside twoLabelHypergraph (∅ : Set Unit) ({false} : Set Bool) := by
  intro heq
  have hu : () ∈ traceOutside twoLabelHypergraph (∅ : Set Unit) ({true} : Set Bool) ∩
      traceOutside twoLabelHypergraph (∅ : Set Unit) ({false} : Set Bool) :=
    ⟨mem_traceOutside_twoLabelHypergraph true (),
      mem_traceOutside_twoLabelHypergraph false ()⟩
  rw [← heq] at hu
  obtain ⟨e, he, -⟩ :=
    (mem_traceOutside_iff twoLabelHypergraph (∅ : Set Unit)
      (({true} : Set Bool) ∩ ({false} : Set Bool)) ()).1 hu
  have ht : e = true := he.1
  have hf : e = false := he.2
  rw [ht] at hf
  exact Bool.noConfusion hf

/-- The probability mass, in the model induced on `U`, that `v` reaches `S`. -/
def cfS (H : Hypergraph V E) (w : E → ℝ) (U : Finset V)
    (S : Set V) (v : V) : ℝ :=
  ∑ omega : Set E, weight w omega * nr H S v (omega ∩ labelsIn H U)

/-- The vertex-cluster version of the covariance world functional. -/
def BfS (H : Hypergraph V E) (w : E → ℝ) (U : Finset V)
    (x : V) (S : Set V) (v : V) (Psi : Set V → ℝ) : ℝ :=
  (∑ omega : Set E, weight w omega *
      (Psi (rCluster H U ({x} : Set V) omega) *
        nr H S v (omega ∩ labelsIn H U))) -
    (∑ omega : Set E, weight w omega *
      Psi (rCluster H U ({x} : Set V) omega)) * cfS H w U S v

/-- The induced marker event is increasing in the open-label configuration. -/
theorem nr_inter_labelsIn_mono (H : Hypergraph V E) (U : Finset V)
    (S : Set V) (v : V) :
    Monotone (fun omega : Set E => nr H S v (omega ∩ labelsIn H U)) := by
  intro a b hab
  unfold nr
  change ind {omega : Set E | ∃ s ∈ S,
      (openHyperGraph H omega).Reachable s v} (a ∩ labelsIn H U) ≤
    ind {omega : Set E | ∃ s ∈ S,
      (openHyperGraph H omega).Reachable s v} (b ∩ labelsIn H U)
  by_cases ha : ∃ s ∈ S, (openHyperGraph H (a ∩ labelsIn H U)).Reachable s v
  · have ha' : a ∩ labelsIn H U ∈
        {omega : Set E | ∃ s ∈ S, (openHyperGraph H omega).Reachable s v} := ha
    have hb' : b ∩ labelsIn H U ∈
        {omega : Set E | ∃ s ∈ S, (openHyperGraph H omega).Reachable s v} :=
      ⟨ha.choose, ha.choose_spec.1,
      ha.choose_spec.2.mono (openHyperGraph_le_of_subset H
        (Set.inter_subset_inter_left _ hab))⟩
    rw [ind_of_mem ha', ind_of_mem hb']
  · have ha' : a ∩ labelsIn H U ∉
        {omega : Set E | ∃ s ∈ S, (openHyperGraph H omega).Reachable s v} := ha
    rw [ind_of_not_mem ha']
    exact ind_nonneg _ _

/-- `BfS` is nonnegative by Harris association. -/
theorem BfS_nonneg (H : Hypergraph V E) {w : E → ℝ}
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ omega : Set E, weight w omega = 1)
    (U : Finset V) (x : V) (S : Set V) (v : V)
    {Psi : Set V → ℝ} (hPsi : Monotone Psi) (hPsi0 : ∀ C, 0 ≤ Psi C) :
    0 ≤ BfS H w U x S v Psi := by
  have hh := harris hw0 hw1
    (f := fun omega : Set E => Psi (rCluster H U ({x} : Set V) omega))
    (g := fun omega : Set E => nr H S v (omega ∩ labelsIn H U))
    (fun omega => hPsi0 _) (fun omega => (nr_nonneg_le_one H S v _).1)
    (fun _ _ hab => hPsi (rCluster_mono H U ({x} : Set V) hab))
    (nr_inter_labelsIn_mono H U S v)
  rw [hm, one_mul] at hh
  unfold BfS cfS
  linarith

/-- A marker outside the current world cannot be reached from `S`, unless it
is itself in `S`; the latter case is explicitly excluded. -/
theorem nr_inter_labelsIn_eq_zero_of_not_mem (H : Hypergraph V E)
    {U : Finset V} {S : Set V} {v : V} (hvU : v ∉ U) (hvS : v ∉ S)
    (omega : Set E) : nr H S v (omega ∩ labelsIn H U) = 0 := by
  unfold nr
  rw [ind_of_not_mem]
  rintro ⟨s, hs, hsv⟩
  have hsvne : s ≠ v := fun h => hvS (h ▸ hs)
  exact hvU (AGBase.mem_of_reachable hsv hsvne)

/-- The covariance vanishes in a world missing the marker. -/
theorem BfS_eq_zero_of_not_mem (H : Hypergraph V E) (w : E → ℝ)
    {U : Finset V} (x : V) {S : Set V} {v : V} (hvU : v ∉ U)
    (hvS : v ∉ S) (Psi : Set V → ℝ) :
    BfS H w U x S v Psi = 0 := by
  unfold BfS cfS
  simp only [nr_inter_labelsIn_eq_zero_of_not_mem H hvU hvS,
    mul_zero, Finset.sum_const_zero]
  ring

/-! ## Weighted-cube dictionary -/

open Percolation.Literature.DecisionTree (ED)
open Percolation.Continuity.CovTauStarN (ED_congr_on)

/-- The owner's vertex-cluster functional on a finite open-label record. -/
def fclV (H : Hypergraph V E) (Psi : Set V → ℝ) (x : V)
    (K : Finset E) : ℝ :=
  Psi (hyperClusterSet H (↑K : Set E) ({x} : Set V))

/-- Reachability of the marker from a source set on a finite label record. -/
def nrF (H : Hypergraph V E) (S : Set V) (v : V) (K : Finset E) : ℝ :=
  nr H S v (↑K : Set E)

/-- Delete from a finite record all labels meeting `W`. -/
def offF [DecidableEq E] (H : Hypergraph V E) (W : Set V)
    (K : Finset E) : Finset E :=
  K.filter fun e => Disjoint (H.incidence e) W

@[simp] theorem mem_offF [DecidableEq E] {H : Hypergraph V E}
    {W : Set V} {K : Finset E} {e : E} :
    e ∈ offF H W K ↔ e ∈ K ∧ Disjoint (H.incidence e) W := by
  simp [offF]

theorem coe_offF [DecidableEq E] (H : Hypergraph V E) (W : Set V)
    (K : Finset E) :
    (↑(offF H W K) : Set E) = off H W (↑K : Set E) := by
  ext e
  simp only [mem_offF, Finset.mem_coe, off, Set.mem_sdiff,
    mem_labelsMeeting, not_not]

/-- The covariance on a finite coordinate world. -/
def covED [DecidableEq E] (H : Hypergraph V E) (D : Finset E)
    (w : E → ℝ) (Psi : Set V → ℝ) (x : V) (S : Set V)
    (v : V) (W : Set V) : ℝ :=
  ED D w (fun K => fclV H Psi x (offF H W K) *
      nrF H S v (offF H W K)) -
    ED D w (fun K => fclV H Psi x (offF H W K)) *
      ED D w (fun K => nrF H S v (offF H W K))

/-- The stopped covariance on a finite coordinate world. -/
def yED [DecidableEq E] (H : Hypergraph V E) (D : Finset E)
    (w : E → ℝ) (Psi : Set V → ℝ) (x : V) (S : Set V)
    (v : V) (N : Set V) : ℝ :=
  ED D w (fun K =>
    ind {L : Finset E | x ∉ TreeHK.reachedBy H N L} K *
      covED H D w Psi x S v (TreeHK.reachedBy H N K))

/-- In an induced world, the restricted vertex cluster is the full cluster of
the finite label record. -/
theorem rCluster_coe_eq {H : Hypergraph V E} {U : Finset V}
    {K : Finset E} (hK : K ⊆ labelsInF H U) (S : Set V) :
    rCluster H U S (↑K : Set E) = hyperClusterSet H (↑K : Set E) S := by
  unfold rCluster
  rw [coe_inter_labelsIn_of_subset hK]

/-- The avoidance indicator of a union is the product of the two complementary
reachability indicators. -/
theorem ind_rAvoid_union_eq {H : Hypergraph V E} {U : Finset V}
    (v : V) (S N : Set V) {K : Finset E} (hK : K ⊆ labelsInF H U) :
    ind (rAvoid H U ({v} : Set V) (S ∪ N)) (↑K : Set E) =
      (1 - nrF H S v K) * (1 - nrF H N v K) := by
  have hcl : rCluster H U ({v} : Set V) (↑K : Set E) =
      hyperClusterSet H (↑K : Set E) ({v} : Set V) :=
    rCluster_coe_eq hK _
  have hav : (↑K : Set E) ∈ rAvoid H U ({v} : Set V) (S ∪ N) ↔
      (¬ ∃ s ∈ S, (openHyperGraph H (↑K : Set E)).Reachable s v) ∧
      (¬ ∃ n ∈ N, (openHyperGraph H (↑K : Set E)).Reachable n v) := by
    simp only [mem_rAvoid, Set.mem_union, or_imp, forall_and, hcl,
      hyperClusterSet, Set.mem_setOf_eq, Set.mem_singleton_iff, exists_eq_left]
    constructor
    · intro h
      exact ⟨fun ⟨s, hs, hsv⟩ => h.1 s hs hsv.symm,
        fun ⟨n, hn, hnv⟩ => h.2 n hn hnv.symm⟩
    · rintro ⟨hS, hN⟩
      exact ⟨fun s hs hvs => hS ⟨s, hs, hvs.symm⟩,
        fun n hn hvn => hN ⟨n, hn, hvn.symm⟩⟩
  unfold nrF nr
  by_cases hS : ∃ s ∈ S, (openHyperGraph H (↑K : Set E)).Reachable s v
  · have hSm : (↑K : Set E) ∈
        {omega : Set E | ∃ s ∈ S, (openHyperGraph H omega).Reachable s v} := hS
    rw [ind_of_mem hSm, ind_of_not_mem (fun h => (hav.1 h).1 hS)]
    ring
  · have hSn : (↑K : Set E) ∉
        {omega : Set E | ∃ s ∈ S, (openHyperGraph H omega).Reachable s v} := hS
    rw [ind_of_not_mem hSn]
    by_cases hN : ∃ n ∈ N, (openHyperGraph H (↑K : Set E)).Reachable n v
    · have hNm : (↑K : Set E) ∈
          {omega : Set E | ∃ n ∈ N, (openHyperGraph H omega).Reachable n v} := hN
      rw [ind_of_mem hNm, ind_of_not_mem (fun h => (hav.1 h).2 hN)]
      ring
    · have hNn : (↑K : Set E) ∉
          {omega : Set E | ∃ n ∈ N, (openHyperGraph H omega).Reachable n v} := hN
      rw [ind_of_not_mem hNn, ind_of_mem (hav.2 ⟨hS, hN⟩)]
      ring

/-- `Mav` in the induced world as a weighted-cube expectation. -/
theorem Mav_eq_ED (H : Hypergraph V E) (w : E → ℝ) (U : Finset V)
    (S : Set V) (v : V) (N : Set V) :
    Mav H w U S v N =
      ED (labelsInF H U) w
        (fun K => (1 - nrF H S v K) * (1 - nrF H N v K)) := by
  unfold Mav
  rw [sum_weight_restrict H w U _ (fun omega => by
    refine AGBase.ind_congr ?_
    simp only [mem_rAvoid]
    unfold rCluster
    rw [Set.inter_assoc, Set.inter_self])]
  exact ED_congr_on _ w fun K hK =>
    ind_rAvoid_union_eq v S N (Finset.mem_powerset.1 hK)

/-- The empty second avoided source removes the second factor. -/
theorem Mav_empty_eq_ED (H : Hypergraph V E) (w : E → ℝ)
    (U : Finset V) (S : Set V) (v : V) :
    Mav H w U S v ∅ =
      ED (labelsInF H U) w (fun K => 1 - nrF H S v K) := by
  rw [Mav_eq_ED]
  refine ED_congr_on _ w fun K _ => ?_
  have hz : nrF H (∅ : Set V) v K = 0 := by
    unfold nrF nr
    rw [ind_of_not_mem]
    exact fun ⟨s, hs, _⟩ => hs
  rw [hz]
  ring

/-- Removing a finite vertex set from the coordinate world is the same as
intersecting each record with the smaller induced coordinate set. -/
theorem offF_eq_inter {H : Hypergraph V E} {U W : Finset V}
    {K : Finset E} (hK : K ⊆ labelsInF H U) :
    offF H (↑W : Set V) K = K ∩ labelsInF H (U \ W) := by
  rw [labelsInF_sdiff]
  ext e
  simp only [mem_offF, Finset.mem_inter, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, hK h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- `BfS` in `U \ W` is the finite-coordinate covariance obtained by closing
the labels meeting `W`. -/
theorem BfS_sdiff_eq_covED (H : Hypergraph V E) (w : E → ℝ)
    (U W : Finset V) (x : V) (S : Set V) (v : V) (Psi : Set V → ℝ) :
    BfS H w (U \ W) x S v Psi =
      covED H (labelsInF H U) w Psi x S v (↑W : Set V) := by
  have hsub : labelsInF H (U \ W) ⊆ labelsInF H U :=
    fun e he => mem_labelsInF.2 (labelsIn_mono H Finset.sdiff_subset
      (mem_labelsInF.1 he))
  have h1 : (∑ omega : Set E, weight w omega *
      (Psi (rCluster H (U \ W) ({x} : Set V) omega) *
        nr H S v (omega ∩ labelsIn H (U \ W)))) =
      ED (labelsInF H (U \ W)) w
        (fun K => fclV H Psi x K * nrF H S v K) := by
    rw [sum_weight_restrict H w (U \ W) _ (fun omega => by
      simp only [rCluster, Set.inter_assoc, Set.inter_self])]
    exact ED_congr_on _ w fun K hK => by
      rw [rCluster_coe_eq (Finset.mem_powerset.1 hK)]
      unfold fclV nrF
      rw [coe_inter_labelsIn_of_subset (Finset.mem_powerset.1 hK)]
  have h2 : (∑ omega : Set E, weight w omega *
      Psi (rCluster H (U \ W) ({x} : Set V) omega)) =
      ED (labelsInF H (U \ W)) w (fclV H Psi x) := by
    rw [sum_weight_restrict H w (U \ W) _ (fun omega => by
      simp only [rCluster, Set.inter_assoc, Set.inter_self])]
    exact ED_congr_on _ w fun K hK => by
      rw [rCluster_coe_eq (Finset.mem_powerset.1 hK)]
      rfl
  have h3 : cfS H w (U \ W) S v =
      ED (labelsInF H (U \ W)) w (nrF H S v) := by
    unfold cfS
    rw [sum_weight_restrict H w (U \ W) _ (fun omega => by
      simp only [Set.inter_assoc, Set.inter_self])]
    exact ED_congr_on _ w fun K hK => by
      unfold nrF
      rw [coe_inter_labelsIn_of_subset (Finset.mem_powerset.1 hK)]
  unfold BfS covED
  rw [h1, h2, h3]
  have e1 : ED (labelsInF H U) w (fun K =>
      fclV H Psi x (offF H (↑W : Set V) K) *
        nrF H S v (offF H (↑W : Set V) K)) =
      ED (labelsInF H (U \ W)) w
        (fun K => fclV H Psi x K * nrF H S v K) := by
    rw [← Percolation.Continuity.CovTauStarN.ED_inter_eq hsub w
      (fun K => fclV H Psi x K * nrF H S v K)]
    exact ED_congr_on _ w fun K hK => by
      rw [offF_eq_inter (Finset.mem_powerset.1 hK)]
  have e2 : ED (labelsInF H U) w
      (fun K => fclV H Psi x (offF H (↑W : Set V) K)) =
      ED (labelsInF H (U \ W)) w (fclV H Psi x) := by
    rw [← Percolation.Continuity.CovTauStarN.ED_inter_eq hsub w (fclV H Psi x)]
    exact ED_congr_on _ w fun K hK => by
      rw [offF_eq_inter (Finset.mem_powerset.1 hK)]
  have e3 : ED (labelsInF H U) w
      (fun K => nrF H S v (offF H (↑W : Set V) K)) =
      ED (labelsInF H (U \ W)) w (nrF H S v) := by
    rw [← Percolation.Continuity.CovTauStarN.ED_inter_eq hsub w (nrF H S v)]
    exact ED_congr_on _ w fun K hK => by
      rw [offF_eq_inter (Finset.mem_powerset.1 hK)]
  rw [e1, e2, e3]

theorem BfS_eq_covED (H : Hypergraph V E) (w : E → ℝ)
    (U : Finset V) (x : V) (S : Set V) (v : V) (Psi : Set V → ℝ) :
    BfS H w U x S v Psi =
      covED H (labelsInF H U) w Psi x S v (∅ : Set V) := by
  simpa only [Finset.sdiff_empty, Finset.coe_empty] using
    BfS_sdiff_eq_covED H w U ∅ x S v Psi

/-- The finite presentation of a vertex set. -/
def verticesFinset (W : Set V) : Finset V :=
  Finset.univ.filter fun v => v ∈ W

@[simp] theorem coe_verticesFinset (W : Set V) :
    (↑(verticesFinset W) : Set V) = W := by
  ext v
  simp [verticesFinset]

/-- The residual world is the ambient world minus the finite reached set. -/
theorem rest_eq_sdiff_vertices {H : Hypergraph V E} {U : Finset V}
    {N : Set V} {K : Finset E} (hK : K ⊆ labelsInF H U) :
    rest H U N (↑K : Set E) =
      U \ verticesFinset (TreeHK.reachedBy H N K) := by
  ext v
  rw [Finset.mem_sdiff, CSHThree.rest_eq_sdiff hK v]
  simp only [verticesFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `Yw` of the covariance world functional is the stopped finite-coordinate
covariance. -/
theorem Yw_BfS_eq_yED (H : Hypergraph V E) (w : E → ℝ)
    (U : Finset V) (x : V) (S : Set V) (v : V) (Psi : Set V → ℝ)
    (N : Set V) :
    Yw H w U x (fun U' => BfS H w U' x S v Psi) N =
      yED H (labelsInF H U) w Psi x S v N := by
  unfold Yw yED
  rw [sum_weight_restrict H w U _ (fun omega => by
    have hrest : rest H U N (omega ∩ labelsIn H U) = rest H U N omega := by
      unfold rest rCluster
      rw [Set.inter_assoc, Set.inter_self]
    have hav : ind (rAvoid H U ({x} : Set V) N)
        (omega ∩ labelsIn H U) =
        ind (rAvoid H U ({x} : Set V) N) omega := by
      refine AGBase.ind_congr ?_
      simp only [mem_rAvoid]
      unfold rCluster
      rw [Set.inter_assoc, Set.inter_self]
    rw [hrest, hav])]
  refine ED_congr_on _ w fun K hKmem => ?_
  have hK : K ⊆ labelsInF H U := Finset.mem_powerset.1 hKmem
  have hrest := rest_eq_sdiff_vertices (H := H) (N := N) hK
  have hind := CSHThree.ind_rAvoid_eq (H := H) (U := U) x N hK
  dsimp only
  rw [hrest, BfS_sdiff_eq_covED, hind, coe_verticesFinset]
  ring

/-! ## The one-source inputs in META-A2 vocabulary -/

/-- A product probability vector equal to `w` on `D` and zero elsewhere. -/
def cubeProb (D : Finset E) (w : E → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) : E → unitInterval :=
  fun e => if he : e ∈ D then ⟨w e, hw0 e, hw1 e⟩ else 0

theorem integral_cubeProb_eq_ED (H : Hypergraph V E) (D : Finset E)
    (w : E → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (Phi : Set E → ℝ) :
    (∫ omega, Phi omega ∂(prodBernoulli (cubeProb D w hw0 hw1))) =
      ED D w (fun K => Phi (↑K : Set E)) := by
  rw [Percolation.Continuity.CovTauStarN.integral_eq_ED]
  apply Percolation.Continuity.CovTauStarN.ED_univ_eq_ED_of_zero D w
  · intro e he
    simp [cubeProb, he]
  · intro e he
    simp [cubeProb, he]

/-- `covH` for the cube whose live coordinates are `D` is `covED D`. -/
theorem covH_cubeProb_eq_covED (H : Hypergraph V E) (D : Finset E)
    (w : E → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (Psi : Set V → ℝ) (x : V) (S : Set V) (v : V) (W : Set V) :
    CSHThree.covH (withProb H (cubeProb D w hw0 hw1)) Psi x S v W =
      covED H D w Psi x S v W := by
  unfold CSHThree.covH covED
  simp only [withProb_prob, hyperClusterSet_withProb]
  rw [integral_cubeProb_eq_ED H, integral_cubeProb_eq_ED H,
    integral_cubeProb_eq_ED H]
  have hmeet : labelsMeeting (withProb H (cubeProb D w hw0 hw1)) W =
      labelsMeeting H W := rfl
  have hfun1 : (fun K : Finset E =>
      Psi (hyperClusterSet H (off (withProb H (cubeProb D w hw0 hw1)) W
        (↑K : Set E)) ({x} : Set V)) *
        nr (withProb H (cubeProb D w hw0 hw1)) S v
          (off (withProb H (cubeProb D w hw0 hw1)) W (↑K : Set E))) =
      fun K => fclV H Psi x (offF H W K) * nrF H S v (offF H W K) := by
    funext K
    rw [show off (withProb H (cubeProb D w hw0 hw1)) W (↑K : Set E) =
      off H W (↑K : Set E) by simp only [off, hmeet], ← coe_offF]
    rfl
  have hfun2 : (fun K : Finset E =>
      Psi (hyperClusterSet H (off (withProb H (cubeProb D w hw0 hw1)) W
        (↑K : Set E)) ({x} : Set V))) =
      fun K => fclV H Psi x (offF H W K) := by
    funext K
    rw [show off (withProb H (cubeProb D w hw0 hw1)) W (↑K : Set E) =
      off H W (↑K : Set E) by simp only [off, hmeet], ← coe_offF]
    rfl
  have hfun3 : (fun K : Finset E =>
      nr (withProb H (cubeProb D w hw0 hw1)) S v
        (off (withProb H (cubeProb D w hw0 hw1)) W (↑K : Set E))) =
      fun K => nrF H S v (offF H W K) := by
    funext K
    rw [show off (withProb H (cubeProb D w hw0 hw1)) W (↑K : Set E) =
      off H W (↑K : Set E) by simp only [off, hmeet], ← coe_offF]
    rfl
  rw [hfun1, hfun2, hfun3]

/-- The stopped `yH` has the corresponding finite-coordinate presentation. -/
theorem yH_cubeProb_eq_yED (H : Hypergraph V E) (D : Finset E)
    (w : E → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (Psi : Set V → ℝ) (x : V) (S : Set V) (v : V) (N : Set V) :
    CSHThree.yH (withProb H (cubeProb D w hw0 hw1)) Psi x S v N =
      yED H D w Psi x S v N := by
  unfold CSHThree.yH yED
  simp only [withProb_prob, avoidEvent_withProb, hyperClusterSet_withProb]
  rw [integral_cubeProb_eq_ED H]
  refine ED_congr_on _ w fun K _ => ?_
  have hind : ind (avoidEvent H ({x} : Set V) N) (↑K : Set E) =
      ind {L : Finset E | x ∉ TreeHK.reachedBy H N L} K := by
    refine AGBase.ind_congr ?_
    change (↑K : Set E) ∈ avoidEvent H ({x} : Set V) N ↔
      x ∉ TreeHK.reachedBy H N K
    rw [TreeHK.reachedBy_eq]
    exact mem_avoidEvent_iff_not_mem H x N (↑K : Set E)
  rw [TreeHK.reachedBy_eq,
    covH_cubeProb_eq_covED H D w hw0 hw1, hind]

/-- The labelled one-source estimate on an arbitrary finite coordinate set. -/
theorem starED (H : Hypergraph V E) (D : Finset E) (w : E → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (N S : Set V) (x v : V) (hvS : v ∉ S)
    (Psi : Set V → ℝ) (hxS : x ∈ S) (hPsi : Monotone Psi)
    (hPsi0 : ∀ C, 0 ≤ Psi C) :
    yED H D w Psi x S v N * ED D w (fun K => 1 - nrF H S v K) ≤
      ED D w (fun K => (1 - nrF H S v K) * (1 - nrF H N v K)) *
        covED H D w Psi x S v (∅ : Set V) := by
  let Hc : Hypergraph V E := withProb H (cubeProb D w hw0 hw1)
  have key := KNAll.Site.HyperStarH.starH_integral Hc N S x v hvS Psi hxS hPsi hPsi0
  have hy : CSHThree.yH Hc Psi x S v N = yED H D w Psi x S v N := by
    simpa only [Hc] using yH_cubeProb_eq_yED H D w hw0 hw1 Psi x S v N
  have hc : CSHThree.covH Hc Psi x S v (∅ : Set V) =
      covED H D w Psi x S v (∅ : Set V) := by
    simpa only [Hc] using
      covH_cubeProb_eq_covED H D w hw0 hw1 Psi x S v (∅ : Set V)
  have hs : (∫ omega, 1 - nr Hc S v omega ∂(prodBernoulli Hc.prob)) =
      ED D w (fun K => 1 - nrF H S v K) := by
    rw [show Hc.prob = cubeProb D w hw0 hw1 from rfl,
      integral_cubeProb_eq_ED H]
    refine ED_congr_on _ w fun K _ => ?_
    rfl
  have hsn : (∫ omega, (1 - nr Hc S v omega) * (1 - nr Hc N v omega)
      ∂(prodBernoulli Hc.prob)) =
      ED D w (fun K => (1 - nrF H S v K) * (1 - nrF H N v K)) := by
    rw [show Hc.prob = cubeProb D w hw0 hw1 from rfl,
      integral_cubeProb_eq_ED H]
    refine ED_congr_on _ w fun K _ => ?_
    rfl
  rw [hy, hs, hsn, hc] at key
  exact key

/-- `(star^H)` in the exact vocabulary consumed by `HyperMetaA2`. -/
theorem yS_mul_mS_le (H : Hypergraph V E) (w : E → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    {x v : V} {S : Set V} (hxS : x ∈ S) (hvS : v ∉ S)
    {Psi : Set V → ℝ} (hPsi : Monotone Psi) (hPsi0 : ∀ C, 0 ≤ Psi C)
    (U : Finset V) (N : Set V) :
    Yw H w U x (fun U' => BfS H w U' x S v Psi) N *
        Mav H w U S v ∅ ≤
      Mav H w U S v N * BfS H w U x S v Psi := by
  rw [Yw_BfS_eq_yED, Mav_empty_eq_ED, Mav_eq_ED, BfS_eq_covED]
  exact starED H (labelsInF H U) w hw0 hw1 N S x v hvS Psi hxS hPsi hPsi0

/-- **Hyperedge A2^H**, with the exact label-record META-A2 induction. -/
theorem a2H (H : Hypergraph V E) (w : E → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ omega : Set E, weight w omega = 1)
    {x v : V} {S : Set V} (hxS : x ∈ S) (hvS : v ∉ S) (o : V)
    {Psi : Set V → ℝ} (hPsi : Monotone Psi) (hPsi0 : ∀ C, 0 ≤ Psi C)
    (U : Finset V) {N N' : Set V} (hNU : N ⊆ (U : Set V))
    (hN'U : N' ⊆ (U : Set V)) :
    Eav H w U S o v N *
        Yw H w U x (fun U' => BfS H w U' x S v Psi) N' ≤
      Mav H w U S v (N ∪ N') *
        Xw H w U x S o v (fun U' => BfS H w U' x S v Psi) (N ∩ N') := by
  have hF0 : ∀ U' : Finset V, 0 ≤ BfS H w U' x S v Psi := fun U' =>
    BfS_nonneg H hw0 hw1 hm U' x S v hPsi hPsi0
  have hFv : ∀ U' : Finset V, v ∉ U' → BfS H w U' x S v Psi = 0 := fun U' hvU' =>
    BfS_eq_zero_of_not_mem H w x hvU' hvS Psi
  have hstar : ∀ U' ⊆ U, ∀ R : Set V, R ⊆ (U' : Set V) →
      Yw H w U' x (fun W => BfS H w W x S v Psi) R * Mav H w U' S v ∅ ≤
        Mav H w U' S v R * BfS H w U' x S v Psi :=
    fun U' _ R _ => yS_mul_mS_le H w hw0 hw1 hxS hvS hPsi hPsi0 U' R
  exact HyperMetaA2.metaA2_of_star H w hw0 hw1 hm x o v S hF0 hFv U hstar
    N N' hNU hN'U

/-- The diagonal `(Htw)` of hyperedge A2^H. -/
theorem p1H (H : Hypergraph V E) (w : E → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ omega : Set E, weight w omega = 1)
    {x v : V} {S : Set V} (hxS : x ∈ S) (hvS : v ∉ S) (o : V)
    {Psi : Set V → ℝ} (hPsi : Monotone Psi) (hPsi0 : ∀ C, 0 ≤ Psi C)
    (U : Finset V) {Y : Set V} (hY : Y ⊆ (U : Set V)) :
    Eav H w U S o v Y *
        Yw H w U x (fun U' => BfS H w U' x S v Psi) Y ≤
      Mav H w U S v Y *
        Xw H w U x S o v (fun U' => BfS H w U' x S v Psi) Y := by
  simpa only [Set.union_self, Set.inter_self] using
    a2H H w hw0 hw1 hm hxS hvS o hPsi hPsi0 U hY hY

/-- `(Htw)` on the whole hypergraph. -/
theorem p1H_univ (H : Hypergraph V E) (w : E → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ omega : Set E, weight w omega = 1)
    {x v : V} {S : Set V} (hxS : x ∈ S) (hvS : v ∉ S) (o : V)
    {Psi : Set V → ℝ} (hPsi : Monotone Psi) (hPsi0 : ∀ C, 0 ≤ Psi C)
    (Y : Set V) :
    Eav H w Finset.univ S o v Y *
        Yw H w Finset.univ x (fun U' => BfS H w U' x S v Psi) Y ≤
      Mav H w Finset.univ S v Y *
        Xw H w Finset.univ x S o v (fun U' => BfS H w U' x S v Psi) Y :=
  p1H H w hw0 hw1 hm hxS hvS o hPsi hPsi0 Finset.univ (by simp)

end KNAll.Site.HyperA2H

end

#print axioms KNAll.Site.HyperA2H.BfS_nonneg
#print axioms KNAll.Site.HyperA2H.BfS_eq_zero_of_not_mem
#print axioms KNAll.Site.HyperA2H.noninjective_trace_inter_regression
#print axioms KNAll.Site.HyperA2H.starED
#print axioms KNAll.Site.HyperA2H.yS_mul_mS_le
#print axioms KNAll.Site.HyperA2H.a2H
#print axioms KNAll.Site.HyperA2H.p1H_univ
