
import Percolation.Literature.TwoClusterGibbsCovariance

import KNConjectures.GuardedDefs
import KNConjectures.GuardedBasic
import KNConjectures.GuardedKernel
import KNConjectures.GuardedDecoy
set_option linter.unusedSectionVars false

/-!
# Guarded two-cluster covariance reduction

Items 26--30 of the guarded Conjecture 6 proof ledger.
-/

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {V : Type*} [Fintype V]

private theorem guardContactTest_antitone_second (x : V) (Y R : Set V)
    (A : Set (Sym2 V)) : Antitone (guardContactTest x Y R A) := by
  intro B B' hBB'
  unfold guardContactTest
  by_cases h' : ((insert x {u | ∃ e ∈ A, u ∈ e}) ∩ R).Nonempty ∧
      Disjoint (Y ∪ {u | ∃ e ∈ B', u ∈ e}) R
  · have hspan : {u : V | ∃ e ∈ B, u ∈ e} ⊆ {u : V | ∃ e ∈ B', u ∈ e} := by
      rintro u ⟨e, he, hue⟩
      exact ⟨e, hBB' he, hue⟩
    have hsub : Y ∪ {u : V | ∃ e ∈ B, u ∈ e} ⊆
        Y ∪ {u : V | ∃ e ∈ B', u ∈ e} := by
      rintro u (hu | hu)
      · exact Or.inl hu
      · exact Or.inr (hspan hu)
    have hdis : Disjoint (Y ∪ {u : V | ∃ e ∈ B, u ∈ e}) R :=
      h'.2.mono hsub Subset.rfl
    rw [if_pos h', if_pos ⟨h'.1, hdis⟩]
  · rw [if_neg h']
    split_ifs
    · norm_num
    · norm_num

theorem guardLevelTest_antitone_second (w : Sym2 V → unitInterval)
    (x : V) (Y : Set V) (D : List V) (O : Set V) (v : V)
    (A : Set (Sym2 V)) (hO : ∀ u : V, O ≠ ({u} : Set V)) :
    Antitone (guardLevelTest w x Y D O v A) := by
  obtain ⟨coeff, hcoeff⟩ := KNAll.Guarded.guard_tail_shape w (insert x Y) D O v
  intro B B' hBB'
  rw [guardLevelTest, hcoeff, guardLevelTest, hcoeff]
  have hprimary : guardEvalTest x Y O O A B' ≤ guardEvalTest x Y O O A B := by
    simp only [guardEvalTest]
    exact guardContactTest_antitone_second x Y O A hBB'
  have hsingle : ∀ u : V,
      guardEvalTest x Y O ({u} : Set V) A B' =
        guardEvalTest x Y O ({u} : Set V) A B := by
    intro u
    have hne : ({u} : Set V) ≠ O := Ne.symm (hO u)
    rw [guardEvalTest, if_neg hne, guardEvalTest, if_neg hne]
    have hs : ∃ q : V, ({u} : Set V) = ({q} : Set V) := ⟨u, rfl⟩
    rw [dif_pos hs, dif_pos hs]
  rw [show (∑ u, coeff u * guardEvalTest x Y O ({u} : Set V) A B') =
      ∑ u, coeff u * guardEvalTest x Y O ({u} : Set V) A B by
    exact Finset.sum_congr rfl fun u _ => by rw [hsingle u]]
  exact add_le_add hprimary (le_refl _)

private theorem guardContactTest_setCl_eq_ind (x : V) (Y R : Set V)
    (ω : BondConfig V) :
    guardContactTest x Y R (BHK2006.setCl ω ({x} : Set V))
        (BHK2006.setCl ω Y) =
      Percolation.Literature.DecisionTree.ind (guardEv R ({x} : Set V) Y) ω := by
  have hxcarrier :
      insert x {u : V | ∃ e ∈ BHK2006.setCl ω ({x} : Set V), u ∈ e} =
        openCluster ω x := by
    rw [BHK2006.setCl_singleton]
    exact (CSH.openCluster_eq_insert_span ω x).symm
  have hycarrier :
      Y ∪ {u : V | ∃ e ∈ BHK2006.setCl ω Y, u ∈ e} =
        {u : V | ∃ y ∈ Y, (openGraph ω).Reachable y u} := by
    ext u
    simp only [mem_union, mem_setOf_eq]
    exact (BHK2006.setReach_iff ω Y u).symm
  have hcontact : (openCluster ω x ∩ R).Nonempty ↔
      ω ∈ sourceConn R ({x} : Set V) := by
    constructor
    · rintro ⟨r, hrx, hrR⟩
      refine ⟨r, hrR, x, mem_singleton x, ?_⟩
      exact hrx.symm
    · rintro ⟨r, hrR, x', hx', hrx⟩
      have hx'x : x' = x := by simpa using hx'
      subst x'
      exact ⟨r, hrx.symm, hrR⟩
  have havoid : Disjoint
      {u : V | ∃ y ∈ Y, (openGraph ω).Reachable y u} R ↔
      ω ∈ sourceAvoid R Y := by
    constructor
    · intro hd r hrR y hy hry
      exact Set.disjoint_left.1 hd ⟨y, hy, hry.symm⟩ hrR
    · intro ha
      apply Set.disjoint_left.2
      rintro r ⟨y, hy, hyr⟩ hrR
      exact ha r hrR y hy hyr.symm
  have htest :
      ((insert x {u : V | ∃ e ∈ BHK2006.setCl ω ({x} : Set V), u ∈ e}) ∩ R).Nonempty ∧
          Disjoint (Y ∪ {u : V | ∃ e ∈ BHK2006.setCl ω Y, u ∈ e}) R ↔
        ω ∈ guardEv R ({x} : Set V) Y := by
    rw [hxcarrier, hycarrier, hcontact, havoid]
    simp only [guardEv, mem_inter_iff, and_comm]
  unfold guardContactTest
  by_cases ht :
      ((insert x {u : V | ∃ e ∈ BHK2006.setCl ω ({x} : Set V), u ∈ e}) ∩ R).Nonempty ∧
        Disjoint (Y ∪ {u : V | ∃ e ∈ BHK2006.setCl ω Y, u ∈ e}) R
  · rw [if_pos ht,
      Percolation.Literature.DecisionTree.ind_of_mem (htest.1 ht)]
  · rw [if_neg ht,
      Percolation.Literature.DecisionTree.ind_of_not_mem (fun h => ht (htest.2 h))]

private theorem guardEv_subset_ownerAvoid (x : V) (Y R : Set V) :
    guardEv R ({x} : Set V) Y ⊆ sourceAvoid ({x} : Set V) Y := by
  rintro ω ⟨havoid, r, hrR, x', hx', hrx⟩
  have hx'x : x' = x := by simpa using hx'
  subst x'
  intro z hz y hy hzy
  have hzx : z = x := by simpa using hz
  subst z
  exact havoid r hrR y hy (hrx.trans hzy)

private theorem guardEvalTest_mul_ind_eq (x : V) (Y O R : Set V)
    (ω : BondConfig V) (hused : R = O ∨ ∃ u : V, R = ({u} : Set V)) :
    guardEvalTest x Y O R (BHK2006.setCl ω ({x} : Set V))
          (BHK2006.setCl ω Y) *
        Percolation.Literature.DecisionTree.ind
          (sourceAvoid ({x} : Set V) Y) ω =
      Percolation.Literature.DecisionTree.ind (guardEv R ({x} : Set V) Y) ω := by
  rcases hused with hRO | ⟨u, hRu⟩
  · subst R
    rw [guardEvalTest, if_pos rfl, guardContactTest_setCl_eq_ind]
    by_cases hω : ω ∈ guardEv O ({x} : Set V) Y
    · rw [Percolation.Literature.DecisionTree.ind_of_mem hω,
        Percolation.Literature.DecisionTree.ind_of_mem
          (guardEv_subset_ownerAvoid x Y O hω)]
      norm_num
    · rw [Percolation.Literature.DecisionTree.ind_of_not_mem hω]
      norm_num
  · subst R
    by_cases huO : ({u} : Set V) = O
    · rw [guardEvalTest, if_pos huO, guardContactTest_setCl_eq_ind]
      by_cases hω : ω ∈ guardEv ({u} : Set V) ({x} : Set V) Y
      · rw [Percolation.Literature.DecisionTree.ind_of_mem hω,
          Percolation.Literature.DecisionTree.ind_of_mem
            (guardEv_subset_ownerAvoid x Y ({u} : Set V) hω)]
        norm_num
      · rw [Percolation.Literature.DecisionTree.ind_of_not_mem hω]
        norm_num
    · rw [guardEvalTest, if_neg huO]
      have hs : ∃ q : V, ({u} : Set V) = ({q} : Set V) := ⟨u, rfl⟩
      rw [dif_pos hs]
      have hchoose : Classical.choose hs = u := by
        exact Set.singleton_eq_singleton_iff.mp (Classical.choose_spec hs).symm
      rw [hchoose]
      have hxcarrier :
          insert x {z : V | ∃ e ∈ BHK2006.setCl ω ({x} : Set V), z ∈ e} =
            openCluster ω x := by
        rw [BHK2006.setCl_singleton]
        exact (CSH.openCluster_eq_insert_span ω x).symm
      simp only [hxcarrier]
      by_cases hD : ω ∈ sourceAvoid ({x} : Set V) Y
      · have heq : u ∈ openCluster ω x ↔
            ω ∈ guardEv ({u} : Set V) ({x} : Set V) Y := by
          constructor
          · intro hxu
            refine ⟨?_, u, mem_singleton u, x, mem_singleton x, hxu.symm⟩
            intro u' hu' y hy huy
            have hu'u : u' = u := by simpa using hu'
            subst u'
            exact hD x (mem_singleton x) y hy (hxu.trans huy)
          · rintro ⟨_, u', hu', x', hx', hu'x'⟩
            have hu'u : u' = u := by simpa using hu'
            have hx'x : x' = x := by simpa using hx'
            subst u'
            subst x'
            exact hu'x'.symm
        by_cases hu : u ∈ openCluster ω x
        · rw [if_pos hu,
            Percolation.Literature.DecisionTree.ind_of_mem hD,
            Percolation.Literature.DecisionTree.ind_of_mem (heq.1 hu)]
          norm_num
        · rw [if_neg hu,
            Percolation.Literature.DecisionTree.ind_of_mem hD,
            Percolation.Literature.DecisionTree.ind_of_not_mem
              (fun h => hu (heq.2 h))]
          norm_num
      · have hnot : ω ∉ guardEv ({u} : Set V) ({x} : Set V) Y :=
          fun h => hD (guardEv_subset_ownerAvoid x Y ({u} : Set V) h)
        rw [Percolation.Literature.DecisionTree.ind_of_not_mem hD,
          Percolation.Literature.DecisionTree.ind_of_not_mem hnot]
        simp

private theorem guardCovD_eq_twoClusterCov_eval
    (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (O R : Set V)
    (g : Set (Sym2 V) → ℝ) (hused : R = O ∨ ∃ u : V, R = ({u} : Set V)) :
    guardCovD w x Y g R =
      twoClusterCov (fun e => (w e : ℝ)) ({x} : Set V) Y
        (sourceAvoid ({x} : Set V) Y) g
        (fun A B => guardEvalTest x Y O R A B) := by
  let w' : Sym2 V → ℝ := fun e => (w e : ℝ)
  let D₀ : Set (BondConfig V) := sourceAvoid ({x} : Set V) Y
  let H : Set (BondConfig V) := guardEv R ({x} : Set V) Y
  have eD : (prodBernoulli w).real D₀ =
      ∑ ω, BHK2006.weight w' ω *
        Percolation.Literature.DecisionTree.ind D₀ ω := by
    exact Percolation.Literature.TwoAvoidanceSets.real_eq_sum_ind w D₀
  have eG : (∫ ω in D₀, g (openEdgeCluster ω x) ∂(prodBernoulli w)) =
      ∑ ω, BHK2006.weight w' ω *
        (g (BHK2006.setCl ω ({x} : Set V)) *
          Percolation.Literature.DecisionTree.ind D₀ ω) := by
    rw [CSH.setIntegral_eq_sum_ind]
    exact Finset.sum_congr rfl fun ω _ => by
      rw [BHK2006.setCl_singleton]
      ring
  have eH : (prodBernoulli w).real H =
      ∑ ω, BHK2006.weight w' ω *
        (guardEvalTest x Y O R (BHK2006.setCl ω ({x} : Set V))
            (BHK2006.setCl ω Y) *
          Percolation.Literature.DecisionTree.ind D₀ ω) := by
    rw [Percolation.Literature.TwoAvoidanceSets.real_eq_sum_ind]
    exact Finset.sum_congr rfl fun ω _ => by
      rw [guardEvalTest_mul_ind_eq x Y O R ω hused]
  have eGH : (∫ ω in H, g (openEdgeCluster ω x) ∂(prodBernoulli w)) =
      ∑ ω, BHK2006.weight w' ω *
        (g (BHK2006.setCl ω ({x} : Set V)) *
          guardEvalTest x Y O R (BHK2006.setCl ω ({x} : Set V))
            (BHK2006.setCl ω Y) *
          Percolation.Literature.DecisionTree.ind D₀ ω) := by
    rw [CSH.setIntegral_eq_sum_ind]
    exact Finset.sum_congr rfl fun ω _ => by
      rw [← guardEvalTest_mul_ind_eq x Y O R ω hused,
        BHK2006.setCl_singleton]
      ring
  change (prodBernoulli w).real D₀ *
      (∫ ω in H, g (openEdgeCluster ω x) ∂(prodBernoulli w)) -
        (∫ ω in D₀, g (openEdgeCluster ω x) ∂(prodBernoulli w)) *
          (prodBernoulli w).real H = _
  rw [eD, eG, eH, eGH]
  rfl

private theorem twoClusterCov_add_second (w : Sym2 V → ℝ) (S T : Set V)
    (D : Set (BondConfig V)) (φ : Set (Sym2 V) → ℝ)
    (h k : Set (Sym2 V) → Set (Sym2 V) → ℝ) :
    twoClusterCov w S T D φ (fun A B => h A B + k A B) =
      twoClusterCov w S T D φ h + twoClusterCov w S T D φ k := by
  unfold twoClusterCov
  simp only [mul_add, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

private theorem twoClusterCov_smul_second (w : Sym2 V → ℝ) (S T : Set V)
    (D : Set (BondConfig V)) (φ : Set (Sym2 V) → ℝ) (c : ℝ)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ) :
    twoClusterCov w S T D φ (fun A B => c * h A B) =
      c * twoClusterCov w S T D φ h := by
  have e1 : (∑ ω, BHK2006.weight w ω *
      (φ (BHK2006.setCl ω S) * (c * h (BHK2006.setCl ω S)
        (BHK2006.setCl ω T)) *
        Percolation.Literature.DecisionTree.ind D ω)) =
      c * ∑ ω, BHK2006.weight w ω *
        (φ (BHK2006.setCl ω S) * h (BHK2006.setCl ω S)
          (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω _ => by ring
  have e2 : (∑ ω, BHK2006.weight w ω *
      ((c * h (BHK2006.setCl ω S) (BHK2006.setCl ω T)) *
        Percolation.Literature.DecisionTree.ind D ω)) =
      c * ∑ ω, BHK2006.weight w ω *
        (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω _ => by ring
  unfold twoClusterCov
  rw [e1, e2]
  ring

private theorem twoClusterCov_sum_second {I : Type*}
    (w : Sym2 V → ℝ) (S T : Set V) (D : Set (BondConfig V))
    (φ : Set (Sym2 V) → ℝ) (s : Finset I)
    (k : I → Set (Sym2 V) → Set (Sym2 V) → ℝ) :
    twoClusterCov w S T D φ (fun A B => ∑ i ∈ s, k i A B) =
      ∑ i ∈ s, twoClusterCov w S T D φ (k i) := by
  induction s using Finset.induction_on with
  | empty => simp [twoClusterCov]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hfun : (fun A B => ∑ j ∈ insert i s, k j A B) =
        fun A B => k i A B + ∑ j ∈ s, k j A B := by
      funext A B
      rw [Finset.sum_insert hi]
    rw [hfun, twoClusterCov_add_second, ih]

theorem guardCSHMargin_eq_twoClusterCov (w : Sym2 V → unitInterval)
    (x : V) (Y : Set V) (D : List V) (O : Set V) (v : V)
    (g : Set (Sym2 V) → ℝ) :
    guardCSHMargin w x Y D O v g =
      twoClusterCov (fun e => (w e : ℝ)) ({x} : Set V) Y
        (sourceAvoid ({x} : Set V) Y) g (guardLevelTest w x Y D O v) := by
  obtain ⟨coeff, hcoeff⟩ := KNAll.Guarded.guard_tail_shape w (insert x Y) D O v
  unfold guardCSHMargin guardLevelTest
  rw [hcoeff, show (fun A B =>
      cshMarg (guardDecoyList w (insert x Y) D)
        (guardObsConst w O v (insert x Y ∪ listSet D)) O ({v} : Set V)
        (fun R => guardEvalTest x Y O R A B)) =
      (fun A B => guardEvalTest x Y O O A B +
        ∑ u, coeff u * guardEvalTest x Y O ({u} : Set V) A B) by
        funext A B
        exact hcoeff _]
  rw [guardCovD_eq_twoClusterCov_eval w x Y O O g (Or.inl rfl)]
  have hu : ∀ u : V, guardCovD w x Y g ({u} : Set V) =
      twoClusterCov (fun e => (w e : ℝ)) ({x} : Set V) Y
        (sourceAvoid ({x} : Set V) Y) g
        (fun A B => guardEvalTest x Y O ({u} : Set V) A B) := fun u =>
    guardCovD_eq_twoClusterCov_eval w x Y O ({u} : Set V) g
      (Or.inr ⟨u, rfl⟩)
  simp_rw [hu]
  have hsum : twoClusterCov (fun e => (w e : ℝ)) ({x} : Set V) Y
      (sourceAvoid ({x} : Set V) Y) g
      (fun A B => ∑ u, coeff u * guardEvalTest x Y O ({u} : Set V) A B) =
      ∑ u, coeff u *
        twoClusterCov (fun e => (w e : ℝ)) ({x} : Set V) Y
          (sourceAvoid ({x} : Set V) Y) g
          (fun A B => guardEvalTest x Y O ({u} : Set V) A B) := by
    rw [twoClusterCov_sum_second]
    exact Finset.sum_congr rfl fun u _ =>
      twoClusterCov_smul_second (fun e => (w e : ℝ)) ({x} : Set V) Y
        (sourceAvoid ({x} : Set V) Y) g (coeff u)
          (fun A B => guardEvalTest x Y O ({u} : Set V) A B)
  rw [← hsum, ← twoClusterCov_add_second]

theorem twoClusterCov_step (w : Sym2 V → ℝ)
    (hm : ∑ ω, BHK2006.weight w ω = 1) (S T : Set V)
    (D : Set (BondConfig V))
    (hD : ∀ ω, ω ∈ D ↔ ∀ s ∈ S, ∀ t ∈ T,
      ¬ (openGraph ω).Reachable s t)
    (φ : Set (Sym2 V) → ℝ)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ) :
    twoClusterCov w S T D φ h -
        twoClusterCov w S T D (BHK2006.gibbsT w S T φ) h =
      (∑ ω, BHK2006.weight w ω *
        Percolation.Literature.DecisionTree.ind D ω) *
        (twoClusterWithinFirst w S T D φ h +
          twoClusterWithinSecond w S T D φ h) := by
  -- Condition first on the `T`-cluster.
  have e1 : ∑ ω, BHK2006.weight w ω *
        (φ (BHK2006.setCl ω S) *
          h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) =
      ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w S T
          (fun A => φ A * h A (BHK2006.setCl ω T))
          (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) :=
    BHK2006.set_sum_cond_cluster' w hm S T
      (fun A B => φ A * h A B) hD
  have e2 : ∑ ω, BHK2006.weight w ω *
        (φ (BHK2006.setCl ω S) *
          Percolation.Literature.DecisionTree.ind D ω) =
      ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w S T φ (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) :=
    BHK2006.set_sum_cond_cluster' w hm S T (fun A _ => φ A) hD
  -- Stationarity of the first marginal after the other half-step.
  have e3 : ∑ ω, BHK2006.weight w ω *
        (BHK2006.gibbsT w S T φ (BHK2006.setCl ω S) *
          Percolation.Literature.DecisionTree.ind D ω) =
      ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w S T φ (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) :=
    (BHK2006.set_sum_cond_cluster w hm S T
      (fun _ B => BHK2006.condS w S T φ B) hD).symm
  -- The product of the two `S`-conditional means.
  have e4 : ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w S T φ (BHK2006.setCl ω T) *
          h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) =
      ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w S T φ (BHK2006.setCl ω T) *
          BHK2006.condS w S T
            (fun A => h A (BHK2006.setCl ω T)) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) := by
    rw [BHK2006.set_sum_cond_cluster' w hm S T
      (fun A B => BHK2006.condS w S T φ B * h A B) hD]
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 1
    congr 1
    have hc : BHK2006.condS w S T
        (fun A => h A (BHK2006.setCl ω T)) (BHK2006.setCl ω T) =
        ∑ η, BHK2006.weight w η *
          h (BHK2006.halfS S T (BHK2006.setCl ω T) η)
            (BHK2006.setCl ω T) := rfl
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    simp only [BHK2006.halfS]
    ring
  -- Condition that same mixed term on the `S`-cluster instead.
  have e5 : ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w S T φ (BHK2006.setCl ω T) *
          h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) =
      ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w T S
          (fun B => BHK2006.condS w S T φ B *
            h (BHK2006.setCl ω S) B) (BHK2006.setCl ω S) *
          Percolation.Literature.DecisionTree.ind D ω) :=
    BHK2006.set_sum_cond_cluster w hm S T
      (fun A B => BHK2006.condS w S T φ B * h A B) hD
  have hgibbs : ∀ A,
      BHK2006.gibbsT w S T φ A =
        BHK2006.condS w T S (BHK2006.condS w S T φ) A := by
    intro A
    rfl
  -- The product of the two `T`-conditional means.
  have e6 : ∑ ω, BHK2006.weight w ω *
        (BHK2006.gibbsT w S T φ (BHK2006.setCl ω S) *
          h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) =
      ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w T S (BHK2006.condS w S T φ)
            (BHK2006.setCl ω S) *
          BHK2006.condS w T S
            (fun B => h (BHK2006.setCl ω S) B) (BHK2006.setCl ω S) *
          Percolation.Literature.DecisionTree.ind D ω) := by
    rw [BHK2006.set_sum_cond_cluster w hm S T
      (fun A B => BHK2006.gibbsT w S T φ A * h A B) hD]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hc : BHK2006.condS w T S
        (fun B => h (BHK2006.setCl ω S) B) (BHK2006.setCl ω S) =
        ∑ η, BHK2006.weight w η *
          h (BHK2006.setCl ω S)
            (BHK2006.halfT S T (BHK2006.setCl ω S) η) := rfl
    apply congrArg (fun z : ℝ => BHK2006.weight w ω *
      (z * Percolation.Literature.DecisionTree.ind D ω))
    rw [hgibbs, hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun η _ => by
      simp only [BHK2006.halfT]
      ring
  have hW1 : twoClusterWithinFirst w S T D φ h =
      (∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w S T
          (fun A => φ A * h A (BHK2006.setCl ω T))
          (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω)) -
      ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w S T φ (BHK2006.setCl ω T) *
          BHK2006.condS w S T
            (fun A => h A (BHK2006.setCl ω T)) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω) := by
    rw [twoClusterWithinFirst, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ => by
      rw [twoClusterCondCovFirst]
      ring
  have hW2 : twoClusterWithinSecond w S T D φ h =
      (∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w T S
          (fun B => BHK2006.condS w S T φ B *
            h (BHK2006.setCl ω S) B) (BHK2006.setCl ω S) *
          Percolation.Literature.DecisionTree.ind D ω)) -
      ∑ ω, BHK2006.weight w ω *
        (BHK2006.condS w T S (BHK2006.condS w S T φ)
            (BHK2006.setCl ω S) *
          BHK2006.condS w T S
            (fun B => h (BHK2006.setCl ω S) B) (BHK2006.setCl ω S) *
          Percolation.Literature.DecisionTree.ind D ω) := by
    rw [twoClusterWithinSecond, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ => by
      rw [BHK2006.condCov]
      ring
  have e45 := e4.symm.trans e5
  rw [twoClusterCov, twoClusterCov, e1, e2, e3, e6, hW1, hW2, e45]
  ring

private theorem twoClusterWithinSecond_nonneg (w : Sym2 V → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, BHK2006.weight w ω = 1) (S T : Set V)
    (D : Set (BondConfig V)) {g : Set (Sym2 V) → ℝ} (hg : Monotone g)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ)
    (hanti : ∀ A, Antitone (h A)) :
    0 ≤ twoClusterWithinSecond w S T D g h := by
  let q : Set (Sym2 V) → ℝ := BHK2006.condS w S T g
  have hq : Antitone q := BHK2006.condS_antitone hw0 hw1 S T hg
  have hcond : ∀ A : Set (Sym2 V),
      0 ≤ BHK2006.condCov w T S q (fun B => h A B) A := by
    intro A
    let f₁ : Set (Sym2 V) → ℝ := fun η => q (BHK2006.halfS T S A η)
    let f₂ : Set (Sym2 V) → ℝ := fun η => h A (BHK2006.halfS T S A η)
    have hf₁ : Antitone f₁ := by
      intro η η' hηη'
      exact hq (BHK2006.halfS_mono T S (B := A) (B' := A)
        (η := η') (η' := η) Subset.rfl hηη')
    have hf₂ : Antitone f₂ := by
      intro η η' hηη'
      exact hanti A (BHK2006.halfS_mono T S (B := A) (B' := A)
        (η := η') (η' := η) Subset.rfl hηη')
    let M : ℝ := ∑ η, |f₁ η|
    let N : ℝ := ∑ η, |f₂ η|
    have hf₁M : ∀ η, f₁ η ≤ M := by
      intro η
      exact (le_abs_self _).trans (Finset.single_le_sum
        (f := fun ξ => |f₁ ξ|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ η))
    have hf₂N : ∀ η, f₂ η ≤ N := by
      intro η
      exact (le_abs_self _).trans (Finset.single_le_sum
        (f := fun ξ => |f₂ ξ|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ η))
    have hH := BHK2006.harris_anti_anti hw0 hw1 hm hf₁ hf₂ hf₁M hf₂N
    rw [BHK2006.condCov]
    change 0 ≤
      (∑ η, BHK2006.weight w η * (f₁ η * f₂ η)) -
        (∑ η, BHK2006.weight w η * f₁ η) *
          ∑ η, BHK2006.weight w η * f₂ η
    exact sub_nonneg.2 hH
  unfold twoClusterWithinSecond
  exact Finset.sum_nonneg fun ω _ =>
    mul_nonneg (BHK2006.weight_nonneg hw0 hw1 ω)
      (mul_nonneg (hcond (BHK2006.setCl ω S))
        (Percolation.Literature.DecisionTree.ind_nonneg D ω))

private theorem twoClusterCov_sub_const (w : Sym2 V → ℝ) (S T : Set V)
    (D : Set (BondConfig V)) (φ : Set (Sym2 V) → ℝ)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ) (c : ℝ) :
    twoClusterCov w S T D (fun A => φ A - c) h =
      twoClusterCov w S T D φ h := by
  have h1 : ∀ ω : BondConfig V,
      BHK2006.weight w ω *
          ((φ (BHK2006.setCl ω S) - c) *
            h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
            Percolation.Literature.DecisionTree.ind D ω) =
        BHK2006.weight w ω *
            (φ (BHK2006.setCl ω S) *
              h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
              Percolation.Literature.DecisionTree.ind D ω) -
          c * (BHK2006.weight w ω *
            (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
              Percolation.Literature.DecisionTree.ind D ω)) := fun ω => by ring
  have h2 : ∀ ω : BondConfig V,
      BHK2006.weight w ω *
          ((φ (BHK2006.setCl ω S) - c) *
            Percolation.Literature.DecisionTree.ind D ω) =
        BHK2006.weight w ω *
            (φ (BHK2006.setCl ω S) *
              Percolation.Literature.DecisionTree.ind D ω) -
          c * (BHK2006.weight w ω *
            Percolation.Literature.DecisionTree.ind D ω) := fun ω => by ring
  simp only [twoClusterCov, h1, h2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem abs_sum_ind_le (w : Sym2 V → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (D : Set (BondConfig V)) {g : BondConfig V → ℝ} {c : ℝ}
    (hg : ∀ ω, |g ω| ≤ c) :
    |∑ ω, BHK2006.weight w ω *
        (g ω * Percolation.Literature.DecisionTree.ind D ω)| ≤
      c * ∑ ω, BHK2006.weight w ω *
        Percolation.Literature.DecisionTree.ind D ω := by
  calc
    |∑ ω, BHK2006.weight w ω *
        (g ω * Percolation.Literature.DecisionTree.ind D ω)| ≤
        ∑ ω, |BHK2006.weight w ω *
          (g ω * Percolation.Literature.DecisionTree.ind D ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, c * (BHK2006.weight w ω *
        Percolation.Literature.DecisionTree.ind D ω) :=
      Finset.sum_le_sum fun ω _ => by
        rw [abs_mul, abs_mul,
          abs_of_nonneg (BHK2006.weight_nonneg hw0 hw1 ω),
          abs_of_nonneg (Percolation.Literature.DecisionTree.ind_nonneg D ω)]
        calc
          BHK2006.weight w ω *
              (|g ω| * Percolation.Literature.DecisionTree.ind D ω) ≤
              BHK2006.weight w ω *
                (c * Percolation.Literature.DecisionTree.ind D ω) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (hg ω)
                (Percolation.Literature.DecisionTree.ind_nonneg D ω))
              (BHK2006.weight_nonneg hw0 hw1 ω)
          _ = c * (BHK2006.weight w ω *
              Percolation.Literature.DecisionTree.ind D ω) := by ring
    _ = c * ∑ ω, BHK2006.weight w ω *
        Percolation.Literature.DecisionTree.ind D ω := by rw [Finset.mul_sum]

private theorem abs_twoClusterCov_le (w : Sym2 V → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, BHK2006.weight w ω = 1) (S T : Set V)
    (D : Set (BondConfig V)) {φ : Set (Sym2 V) → ℝ}
    {h : Set (Sym2 V) → Set (Sym2 V) → ℝ} {δ M : ℝ}
    (hφ : ∀ A A', φ A - φ A' ≤ δ) (hM : ∀ A B, |h A B| ≤ M) :
    |twoClusterCov w S T D φ h| ≤ 2 * δ * M := by
  have hδ : 0 ≤ δ := by simpa using hφ ∅ ∅
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ∅ ∅)
  set mD : ℝ := ∑ ω, BHK2006.weight w ω *
    Percolation.Literature.DecisionTree.ind D ω with hmD
  have hmD0 : 0 ≤ mD := Finset.sum_nonneg fun ω _ =>
    mul_nonneg (BHK2006.weight_nonneg hw0 hw1 ω)
      (Percolation.Literature.DecisionTree.ind_nonneg D ω)
  have hmD1 : mD ≤ 1 := by
    calc
      mD ≤ ∑ ω, BHK2006.weight w ω := Finset.sum_le_sum fun ω _ => by
        simpa using mul_le_mul_of_nonneg_left
          (BHK2006.ind_le_one D ω)
          (BHK2006.weight_nonneg hw0 hw1 ω)
      _ = 1 := hm
  rw [← twoClusterCov_sub_const w S T D φ h (φ ∅)]
  set ψ : Set (Sym2 V) → ℝ := fun A => φ A - φ ∅ with hψ
  have hψb : ∀ A, |ψ A| ≤ δ := fun A =>
    abs_sub_le_iff.2 ⟨hφ A ∅, by linarith [hφ ∅ A]⟩
  have b1 : |∑ ω, BHK2006.weight w ω *
      (ψ (BHK2006.setCl ω S) *
        h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
        Percolation.Literature.DecisionTree.ind D ω)| ≤ δ * M * mD := by
    have hb := abs_sum_ind_le w hw0 hw1 D
      (g := fun ω => ψ (BHK2006.setCl ω S) *
        h (BHK2006.setCl ω S) (BHK2006.setCl ω T)) (c := δ * M)
      (fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hψb _) (hM _ _) (abs_nonneg _) hδ)
    simpa only [hmD] using hb
  have b2 : |∑ ω, BHK2006.weight w ω *
      (ψ (BHK2006.setCl ω S) *
        Percolation.Literature.DecisionTree.ind D ω)| ≤ δ * mD :=
    abs_sum_ind_le w hw0 hw1 D
      (g := fun ω => ψ (BHK2006.setCl ω S)) (fun ω => hψb _)
  have b3 : |∑ ω, BHK2006.weight w ω *
      (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
        Percolation.Literature.DecisionTree.ind D ω)| ≤ M * mD :=
    abs_sum_ind_le w hw0 hw1 D
      (g := fun ω => h (BHK2006.setCl ω S) (BHK2006.setCl ω T))
      (fun ω => hM _ _)
  have hcov : twoClusterCov w S T D ψ h =
      mD * (∑ ω, BHK2006.weight w ω *
        (ψ (BHK2006.setCl ω S) *
          h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω)) -
      (∑ ω, BHK2006.weight w ω *
        (ψ (BHK2006.setCl ω S) *
          Percolation.Literature.DecisionTree.ind D ω)) *
      (∑ ω, BHK2006.weight w ω *
        (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω)) := rfl
  rw [hcov]
  have t1 : |mD * ∑ ω, BHK2006.weight w ω *
      (ψ (BHK2006.setCl ω S) *
        h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
        Percolation.Literature.DecisionTree.ind D ω)| ≤ δ * M := by
    rw [abs_mul, abs_of_nonneg hmD0]
    calc
      mD * |∑ ω, BHK2006.weight w ω *
          (ψ (BHK2006.setCl ω S) *
            h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
            Percolation.Literature.DecisionTree.ind D ω)| ≤
          1 * (δ * M * mD) :=
        mul_le_mul hmD1 b1 (abs_nonneg _) zero_le_one
      _ ≤ δ * M := by
        rw [one_mul]
        exact mul_le_of_le_one_right (mul_nonneg hδ hM0) hmD1
  have t2 : |(∑ ω, BHK2006.weight w ω *
      (ψ (BHK2006.setCl ω S) *
        Percolation.Literature.DecisionTree.ind D ω)) *
      (∑ ω, BHK2006.weight w ω *
        (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω))| ≤ δ * M := by
    rw [abs_mul]
    calc
      |∑ ω, BHK2006.weight w ω *
          (ψ (BHK2006.setCl ω S) *
            Percolation.Literature.DecisionTree.ind D ω)| *
          |∑ ω, BHK2006.weight w ω *
            (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
              Percolation.Literature.DecisionTree.ind D ω)| ≤
          (δ * mD) * (M * mD) :=
        mul_le_mul b2 b3 (abs_nonneg _) (by positivity)
      _ ≤ δ * M := by
        nlinarith [mul_nonneg hδ hM0, mul_le_one₀ hmD1 hmD0 hmD1]
  calc
    |mD * (∑ ω, BHK2006.weight w ω *
          (ψ (BHK2006.setCl ω S) *
            h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
            Percolation.Literature.DecisionTree.ind D ω)) -
        (∑ ω, BHK2006.weight w ω *
          (ψ (BHK2006.setCl ω S) *
            Percolation.Literature.DecisionTree.ind D ω)) *
        (∑ ω, BHK2006.weight w ω *
          (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
            Percolation.Literature.DecisionTree.ind D ω))| ≤
        |mD * ∑ ω, BHK2006.weight w ω *
          (ψ (BHK2006.setCl ω S) *
            h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
            Percolation.Literature.DecisionTree.ind D ω)| +
        |(∑ ω, BHK2006.weight w ω *
          (ψ (BHK2006.setCl ω S) *
            Percolation.Literature.DecisionTree.ind D ω)) *
          (∑ ω, BHK2006.weight w ω *
            (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
              Percolation.Literature.DecisionTree.ind D ω))| := abs_sub _ _
    _ ≤ 2 * δ * M := by linarith

private theorem regenWeight_le_one (w : Sym2 V → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, BHK2006.weight w ω = 1) (T : Set V) :
    BHK2006.regenWeight w T ≤ 1 := by
  calc
    BHK2006.regenWeight w T ≤ ∑ η, BHK2006.weight w η :=
      Finset.sum_le_sum fun η _ => by
        simpa [BHK2006.regenWeight] using mul_le_mul_of_nonneg_left
          (BHK2006.ind_le_one (BHK2006.regenT T) η)
          (BHK2006.weight_nonneg hw0 hw1 η)
    _ = 1 := hm

theorem twoClusterCov_nonneg_of_withinFirst (w : Sym2 V → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, BHK2006.weight w ω = 1) (S T : Set V)
    (D : Set (BondConfig V))
    (hD : ∀ ω, ω ∈ D ↔ ∀ s ∈ S, ∀ t ∈ T,
      ¬ (openGraph ω).Reachable s t)
    (hε : 0 < BHK2006.regenWeight w T)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ)
    (hanti : ∀ A, Antitone (h A))
    (hwithin : ∀ g : Set (Sym2 V) → ℝ, Monotone g →
      (∀ A, 0 ≤ g A) → 0 ≤ twoClusterWithinFirst w S T D g h)
    {f : Set (Sym2 V) → ℝ} (hf : Monotone f) :
    0 ≤ twoClusterCov w S T D f h := by
  set f₀ : Set (Sym2 V) → ℝ := fun A => f A - f ∅ with hf₀
  have hf₀m : Monotone f₀ := fun A A' hAA' => sub_le_sub_right (hf hAA') _
  have hf₀0 : ∀ A, 0 ≤ f₀ A := fun A => sub_nonneg.2 (hf (Set.empty_subset A))
  set c : ℝ := f Set.univ - f ∅ with hc
  have hosc : ∀ A A', f₀ A - f₀ A' ≤ c := fun A A' => by
    simp only [hf₀, hc]
    linarith [hf (Set.subset_univ A), hf (Set.empty_subset A')]
  set M : ℝ := ∑ A : Set (Sym2 V), ∑ B : Set (Sym2 V), |h A B| with hMdef
  have hM : ∀ A B, |h A B| ≤ M := by
    intro A B
    calc
      |h A B| ≤ ∑ B' : Set (Sym2 V), |h A B'| :=
        Finset.single_le_sum (f := fun B' => |h A B'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ B)
      _ ≤ M := by
        rw [hMdef]
        exact Finset.single_le_sum
          (f := fun A' : Set (Sym2 V) => ∑ B' : Set (Sym2 V), |h A' B'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ A)
  set mD : ℝ := ∑ ω, BHK2006.weight w ω *
    Percolation.Literature.DecisionTree.ind D ω with hmD
  have hmD0 : 0 ≤ mD := Finset.sum_nonneg fun ω _ =>
    mul_nonneg (BHK2006.weight_nonneg hw0 hw1 ω)
      (Percolation.Literature.DecisionTree.ind_nonneg D ω)
  set ρ : ℝ := 1 - BHK2006.regenWeight w T with hρ
  have hρ0 : 0 ≤ ρ := sub_nonneg.2 (regenWeight_le_one w hw0 hw1 hm T)
  have hρ1 : ρ < 1 := by simp only [hρ]; linarith
  have hstep : ∀ (g : Set (Sym2 V) → ℝ), Monotone g →
      (∀ A, 0 ≤ g A) →
      twoClusterCov w S T D (BHK2006.gibbsT w S T g) h ≤
        twoClusterCov w S T D g h := by
    intro g hg hg0
    have hfirst := hwithin g hg hg0
    have hsecond := twoClusterWithinSecond_nonneg w hw0 hw1 hm S T D hg h hanti
    have heq := twoClusterCov_step w hm S T D hD g h
    have hnonneg : 0 ≤ mD *
        (twoClusterWithinFirst w S T D g h +
          twoClusterWithinSecond w S T D g h) :=
      mul_nonneg hmD0 (add_nonneg hfirst hsecond)
    rw [← hmD] at heq
    linarith
  have hit := fun n => BHK2006.gibbsT_iterate_mono_nonneg
    hw0 hw1 S T hf₀m hf₀0 n
  have hdesc : ∀ n : ℕ,
      twoClusterCov w S T D ((BHK2006.gibbsT w S T)^[n] f₀) h ≤
        twoClusterCov w S T D f₀ h := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hstep _ (hit n).1 (hit n).2).trans ih
  have key : ∀ n : ℕ,
      -(2 * (ρ ^ n * c) * M) ≤ twoClusterCov w S T D f₀ h := by
    intro n
    have hb : |twoClusterCov w S T D
        ((BHK2006.gibbsT w S T)^[n] f₀) h| ≤ 2 * (ρ ^ n * c) * M :=
      abs_twoClusterCov_le w hw0 hw1 hm S T D
        (BHK2006.gibbsT_iterate_sub_le hw0 hw1 hm S T n hosc) hM
    have hlower : -(2 * (ρ ^ n * c) * M) ≤
        twoClusterCov w S T D ((BHK2006.gibbsT w S T)^[n] f₀) h := by
      linarith [neg_abs_le
        (twoClusterCov w S T D ((BHK2006.gibbsT w S T)^[n] f₀) h)]
    exact hlower.trans (hdesc n)
  have hlim : Filter.Tendsto (fun n : ℕ => -(2 * (ρ ^ n * c) * M))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ρ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have ht : Filter.Tendsto (fun n : ℕ => -(2 * (ρ ^ n * c) * M))
        Filter.atTop (nhds (-(2 * (0 * c) * M))) :=
      (((h0.mul_const c).const_mul 2).mul_const M).neg
    simpa using ht
  have hge : 0 ≤ twoClusterCov w S T D f₀ h := le_of_tendsto' hlim key
  rwa [hf₀, twoClusterCov_sub_const] at hge

theorem pair_guardGlobal_of_within (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (s₁ s₂ v : V) (hadm : PairGuardAdmissible x Y D s₁ s₂ v)
    (hwithin : ∀ g : Set (Sym2 V) → ℝ, Monotone g →
      0 ≤ guardWithin w x Y D ({s₁, s₂} : Set V) v g) :
    PairGuardCSHHolds w x Y D s₁ s₂ v := by
  have hw0 : ∀ e, 0 ≤ (w e : ℝ) := fun e => (w e).2.1
  have hw1 : ∀ e, (w e : ℝ) ≤ 1 := fun e => (w e).2.2
  have hm : ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω = 1 := by
    have hmass := BHK2006.integral_prodBernoulli_eq_sum w (fun _ => (1 : ℝ))
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmass
    exact hmass.symm
  have hsep : ∀ ω, ω ∈ sourceAvoid ({x} : Set V) Y ↔
      ∀ s ∈ ({x} : Set V), ∀ t ∈ Y, ¬ (openGraph ω).Reachable s t := by
    intro ω
    simp [sourceAvoid]
  have hregen : 0 < BHK2006.regenWeight (fun e => (w e : ℝ)) Y := by
    rw [BHK2006.regenWeight_eq_prod w Y]
    refine Finset.prod_pos fun e he => ?_
    exact sub_pos.2 (unitInterval.coe_lt_one.2 (hw e).2)
  have hpair : ∀ u : V, ({s₁, s₂} : Set V) ≠ ({u} : Set V) := by
    intro u heq
    have h₁ : s₁ = u := by
      have : s₁ ∈ ({u} : Set V) := heq ▸ (by simp)
      simpa using this
    have h₂ : s₂ = u := by
      have : s₂ ∈ ({u} : Set V) := heq ▸ (by simp)
      simpa using this
    exact hadm.1 (h₁.trans h₂.symm)
  intro g hg
  rw [guardCSHMargin_eq_twoClusterCov]
  refine twoClusterCov_nonneg_of_withinFirst (fun e => (w e : ℝ))
    hw0 hw1 hm ({x} : Set V) Y (sourceAvoid ({x} : Set V) Y)
    hsep hregen (guardLevelTest w x Y D ({s₁, s₂} : Set V) v)
    (fun A => guardLevelTest_antitone_second w x Y D
      ({s₁, s₂} : Set V) v A hpair) ?_ hg
  intro g' hg' _hg'0
  exact hwithin g' hg'

end KNAll.Guarded

end
