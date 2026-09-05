
import Percolation.Continuity.CovTau.MetaA2
import Percolation.Continuity.CovTau.StarBridgeS
import Percolation.Continuity.CovTau.MetaA2Anti
import Percolation.Literature.LatticeModels.ProdBernoulliCoupling

import KNConjectures.GuardedDefs
import KNConjectures.GuardedBasic
set_option linter.unusedSectionVars false

/-!
# The guarded induced-world kernel

Items 12--18 of the guarded Conjecture 6 proof ledger.
-/

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open Percolation.Continuity.CovTau
open scoped Classical

variable {V : Type*} [Fintype V]

private theorem sourceAvoid_isLowerSet (R B : Set V) :
    IsLowerSet (sourceAvoid R B) := by
  intro ω ω' hω'ω hω r hr b hb hconn
  exact hω r hr b hb (hconn.mono (openGraph_mono hω'ω))

private theorem sourceAvoid_anti_source {R R' B : Set V} (hRR' : R ⊆ R') :
    sourceAvoid R' B ⊆ sourceAvoid R B := by
  intro ω hω r hr
  exact hω r (hRR' hr)

private theorem sourceAvoid_anti_target {R B B' : Set V} (hBB' : B ⊆ B') :
    sourceAvoid R B' ⊆ sourceAvoid R B := by
  intro ω hω r hr b hb
  exact hω r hr b (hBB' hb)

private theorem prodBernoulli_real_anti_of_isLowerSet
    {ι : Type*} {p q : ι → unitInterval} (hpq : p ≤ q)
    {A : Set (Set ι)} (hA : IsLowerSet A) (hAm : MeasurableSet A) :
    (prodBernoulli q).real A ≤ (prodBernoulli p).real A := by
  have hcomp := prodBernoulli_real_mono_of_isUpperSet hpq hA.compl hAm.compl
  rw [probReal_compl_eq_one_sub hAm, probReal_compl_eq_one_sub hAm] at hcomp
  linarith

private theorem inducedWeight_mono {w : Sym2 V → unitInterval} {U U' : Set V}
    (hU'U : U' ⊆ U) : inducedWeight w U' ≤ inducedWeight w U := by
  intro e
  by_cases he : ∀ u ∈ e, u ∈ U'
  · have heU : ∀ u ∈ e, u ∈ U := fun u hu => hU'U (he u hu)
    change (if ∀ u ∈ e, u ∈ U' then w e else 0) ≤
      if ∀ u ∈ e, u ∈ U then w e else 0
    rw [if_pos he, if_pos heU]
  · change (if ∀ u ∈ e, u ∈ U' then w e else 0) ≤
      if ∀ u ∈ e, u ∈ U then w e else 0
    rw [if_neg he]
    exact bot_le

private theorem sourceKernel_nonneg (w : Sym2 V → unitInterval)
    (U R B K : Set V) : 0 ≤ sourceKernel w U R B K := by
  unfold sourceKernel
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

theorem sourceKernel_mono_cluster (w : Sym2 V → unitInterval) (U R B : Set V)
    {K K' : Set V} (hKK' : K ⊆ K') (_hK'U : K' ⊆ U) :
    sourceKernel w U R B K ≤ sourceKernel w U R B K' := by
  unfold sourceKernel
  by_cases hK : (K ∩ (R ∩ U)).Nonempty
  · have hK' : (K' ∩ (R ∩ U)).Nonempty := by
      rcases hK with ⟨u, huK, huR, huU⟩
      exact ⟨u, hKK' huK, huR, huU⟩
    rw [if_pos hK, if_pos hK']
    have hsources : (R ∩ U) \ K' ⊆ (R ∩ U) \ K := by
      rintro u ⟨huRU, huK'⟩
      exact ⟨huRU, fun huK => huK' (hKK' huK)⟩
    have hevents :
        sourceAvoid ((R ∩ U) \ K) (B ∩ U) ⊆
          sourceAvoid ((R ∩ U) \ K') (B ∩ U) :=
      sourceAvoid_anti_source hsources
    have hworlds : U \ K' ⊆ U \ K := by
      rintro u ⟨huU, huK'⟩
      exact ⟨huU, fun huK => huK' (hKK' huK)⟩
    calc
      worldProb w (U \ K) (sourceAvoid ((R ∩ U) \ K) (B ∩ U)) ≤
          worldProb w (U \ K) (sourceAvoid ((R ∩ U) \ K') (B ∩ U)) :=
        measureReal_mono hevents
      _ ≤ worldProb w (U \ K')
          (sourceAvoid ((R ∩ U) \ K') (B ∩ U)) :=
        prodBernoulli_real_anti_of_isLowerSet (inducedWeight_mono hworlds)
          (sourceAvoid_isLowerSet _ _) MeasurableSet.of_discrete
  · rw [if_neg hK]
    split_ifs
    · exact measureReal_nonneg
    · exact le_rfl

theorem sourceKernel_anti_target (w : Sym2 V → unitInterval) (U R K : Set V)
    {B B' : Set V} (hBB' : B ⊆ B') :
    sourceKernel w U R B' K ≤ sourceKernel w U R B K := by
  unfold sourceKernel
  by_cases hK : (K ∩ (R ∩ U)).Nonempty
  · rw [if_pos hK, if_pos hK]
    exact measureReal_mono (sourceAvoid_anti_target
      (Set.inter_subset_inter_left U hBB'))
  · simp [hK]

private theorem inducedWeight_delete_bar (w : Sym2 V → unitInterval)
    (U K : Set V) :
    (fun e => if e ∈ bar K then (0 : unitInterval) else inducedWeight w U e) =
      inducedWeight w (U \ K) := by
  funext e
  simp only [inducedWeight]
  by_cases heK : e ∈ bar K
  · rw [if_pos heK]
    have hnot : ¬ ∀ u ∈ e, u ∈ U \ K := by
      rcases heK with ⟨u, hue, huK⟩
      exact fun h => (h u hue).2 huK
    rw [if_neg hnot]
  · rw [if_neg heK]
    have hnoK : ∀ u ∈ e, u ∉ K := by
      intro u hue huK
      exact heK ⟨u, hue, huK⟩
    by_cases hU : ∀ u ∈ e, u ∈ U
    · rw [if_pos hU, if_pos (fun u hu => ⟨hU u hu, hnoK u hu⟩)]
    · rw [if_neg hU]
      have hUK : ¬ ∀ u ∈ e, u ∈ U \ K := fun h => hU fun u hu => (h u hu).1
      rw [if_neg hUK]

private theorem sum_weight_ind_sdiff_bar_eq_worldProb
    (w : Sym2 V → unitInterval) (U K : Set V)
    (E : Set (BondConfig V)) :
    (∑ η, BHK2006.weight (fun e => (inducedWeight w U e : ℝ)) η *
        Percolation.Literature.DecisionTree.ind E (η \ bar K)) =
      worldProb w (U \ K) E := by
  rw [CovTau.sum_weight_mul_eq_integral]
  rw [BHK2006.integral_comp_sdiff_prodBernoulli]
  rw [inducedWeight_delete_bar]
  rw [CovTau.ind_eq_indicator_one,
    integral_indicator_one MeasurableSet.of_discrete]
  rfl

private def clusterCarrier (z : V) (L : Set (Sym2 V)) : Set V :=
  insert z {u | ∃ e ∈ L, u ∈ e}

private theorem clusterCarrier_openEdgeCluster (ω : BondConfig V) (z : V) :
    clusterCarrier z (openEdgeCluster ω z) = openCluster ω z := by
  exact (CSH.openCluster_eq_insert_span ω z).symm

private theorem singletonAvoid_iff_disjoint_cluster (ω : BondConfig V)
    (z : V) (B : Set V) :
    ω ∈ sourceAvoid ({z} : Set V) B ↔ Disjoint (openCluster ω z) B := by
  rw [Set.disjoint_left]
  constructor
  · intro h u huC huB
    exact h z (by simp) u huB huC
  · intro h r hr b hb hrb
    have hrz : r = z := by simpa using hr
    subst r
    exact h hrb hb

private theorem singletonContact_iff_cluster_inter (ω : BondConfig V)
    (R : Set V) (z : V) :
    ω ∈ sourceConn R ({z} : Set V) ↔
      (openCluster ω z ∩ R).Nonempty := by
  constructor
  · rintro ⟨r, hrR, z', hz', hrz⟩
    have hz'z : z' = z := by simpa using hz'
    subst z'
    exact ⟨r, hrz.symm, hrR⟩
  · rintro ⟨r, hzr, hrR⟩
    exact ⟨r, hrR, z, by simp, hzr.symm⟩

private theorem sourceAvoid_residual_iff (ω : BondConfig V) (z : V)
    (R B : Set V) (hzB : ω ∈ sourceAvoid ({z} : Set V) B) :
    ω ∈ sourceAvoid R B ↔
      ω \ bar (openCluster ω z) ∈ sourceAvoid (R \ openCluster ω z) B := by
  constructor
  · intro h r hr b hb hconn
    exact h r hr.1 b hb (hconn.mono (openGraph_mono Set.sdiff_subset))
  · intro h r hr b hb hconn
    by_cases hrC : r ∈ openCluster ω z
    · exact hzB z (by simp) b hb (hrC.trans hconn)
    · have hzr : ¬ (openGraph ω).Reachable z r := hrC
      have hbar :
          {e : Sym2 V | ∃ u ∈ e,
            u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'} =
            bar (openCluster ω z) := by
        simpa [BHK2006.barOf] using (barOf_singleton_eq_bar z ω)
      have hres := LonePortSumGeneral.reachable_sdiff_bar_iff
        (s := z) (x := r) (ω := ω) hzr b
      rw [hbar] at hres
      exact h r ⟨hr, hrC⟩ b hb (hres.2 hconn)

theorem sourceKernel_tower (w : Sym2 V → unitInterval) (U R B : Set V) (z : V)
    (hinside : insert z (R ∪ B) ⊆ U) :
    (∫ ω in sourceAvoid ({z} : Set V) B,
      sourceKernel w U R B (sourceCluster ω ({z} : Set V))
        ∂(prodBernoulli (inducedWeight w U))) =
      worldGuardMass w U R z B := by
  classical
  have hzU : z ∈ U := hinside (by simp)
  have hRU : R ⊆ U := fun r hr => hinside (by simp [hr])
  have hBU : B ⊆ U := fun b hb => hinside (by simp [hb])
  have hRi : R ∩ U = R := Set.inter_eq_left.2 hRU
  have hBi : B ∩ U = B := Set.inter_eq_left.2 hBU
  let p : Sym2 V → unitInterval := inducedWeight w U
  let pr : Sym2 V → ℝ := fun e => (p e : ℝ)
  have hm : ∑ ω, BHK2006.weight pr ω = 1 := by
    have h1 := BHK2006.integral_prodBernoulli_eq_sum p fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  let Φ : Set (Sym2 V) → BondConfig V → ℝ := fun L η =>
    if Disjoint (clusterCarrier z L) B then
      if (clusterCarrier z L ∩ R).Nonempty then
        Percolation.Literature.DecisionTree.ind
          (sourceAvoid (R \ clusterCarrier z L) B) η
      else 0
    else 0
  have hbar (ω : BondConfig V) :
      {e : Sym2 V | ∃ u ∈ e,
        u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'} =
          bar (openCluster ω z) := by
    simpa [BHK2006.barOf] using (barOf_singleton_eq_bar z ω)
  have hleft : ∀ ω : BondConfig V,
      Φ (openEdgeCluster ω z)
          (ω \ {e : Sym2 V | ∃ u ∈ e,
            u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'}) =
        Percolation.Literature.DecisionTree.ind (guardEv R ({z} : Set V) B) ω := by
    intro ω
    rw [hbar]
    dsimp only [Φ]
    rw [clusterCarrier_openEdgeCluster]
    by_cases hzavoid : ω ∈ sourceAvoid ({z} : Set V) B
    · have hdis := (singletonAvoid_iff_disjoint_cluster ω z B).1 hzavoid
      rw [if_pos hdis]
      by_cases hcontact : ω ∈ sourceConn R ({z} : Set V)
      · have hne := (singletonContact_iff_cluster_inter ω R z).1 hcontact
        rw [if_pos hne]
        have hres := sourceAvoid_residual_iff ω z R B hzavoid
        by_cases hRavoid : ω ∈ sourceAvoid R B
        · rw [Percolation.Literature.DecisionTree.ind_of_mem (hres.1 hRavoid),
            Percolation.Literature.DecisionTree.ind_of_mem
              (show ω ∈ guardEv R ({z} : Set V) B from ⟨hRavoid, hcontact⟩)]
        · rw [Percolation.Literature.DecisionTree.ind_of_not_mem
              (fun h => hRavoid (hres.2 h)),
            Percolation.Literature.DecisionTree.ind_of_not_mem
              (fun h => hRavoid h.1)]
      · have hempty : ¬ (openCluster ω z ∩ R).Nonempty :=
          fun h => hcontact ((singletonContact_iff_cluster_inter ω R z).2 h)
        rw [if_neg hempty,
          Percolation.Literature.DecisionTree.ind_of_not_mem (fun h => hcontact h.2)]
    · have hdis : ¬ Disjoint (openCluster ω z) B :=
        fun h => hzavoid ((singletonAvoid_iff_disjoint_cluster ω z B).2 h)
      rw [if_neg hdis,
        Percolation.Literature.DecisionTree.ind_of_not_mem]
      rintro ⟨hRavoid, hcontact⟩
      rcases hcontact with ⟨r, hrR, z', hz', hrz⟩
      have hz'z : z' = z := by simpa using hz'
      subst z'
      apply hzavoid
      intro z' hz' b hb hzb
      ·
        have hz'z : z' = z := by simpa using hz'
        subst z'
        exact hRavoid r hrR b hb (hrz.trans hzb)
  have hright : ∀ ω : BondConfig V,
      (∑ η, BHK2006.weight pr η *
        Φ (openEdgeCluster ω z)
          (η \ {e : Sym2 V | ∃ u ∈ e,
            u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'})) =
        sourceKernel w U R B (openCluster ω z) *
          Percolation.Literature.DecisionTree.ind
            (sourceAvoid ({z} : Set V) B) ω := by
    intro ω
    rw [hbar]
    dsimp only [Φ]
    rw [clusterCarrier_openEdgeCluster]
    by_cases hzavoid : ω ∈ sourceAvoid ({z} : Set V) B
    · have hdis := (singletonAvoid_iff_disjoint_cluster ω z B).1 hzavoid
      simp only [if_pos hdis,
        Percolation.Literature.DecisionTree.ind_of_mem hzavoid, mul_one]
      by_cases hne : (openCluster ω z ∩ R).Nonempty
      · simp only [if_pos hne]
        rw [sum_weight_ind_sdiff_bar_eq_worldProb]
        simp only [sourceKernel, hRi, hBi, if_pos hne]
      · simp only [if_neg hne, mul_zero, Finset.sum_const_zero]
        simp [sourceKernel, hRi, hne]
    · have hdis : ¬ Disjoint (openCluster ω z) B :=
        fun h => hzavoid ((singletonAvoid_iff_disjoint_cluster ω z B).2 h)
      simp only [if_neg hdis, mul_zero, Finset.sum_const_zero,
        Percolation.Literature.DecisionTree.ind_of_not_mem hzavoid]
  have key := BHK2006.sum_cond_cluster_sdiff pr hm z Φ
  simp_rw [hleft] at key
  simp_rw [hright] at key
  simp only [KNAll.Guarded.sourceCluster_singleton]
  rw [← CovTau.sum_weight_mul_ind p
      (fun ω => sourceKernel w U R B (openCluster ω z))
      (sourceAvoid ({z} : Set V) B)]
  rw [worldGuardMass, if_pos hzU, hRi, hBi]
  unfold worldProb
  change (∑ ω, BHK2006.weight (fun e => (p e : ℝ)) ω *
      (sourceKernel w U R B (openCluster ω z) *
        Percolation.Literature.DecisionTree.ind (sourceAvoid ({z} : Set V) B) ω)) =
    (prodBernoulli p).real (guardEv R ({z} : Set V) B)
  rw [← CovTau.sum_weight_ind p (guardEv R ({z} : Set V) B)]
  simpa only [pr, p, mul_comm] using key.symm

private theorem sourceKernel_inter_world (w : Sym2 V → unitInterval)
    (U R B K : Set V) :
    sourceKernel w U R B (K ∩ U) = sourceKernel w U R B K := by
  have hcontact : (K ∩ U) ∩ (R ∩ U) = K ∩ (R ∩ U) := by
    ext u
    simp only [mem_inter_iff]
    tauto
  have hworld : U \ (K ∩ U) = U \ K := by
    ext u
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hsource : (R ∩ U) \ (K ∩ U) = (R ∩ U) \ K := by
    ext u
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  simp only [sourceKernel, hcontact, hworld, hsource]

private theorem sourceAvoid_singleton_raw (v : V) (A : Set V) :
    sourceAvoid ({v} : Set V) A =
      {ω : BondConfig V | ∀ a ∈ A, ¬ (openGraph ω).Reachable v a} := by
  ext ω
  simp [sourceAvoid]

private theorem worldAvoidMass_eq (w : Sym2 V → unitInterval)
    (U A : Set V) (v : V) (hvU : v ∈ U) (hAU : A ⊆ U) :
    worldAvoidMass w U v A =
      (prodBernoulli (inducedWeight w U)).real
        (sourceAvoid ({v} : Set V) A) := by
  rw [worldAvoidMass, if_pos hvU, worldProb,
    Set.inter_eq_left.2 hAU]

theorem guarded_exchange (w : Sym2 V → unitInterval) (U X R N N' : Set V)
    (x v : V) (hdis : Disjoint N N')
    (hinside : insert x (insert v (X ∪ R ∪ N ∪ N')) ⊆ U) :
    worldGuardMass w U R v (X ∪ N) * worldAvoidMass w U v (X ∪ N') ≤
      worldAvoidMass w U v (X ∪ N ∪ N') * worldGuardMass w U R v X := by
  classical
  have hvU : v ∈ U := hinside (by simp)
  have hXU : X ⊆ U := fun a ha => hinside (by simp [ha])
  have hRU : R ⊆ U := fun a ha => hinside (by simp [ha])
  have hNU : N ⊆ U := fun a ha => hinside (by simp [ha])
  have hN'U : N' ⊆ U := fun a ha => hinside (by simp [ha])
  have hXN_U : X ∪ N ⊆ U := Set.union_subset hXU hNU
  have hXN'_U : X ∪ N' ⊆ U := Set.union_subset hXU hN'U
  have hXNN'_U : X ∪ N ∪ N' ⊆ U :=
    Set.union_subset hXN_U hN'U
  have hinter : (X ∪ N) ∩ (X ∪ N') = X := by
    ext a
    constructor
    · rintro ⟨haX | haN, haX' | haN'⟩
      · exact haX
      · exact haX
      · exact haX'
      · exact False.elim (Set.disjoint_left.1 hdis haN haN')
    · intro haX
      exact ⟨Or.inl haX, Or.inl haX⟩
  have hunion : (X ∪ N) ∪ (X ∪ N') = X ∪ N ∪ N' := by
    ext a
    simp only [mem_union]
    tauto
  let p : Sym2 V → unitInterval := inducedWeight w U
  let pr : Sym2 V → ℝ := fun e => (p e : ℝ)
  have hp0 : ∀ e, 0 ≤ pr e := fun e => (p e).2.1
  have hp1 : ∀ e, pr e ≤ 1 := fun e => (p e).2.2
  have hm : ∑ ω, BHK2006.weight pr ω = 1 := by
    have h1 := BHK2006.integral_prodBernoulli_eq_sum p fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  let F : Set (Sym2 V) → ℝ := fun L =>
    sourceKernel w U R (X ∪ N) (clusterCarrier v L ∩ U)
  have hFmono : Monotone F := by
    intro L L' hLL'
    apply sourceKernel_mono_cluster w U R (X ∪ N)
    · exact Set.inter_subset_inter_left U
        (Set.insert_subset_insert fun u ⟨e, he, hue⟩ => ⟨e, hLL' he, hue⟩)
    · exact Set.inter_subset_right
  have hF0 : ∀ L, 0 ≤ F L := fun L => sourceKernel_nonneg _ _ _ _ _
  have hcore := BHK2006.core pr hp0 hp1 hm (Finset.univ : Finset V)
    v (Finset.mem_univ v) (X ∪ N) (X ∪ N') (by simp) (by simp)
    F (fun _ => (1 : ℝ)) hFmono monotone_const hF0 (fun _ => zero_le_one)
  simp only [CovTau.rC_univ, CovTau.rD_univ, one_mul, mul_one] at hcore
  rw [← sourceAvoid_singleton_raw v (X ∪ N),
    ← sourceAvoid_singleton_raw v (X ∪ N'),
    ← sourceAvoid_singleton_raw v ((X ∪ N) ∩ (X ∪ N')),
    ← sourceAvoid_singleton_raw v ((X ∪ N) ∪ (X ∪ N'))] at hcore
  rw [CovTau.sum_weight_mul_ind p,
    CovTau.sum_weight_ind p,
    CovTau.sum_weight_mul_ind p,
    CovTau.sum_weight_ind p] at hcore
  have hFintegral : ∀ A : Set V,
      (∫ ω in sourceAvoid ({v} : Set V) A,
        F (openEdgeCluster ω v) ∂(prodBernoulli p)) =
      ∫ ω in sourceAvoid ({v} : Set V) A,
        sourceKernel w U R (X ∪ N) (openCluster ω v) ∂(prodBernoulli p) := by
    intro A
    refine setIntegral_congr_fun MeasurableSet.of_discrete fun ω _ => ?_
    dsimp only [F]
    rw [clusterCarrier_openEdgeCluster, sourceKernel_inter_world]
  rw [hFintegral (X ∪ N), hFintegral ((X ∪ N) ∩ (X ∪ N')),
    hinter, hunion] at hcore
  have htXN := sourceKernel_tower w U R (X ∪ N) v (by
    intro a ha
    rcases ha with rfl | ha
    · exact hvU
    · rcases ha with ha | ha
      · exact hRU ha
      · exact hXN_U ha)
  have htX := sourceKernel_tower w U R X v (by
    intro a ha
    rcases ha with rfl | ha
    · exact hvU
    · rcases ha with ha | ha
      · exact hRU ha
      · exact hXU ha)
  simp only [KNAll.Guarded.sourceCluster_singleton] at htXN htX
  have hmid :
      (∫ ω in sourceAvoid ({v} : Set V) X,
        sourceKernel w U R (X ∪ N) (openCluster ω v) ∂prodBernoulli p) ≤
      ∫ ω in sourceAvoid ({v} : Set V) X,
        sourceKernel w U R X (openCluster ω v) ∂prodBernoulli p := by
    refine setIntegral_mono_on (Integrable.of_finite).integrableOn
      (Integrable.of_finite).integrableOn MeasurableSet.of_discrete fun ω _ => ?_
    exact sourceKernel_anti_target w U R (openCluster ω v) Set.subset_union_left
  rw [htXN] at hcore
  have hmassXN' := worldAvoidMass_eq w U (X ∪ N') v hvU hXN'_U
  have hmassXNN' := worldAvoidMass_eq w U (X ∪ N ∪ N') v hvU hXNN'_U
  have hmassXNN'0 : 0 ≤ worldAvoidMass w U v (X ∪ N ∪ N') := by
    rw [hmassXNN']
    exact measureReal_nonneg
  rw [← hmassXN', ← hmassXNN'] at hcore
  calc
    worldGuardMass w U R v (X ∪ N) * worldAvoidMass w U v (X ∪ N') ≤
        (∫ ω in sourceAvoid ({v} : Set V) X,
          sourceKernel w U R (X ∪ N) (openCluster ω v) ∂prodBernoulli p) *
          worldAvoidMass w U v (X ∪ N ∪ N') := hcore
    _ ≤ (∫ ω in sourceAvoid ({v} : Set V) X,
          sourceKernel w U R X (openCluster ω v) ∂prodBernoulli p) *
          worldAvoidMass w U v (X ∪ N ∪ N') :=
      mul_le_mul_of_nonneg_right hmid hmassXNN'0
    _ = worldAvoidMass w U v (X ∪ N ∪ N') * worldGuardMass w U R v X := by
      rw [htX]
      ring

/-! ### Finite-world dictionary for the guarded four-functions induction -/

private theorem inducedWeight_coe_eq_zeroed (w : Sym2 V → unitInterval)
    (U : Finset V) :
    inducedWeight w (↑U : Set V) =
      fun e => if e ∈ (BHK2006.edgesIn U)ᶜ then (0 : unitInterval) else w e := by
  funext e
  simp only [inducedWeight]
  have hin : (∀ u ∈ e, u ∈ (↑U : Set V)) ↔ e ∈ BHK2006.edgesIn U := by
    rfl
  by_cases he : e ∈ BHK2006.edgesIn U
  · rw [if_pos (hin.2 he)]
    simp [he]
  · rw [if_neg (fun h => he (hin.1 h))]
    simp [he]

private theorem integral_induced_coe_eq_sum (w : Sym2 V → unitInterval)
    (U : Finset V) (f : BondConfig V → ℝ) :
    (∫ ω, f ω ∂prodBernoulli (inducedWeight w (↑U : Set V))) =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        f (ω ∩ BHK2006.edgesIn U) := by
  calc
    (∫ ω, f ω ∂prodBernoulli (inducedWeight w (↑U : Set V))) =
        ∫ ω, f (ω \ (BHK2006.edgesIn U)ᶜ) ∂prodBernoulli w := by
          symm
          apply BHK2006.integral_comp_sdiff_prodBernoulli'
          · intro e he
            have he' : ¬ ∀ u ∈ e, u ∈ (↑U : Set V) := by
              simpa only [BHK2006.edgesIn, mem_compl_iff, mem_setOf_eq,
                Finset.mem_coe] using he
            simp only [inducedWeight, if_neg he']
          · intro e he
            have he' : ∀ u ∈ e, u ∈ (↑U : Set V) := by
              simpa only [BHK2006.edgesIn, mem_compl_iff, mem_setOf_eq,
                Finset.mem_coe, not_not] using he
            simp only [inducedWeight, if_pos he']
    _ = ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        f (ω ∩ BHK2006.edgesIn U) := by
      simp only [Set.sdiff_compl]
      rw [BHK2006.integral_prodBernoulli_eq_sum]

private theorem worldProb_coe_eq_sum (w : Sym2 V → unitInterval)
    (U : Finset V) (E : Set (BondConfig V)) :
    worldProb w (↑U : Set V) E =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        Percolation.Literature.DecisionTree.ind E
          (ω ∩ BHK2006.edgesIn U) := by
  unfold worldProb
  rw [← integral_indicator_one MeasurableSet.of_discrete,
    ← CovTau.ind_eq_indicator_one, integral_induced_coe_eq_sum]

private theorem setIntegral_induced_coe_eq_sum (w : Sym2 V → unitInterval)
    (U : Finset V) (E : Set (BondConfig V)) (f : BondConfig V → ℝ) :
    (∫ ω in E, f ω ∂prodBernoulli (inducedWeight w (↑U : Set V))) =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        (f (ω ∩ BHK2006.edgesIn U) *
          Percolation.Literature.DecisionTree.ind E
            (ω ∩ BHK2006.edgesIn U)) := by
  rw [← integral_indicator MeasurableSet.of_discrete,
    integral_induced_coe_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∩ BHK2006.edgesIn U ∈ E
  · rw [indicator_of_mem hω,
      Percolation.Literature.DecisionTree.ind_of_mem hω]
    ring
  · rw [indicator_of_notMem hω,
      Percolation.Literature.DecisionTree.ind_of_not_mem hω, mul_zero]
    ring

private theorem sourceAvoid_restricted_iff_rD (U : Finset V)
    (r : V) (B : Set V) (ω : BondConfig V) (hrU : r ∈ U) :
    ω ∩ BHK2006.edgesIn U ∈
        sourceAvoid ({r} : Set V) (B ∩ (↑U : Set V)) ↔
      ω ∈ BHK2006.rD U r B := by
  simp only [sourceAvoid, mem_singleton_iff, forall_eq, mem_inter_iff,
    BHK2006.rD, mem_setOf_eq]
  constructor
  · intro h b hb hrb
    have hbU : b ∈ U := by
      by_cases hbr : b = r
      · simpa [hbr] using hrU
      · exact SandwichBHK.mem_of_reachable hrb (Ne.symm hbr)
    exact h b ⟨hb, hbU⟩ hrb
  · intro h b hbU
    exact h b hbU.1

private theorem sourceCluster_restricted_mem_iff_sC (U : Finset V)
    (N : Set V) (ω : BondConfig V) {u : V} (huU : u ∈ U) :
    u ∈ sourceCluster (ω ∩ BHK2006.edgesIn U) (N ∩ (↑U : Set V)) ↔
      u ∈ CovTau.sC U N ω := by
  simp only [sourceCluster, mem_iUnion, CovTau.mem_sC]
  constructor
  · rintro ⟨n, ⟨hnN, -⟩, hnu⟩
    exact ⟨n, hnN, hnu⟩
  · rintro ⟨n, hnN, hnu⟩
    have hnU : n ∈ U := by
      by_cases hnu' : n = u
      · simpa [hnu'] using huU
      · exact SandwichBHK.mem_of_reachable hnu.symm (Ne.symm hnu')
    exact ⟨n, ⟨hnN, hnU⟩, hnu⟩

private theorem worldRemainder_eq_rest (U : Finset V) (N : Set V)
    (ω : BondConfig V) :
    (↑U : Set V) \
        sourceCluster (ω ∩ BHK2006.edgesIn U) (N ∩ (↑U : Set V)) =
      (↑(CovTau.rest U N ω) : Set V) := by
  ext u
  simp only [mem_sdiff, Finset.mem_coe, CovTau.mem_rest]
  constructor
  · rintro ⟨huU, huC⟩
    exact ⟨huU, fun huSC => huC ((sourceCluster_restricted_mem_iff_sC U N ω huU).2 huSC)⟩
  · rintro ⟨huU, huSC⟩
    exact ⟨huU, fun huC => huSC ((sourceCluster_restricted_mem_iff_sC U N ω huU).1 huC)⟩

private theorem worldAvoidMass_eq_Mav (w : Sym2 V → unitInterval)
    (U : Finset V) (A : Set V) (v : V) (hvU : v ∈ U) :
    worldAvoidMass w (↑U : Set V) v A =
      CovTau.Mav (fun e => (w e : ℝ)) U A v ∅ := by
  rw [worldAvoidMass,
    if_pos (show v ∈ (↑U : Set V) from hvU), worldProb_coe_eq_sum]
  unfold CovTau.Mav
  simp only [Set.union_empty]
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  apply BystanderBHK.ind_congr
  exact sourceAvoid_restricted_iff_rD U v A ω hvU

private theorem guardedWorldY_eq_Yw (w : Sym2 V → unitInterval)
    (U : Finset V) (x : V) (N : Set V) (h : Set V → ℝ)
    (hxU : x ∈ U) :
    guardedWorldY w (↑U : Set V) x N h =
      CovTau.Yw (fun e => (w e : ℝ)) U x (fun W => h (↑W : Set V)) N := by
  rw [guardedWorldY,
    if_pos (show x ∈ (↑U : Set V) from hxU), setIntegral_induced_coe_eq_sum]
  unfold CovTau.Yw
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  rw [worldRemainder_eq_rest]
  congr 1
  apply BystanderBHK.ind_congr
  exact sourceAvoid_restricted_iff_rD U x N ω hxU

/-! The guarded observer factor has to retain avoidance by every member of `R`.
The following finite-world event is the convenient form for the star decomposition. -/

private def finiteGuardEv (U : Finset V) (R : Set V) (v : V)
    (B : Set V) : Set (BondConfig V) :=
  {ω | ω ∩ BHK2006.edgesIn U ∈ guardEv R ({v} : Set V) B}

private def finiteGuardMass (wr : Sym2 V → ℝ) (U : Finset V)
    (R : Set V) (v : V) (B : Set V) : ℝ :=
  ∑ ω, BHK2006.weight wr ω *
    Percolation.Literature.DecisionTree.ind (finiteGuardEv U R v B) ω

private theorem finiteGuardEv_diff_meeting (U Z : Finset V) (R : Set V)
    (v : V) (B : Set V) (ω : BondConfig V) :
    ω \ BHK2006.meeting Z ∈ finiteGuardEv (U \ Z) R v B ↔
      ω ∈ finiteGuardEv (U \ Z) R v B := by
  simp only [finiteGuardEv, mem_setOf_eq, BHK2006.diff_meeting_inter_edgesIn]

private theorem finiteGuardEv_restrict_iff {U Z : Finset V}
    (hZU : Z ⊆ U) {R B : Set V} (hZB : (↑Z : Set V) ⊆ B)
    (hRZ : Disjoint R (↑Z : Set V)) (v : V) (ω : BondConfig V) :
    ω ∈ finiteGuardEv U R v B ↔
      ω ∈ finiteGuardEv (U \ Z) R v
        ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) := by
  simp only [finiteGuardEv, mem_setOf_eq, guardEv, mem_inter_iff]
  constructor
  · rintro ⟨hav, hcon⟩
    have hav' : ω ∩ BHK2006.edgesIn (U \ Z) ∈
        sourceAvoid R ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) := by
      intro r hr
      have hrZ : r ∉ Z := fun hr' => Set.disjoint_left.1 hRZ hr hr'
      exact (BHK2006.mem_rD_iff_restrict hZU hrZ hZB ω).1 (hav r hr)
    refine ⟨hav', ?_⟩
    rcases hcon with ⟨r, hr, z, hz, hrz⟩
    have hzv : z = v := by simpa using hz
    subst z
    have hrZ : r ∉ Z := fun hr' => Set.disjoint_left.1 hRZ hr hr'
    have hS : ∀ n ∈ BHK2006.rS U Z ω,
        ¬(openGraph (ω ∩ BHK2006.edgesIn (U \ Z))).Reachable r n :=
      fun n hn => hav' r hr n (Or.inr hn)
    exact ⟨r, hr, v, by simp,
      (BHK2006.reach_restrict hrZ hS hrz).2⟩
  · rintro ⟨hav, hcon⟩
    have hav' : ω ∩ BHK2006.edgesIn U ∈ sourceAvoid R B := by
      intro r hr
      have hrZ : r ∉ Z := fun hr' => Set.disjoint_left.1 hRZ hr hr'
      exact (BHK2006.mem_rD_iff_restrict hZU hrZ hZB ω).2 (hav r hr)
    refine ⟨hav', ?_⟩
    rcases hcon with ⟨r, hr, z, hz, hrz⟩
    have hzv : z = v := by simpa using hz
    subst z
    exact ⟨r, hr, v, by simp,
      hrz.mono (BHK2006.openGraph_le
        (Set.inter_subset_inter_right _
          (BHK2006.edgesIn_mono Finset.sdiff_subset)))⟩

private theorem worldGuardMass_eq_finiteGuardMass
    (w : Sym2 V → unitInterval) (U : Finset V) (R B : Set V) (v : V)
    (hvU : v ∈ U) (hRU : R ⊆ (↑U : Set V)) (hBU : B ⊆ (↑U : Set V)) :
    worldGuardMass w (↑U : Set V) R v B =
      finiteGuardMass (fun e => (w e : ℝ)) U R v B := by
  rw [worldGuardMass, if_pos (show v ∈ (↑U : Set V) from hvU),
    Set.inter_eq_left.2 hRU, Set.inter_eq_left.2 hBU,
    worldProb_coe_eq_sum]
  unfold finiteGuardMass
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  apply BystanderBHK.ind_congr
  rfl

private theorem finiteGuardMass_step (wr : Sym2 V → ℝ) {U Z : Finset V}
    (hZU : Z ⊆ U) {R B : Set V} (hZB : (↑Z : Set V) ⊆ B)
    (hRZ : Disjoint R (↑Z : Set V)) (v : V)
    (hm : ∑ ω, BHK2006.weight wr ω = 1) :
    finiteGuardMass wr U R v B =
      ∑ ω, BHK2006.weight wr ω *
        finiteGuardMass wr (U \ Z) R v
          ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) := by
  let A : Set (Sym2 V) := BHK2006.meeting Z
  let Φ : BondConfig V → BondConfig V → ℝ := fun ζ η =>
    Percolation.Literature.DecisionTree.ind
      (finiteGuardEv (U \ Z) R v
        ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ζ)) η
  have h1 : ∀ ω : BondConfig V,
      Percolation.Literature.DecisionTree.ind (finiteGuardEv U R v B) ω =
        Φ (ω ∩ A) (ω \ A) := by
    intro ω
    dsimp only [Φ, A]
    apply BystanderBHK.ind_congr
    rw [BHK2006.rS_inter_meeting,
      finiteGuardEv_diff_meeting]
    exact finiteGuardEv_restrict_iff hZU hZB hRZ v ω
  have h2 : ∀ ω η : BondConfig V,
      Φ (ω ∩ A) (η \ A) =
        Percolation.Literature.DecisionTree.ind
          (finiteGuardEv (U \ Z) R v
            ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω)) η := by
    intro ω η
    dsimp only [Φ, A]
    rw [BHK2006.rS_inter_meeting]
    apply BystanderBHK.ind_congr
    exact finiteGuardEv_diff_meeting U Z R v _ η
  unfold finiteGuardMass
  calc
    (∑ ω, BHK2006.weight wr ω *
        Percolation.Literature.DecisionTree.ind (finiteGuardEv U R v B) ω) =
        (∑ ω, BHK2006.weight wr ω) *
          ∑ ω, BHK2006.weight wr ω * Φ (ω ∩ A) (ω \ A) := by
      rw [hm, one_mul]
      simp_rw [h1]
    _ = ∑ ω, BHK2006.weight wr ω *
        ∑ η, BHK2006.weight wr η * Φ (ω ∩ A) (η \ A) :=
      BHK2006.blockFubini wr A Φ
    _ = ∑ ω, BHK2006.weight wr ω *
        ∑ η, BHK2006.weight wr η *
          Percolation.Literature.DecisionTree.ind
            (finiteGuardEv (U \ Z) R v
              ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω)) η := by
      simp_rw [h2]

private theorem sourceAvoid_restricted_iff_subset_rest (U : Finset V)
    (R N : Set V) (ω : BondConfig V) (hRU : R ⊆ (↑U : Set V)) :
    ω ∩ BHK2006.edgesIn U ∈ sourceAvoid R N ↔
      R ⊆ (↑(CovTau.rest U N ω) : Set V) := by
  constructor
  · intro hav r hr
    rw [Finset.mem_coe, CovTau.mem_rest]
    refine ⟨hRU hr, ?_⟩
    rintro ⟨n, hn, hnr⟩
    exact hav r hr n hn hnr.symm
  · intro hrest r hr n hn hrn
    have hrnot := (CovTau.mem_rest.1 (show r ∈ CovTau.rest U N ω from hrest hr)).2
    exact hrnot ⟨n, hn, hrn.symm⟩

private def guardedPure (w : Sym2 V → unitInterval) (R : Set V) (v : V)
    (X : Set V) (h : Set V → ℝ) (W : Finset V) : ℝ :=
  if R ⊆ (↑W : Set V) then
    worldGuardPrice w (↑W : Set V) R v X * h (↑W : Set V)
  else 0

private theorem guardedWorldX_eq_Yw (w : Sym2 V → unitInterval)
    (U : Finset V) (R : Set V) (x v : V) (X N : Set V)
    (h : Set V → ℝ) (hxU : x ∈ U) (hvU : v ∈ U)
    (hRU : R ⊆ (↑U : Set V)) (hNU : N ⊆ (↑U : Set V)) :
    guardedWorldX w (↑U : Set V) R x v X N h =
      CovTau.Yw (fun e => (w e : ℝ)) U x (guardedPure w R v X h) N := by
  rw [guardedWorldX,
    if_pos (show x ∈ (↑U : Set V) ∧ v ∈ (↑U : Set V) from ⟨hxU, hvU⟩),
    Set.inter_eq_left.2 hNU, Set.inter_eq_left.2 hRU,
    setIntegral_induced_coe_eq_sum]
  unfold CovTau.Yw
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  have hrem := worldRemainder_eq_rest U N ω
  rw [Set.inter_eq_left.2 hNU] at hrem
  rw [hrem]
  have hxiff :
      ω ∩ BHK2006.edgesIn U ∈ sourceAvoid ({x} : Set V) N ↔
        ω ∈ BHK2006.rD U x N :=
    by simpa only [Set.inter_eq_left.2 hNU] using
      sourceAvoid_restricted_iff_rD U x N ω hxU
  have hRiff :
      ω ∩ BHK2006.edgesIn U ∈ sourceAvoid R N ↔
        R ⊆ (↑(CovTau.rest U N ω) : Set V) :=
    sourceAvoid_restricted_iff_subset_rest U R N ω hRU
  by_cases hxav : ω ∈ BHK2006.rD U x N
  · have hxav' := hxiff.2 hxav
    rw [Percolation.Literature.DecisionTree.ind_of_mem hxav]
    by_cases hRav : R ⊆ (↑(CovTau.rest U N ω) : Set V)
    · have hRav' := hRiff.2 hRav
      rw [guardedPure, if_pos hRav,
        Percolation.Literature.DecisionTree.ind_of_mem
          (show ω ∩ BHK2006.edgesIn U ∈
            sourceAvoid ({x} : Set V) N ∩ sourceAvoid R N from
            ⟨hxav', hRav'⟩)]
    · have hRav' : ω ∩ BHK2006.edgesIn U ∉ sourceAvoid R N :=
        fun ha => hRav (hRiff.1 ha)
      rw [guardedPure, if_neg hRav,
        Percolation.Literature.DecisionTree.ind_of_not_mem
          (show ω ∩ BHK2006.edgesIn U ∉
            sourceAvoid ({x} : Set V) N ∩ sourceAvoid R N from
            fun ha => hRav' ha.2)]
      ring
  · have hxav' : ω ∩ BHK2006.edgesIn U ∉ sourceAvoid ({x} : Set V) N :=
      fun ha => hxav (hxiff.1 ha)
    rw [Percolation.Literature.DecisionTree.ind_of_not_mem hxav,
      Percolation.Literature.DecisionTree.ind_of_not_mem
        (show ω ∩ BHK2006.edgesIn U ∉
          sourceAvoid ({x} : Set V) N ∩ sourceAvoid R N from
          fun ha => hxav' ha.1)]
    ring

/-! The four exact star recursions used below. -/

private theorem worldGuardMass_step (w : Sym2 V → unitInterval)
    {U Z : Finset V} (hZU : Z ⊆ U) {R B : Set V}
    (hRU : R ⊆ (↑U : Set V)) (hBU : B ⊆ (↑U : Set V))
    (hZB : (↑Z : Set V) ⊆ B) (hRZ : Disjoint R (↑Z : Set V))
    (v : V) (hvU : v ∈ U) (hvZ : v ∉ Z)
    (hm : ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω = 1) :
    worldGuardMass w (↑U : Set V) R v B =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        worldGuardMass w (↑(U \ Z) : Set V) R v
          ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) := by
  have hvUZ : v ∈ U \ Z := Finset.mem_sdiff.2 ⟨hvU, hvZ⟩
  have hRUZ : R ⊆ (↑(U \ Z) : Set V) := by
    intro r hr
    exact Finset.mem_sdiff.2 ⟨hRU hr,
      fun hrZ => Set.disjoint_left.1 hRZ hr hrZ⟩
  rw [worldGuardMass_eq_finiteGuardMass w U R B v hvU hRU hBU,
    finiteGuardMass_step (fun e => (w e : ℝ)) hZU hZB hRZ v hm]
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  symm
  apply worldGuardMass_eq_finiteGuardMass w (U \ Z) R
    ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) v hvUZ hRUZ
  rintro a (ha | ha)
  · exact Finset.mem_sdiff.2 ⟨hBU ha.1, ha.2⟩
  · exact BHK2006.rS_subset U Z ω ha

private theorem guardedWorldY_step (w : Sym2 V → unitInterval)
    {U Z : Finset V} (hZU : Z ⊆ U) {x : V} (hxU : x ∈ U)
    (hxZ : x ∉ Z) {N : Set V} (_hNU : N ⊆ (↑U : Set V))
    (hZN : (↑Z : Set V) ⊆ N) (h : Set V → ℝ)
    (hm : ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω = 1) :
    guardedWorldY w (↑U : Set V) x N h =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        guardedWorldY w (↑(U \ Z) : Set V) x
          ((N \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) h := by
  have hxUZ : x ∈ U \ Z := Finset.mem_sdiff.2 ⟨hxU, hxZ⟩
  rw [guardedWorldY_eq_Yw w U x N h hxU,
    CovTau.Yw_step hZU hxZ hZN (fun e => (w e : ℝ)) hm]
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  exact (guardedWorldY_eq_Yw w (U \ Z) x
    ((N \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) h hxUZ).symm

private theorem worldAvoidMass_step (w : Sym2 V → unitInterval)
    {U Z : Finset V} (hZU : Z ⊆ U) {B : Set V}
    (_hBU : B ⊆ (↑U : Set V)) (hZB : (↑Z : Set V) ⊆ B)
    (v : V) (hvU : v ∈ U) (hvZ : v ∉ Z)
    (hm : ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω = 1) :
    worldAvoidMass w (↑U : Set V) v B =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        worldAvoidMass w (↑(U \ Z) : Set V) v
          ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) := by
  have hvUZ : v ∈ U \ Z := Finset.mem_sdiff.2 ⟨hvU, hvZ⟩
  rw [worldAvoidMass_eq_Mav w U B v hvU]
  have hswap :
      CovTau.Mav (fun e => (w e : ℝ)) U B v ∅ =
        CovTau.Mav (fun e => (w e : ℝ)) U ∅ v B := by
    unfold CovTau.Mav
    simp only [Set.union_empty, Set.empty_union]
  rw [hswap, CovTau.Mav_step hZU hvU hvZ hZB
    (fun e => (w e : ℝ)) hm]
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  calc
    CovTau.Mav (fun e => (w e : ℝ)) (U \ Z) ∅ v
        ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) =
        CovTau.Mav (fun e => (w e : ℝ)) (U \ Z)
          ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) v ∅ := by
      unfold CovTau.Mav
      simp only [Set.empty_union, Set.union_empty]
    _ = worldAvoidMass w (↑(U \ Z) : Set V) v
        ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) :=
      (worldAvoidMass_eq_Mav w (U \ Z)
        ((B \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) v hvUZ).symm

private theorem guardedWorldX_step (w : Sym2 V → unitInterval)
    {U Z : Finset V} (hZU : Z ⊆ U) {R : Set V}
    (hRU : R ⊆ (↑U : Set V)) (hRZ : Disjoint R (↑Z : Set V))
    {x v : V} (hxU : x ∈ U) (hvU : v ∈ U) (hxZ : x ∉ Z)
    (hvZ : v ∉ Z) (X : Set V) {N : Set V}
    (hNU : N ⊆ (↑U : Set V)) (hZN : (↑Z : Set V) ⊆ N)
    (h : Set V → ℝ)
    (hm : ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω = 1) :
    guardedWorldX w (↑U : Set V) R x v X N h =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        guardedWorldX w (↑(U \ Z) : Set V) R x v X
          ((N \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) h := by
  have hxUZ : x ∈ U \ Z := Finset.mem_sdiff.2 ⟨hxU, hxZ⟩
  have hvUZ : v ∈ U \ Z := Finset.mem_sdiff.2 ⟨hvU, hvZ⟩
  have hRUZ : R ⊆ (↑(U \ Z) : Set V) := by
    intro r hr
    exact Finset.mem_sdiff.2 ⟨hRU hr,
      fun hrZ => Set.disjoint_left.1 hRZ hr hrZ⟩
  rw [guardedWorldX_eq_Yw w U R x v X N h hxU hvU hRU hNU,
    CovTau.Yw_step hZU hxZ hZN (fun e => (w e : ℝ)) hm]
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  symm
  apply guardedWorldX_eq_Yw w (U \ Z) R x v X
    ((N \ (↑Z : Set V)) ∪ BHK2006.rS U Z ω) h hxUZ hvUZ hRUZ
  rintro a (ha | ha)
  · exact Finset.mem_sdiff.2 ⟨hNU ha.1, ha.2⟩
  · exact BHK2006.rS_subset U Z ω ha

/-! The three degenerate branches of the guarded induction. -/

private theorem worldGuardMass_eq_zero_of_target_mem
    (w : Sym2 V → unitInterval) (U R B : Set V) (v : V) (hvB : v ∈ B) :
    worldGuardMass w U R v B = 0 := by
  unfold worldGuardMass
  by_cases hvU : v ∈ U
  · rw [if_pos hvU]
    have hempty : guardEv (R ∩ U) ({v} : Set V) (B ∩ U) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro ω ⟨hav, r, hr, z, hz, hrz⟩
      have hzv : z = v := by simpa using hz
      subst z
      exact hav r hr v ⟨hvB, hvU⟩ hrz
    rw [worldProb, hempty, measureReal_empty]
  · rw [if_neg hvU]

private theorem guardedWorldY_eq_zero_of_mem (w : Sym2 V → unitInterval)
    (U : Finset V) (x : V) (N : Set V) (h : Set V → ℝ)
    (hxU : x ∈ U) (hxN : x ∈ N) :
    guardedWorldY w (↑U : Set V) x N h = 0 := by
  rw [guardedWorldY_eq_Yw w U x N h hxU,
    CovTau.Yw_eq_zero_of_mem _ _ _ _ hxN]

private theorem worldGuardMass_eq_zero_of_source_inter
    (w : Sym2 V → unitInterval) (U R B : Set V) (v : V)
    (hRB : (R ∩ B ∩ U).Nonempty) : worldGuardMass w U R v B = 0 := by
  unfold worldGuardMass
  by_cases hvU : v ∈ U
  · rw [if_pos hvU]
    have hempty : guardEv (R ∩ U) ({v} : Set V) (B ∩ U) = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro ω ⟨hav, -⟩
      rcases hRB with ⟨r, ⟨hrR, hrB⟩, hrU⟩
      exact hav r ⟨hrR, hrU⟩ r ⟨hrB, hrU⟩
        (SimpleGraph.Reachable.refl r)
    rw [worldProb, hempty, measureReal_empty]
  · rw [if_neg hvU]

private theorem worldAvoidMass_nonneg (w : Sym2 V → unitInterval)
    (U : Set V) (v : V) (B : Set V) : 0 ≤ worldAvoidMass w U v B := by
  unfold worldAvoidMass
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

private theorem worldGuardMass_nonneg (w : Sym2 V → unitInterval)
    (U R : Set V) (v : V) (B : Set V) : 0 ≤ worldGuardMass w U R v B := by
  unfold worldGuardMass
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

private theorem worldGuardPrice_nonneg (w : Sym2 V → unitInterval)
    (U R : Set V) (v : V) (X : Set V) :
    0 ≤ worldGuardPrice w U R v X := by
  exact div_nonneg (worldGuardMass_nonneg w U R v X)
    (worldAvoidMass_nonneg w U v X)

private theorem worldGuardMass_le_worldAvoidMass
    (w : Sym2 V → unitInterval) (U R B : Set V) (v : V) :
    worldGuardMass w U R v B ≤ worldAvoidMass w U v B := by
  unfold worldGuardMass worldAvoidMass
  by_cases hvU : v ∈ U
  · rw [if_pos hvU, if_pos hvU]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    rintro ω ⟨hav, r, hr, z, hz, hrz⟩
    have hzv : z = v := by simpa using hz
    subst z
    intro v' hv' b hb hvb
    have hv'v : v' = v := by simpa using hv'
    subst v'
    exact hav r hr b hb (hrz.trans hvb)
  · rw [if_neg hvU, if_neg hvU]

private theorem worldGuardMass_anti_target (w : Sym2 V → unitInterval)
    (U R : Set V) (v : V) {B B' : Set V} (hBB' : B ⊆ B') :
    worldGuardMass w U R v B' ≤ worldGuardMass w U R v B := by
  unfold worldGuardMass
  by_cases hvU : v ∈ U
  · rw [if_pos hvU, if_pos hvU]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    rintro ω ⟨hav, hcon⟩
    exact ⟨sourceAvoid_anti_target
      (Set.inter_subset_inter_left U hBB') hav, hcon⟩
  · rw [if_neg hvU, if_neg hvU]

private theorem worldAvoidMass_anti_target (w : Sym2 V → unitInterval)
    (U : Set V) (v : V) {B B' : Set V} (hBB' : B ⊆ B') :
    worldAvoidMass w U v B' ≤ worldAvoidMass w U v B := by
  unfold worldAvoidMass
  by_cases hvU : v ∈ U
  · rw [if_pos hvU, if_pos hvU]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    exact sourceAvoid_anti_target
      (Set.inter_subset_inter_left U hBB')
  · rw [if_neg hvU, if_neg hvU]

private theorem worldAvoidMass_congr_target (w : Sym2 V → unitInterval)
    (U : Set V) (v : V) {B B' : Set V} (hBB' : B ∩ U = B' ∩ U) :
    worldAvoidMass w U v B = worldAvoidMass w U v B' := by
  unfold worldAvoidMass
  rw [hBB']

private theorem worldGuardMass_congr_target (w : Sym2 V → unitInterval)
    (U R : Set V) (v : V) {B B' : Set V} (hBB' : B ∩ U = B' ∩ U) :
    worldGuardMass w U R v B = worldGuardMass w U R v B' := by
  unfold worldGuardMass
  rw [hBB']

private theorem worldGuardPrice_congr_target (w : Sym2 V → unitInterval)
    (U R : Set V) (v : V) {X X' : Set V} (hXX' : X ∩ U = X' ∩ U) :
    worldGuardPrice w U R v X = worldGuardPrice w U R v X' := by
  unfold worldGuardPrice
  rw [worldGuardMass_congr_target w U R v hXX',
    worldAvoidMass_congr_target w U v hXX']

private theorem guardedWorldX_congr_base (w : Sym2 V → unitInterval)
    (U R : Set V) (x v : V) {X X' N : Set V} (hXX' : X ∩ U = X' ∩ U)
    (h : Set V → ℝ) :
    guardedWorldX w U R x v X N h = guardedWorldX w U R x v X' N h := by
  unfold guardedWorldX
  split_ifs
  · apply setIntegral_congr_fun MeasurableSet.of_discrete
    intro ω _
    apply congrArg₂ (· * ·) _ rfl
    apply worldGuardPrice_congr_target
    let W := U \ sourceCluster ω (N ∩ U)
    show X ∩ W = X' ∩ W
    calc
      X ∩ W = (X ∩ U) ∩ W := by
        ext a
        dsimp only [W]
        simp only [mem_inter_iff, mem_sdiff]
        tauto
      _ = (X' ∩ U) ∩ W := by rw [hXX']
      _ = X' ∩ W := by
        ext a
        dsimp only [W]
        simp only [mem_inter_iff, mem_sdiff]
        tauto
  · rfl

private theorem guardedWorldY_nonneg (w : Sym2 V → unitInterval)
    (U : Finset V) (x : V) (N : Set V) (h : Set V → ℝ)
    (hxU : x ∈ U) (h0 : ∀ W ⊆ (↑U : Set V), 0 ≤ h W) :
    0 ≤ guardedWorldY w (↑U : Set V) x N h := by
  rw [guardedWorldY_eq_Yw w U x N h hxU]
  unfold CovTau.Yw
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg
    (BHK2006.weight_nonneg (fun e => (w e).2.1) (fun e => (w e).2.2) ω)
    (mul_nonneg
      (h0 (↑(CovTau.rest U N ω) : Set V)
        (fun u hu => CovTau.rest_subset U N ω hu))
      (Percolation.Literature.DecisionTree.ind_nonneg _ _))

private theorem guardedWorldX_nonneg (w : Sym2 V → unitInterval)
    (U : Finset V) (R : Set V) (x v : V) (X N : Set V)
    (h : Set V → ℝ) (hxU : x ∈ U) (hvU : v ∈ U)
    (hRU : R ⊆ (↑U : Set V)) (hNU : N ⊆ (↑U : Set V))
    (h0 : ∀ W ⊆ (↑U : Set V), 0 ≤ h W) :
    0 ≤ guardedWorldX w (↑U : Set V) R x v X N h := by
  rw [guardedWorldX_eq_Yw w U R x v X N h hxU hvU hRU hNU]
  unfold CovTau.Yw
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg
  · exact BHK2006.weight_nonneg (fun e => (w e).2.1)
      (fun e => (w e).2.2) ω
  · apply mul_nonneg
    · unfold guardedPure
      split_ifs
      · apply mul_nonneg
        · exact worldGuardPrice_nonneg w _ R v X
        · exact h0 (↑(CovTau.rest U N ω) : Set V)
            (fun u hu => CovTau.rest_subset U N ω hu)
      · exact le_rfl
    · exact Percolation.Literature.DecisionTree.ind_nonneg _ _

private theorem guardedWorldX_empty (w : Sym2 V → unitInterval)
    (U : Finset V) (R : Set V) (x v : V) (X : Set V)
    (h : Set V → ℝ) (hxU : x ∈ U) (hvU : v ∈ U)
    (hRU : R ⊆ (↑U : Set V))
    (hm : ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω = 1) :
    guardedWorldX w (↑U : Set V) R x v X ∅ h =
      worldGuardPrice w (↑U : Set V) R v X * h (↑U : Set V) := by
  rw [guardedWorldX_eq_Yw w U R x v X (∅ : Set V) h hxU hvU hRU
    (Set.empty_subset (↑U : Set V))]
  unfold CovTau.Yw
  have hind : ∀ ω : BondConfig V,
      Percolation.Literature.DecisionTree.ind
        (BHK2006.rD U x (∅ : Set V)) ω = 1 :=
    fun ω => Percolation.Literature.DecisionTree.ind_of_mem fun _ ha => ha.elim
  simp only [CovTau.rest_empty, hind, mul_one]
  rw [← Finset.sum_mul, hm, one_mul, guardedPure, if_pos hRU]

private theorem guarded_two_source_fin (w : Sym2 V → unitInterval)
    (x v : V) (h : Set V → ℝ) :
    ∀ (U : Finset V) (X R N N' : Set V),
    insert x (insert v (X ∪ R ∪ N ∪ N')) ⊆ (↑U : Set V) →
    x ∈ X → v ∉ X → Disjoint R (insert v X) →
    (∀ W ⊆ (↑U : Set V), 0 ≤ h W) →
    (∀ W ⊆ (↑U : Set V), v ∉ W → h W = 0) →
    (∀ (W Q : Set V), W ⊆ (↑U : Set V) → Q ⊆ W →
      guardedWorldY w W x Q h * worldAvoidMass w W v X ≤
        worldAvoidMass w W v (X ∪ Q) * h W) →
    (∀ (W Q Q' : Set V), W ⊆ (↑U : Set V) → Q ⊆ Q' → Q' ⊆ W →
      guardedWorldY w W x Q' h ≤ guardedWorldY w W x Q h) →
    worldGuardMass w (↑U : Set V) R v (X ∪ N) *
        guardedWorldY w (↑U : Set V) x N' h ≤
      worldAvoidMass w (↑U : Set V) v (X ∪ N ∪ N') *
        guardedWorldX w (↑U : Set V) R x v X (N ∩ N') h := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    intro X R N N' hinside hxX hvX hR h0 hv0 hstopped hanti
    let wr : Sym2 V → ℝ := fun e => (w e : ℝ)
    have hw0 : ∀ e, 0 ≤ wr e := fun e => (w e).2.1
    have hw1 : ∀ e, wr e ≤ 1 := fun e => (w e).2.2
    have hm : ∑ ω, BHK2006.weight wr ω = 1 := by
      have h1 := BHK2006.integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
      exact h1.symm
    have hxU : x ∈ U := hinside (by simp)
    have hvU : v ∈ U := hinside (by simp)
    have hXU : X ⊆ (↑U : Set V) := fun a ha => hinside (by simp [ha])
    have hRU : R ⊆ (↑U : Set V) := fun a ha => hinside (by simp [ha])
    have hNU : N ⊆ (↑U : Set V) := fun a ha => hinside (by simp [ha])
    have hN'U : N' ⊆ (↑U : Set V) := fun a ha => hinside (by simp [ha])
    have hNN'U : N ∩ N' ⊆ (↑U : Set V) :=
      (Set.inter_subset_left.trans hNU)
    have hRHS : 0 ≤ worldAvoidMass w (↑U : Set V) v (X ∪ N ∪ N') *
        guardedWorldX w (↑U : Set V) R x v X (N ∩ N') h :=
      mul_nonneg (worldAvoidMass_nonneg w _ v _)
        (guardedWorldX_nonneg w U R x v X (N ∩ N') h hxU hvU hRU
          hNN'U h0)
    set Z : Finset V := U.filter fun u => u ∈ N ∧ u ∈ N' with hZ
    have hZU : Z ⊆ U := Finset.filter_subset _ _
    have hmemZ : ∀ u, u ∈ Z ↔ u ∈ N ∧ u ∈ N' := fun u => by
      simp only [hZ, Finset.mem_filter, and_iff_right_iff_imp]
      exact fun hu => hNU hu.1
    have hZN : (↑Z : Set V) ⊆ N := fun u hu => ((hmemZ u).1 hu).1
    have hZN' : (↑Z : Set V) ⊆ N' := fun u hu => ((hmemZ u).1 hu).2
    have hNN'Z : N ∩ N' = (↑Z : Set V) := Set.ext fun u => by
      rw [Finset.mem_coe, hmemZ]
      rfl
    rcases Z.eq_empty_or_nonempty with hZe | hZne
    · have hNN' : N ∩ N' = ∅ := by rw [hNN'Z, hZe, Finset.coe_empty]
      rw [hNN', guardedWorldX_empty w U R x v X h hxU hvU hRU hm]
      have hst := hstopped (↑U : Set V) N' (Set.Subset.rfl) hN'U
      have hexc := guarded_exchange w (↑U : Set V) X R N N' x v
        (Set.disjoint_iff_inter_eq_empty.2 hNN') hinside
      have hE := worldGuardMass_nonneg w (↑U : Set V) R v (X ∪ N)
      have hM := worldAvoidMass_nonneg w (↑U : Set V) v (X ∪ N ∪ N')
      have hH := h0 (↑U : Set V) Set.Subset.rfl
      have hM0 := worldAvoidMass_nonneg w (↑U : Set V) v X
      have key :
          worldGuardMass w (↑U : Set V) R v (X ∪ N) *
              guardedWorldY w (↑U : Set V) x N' h *
              worldAvoidMass w (↑U : Set V) v X ≤
            worldAvoidMass w (↑U : Set V) v (X ∪ N ∪ N') *
              (worldGuardMass w (↑U : Set V) R v X * h (↑U : Set V)) :=
        calc
          worldGuardMass w (↑U : Set V) R v (X ∪ N) *
                guardedWorldY w (↑U : Set V) x N' h *
                worldAvoidMass w (↑U : Set V) v X =
              worldGuardMass w (↑U : Set V) R v (X ∪ N) *
                (guardedWorldY w (↑U : Set V) x N' h *
                  worldAvoidMass w (↑U : Set V) v X) := by ring
          _ ≤ worldGuardMass w (↑U : Set V) R v (X ∪ N) *
                (worldAvoidMass w (↑U : Set V) v (X ∪ N') * h (↑U : Set V)) :=
            mul_le_mul_of_nonneg_left hst hE
          _ = (worldGuardMass w (↑U : Set V) R v (X ∪ N) *
                worldAvoidMass w (↑U : Set V) v (X ∪ N')) * h (↑U : Set V) := by ring
          _ ≤ (worldAvoidMass w (↑U : Set V) v (X ∪ N ∪ N') *
                worldGuardMass w (↑U : Set V) R v X) * h (↑U : Set V) :=
            mul_le_mul_of_nonneg_right hexc hH
          _ = _ := by ring
      rcases hM0.eq_or_lt with hM0e | hM0p
      · have hE0 : worldGuardMass w (↑U : Set V) R v (X ∪ N) = 0 :=
          le_antisymm
            ((worldGuardMass_le_worldAvoidMass w (↑U : Set V) R (X ∪ N) v).trans
              ((worldAvoidMass_anti_target w (↑U : Set V) v
                (show X ⊆ X ∪ N from Set.subset_union_left)).trans hM0e.symm.le))
            hE
        rw [hE0, zero_mul]
        exact mul_nonneg hM
          (mul_nonneg (worldGuardPrice_nonneg w (↑U : Set V) R v X) hH)
      · unfold worldGuardPrice
        calc
          worldGuardMass w (↑U : Set V) R v (X ∪ N) *
              guardedWorldY w (↑U : Set V) x N' h =
            worldGuardMass w (↑U : Set V) R v (X ∪ N) *
              guardedWorldY w (↑U : Set V) x N' h *
                worldAvoidMass w (↑U : Set V) v X /
                  worldAvoidMass w (↑U : Set V) v X := by field_simp
          _ ≤ worldAvoidMass w (↑U : Set V) v (X ∪ N ∪ N') *
                (worldGuardMass w (↑U : Set V) R v X * h (↑U : Set V)) /
                  worldAvoidMass w (↑U : Set V) v X :=
            div_le_div_of_nonneg_right key hM0p.le
          _ = worldAvoidMass w (↑U : Set V) v (X ∪ N ∪ N') *
                (worldGuardMass w (↑U : Set V) R v X /
                  worldAvoidMass w (↑U : Set V) v X * h (↑U : Set V)) := by
            field_simp
    · by_cases hvZmem : v ∈ Z
      · rw [worldGuardMass_eq_zero_of_target_mem w (↑U : Set V) R (X ∪ N) v
            (Or.inr (hZN hvZmem)), zero_mul]
        exact hRHS
      by_cases hxZmem : x ∈ Z
      · rw [guardedWorldY_eq_zero_of_mem w U x N' h hxU (hZN' hxZmem), mul_zero]
        exact hRHS
      by_cases hRZne : (R ∩ (↑Z : Set V)).Nonempty
      · have hbad : (R ∩ (X ∪ N) ∩ (↑U : Set V)).Nonempty := by
          rcases hRZne with ⟨r, hrR, hrZ⟩
          exact ⟨r, ⟨hrR, Or.inr (hZN hrZ)⟩, hZU hrZ⟩
        rw [worldGuardMass_eq_zero_of_source_inter w (↑U : Set V) R
          (X ∪ N) v hbad, zero_mul]
        exact hRHS
      have hRZ : Disjoint R (↑Z : Set V) := Set.disjoint_left.2 fun r hrR hrZ =>
        hRZne ⟨r, hrR, hrZ⟩
      have hss : U \ Z ⊂ U := Finset.sdiff_ssubset hZU hZne
      have hU'U : (↑(U \ Z) : Set V) ⊆ (↑U : Set V) := fun u hu =>
        (Finset.mem_sdiff.1 hu).1
      have hxUZ : x ∈ U \ Z := Finset.mem_sdiff.2 ⟨hxU, hxZmem⟩
      have hvUZ : v ∈ U \ Z := Finset.mem_sdiff.2 ⟨hvU, hvZmem⟩
      set X₀ : Set V := X ∩ (↑(U \ Z) : Set V) with hX₀
      have hX₀U : X₀ ⊆ (↑(U \ Z) : Set V) := Set.inter_subset_right
      have hxX₀ : x ∈ X₀ := ⟨hxX, hxUZ⟩
      have hvX₀ : v ∉ X₀ := fun hv => hvX hv.1
      have hRX₀ : Disjoint R (insert v X₀) :=
        hR.mono_right (Set.insert_subset_insert Set.inter_subset_left)
      have hRUZ : R ⊆ (↑(U \ Z) : Set V) := by
        intro r hr
        exact Finset.mem_sdiff.2 ⟨hRU hr,
          fun hrZ => Set.disjoint_left.1 hRZ hr hrZ⟩
      have hdiffE : (X ∪ N) \ (↑Z : Set V) = X₀ ∪ (N \ (↑Z : Set V)) := by
        ext a
        simp only [mem_sdiff, mem_union, hX₀, mem_inter_iff,
          Finset.mem_coe, Finset.mem_sdiff]
        constructor
        · rintro ⟨haX | haN, haZ⟩
          · exact Or.inl ⟨haX, hXU haX, haZ⟩
          · exact Or.inr ⟨haN, haZ⟩
        · rintro (⟨haX, -, haZ⟩ | ⟨haN, haZ⟩)
          · exact ⟨Or.inl haX, haZ⟩
          · exact ⟨Or.inr haN, haZ⟩
      have hdiffM : (X ∪ N ∪ N') \ (↑Z : Set V) =
          (X₀ ∪ (N \ (↑Z : Set V))) ∪ (N' \ (↑Z : Set V)) := by
        ext a
        simp only [mem_sdiff, mem_union, hX₀, mem_inter_iff,
          Finset.mem_coe, Finset.mem_sdiff]
        constructor
        · rintro ⟨(haX | haN) | haN', haZ⟩
          · exact Or.inl (Or.inl ⟨haX, hXU haX, haZ⟩)
          · exact Or.inl (Or.inr ⟨haN, haZ⟩)
          · exact Or.inr ⟨haN', haZ⟩
        · rintro ((⟨haX, -, haZ⟩ | ⟨haN, haZ⟩) | ⟨haN', haZ⟩)
          · exact ⟨Or.inl (Or.inl haX), haZ⟩
          · exact ⟨Or.inl (Or.inr haN), haZ⟩
          · exact ⟨Or.inr haN', haZ⟩
      have eE := worldGuardMass_step w hZU hRU
        (Set.union_subset hXU hNU) (hZN.trans Set.subset_union_right) hRZ
        v hvU hvZmem hm
      rw [hdiffE] at eE
      have eY := guardedWorldY_step w hZU hxU hxZmem hN'U hZN' h hm
      have eM := worldAvoidMass_step w hZU
        (Set.union_subset (Set.union_subset hXU hNU) hN'U)
        (fun z hz => Or.inl (Or.inr (hZN hz)))
        v hvU hvZmem hm
      rw [hdiffM] at eM
      have eX : guardedWorldX w (↑U : Set V) R x v X (N ∩ N') h =
          ∑ ω, BHK2006.weight wr ω *
            guardedWorldX w (↑(U \ Z) : Set V) R x v X₀
              (BHK2006.rS U Z ω) h := by
        rw [hNN'Z]
        have hs := guardedWorldX_step w hZU hRU hRZ hxU hvU hxZmem hvZmem
          X (hZU : (↑Z : Set V) ⊆ (↑U : Set V)) (Set.Subset.rfl) h hm
        simp only [Set.sdiff_self, Set.empty_union] at hs
        rw [hs]
        refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
        apply guardedWorldX_congr_base
        simp only [hX₀, Set.inter_assoc, Set.inter_self]
      set e : Set V → ℝ := fun η =>
        worldGuardMass w (↑(U \ Z) : Set V) R v
          ((X₀ ∪ (N \ (↑Z : Set V))) ∪ (η ∩ (↑(U \ Z) : Set V)))
      set y : Set V → ℝ := fun η =>
        guardedWorldY w (↑(U \ Z) : Set V) x
          ((N' \ (↑Z : Set V)) ∪ (η ∩ (↑(U \ Z) : Set V))) h
      set m : Set V → ℝ := fun η =>
        worldAvoidMass w (↑(U \ Z) : Set V) v
          (((X₀ ∪ (N \ (↑Z : Set V))) ∪ (N' \ (↑Z : Set V))) ∪
            (η ∩ (↑(U \ Z) : Set V)))
      set chi : Set V → ℝ := fun η =>
        guardedWorldX w (↑(U \ Z) : Set V) R x v X₀
          (η ∩ (↑(U \ Z) : Set V)) h
      set wp : Set V → ℝ := BHK2006.weight (CovTau.pZ wr U Z) with hwp
      have hrSU : ∀ ω : BondConfig V,
          BHK2006.rS U Z ω ∩ (↑(U \ Z) : Set V) = BHK2006.rS U Z ω :=
        fun ω => Set.inter_eq_left.2 (BHK2006.rS_subset U Z ω)
      have hE' : worldGuardMass w (↑U : Set V) R v (X ∪ N) =
          ∑ η, wp η * e η := by
        rw [eE, ← CovTau.sum_weight_rS hm U Z e]
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [e, hrSU, wr]
      have hY' : guardedWorldY w (↑U : Set V) x N' h =
          ∑ η, wp η * y η := by
        rw [eY, ← CovTau.sum_weight_rS hm U Z y]
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [y, hrSU, wr]
      have hM' : worldAvoidMass w (↑U : Set V) v (X ∪ N ∪ N') =
          ∑ η, wp η * m η := by
        rw [eM, ← CovTau.sum_weight_rS hm U Z m]
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [m, hrSU, wr]
      have hX' : guardedWorldX w (↑U : Set V) R x v X (N ∩ N') h =
          ∑ η, wp η * chi η := by
        rw [eX, ← CovTau.sum_weight_rS hm U Z chi]
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [chi, hrSU, wr]
      have hp0 : ∀ a, 0 ≤ CovTau.pZ wr U Z a := fun a =>
        (CovTau.pZ_mem hw0 hw1 hm U Z a).1
      have hp1 : ∀ a, CovTau.pZ wr U Z a ≤ 1 := fun a =>
        (CovTau.pZ_mem hw0 hw1 hm U Z a).2
      have hwp0 : ∀ η, 0 ≤ wp η := fun η =>
        BHK2006.weight_nonneg hp0 hp1 η
      have he0 : ∀ η, 0 ≤ e η := fun η => worldGuardMass_nonneg w _ R v _
      have hy0 : ∀ η, 0 ≤ y η := fun η =>
        guardedWorldY_nonneg w (U \ Z) x _ h hxUZ
          (fun W hW => h0 W (hW.trans hU'U))
      have hm0 : ∀ η, 0 ≤ m η := fun η => worldAvoidMass_nonneg w _ v _
      have hchi0 : ∀ η, 0 ≤ chi η := fun η =>
        guardedWorldX_nonneg w (U \ Z) R x v X₀ _ h hxUZ hvUZ hRUZ
          Set.inter_subset_right (fun W hW => h0 W (hW.trans hU'U))
      have h0' : ∀ W ⊆ (↑(U \ Z) : Set V), 0 ≤ h W := fun W hW =>
        h0 W (hW.trans hU'U)
      have hv0' : ∀ W ⊆ (↑(U \ Z) : Set V), v ∉ W → h W = 0 :=
        fun W hW => hv0 W (hW.trans hU'U)
      have hstopped' : ∀ (W Q : Set V), W ⊆ (↑(U \ Z) : Set V) → Q ⊆ W →
          guardedWorldY w W x Q h * worldAvoidMass w W v X₀ ≤
            worldAvoidMass w W v (X₀ ∪ Q) * h W := by
        intro W Q hW hQ
        have hs := hstopped W Q (hW.trans hU'U) hQ
        have hXW : X ∩ W = X₀ ∩ W := by
          ext a
          simp only [hX₀, mem_inter_iff]
          constructor
          · intro ha
            exact ⟨⟨ha.1, hW ha.2⟩, ha.2⟩
          · intro ha
            exact ⟨ha.1.1, ha.2⟩
        have hXQW : (X ∪ Q) ∩ W = (X₀ ∪ Q) ∩ W := by
          ext a
          simp only [mem_inter_iff, mem_union]
          constructor
          · rintro ⟨haX | haQ, haW⟩
            · exact ⟨Or.inl ⟨haX, hW haW⟩, haW⟩
            · exact ⟨Or.inr haQ, haW⟩
          · rintro ⟨haX | haQ, haW⟩
            · exact ⟨Or.inl haX.1, haW⟩
            · exact ⟨Or.inr haQ, haW⟩
        rw [worldAvoidMass_congr_target w W v hXW,
          worldAvoidMass_congr_target w W v hXQW] at hs
        exact hs
      have hanti' : ∀ (W Q Q' : Set V), W ⊆ (↑(U \ Z) : Set V) →
          Q ⊆ Q' → Q' ⊆ W →
          guardedWorldY w W x Q' h ≤ guardedWorldY w W x Q h :=
        fun W Q Q' hW => hanti W Q Q' (hW.trans hU'U)
      rw [hE', hY', hM', hX', mul_comm (∑ η, wp η * m η)]
      refine four_functions_theorem_univ
        (fun η => wp η * e η) (fun η => wp η * y η)
        (fun η => wp η * chi η) (fun η => wp η * m η)
        (fun η => mul_nonneg (hwp0 η) (he0 η))
        (fun η => mul_nonneg (hwp0 η) (hy0 η))
        (fun η => mul_nonneg (hwp0 η) (hchi0 η))
        (fun η => mul_nonneg (hwp0 η) (hm0 η)) fun a b => ?_
      set S' : Set V := a ∩ (↑(U \ Z) : Set V)
      set T' : Set V := b ∩ (↑(U \ Z) : Set V)
      set P : Set V := S' ∪ (N \ (↑Z : Set V)) \ T'
      set P' : Set V := T' ∪ (N' \ (↑Z : Set V)) \ S'
      have hPU : P ⊆ (↑(U \ Z) : Set V) := by
        rintro u (hu | ⟨⟨huN, huZ⟩, -⟩)
        · exact hu.2
        · exact Finset.mem_sdiff.2 ⟨hNU huN, huZ⟩
      have hP'U : P' ⊆ (↑(U \ Z) : Set V) := by
        rintro u (hu | ⟨⟨huN, huZ⟩, -⟩)
        · exact hu.2
        · exact Finset.mem_sdiff.2 ⟨hN'U huN, huZ⟩
      have hinside' : insert x (insert v (X₀ ∪ R ∪ P ∪ P')) ⊆
          (↑(U \ Z) : Set V) := by
        intro u hu
        rcases hu with rfl | rfl | (((hu | hu) | hu) | hu)
        · exact hxUZ
        · exact hvUZ
        · exact hX₀U hu
        · exact hRUZ hu
        · exact hPU hu
        · exact hP'U hu
      have hIH := ih (U \ Z) hss X₀ R P P' hinside' hxX₀ hvX₀ hRX₀
        h0' hv0' hstopped' hanti'
      have hkeyZ : ∀ u, u ∈ N → u ∈ N' → u ∈ (↑Z : Set V) :=
        fun u h1 h2 => (hmemZ u).2 ⟨h1, h2⟩
      have h1 : e a ≤ worldGuardMass w (↑(U \ Z) : Set V) R v (X₀ ∪ P) := by
        dsimp only [e]
        apply worldGuardMass_anti_target
        rintro u (hu | hu)
        · exact Or.inl (Or.inl hu)
        · rcases hu with hu | ⟨huN, -⟩
          · exact Or.inr hu
          · exact Or.inl (Or.inr huN)
      have h2 : y b ≤ guardedWorldY w (↑(U \ Z) : Set V) x P' h :=
        hanti' (↑(U \ Z) : Set V) P'
          ((N' \ (↑Z : Set V)) ∪ T') Set.Subset.rfl
          (by rintro u (hu | ⟨hu, -⟩); exacts [Or.inr hu, Or.inl hu])
          (by
            rintro u (⟨huN, huZ⟩ | hu)
            · exact Finset.mem_sdiff.2 ⟨hN'U huN, huZ⟩
            · exact hu.2)
      have hunion : P ∪ P' =
          ((N \ (↑Z : Set V)) ∪ (N' \ (↑Z : Set V))) ∪
            ((a ∪ b) ∩ (↑(U \ Z) : Set V)) := by
        ext u
        constructor
        · rintro ((hS | ⟨hA, -⟩) | (hT | ⟨hA', -⟩))
          · exact Or.inr ⟨Or.inl hS.1, hS.2⟩
          · exact Or.inl (Or.inl hA)
          · exact Or.inr ⟨Or.inr hT.1, hT.2⟩
          · exact Or.inl (Or.inr hA')
        · rintro ((hN | hN') | ⟨ha | hb, hU⟩)
          · by_cases hT : u ∈ T'
            · exact Or.inr (Or.inl hT)
            · exact Or.inl (Or.inr ⟨hN, hT⟩)
          · by_cases hS : u ∈ S'
            · exact Or.inl (Or.inl hS)
            · exact Or.inr (Or.inr ⟨hN', hS⟩)
          · exact Or.inl (Or.inl ⟨ha, hU⟩)
          · exact Or.inr (Or.inl ⟨hb, hU⟩)
      have hinter : P ∩ P' = (a ∩ b) ∩ (↑(U \ Z) : Set V) := by
        ext u
        constructor
        · rintro ⟨hS | ⟨⟨hN, hZ'⟩, hT⟩,
              hT' | ⟨⟨hN', -⟩, hS'⟩⟩
          · exact ⟨⟨hS.1, hT'.1⟩, hS.2⟩
          · exact absurd hS hS'
          · exact absurd hT' hT
          · exact absurd (hkeyZ u hN hN') hZ'
        · rintro ⟨⟨ha, hb⟩, hU⟩
          exact ⟨Or.inl ⟨ha, hU⟩, Or.inl ⟨hb, hU⟩⟩
      have h3 : e a * y b ≤ m (a ∪ b) * chi (a ∩ b) :=
        calc
          e a * y b ≤
              worldGuardMass w (↑(U \ Z) : Set V) R v (X₀ ∪ P) *
                guardedWorldY w (↑(U \ Z) : Set V) x P' h :=
            mul_le_mul h1 h2 (hy0 b)
              (worldGuardMass_nonneg w _ R v _)
          _ ≤ worldAvoidMass w (↑(U \ Z) : Set V) v (X₀ ∪ P ∪ P') *
                guardedWorldX w (↑(U \ Z) : Set V) R x v X₀ (P ∩ P') h := hIH
          _ = m (a ∪ b) * chi (a ∩ b) := by
            have hmassset : X₀ ∪ P ∪ P' =
                ((X₀ ∪ (N \ (↑Z : Set V))) ∪ (N' \ (↑Z : Set V))) ∪
                  ((a ∪ b) ∩ (↑(U \ Z) : Set V)) := by
              calc
                X₀ ∪ P ∪ P' = X₀ ∪ (P ∪ P') := Set.union_assoc _ _ _
                _ = X₀ ∪ (((N \ (↑Z : Set V)) ∪ (N' \ (↑Z : Set V))) ∪
                    ((a ∪ b) ∩ (↑(U \ Z) : Set V))) :=
                  congrArg (fun T : Set V => X₀ ∪ T) hunion
                _ = _ := by ac_rfl
            dsimp only [m, chi]
            rw [hmassset, hinter]
      have hwab := BHK2006.weight_inter_mul_union (CovTau.pZ wr U Z) a b
      show wp a * e a * (wp b * y b) ≤
        wp (a ∩ b) * chi (a ∩ b) * (wp (a ∪ b) * m (a ∪ b))
      calc
        wp a * e a * (wp b * y b) = (wp a * wp b) * (e a * y b) := by ring
        _ ≤ (wp (a ∩ b) * wp (a ∪ b)) *
              (m (a ∪ b) * chi (a ∩ b)) := by
          rw [hwp, hwab]
          exact mul_le_mul_of_nonneg_left h3
            (mul_nonneg (hwp0 _) (hwp0 _))
        _ = _ := by ring

theorem guarded_two_source (w : Sym2 V → unitInterval) (U X R N N' : Set V)
    (x v : V) (h : Set V → ℝ)
    (hinside : insert x (insert v (X ∪ R ∪ N ∪ N')) ⊆ U)
    (hxX : x ∈ X) (hvX : v ∉ X) (hR : Disjoint R (insert v X))
    (h0 : ∀ W ⊆ U, 0 ≤ h W)
    (hv0 : ∀ W ⊆ U, v ∉ W → h W = 0)
    (hstopped : ∀ (W Q : Set V), W ⊆ U → Q ⊆ W →
      guardedWorldY w W x Q h * worldAvoidMass w W v X ≤
        worldAvoidMass w W v (X ∪ Q) * h W)
    (hanti : ∀ (W Q Q' : Set V), W ⊆ U → Q ⊆ Q' → Q' ⊆ W →
      guardedWorldY w W x Q' h ≤ guardedWorldY w W x Q h) :
    worldGuardMass w U R v (X ∪ N) * guardedWorldY w U x N' h ≤
      worldAvoidMass w U v (X ∪ N ∪ N') *
        guardedWorldX w U R x v X (N ∩ N') h := by
  let Uf : Finset V := Finset.univ.filter fun u => u ∈ U
  have hUf : (↑Uf : Set V) = U := by
    ext u
    simp only [Uf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hUf] at hinside h0 hv0 hstopped hanti ⊢
  exact guarded_two_source_fin w x v h Uf X R N N' hinside hxX hvX hR
    h0 hv0 hstopped hanti

private theorem sourceConn_isUpperSet (R X : Set V) :
    IsUpperSet (sourceConn R X) := by
  intro ω ω' hω hconn
  rcases hconn with ⟨r, hr, x, hx, hrx⟩
  exact ⟨r, hr, x, hx, hrx.mono (openGraph_mono hω)⟩

private theorem sourceAvoid_eq_compl_sourceConn (R X : Set V) :
    sourceAvoid R X = (sourceConn R X)ᶜ := by
  ext ω
  simp only [sourceAvoid, sourceConn, mem_setOf_eq, mem_compl_iff]
  push Not
  rfl

private theorem sourceWorldCov_sub_const (w : Sym2 V → unitInterval)
    (U : Set V) (x : V) (g : Set (Sym2 V) → ℝ) (c : ℝ)
    (R X : Set V) :
    sourceWorldCov w U x (fun C => g C - c) R X =
      sourceWorldCov w U x g R X := by
  unfold sourceWorldCov
  by_cases hxU : x ∈ U
  · rw [if_pos hxU, if_pos hxU]
    rw [integral_sub Integrable.of_finite Integrable.of_finite,
      integral_sub Integrable.of_finite Integrable.of_finite]
    simp only [integral_const, measureReal_restrict_apply_univ,
      probReal_univ, smul_eq_mul, one_mul]
    unfold worldProb
    ring
  · rw [if_neg hxU, if_neg hxU]

private def sourceAvoidClusterInd (R X : Set V) (C : Set (Sym2 V)) : ℝ :=
  if ∀ r ∈ R, ¬ (r ∈ X ∨ ∃ e ∈ C, r ∈ e) then 1 else 0

private def sourceContactClusterInd (R : Set V) (v : V)
    (C : Set (Sym2 V)) : ℝ :=
  if ∃ r ∈ R, r = v ∨ ∃ e ∈ C, r ∈ e then 1 else 0

private theorem sourceAvoidClusterInd_setCl (R X : Set V)
    (ω : BondConfig V) :
    sourceAvoidClusterInd R X (BHK2006.setCl ω X) =
      Percolation.Literature.DecisionTree.ind (sourceAvoid R X) ω := by
  have hp : (∀ r ∈ R, ¬ (r ∈ X ∨
      ∃ e ∈ BHK2006.setCl ω X, r ∈ e)) ↔ ω ∈ sourceAvoid R X := by
    constructor
    · intro hp r hr x hx hrx
      exact hp r hr ((BHK2006.setReach_iff ω X r).1
        ⟨x, hx, hrx.symm⟩)
    · intro hav r hr hreach
      rcases (BHK2006.setReach_iff ω X r).2 hreach with ⟨x, hx, hxr⟩
      exact hav r hr x hx hxr.symm
  unfold sourceAvoidClusterInd
  by_cases hav : ω ∈ sourceAvoid R X
  · rw [if_pos (hp.2 hav),
      Percolation.Literature.DecisionTree.ind_of_mem hav]
  · rw [if_neg (fun h => hav (hp.1 h)),
      Percolation.Literature.DecisionTree.ind_of_not_mem hav]

private theorem sourceContactClusterInd_openCluster (R : Set V) (v : V)
    (ω : BondConfig V) :
    sourceContactClusterInd R v (openEdgeCluster ω v) =
      Percolation.Literature.DecisionTree.ind
        (sourceConn R ({v} : Set V)) ω := by
  have hp : (∃ r ∈ R, r = v ∨ ∃ e ∈ openEdgeCluster ω v, r ∈ e) ↔
      ω ∈ sourceConn R ({v} : Set V) := by
    constructor
    · rintro ⟨r, hr, hrv | ⟨e, he, hre⟩⟩
      · exact ⟨r, hr, v, by simp, hrv.symm ▸ SimpleGraph.Reachable.refl v⟩
      · exact ⟨r, hr, v, by simp,
          ((reachable_iff_exists_mem_openEdgeCluster ω v r).2
            (Or.inr ⟨e, he, hre⟩)).symm⟩
    · rintro ⟨r, hr, z, hz, hrz⟩
      have hzv : z = v := by simpa using hz
      subst z
      exact ⟨r, hr, (reachable_iff_exists_mem_openEdgeCluster ω v r).1 hrz.symm⟩
  unfold sourceContactClusterInd
  by_cases hcon : ω ∈ sourceConn R ({v} : Set V)
  · rw [if_pos (hp.2 hcon),
      Percolation.Literature.DecisionTree.ind_of_mem hcon]
  · rw [if_neg (fun h => hcon (hp.1 h)),
      Percolation.Literature.DecisionTree.ind_of_not_mem hcon]

private theorem sourceAvoidClusterInd_antitone (R X : Set V) :
    Antitone (sourceAvoidClusterInd R X) := by
  intro C C' hCC'
  unfold sourceAvoidClusterInd
  by_cases hC' : ∀ r ∈ R, ¬ (r ∈ X ∨ ∃ e ∈ C', r ∈ e)
  · have hC : ∀ r ∈ R, ¬ (r ∈ X ∨ ∃ e ∈ C, r ∈ e) := by
      intro r hr
      rintro (hrX | ⟨e, he, hre⟩)
      · exact hC' r hr (Or.inl hrX)
      · exact hC' r hr (Or.inr ⟨e, hCC' he, hre⟩)
    rw [if_pos hC', if_pos hC]
  · rw [if_neg hC']
    split_ifs <;> norm_num

private theorem sourceContactClusterInd_monotone (R : Set V) (v : V) :
    Monotone (sourceContactClusterInd R v) := by
  intro C C' hCC'
  unfold sourceContactClusterInd
  by_cases hC : ∃ r ∈ R, r = v ∨ ∃ e ∈ C, r ∈ e
  · have hC' : ∃ r ∈ R, r = v ∨ ∃ e ∈ C', r ∈ e := by
      rcases hC with ⟨r, hr, hrv | ⟨e, he, hre⟩⟩
      · exact ⟨r, hr, Or.inl hrv⟩
      · exact ⟨r, hr, Or.inr ⟨e, hCC' he, hre⟩⟩
    rw [if_pos hC, if_pos hC']
  · rw [if_neg hC]
    split_ifs <;> norm_num

private theorem sourceAvoidClusterInd_nonneg (R X : Set V) (C : Set (Sym2 V)) :
    0 ≤ sourceAvoidClusterInd R X C := by
  unfold sourceAvoidClusterInd
  split_ifs <;> norm_num

private theorem sourceContactClusterInd_nonneg (R : Set V) (v : V)
    (C : Set (Sym2 V)) : 0 ≤ sourceContactClusterInd R v C := by
  unfold sourceContactClusterInd
  split_ifs <;> norm_num

private theorem sourceWorldCov_nonneg (w : Sym2 V → unitInterval)
    (U : Set V) (x : V) (g : Set (Sym2 V) → ℝ) (R X : Set V)
    (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) :
    0 ≤ sourceWorldCov w U x g R X := by
  unfold sourceWorldCov
  by_cases hxU : x ∈ U
  · rw [if_pos hxU]
    have hh := CSH.setIntegral_edgeFun_ge (inducedWeight w U) x g hg hg0
      (sourceConn (R ∩ U) (X ∩ U)) (sourceConn_isUpperSet _ _)
    unfold worldProb
    linarith [hh]
  · rw [if_neg hxU]

private theorem sourceWorldCov_guardPrice_le_of_nonneg
    (w : Sym2 V → unitInterval) (U X R : Set V) (x v : V)
    (g : Set (Sym2 V) → ℝ) (hxX : x ∈ X) (_hvX : v ∉ X)
    (_hR : Disjoint R (insert v X)) (hg : Monotone g)
    (hg0 : ∀ C, 0 ≤ g C) :
    worldGuardPrice w U R v X *
        sourceWorldCov w U x g ({v} : Set V) X ≤
      sourceWorldCov w U x g R X := by
  classical
  by_cases hxU : x ∈ U
  swap
  · simp only [sourceWorldCov, if_neg hxU, mul_zero]
    exact le_rfl
  by_cases hvU : v ∈ U
  swap
  · have hp0 : worldGuardPrice w U R v X = 0 := by
      unfold worldGuardPrice worldGuardMass worldAvoidMass
      rw [if_neg hvU, if_neg hvU, zero_div]
    rw [hp0, zero_mul]
    exact sourceWorldCov_nonneg w U x g R X hg hg0
  set p : Sym2 V → unitInterval := inducedWeight w U with hp
  set μ : Measure (BondConfig V) := prodBernoulli p with hμ
  set R₀ : Set V := R ∩ U with hR₀
  set X₀ : Set V := X ∩ U with hX₀
  set f : BondConfig V → ℝ := fun ω => g (openEdgeCluster ω x) with hf
  set m₀ : ℝ := ∫ ω, f ω ∂μ with hm₀
  set A : Set (BondConfig V) := sourceConn R₀ X₀ with hA
  set B : Set (BondConfig V) := sourceConn R₀ ({v} : Set V) with hB
  set D : Set (BondConfig V) := sourceAvoid ({v} : Set V) X₀ with hD
  set J : Set (BondConfig V) := guardEv R₀ ({v} : Set V) X₀ with hJ
  set Q : Set (BondConfig V) := sourceConn ({v} : Set V) X₀ with hQ
  have hxX₀ : x ∈ X₀ := ⟨hxX, hxU⟩
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T :=
    fun _ => MeasurableSet.of_discrete
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)),
      IntegrableOn k T μ := fun _ _ => (Integrable.of_finite).integrableOn
  have hn := fun (T : Set (BondConfig V)) =>
    (measureReal_nonneg : 0 ≤ μ.real T)
  have hHarris : μ.real (A ∪ B) * m₀ ≤ ∫ ω in A ∪ B, f ω ∂μ := by
    simpa only [hf, hm₀, hμ] using
      CSH.setIntegral_edgeFun_ge p x g hg hg0 (A ∪ B)
        ((sourceConn_isUpperSet _ _).union (sourceConn_isUpperSet _ _))
  have hDset :
      {ω : BondConfig V | ∀ s ∈ X₀, ∀ t ∈ ({v} : Set V),
        ¬(openGraph ω).Reachable s t} = D := by
    ext ω
    simp only [hD, sourceAvoid, mem_setOf_eq, mem_singleton_iff, forall_eq]
    constructor
    · intro hav z hz hvz
      exact hav z hz hvz.symm
    · intro hav z hz hzv
      exact hav z hz hzv.symm
  let F : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun C _ =>
    g (openEdgeCluster C x)
  let G : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun C E =>
    -(sourceAvoidClusterInd R₀ X₀ C * sourceContactClusterInd R₀ v E)
  have hF1 : ∀ E, Monotone fun C => F C E := fun _ C C' hCC' =>
    hg (BHK2006.openEdgeCluster_mono hCC' x)
  have hF2 : ∀ C, Antitone fun E => F C E := fun _ => antitone_const
  have hG1 : ∀ E, Monotone fun C => G C E := by
    intro E C C' hCC'
    dsimp only [G]
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_right
      (sourceAvoidClusterInd_antitone R₀ X₀ hCC')
      (sourceContactClusterInd_nonneg R₀ v E)
  have hG2 : ∀ C, Antitone fun E => G C E := by
    intro C E E' hEE'
    dsimp only [G]
    apply neg_le_neg
    exact mul_le_mul_of_nonneg_left
      (sourceContactClusterInd_monotone R₀ v hEE')
      (sourceAvoidClusterInd_nonneg R₀ X₀ C)
  have hFval : ∀ ω : BondConfig V,
      F (⋃ s ∈ X₀, openEdgeCluster ω s)
          (⋃ t ∈ ({v} : Set V), openEdgeCluster ω t) = f ω := by
    intro ω
    dsimp only [F, f]
    rw [CovTauStarN.openEdgeCluster_biUnion_eq hxX₀]
  have hGval : ∀ ω : BondConfig V,
      sourceAvoidClusterInd R₀ X₀ (⋃ s ∈ X₀, openEdgeCluster ω s) *
          sourceContactClusterInd R₀ v
            (⋃ t ∈ ({v} : Set V), openEdgeCluster ω t) =
        Percolation.Literature.DecisionTree.ind J ω := by
    intro ω
    simp only [Set.biUnion_singleton]
    have hset : (⋃ s ∈ X₀, openEdgeCluster ω s) = BHK2006.setCl ω X₀ := rfl
    rw [hset, sourceAvoidClusterInd_setCl,
      sourceContactClusterInd_openCluster, ← BHK2006.ind_inter]
    rfl
  have hBHK := BHK2006_twoSetConditionalAssociation p X₀ ({v} : Set V)
    F G hF1 hF2 hG1 hG2
  rw [hDset] at hBHK
  simp_rw [hFval] at hBHK
  change
    (∫ ω in D, f ω ∂μ) *
        (∫ ω in D, -(sourceAvoidClusterInd R₀ X₀
          (⋃ s ∈ X₀, openEdgeCluster ω s) *
          sourceContactClusterInd R₀ v
            (⋃ t ∈ ({v} : Set V), openEdgeCluster ω t)) ∂μ) ≤
      μ.real D *
        ∫ ω in D, f ω *
          (-(sourceAvoidClusterInd R₀ X₀
            (⋃ s ∈ X₀, openEdgeCluster ω s) *
            sourceContactClusterInd R₀ v
              (⋃ t ∈ ({v} : Set V), openEdgeCluster ω t))) ∂μ at hBHK
  simp_rw [hGval] at hBHK
  have hDJ : D ∩ J = J := by
    apply Set.inter_eq_right.2
    rintro ω ⟨hav, r, hr, z, hz, hrz⟩
    have hzv : z = v := by simpa using hz
    subst z
    intro v' hv' a ha hva
    have hv'v : v' = v := by simpa using hv'
    subst v'
    exact hav r hr a ha (hrz.trans hva)
  have hprod : ∀ (T : Set (BondConfig V)) (k : BondConfig V → ℝ),
      (∫ ω in D, k ω *
          Percolation.Literature.DecisionTree.ind T ω ∂μ) =
        ∫ ω in D ∩ T, k ω ∂μ := by
    intro T k
    rw [← KNPreFKG.setIntegral_mul_indicator_one μ D T k]
    refine setIntegral_congr_fun (hmeas D) fun ω _ => ?_
    rw [congrFun (CovTau.ind_eq_indicator_one T) ω]
  have hindJ : (∫ ω in D,
      Percolation.Literature.DecisionTree.ind J ω ∂μ) = μ.real J := by
    have hs := hprod J (fun _ => (1 : ℝ))
    simp only [one_mul, integral_const, measureReal_restrict_apply_univ,
      hDJ, smul_eq_mul, mul_one] at hs
    exact hs
  have hfindJ : (∫ ω in D, f ω *
      Percolation.Literature.DecisionTree.ind J ω ∂μ) =
      ∫ ω in J, f ω ∂μ := by
    rw [hprod, hDJ]
  have hneg1 : (∫ ω in D,
      -Percolation.Literature.DecisionTree.ind J ω ∂μ) =
      -(∫ ω in D, Percolation.Literature.DecisionTree.ind J ω ∂μ) := by
    rw [integral_neg]
  have hneg2 : (∫ ω in D, f ω *
      (-Percolation.Literature.DecisionTree.ind J ω) ∂μ) =
      -(∫ ω in D, f ω *
        Percolation.Literature.DecisionTree.ind J ω ∂μ) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun (hmeas D) fun ω _ => by ring
  rw [hneg1, hneg2, hindJ, hfindJ] at hBHK
  have hBHK' : μ.real D * (∫ ω in J, f ω ∂μ) ≤
      μ.real J * (∫ ω in D, f ω ∂μ) := by
    linarith [hBHK]
  have hUdiff : (A ∪ B) \ A = J := by
    ext ω
    simp only [hA, hB, hJ, guardEv, mem_sdiff, mem_union, mem_inter_iff]
    constructor
    · rintro ⟨ha | hb, hna⟩
      · exact absurd ha hna
      · refine ⟨?_, hb⟩
        intro r hr a ha hra
        exact hna ⟨r, hr, a, ha, hra⟩
    · rintro ⟨hav, hb⟩
      exact ⟨Or.inr hb, fun ⟨r, hr, a, ha, hra⟩ => hav r hr a ha hra⟩
  have hUint : (∫ ω in A ∪ B, f ω ∂μ) =
      (∫ ω in A, f ω ∂μ) + ∫ ω in J, f ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas A) (hint f (A ∪ B)),
      Set.inter_eq_right.2 Set.subset_union_left, hUdiff]
  have hUμ : μ.real (A ∪ B) = μ.real A + μ.real J := by
    rw [← measureReal_inter_add_sdiff (s := A ∪ B)
      (h := measure_ne_top _ _) (hmeas A),
      Set.inter_eq_right.2 Set.subset_union_left, hUdiff]
  have hAineq : μ.real J * m₀ - (∫ ω in J, f ω ∂μ) ≤
      (∫ ω in A, f ω ∂μ) - μ.real A * m₀ := by
    rw [hUint, hUμ] at hHarris
    linarith
  have hDQ : D = Qᶜ := by
    simp only [hD, hQ]
    exact sourceAvoid_eq_compl_sourceConn ({v} : Set V) X₀
  have hDint : (∫ ω in D, f ω ∂μ) =
      m₀ - ∫ ω in Q, f ω ∂μ := by
    have hs := integral_add_compl (hmeas Q) (Integrable.of_finite (f := f) (μ := μ))
    rw [← hDQ] at hs
    rw [hm₀]
    linarith
  have hDμ : μ.real D = 1 - μ.real Q := by
    have hs : μ.real (Set.univ : Set (BondConfig V)) =
        μ.real (Set.univ ∩ Q) + μ.real (Set.univ \ Q) :=
      (measureReal_inter_add_sdiff (s := Set.univ)
        (h := measure_ne_top _ _) (hmeas Q)).symm
    rw [probReal_univ, Set.univ_inter, ← compl_eq_univ_sdiff, ← hDQ] at hs
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hAineq (hn D)
  have hkey : μ.real J *
      ((∫ ω in Q, f ω ∂μ) - m₀ * μ.real Q) ≤
      μ.real D * ((∫ ω in A, f ω ∂μ) - m₀ * μ.real A) := by
    rw [hDint, hDμ] at hBHK'
    rw [hDμ] at hscaled
    rw [hDμ]
    nlinarith [hBHK', hscaled, hn J, hn Q]
  have hprice : worldGuardPrice w U R v X = μ.real J / μ.real D := by
    unfold worldGuardPrice worldGuardMass worldAvoidMass worldProb
    rw [if_pos hvU, if_pos hvU]
  have hcovv : sourceWorldCov w U x g ({v} : Set V) X =
      (∫ ω in Q, f ω ∂μ) - m₀ * μ.real Q := by
    unfold sourceWorldCov worldProb
    rw [if_pos hxU]
    have hvinter : ({v} : Set V) ∩ U = ({v} : Set V) := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · intro hz
        subst z
        exact ⟨rfl, hvU⟩
    rw [hvinter]
  have hcovR : sourceWorldCov w U x g R X =
      (∫ ω in A, f ω ∂μ) - m₀ * μ.real A := by
    unfold sourceWorldCov worldProb
    rw [if_pos hxU]
  rw [hprice, hcovv, hcovR]
  rcases (hn D).eq_or_lt with hD0 | hDp
  · rw [← hD0, div_zero, zero_mul]
    simpa only [hcovR] using sourceWorldCov_nonneg w U x g R X hg hg0
  · calc
      μ.real J / μ.real D *
          ((∫ ω in Q, f ω ∂μ) - m₀ * μ.real Q) =
        (μ.real J * ((∫ ω in Q, f ω ∂μ) - m₀ * μ.real Q)) /
          μ.real D := by ring
      _ ≤ (μ.real D * ((∫ ω in A, f ω ∂μ) - m₀ * μ.real A)) /
          μ.real D := div_le_div_of_nonneg_right hkey hDp.le
      _ = (∫ ω in A, f ω ∂μ) - m₀ * μ.real A := by field_simp

theorem sourceWorldCov_guardPrice_le (w : Sym2 V → unitInterval) (U X R : Set V)
    (x v : V) (g : Set (Sym2 V) → ℝ) (hxX : x ∈ X) (hvX : v ∉ X)
    (hR : Disjoint R (insert v X)) (hg : Monotone g) :
    worldGuardPrice w U R v X *
        sourceWorldCov w U x g ({v} : Set V) X ≤
      sourceWorldCov w U x g R X := by
  let g₀ : Set (Sym2 V) → ℝ := fun C => g C - g ∅
  have hg₀ : Monotone g₀ := fun C C' hCC' => sub_le_sub_right (hg hCC') _
  have hg₀0 : ∀ C, 0 ≤ g₀ C := fun C =>
    sub_nonneg.2 (hg (Set.empty_subset C))
  have key := sourceWorldCov_guardPrice_le_of_nonneg w U X R x v g₀
    hxX hvX hR hg₀ hg₀0
  rw [sourceWorldCov_sub_const w U x g (g ∅) ({v} : Set V) X,
    sourceWorldCov_sub_const w U x g (g ∅) R X] at key
  exact key

private theorem restricted_singleton_conn_iff (U : Finset V)
    (X : Set V) (v : V) (hvX : v ∉ X) (ω : BondConfig V) :
    ω ∩ BHK2006.edgesIn U ∈
        sourceConn (({v} : Set V) ∩ (↑U : Set V)) (X ∩ (↑U : Set V)) ↔
      ∃ s ∈ X,
        (openGraph (ω ∩ BHK2006.edgesIn U)).Reachable s v := by
  constructor
  · rintro ⟨z, ⟨hzv, -⟩, s, ⟨hsX, -⟩, hzs⟩
    have hzv' : z = v := by simpa using hzv
    subst z
    exact ⟨s, hsX, hzs.symm⟩
  · rintro ⟨s, hsX, hsv⟩
    have hsvne : s ≠ v := fun h => hvX (h ▸ hsX)
    have hvU : v ∈ U :=
      SandwichBHK.mem_of_reachable hsv hsvne
    have hsU : s ∈ U :=
      SandwichBHK.mem_of_reachable hsv.symm (Ne.symm hsvne)
    exact ⟨v, ⟨by simp, hvU⟩, s, ⟨hsX, hsU⟩, hsv.symm⟩

private theorem sourceWorldCov_coe_eq_BfS (w : Sym2 V → unitInterval)
    (U : Finset V) (x : V) (X : Set V) (v : V)
    (g : Set (Sym2 V) → ℝ) (hxU : x ∈ U) (hvX : v ∉ X) :
    sourceWorldCov w (↑U : Set V) x g ({v} : Set V) X =
      CovTau.BfS (fun e => (w e : ℝ)) U x X v g := by
  let C : Set (BondConfig V) :=
    {ω | ∃ s ∈ X,
      (openGraph (ω ∩ BHK2006.edgesIn U)).Reachable s v}
  have hconn : ∀ ω : BondConfig V,
      ω ∩ BHK2006.edgesIn U ∈
          sourceConn (({v} : Set V) ∩ (↑U : Set V)) (X ∩ (↑U : Set V)) ↔
        ω ∈ C := fun ω => restricted_singleton_conn_iff U X v hvX ω
  unfold sourceWorldCov CovTau.BfS CovTau.tfE CovTau.cfS
  rw [if_pos (show x ∈ (↑U : Set V) from hxU),
    setIntegral_induced_coe_eq_sum, integral_induced_coe_eq_sum,
    worldProb_coe_eq_sum]
  have hfirst :
      (∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        (g (openEdgeCluster (ω ∩ BHK2006.edgesIn U) x) *
          Percolation.Literature.DecisionTree.ind
            (sourceConn (({v} : Set V) ∩ (↑U : Set V))
              (X ∩ (↑U : Set V)))
            (ω ∩ BHK2006.edgesIn U))) =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        (g (BHK2006.rC U x ω) *
          Percolation.Literature.DecisionTree.ind C ω) := by
    refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
    rw [show openEdgeCluster (ω ∩ BHK2006.edgesIn U) x =
      BHK2006.rC U x ω from rfl]
    congr 1
    apply BystanderBHK.ind_congr
    exact hconn ω
  rw [hfirst]
  have hplain :
      (∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        g (openEdgeCluster (ω ∩ BHK2006.edgesIn U) x)) =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        g (BHK2006.rC U x ω) := by rfl
  have hprob :
      (∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        Percolation.Literature.DecisionTree.ind
          (sourceConn (({v} : Set V) ∩ (↑U : Set V))
            (X ∩ (↑U : Set V)))
          (ω ∩ BHK2006.edgesIn U)) =
      ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω *
        Percolation.Literature.DecisionTree.ind C ω := by
    refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
    apply BystanderBHK.ind_congr
    exact hconn ω
  rw [hplain, hprob]

private theorem sourceWorldCov_singleton_eq_zero_of_not_mem
    (w : Sym2 V → unitInterval) (W : Set V) (x v : V) (X : Set V)
    (g : Set (Sym2 V) → ℝ) (hvW : v ∉ W) :
    sourceWorldCov w W x g ({v} : Set V) X = 0 := by
  unfold sourceWorldCov
  by_cases hxW : x ∈ W
  · rw [if_pos hxW]
    have hvinter : ({v} : Set V) ∩ W = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false,
        iff_false]
      rintro ⟨rfl, hvW'⟩
      exact hvW hvW'
    rw [hvinter]
    have hconn : sourceConn ∅ (X ∩ W) = ∅ := by
      ext ω
      simp [sourceConn]
    rw [hconn]
    simp only [Measure.restrict_empty, integral_zero_measure, worldProb,
      measureReal_empty, mul_zero, sub_zero]
  · rw [if_neg hxW]

private theorem guardedWorldY_sourceCov_eq_Yw_BfS
    (w : Sym2 V → unitInterval) (U : Finset V) (x : V) (X : Set V)
    (v : V) (g : Set (Sym2 V) → ℝ) (N : Set V)
    (hxU : x ∈ U) (hvX : v ∉ X) :
    guardedWorldY w (↑U : Set V) x N
        (fun W => sourceWorldCov w W x g ({v} : Set V) X) =
      CovTau.Yw (fun e => (w e : ℝ)) U x
        (fun U' => CovTau.BfS (fun e => (w e : ℝ)) U' x X v g) N := by
  rw [guardedWorldY_eq_Yw w U x N
    (fun W => sourceWorldCov w W x g ({v} : Set V) X) hxU]
  unfold CovTau.Yw
  refine Finset.sum_congr rfl fun ω _ => congrArg _ ?_
  by_cases hav : ω ∈ BHK2006.rD U x N
  · rw [Percolation.Literature.DecisionTree.ind_of_mem hav]
    have hxrest : x ∈ CovTau.rest U N ω := by
      rw [CovTau.mem_rest]
      exact ⟨hxU, (CovTau.not_mem_sC_iff U N ω x).2 hav⟩
    dsimp only
    rw [sourceWorldCov_coe_eq_BfS w (CovTau.rest U N ω)
      x X v g hxrest hvX]
  · rw [Percolation.Literature.DecisionTree.ind_of_not_mem hav,
      mul_zero, mul_zero]

private theorem guardHorizontal_sub_const (w : Sym2 V → unitInterval)
    (x : V) (Y X O : Set V) (v : V) (g : Set (Sym2 V) → ℝ) (c : ℝ) :
    guardHorizontal w x Y X O v (fun C => g C - c) =
      guardHorizontal w x Y X O v g := by
  unfold guardHorizontal
  simp_rw [sourceWorldCov_sub_const w]

private theorem inducedWeight_univ (w : Sym2 V → unitInterval) :
    inducedWeight w (Set.univ : Set V) = w := by
  funext e
  simp [inducedWeight]

private theorem worldGuardPrice_univ_eq_guardObsConst
    (w : Sym2 V → unitInterval) (O : Set V) (v : V) (A : Set V) :
    worldGuardPrice w Set.univ O v A = guardObsConst w O v A := by
  unfold worldGuardPrice worldGuardMass worldAvoidMass worldProb guardObsConst
  simp only [mem_univ, if_true, inter_univ, inducedWeight_univ]

private theorem guardedWorldY_univ_eq (w : Sym2 V → unitInterval)
    (x : V) (N : Set V) (h : Set V → ℝ) :
    guardedWorldY w Set.univ x N h =
      ∫ ω in sourceAvoid ({x} : Set V) N,
        h (Set.univ \ sourceCluster ω N) ∂(prodBernoulli w) := by
  unfold guardedWorldY
  simp only [mem_univ, if_true, inter_univ, inducedWeight_univ]

private theorem guardedWorldX_univ_eq (w : Sym2 V → unitInterval)
    (O : Set V) (x v : V) (X N : Set V) (h : Set V → ℝ) :
    guardedWorldX w Set.univ O x v X N h =
      ∫ ω in sourceAvoid ({x} : Set V) N ∩ sourceAvoid O N,
        worldGuardPrice w (Set.univ \ sourceCluster ω N) O v X *
          h (Set.univ \ sourceCluster ω N) ∂(prodBernoulli w) := by
  unfold guardedWorldX
  simp only [mem_univ, and_self, if_true, inter_univ, inducedWeight_univ]

private theorem coeWeight_sum_eq_one (w : Sym2 V → unitInterval) :
    ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω = 1 := by
  have h := BHK2006.integral_prodBernoulli_eq_sum w
    (fun _ : BondConfig V => (1 : ℝ))
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  exact h.symm

private theorem sourceWorldCov_guarded_stopped
    (w : Sym2 V → unitInterval) (X : Set V) (x v : V)
    (g : Set (Sym2 V) → ℝ) (hxX : x ∈ X) (hvX : v ∉ X)
    (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) (W Q : Set V) :
    guardedWorldY w W x Q
        (fun W' => sourceWorldCov w W' x g ({v} : Set V) X) *
        worldAvoidMass w W v X ≤
      worldAvoidMass w W v (X ∪ Q) *
        sourceWorldCov w W x g ({v} : Set V) X := by
  by_cases hxW : x ∈ W
  swap
  · simp [guardedWorldY, sourceWorldCov, hxW]
  by_cases hvW : v ∈ W
  swap
  · simp [worldAvoidMass, hvW]
  let Wf : Finset V := Finset.univ.filter fun u => u ∈ W
  have hWf : (↑Wf : Set V) = W := by
    ext u
    simp only [Wf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and]
  have hxWf : x ∈ Wf := by
    change x ∈ (↑Wf : Set V)
    rw [hWf]
    exact hxW
  have hvWf : v ∈ Wf := by
    change v ∈ (↑Wf : Set V)
    rw [hWf]
    exact hvW
  rw [← hWf,
    guardedWorldY_sourceCov_eq_Yw_BfS w Wf x X v g Q hxWf hvX,
    worldAvoidMass_eq_Mav w Wf X v hvWf,
    worldAvoidMass_eq_Mav w Wf (X ∪ Q) v hvWf,
    sourceWorldCov_coe_eq_BfS w Wf x X v g hxWf hvX]
  have hM :
      CovTau.Mav (fun e => (w e : ℝ)) Wf (X ∪ Q) v ∅ =
        CovTau.Mav (fun e => (w e : ℝ)) Wf X v Q := by
    unfold CovTau.Mav
    simp only [Set.union_empty]
  rw [hM]
  exact CovTauStarN.yS_mul_mS_le (fun e => (w e : ℝ))
    (fun e => (w e).2.1) (fun e => (w e).2.2) hxX hvX hg hg0 Wf Q

private theorem sourceWorldCov_guarded_antitone
    (w : Sym2 V → unitInterval) (X : Set V) (x v : V)
    (g : Set (Sym2 V) → ℝ) (hvX : v ∉ X)
    (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C)
    (W Q Q' : Set V) (hQQ' : Q ⊆ Q') (hQ'W : Q' ⊆ W) :
    guardedWorldY w W x Q'
        (fun W' => sourceWorldCov w W' x g ({v} : Set V) X) ≤
      guardedWorldY w W x Q
        (fun W' => sourceWorldCov w W' x g ({v} : Set V) X) := by
  by_cases hxW : x ∈ W
  swap
  · simp [guardedWorldY, hxW]
  let Wf : Finset V := Finset.univ.filter fun u => u ∈ W
  have hWf : (↑Wf : Set V) = W := by
    ext u
    simp only [Wf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and]
  have hxWf : x ∈ Wf := by
    change x ∈ (↑Wf : Set V)
    rw [hWf]
    exact hxW
  have hQ'Wf : Q' ⊆ (↑Wf : Set V) := by
    rw [hWf]
    exact hQ'W
  rw [← hWf,
    guardedWorldY_sourceCov_eq_Yw_BfS w Wf x X v g Q' hxWf hvX,
    guardedWorldY_sourceCov_eq_Yw_BfS w Wf x X v g Q hxWf hvX]
  apply CovTau.Yw_antitone_of_le (fun e => (w e : ℝ))
    (fun e => (w e).2.1) (fun e => (w e).2.2)
    (coeWeight_sum_eq_one w) x
    (fun U' => CovTau.BfS (fun e => (w e : ℝ)) U' x X v g) Wf
  · intro U' _ u
    exact CovTauStarN.yS_le_bS (fun e => (w e : ℝ))
      (fun e => (w e).2.1) (fun e => (w e).2.2) x hvX hg hg0 U'
        ({u} : Set V)
  · exact hQQ'
  · exact hQ'Wf

private theorem sourceWorldCov_global_two_source
    (w : Sym2 V → unitInterval) (x : V) (Y X O : Set V) (v : V)
    (g : Set (Sym2 V) → ℝ) (hxX : x ∈ X) (hvX : v ∉ X)
    (hO : Disjoint O (insert v (X ∪ Y))) (hg : Monotone g)
    (hg0 : ∀ C, 0 ≤ g C) :
    worldGuardMass w Set.univ O v (X ∪ Y) *
        guardedWorldY w Set.univ x Y
          (fun W => sourceWorldCov w W x g ({v} : Set V) X) ≤
      worldAvoidMass w Set.univ v (X ∪ Y) *
        guardedWorldX w Set.univ O x v X Y
          (fun W => sourceWorldCov w W x g ({v} : Set V) X) := by
  have hOsmall : Disjoint O (insert v X) :=
    hO.mono_right (Set.insert_subset_insert Set.subset_union_left)
  have htwo := guarded_two_source w Set.univ X O Y Y x v
    (fun W => sourceWorldCov w W x g ({v} : Set V) X)
    (Set.subset_univ _) hxX hvX hOsmall
    (fun W _ => sourceWorldCov_nonneg w W x g ({v} : Set V) X hg hg0)
    (fun W _ hvW =>
      sourceWorldCov_singleton_eq_zero_of_not_mem w W x v X g hvW)
    (fun W Q _ _ =>
      sourceWorldCov_guarded_stopped w X x v g hxX hvX hg hg0 W Q)
    (fun W Q Q' _ hQQ' hQ'W =>
      sourceWorldCov_guarded_antitone w X x v g hvX hg hg0 W Q Q'
        hQQ' hQ'W)
  have hXYY : X ∪ Y ∪ Y = X ∪ Y := by
    ext u
    simp only [mem_union]
    tauto
  rw [hXYY, Set.inter_self] at htwo
  exact htwo

theorem guardHorizontal_nonneg (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y X O : Set V)
    (v : V) (g : Set (Sym2 V) → ℝ) (hxX : x ∈ X) (hvX : v ∉ X)
    (hO : Disjoint O (insert v (X ∪ Y))) (hg : Monotone g) :
    0 ≤ guardHorizontal w x Y X O v g := by
  rw [← guardHorizontal_sub_const w x Y X O v g (g ∅)]
  let g₀ : Set (Sym2 V) → ℝ := fun C => g C - g ∅
  change 0 ≤ guardHorizontal w x Y X O v g₀
  have hg₀ : Monotone g₀ := fun C C' hCC' =>
    sub_le_sub_right (hg hCC') _
  have hg₀0 : ∀ C, 0 ≤ g₀ C := fun C =>
    sub_nonneg.2 (hg (Set.empty_subset C))
  have hOsmall : Disjoint O (insert v X) :=
    hO.mono_right (Set.insert_subset_insert Set.subset_union_left)
  by_cases hvY : v ∈ Y
  · have hprice0 : worldGuardPrice w Set.univ O v (X ∪ Y) = 0 := by
      unfold worldGuardPrice
      rw [worldGuardMass_eq_zero_of_target_mem w Set.univ O (X ∪ Y) v
        (Or.inr hvY), zero_div]
    have hobs0 : guardObsConst w O v (X ∪ Y) = 0 := by
      rw [← worldGuardPrice_univ_eq_guardObsConst]
      exact hprice0
    unfold guardHorizontal
    rw [hobs0, zero_mul, sub_zero]
    exact setIntegral_nonneg MeasurableSet.of_discrete fun ω _ =>
      sourceWorldCov_nonneg w (Set.univ \ sourceCluster ω Y) x g₀ O X
        hg₀ hg₀0
  · have hvXY : v ∉ X ∪ Y := by
      rintro (hvX' | hvY')
      · exact hvX hvX'
      · exact hvY hvY'
    have hempty : (∅ : BondConfig V) ∈
        sourceAvoid ({v} : Set V) (X ∪ Y) := by
      intro q hq b hb hreach
      have hqv : q = v := by simpa using hq
      subst q
      rw [HullPort.reachable_empty_iff] at hreach
      exact hvXY (hreach ▸ hb)
    have hMpos : 0 < worldAvoidMass w Set.univ v (X ∪ Y) := by
      unfold worldAvoidMass worldProb
      rw [if_pos (Set.mem_univ v), Set.inter_univ, inducedWeight_univ]
      exact prodBernoulli_real_pos_of_nonempty hw ⟨∅, hempty⟩
    have htwo := sourceWorldCov_global_two_source w x Y X O v g₀
      hxX hvX hO hg₀ hg₀0
    have hprice :
        worldGuardPrice w Set.univ O v (X ∪ Y) *
            guardedWorldY w Set.univ x Y
              (fun W => sourceWorldCov w W x g₀ ({v} : Set V) X) ≤
          guardedWorldX w Set.univ O x v X Y
            (fun W => sourceWorldCov w W x g₀ ({v} : Set V) X) := by
      unfold worldGuardPrice
      calc
        worldGuardMass w Set.univ O v (X ∪ Y) /
              worldAvoidMass w Set.univ v (X ∪ Y) *
              guardedWorldY w Set.univ x Y
                (fun W => sourceWorldCov w W x g₀ ({v} : Set V) X) =
            (worldGuardMass w Set.univ O v (X ∪ Y) *
              guardedWorldY w Set.univ x Y
                (fun W => sourceWorldCov w W x g₀ ({v} : Set V) X)) /
              worldAvoidMass w Set.univ v (X ∪ Y) := by ring
        _ ≤ (worldAvoidMass w Set.univ v (X ∪ Y) *
              guardedWorldX w Set.univ O x v X Y
                (fun W => sourceWorldCov w W x g₀ ({v} : Set V) X)) /
              worldAvoidMass w Set.univ v (X ∪ Y) :=
          div_le_div_of_nonneg_right htwo hMpos.le
        _ = guardedWorldX w Set.univ O x v X Y
              (fun W => sourceWorldCov w W x g₀ ({v} : Set V) X) := by
          field_simp
    have hXle :
        guardedWorldX w Set.univ O x v X Y
            (fun W => sourceWorldCov w W x g₀ ({v} : Set V) X) ≤
          ∫ ω in sourceAvoid ({x} : Set V) Y ∩ sourceAvoid O Y,
            sourceWorldCov w (Set.univ \ sourceCluster ω Y) x g₀ O X
              ∂(prodBernoulli w) := by
      rw [guardedWorldX_univ_eq]
      refine setIntegral_mono_on (Integrable.of_finite).integrableOn
        (Integrable.of_finite).integrableOn MeasurableSet.of_discrete ?_
      intro ω _
      exact sourceWorldCov_guardPrice_le w
        (Set.univ \ sourceCluster ω Y) X O x v g₀ hxX hvX hOsmall hg₀
    have hmain := hprice.trans hXle
    rw [worldGuardPrice_univ_eq_guardObsConst,
      guardedWorldY_univ_eq] at hmain
    unfold guardHorizontal
    linarith

end KNAll.Guarded

end
