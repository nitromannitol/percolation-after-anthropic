import KNConjectures.AvoidedDefs

set_option linter.unusedSectionVars false

/-!
# Projection onto one explored vertex cluster

This file restates the cluster projection from `CovTau.Transfer` using vertex sets throughout.
For a vertex set `K`, `bar K` is the set of pairs meeting `K`; the projected functional subtracts
the expected value of the cluster functional in a fresh configuration with those pairs deleted.
-/

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity
open scoped Classical

variable {V : Type*} [Fintype V]

/-- The set of pairs having at least one endpoint in `K`. -/
def bar (K : Set V) : Set (Sym2 V) :=
  {e | ∃ v ∈ e, v ∈ K}

/-- The projection of `F(C_o) - F(C_a)` onto an explored vertex cluster `K`. -/
def projFunA (w : Sym2 V → unitInterval) (a : V) (F : Set V → ℝ) (K : Set V) : ℝ :=
  F K - ∫ η, F (openCluster (η \ bar K) a) ∂(prodBernoulli w)

/-- For a cluster rooted at `o`, the BHK deleted-pair set is exactly the set of pairs meeting its
vertex cluster. -/
theorem barOf_singleton_eq_bar (o : V) (ω : BondConfig V) :
    BHK2006.barOf {o} (openEdgeCluster ω o) = bar (openCluster ω o) := by
  ext e
  simp only [BHK2006.barOf, bar, mem_setOf_eq, mem_singleton_iff,
    KNPreFKG.openCluster_eq_setOf_openEdgeCluster]

/-- The vertex-cluster projection is increasing on all vertex sets. -/
theorem monotone_projFunA (w : Sym2 V → unitInterval) (a : V) (F : Set V → ℝ)
    (hF : ∀ K L : Set V, K ⊆ L → F K ≤ F L) :
    Monotone (projFunA w a F) := by
  intro K L hKL
  unfold projFunA
  refine sub_le_sub (hF K L hKL) ?_
  refine integral_mono Integrable.of_finite Integrable.of_finite fun η => hF _ _ (openCluster_mono ?_ a)
  intro e he
  exact ⟨he.1, fun heK => he.2 (by
    obtain ⟨v, hve, hvK⟩ := heK
    exact ⟨v, hve, hKL hvK⟩)⟩

/-- On disconnection of `o` from `a`, integration over any event determined by the open edge
cluster of `o` is unchanged by replacing the cluster difference with its vertex-cluster
projection. -/
theorem setIntegral_sub_eq_projFunA (w : Sym2 V → unitInterval) (a o : V) (F : Set V → ℝ)
    (𝒮 : Set (Set (Sym2 V))) :
    ∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable o a} ∩
          {ω | openEdgeCluster ω o ∈ 𝒮},
        (F (openCluster ω o) - F (openCluster ω a)) ∂(prodBernoulli w) =
      ∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable o a} ∩
          {ω | openEdgeCluster ω o ∈ 𝒮},
        projFunA w a F (openCluster ω o) ∂(prodBernoulli w) := by
  simpa only [projFunA, KNPreFKG.clusterFun_openEdgeCluster, barOf_singleton_eq_bar] using
    (CovTau.setIntegral_sub_eq_projFun w a o F 𝒮)

/-- The projection identity on disconnection from `a` and connection from `o` to a finite set
`T`, with the disconnection event written in the avoided-set vocabulary. -/
theorem setIntegral_sub_eq_projFunA_conn (w : Sym2 V → unitInterval) (a o : V)
    (F : Set V → ℝ) (T : Finset V) :
    ∫ ω in {ω : BondConfig V | ∀ y ∈ ({a} : Set V), ¬ (openGraph ω).Reachable o y} ∩
          (⋃ t ∈ T, openConn o t),
        (F (openCluster ω o) - F (openCluster ω a)) ∂(prodBernoulli w) =
      ∫ ω in {ω : BondConfig V | ∀ y ∈ ({a} : Set V), ¬ (openGraph ω).Reachable o y} ∩
          (⋃ t ∈ T, openConn o t),
        projFunA w a F (openCluster ω o) ∂(prodBernoulli w) := by
  let 𝒮 : Set (Set (Sym2 V)) :=
    {K | ∃ t ∈ T, t = o ∨ ∃ e ∈ K, t ∈ e}
  have hcluster : {ω : BondConfig V | openEdgeCluster ω o ∈ 𝒮} =
      ⋃ t ∈ T, openConn o t := by
    ext ω
    simp only [𝒮, mem_setOf_eq, mem_iUnion, exists_prop, openConn,
      reachable_iff_exists_mem_openEdgeCluster]
  have havoid : {ω : BondConfig V | ∀ y ∈ ({a} : Set V), ¬ (openGraph ω).Reachable o y} =
      {ω : BondConfig V | ¬ (openGraph ω).Reachable o a} := by
    ext ω
    simp
  rw [havoid, ← hcluster]
  exact setIntegral_sub_eq_projFunA w a o F 𝒮

/-- The integral of the projection on avoidance of `a` is the difference of the two unconditional
cluster means. -/
theorem setIntegral_projFunA_avoid (w : Sym2 V → unitInterval) (a o : V) (F : Set V → ℝ) :
    ∫ ω in {ω : BondConfig V | ∀ y ∈ ({a} : Set V), ¬ (openGraph ω).Reachable o y},
        projFunA w a F (openCluster ω o) ∂(prodBernoulli w) =
      (∫ ω, F (openCluster ω o) ∂(prodBernoulli w)) -
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) := by
  let D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable o a}
  have havoid : {ω : BondConfig V | ∀ y ∈ ({a} : Set V), ¬ (openGraph ω).Reachable o y} = D := by
    ext ω
    simp [D]
  rw [havoid]
  have hproj :
      ∫ ω in D, (F (openCluster ω o) - F (openCluster ω a)) ∂(prodBernoulli w) =
        ∫ ω in D, projFunA w a F (openCluster ω o) ∂(prodBernoulli w) := by
    simpa only [D, mem_univ, setOf_true, inter_univ] using
      (setIntegral_sub_eq_projFunA w a o F (Set.univ : Set (Set (Sym2 V))))
  have hzero :
      ∫ ω in Dᶜ, (F (openCluster ω o) - F (openCluster ω a)) ∂(prodBernoulli w) = 0 := by
    refine (setIntegral_congr_fun (MeasurableSet.of_discrete) (g := fun _ => (0 : ℝ)) fun ω hω => ?_).trans (by simp)
    simp only [D, mem_compl_iff, mem_setOf_eq, not_not] at hω
    rw [KNPreFKG.openCluster_eq_of_reachable hω, sub_self]
  calc
    ∫ ω in D, projFunA w a F (openCluster ω o) ∂(prodBernoulli w) =
        ∫ ω in D, (F (openCluster ω o) - F (openCluster ω a)) ∂(prodBernoulli w) := hproj.symm
    _ = ∫ ω, (F (openCluster ω o) - F (openCluster ω a)) ∂(prodBernoulli w) := by
      have hsplit := integral_add_compl (MeasurableSet.of_discrete : MeasurableSet D)
        (Integrable.of_finite (f := fun ω : BondConfig V => F (openCluster ω o) - F (openCluster ω a))
          (μ := prodBernoulli w))
      rw [hzero, add_zero] at hsplit
      exact hsplit
    _ = (∫ ω, F (openCluster ω o) ∂(prodBernoulli w)) -
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) := by
      rw [integral_sub Integrable.of_finite Integrable.of_finite]

end KNAll

end
