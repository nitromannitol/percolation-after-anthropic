import Hypergraph.HyperUpper

/-!
# The short tail of the hyperedge gluing argument

This module isolates the only theorem that has to be generalized from the graph proof:
`HyperFixedClusterComparison`.  It is the hypergraph form of the fixed-minimizer
Conjecture 4 theorem.  Once that theorem is available, the indicator specialization and
Harris' inequality prove `HyperedgeGluing` without importing any lattice geometry.

Every theorem declaration below has an explicit proof.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open scoped Classical

/-- The cluster of one vertex, written with the set-valued hypergraph cluster API. -/
abbrev hyperVertexCluster {W L : Type*} (H : Hypergraph W L) (ω : Set L) (x : W) : Set W :=
  hyperClusterSet H ω ({x} : Set W)

@[simp] theorem mem_hyperVertexCluster_iff {W L : Type*} (H : Hypergraph W L)
    (ω : Set L) (x y : W) :
    y ∈ hyperVertexCluster H ω x ↔ ω ∈ hyperConn H x y := by
  simp only [hyperVertexCluster, hyperClusterSet, hyperConn, mem_setOf_eq,
    mem_singleton_iff, exists_eq_left]

/--
The one genuinely difficult input.

For an increasing cluster functional `F`, suppose `a ∈ A` minimizes its unconditional
cluster mean among the relays.  Then, after restricting to the event that `o` reaches
some relay, the mean at `a` is still no larger than the mean at `o`.

This is exactly the theorem proved as `conjecture4Fixed_holds` in the verified graph
proof.  The hypergraph port must prove this proposition by carrying exposed *label sets*
through the avoided first-relay/surplus-transfer induction.
-/
def HyperFixedClusterComparison : Prop :=
  ∀ (W L : Type) [Fintype W] [Fintype L]
      (H : Hypergraph W L) (A : Finset W) (o a : W) (F : Set W → ℝ),
    a ∈ A →
    (∀ K K' : Set W, K ⊆ K' → F K ≤ F K') →
    (∀ x ∈ A,
      (∫ ω, F (hyperVertexCluster H ω a) ∂(prodBernoulli H.prob)) ≤
        ∫ ω, F (hyperVertexCluster H ω x) ∂(prodBernoulli H.prob)) →
    (∫ ω in ⋃ x ∈ A, hyperConn H o x,
        F (hyperVertexCluster H ω a) ∂(prodBernoulli H.prob)) ≤
      ∫ ω in ⋃ x ∈ A, hyperConn H o x,
        F (hyperVertexCluster H ω o) ∂(prodBernoulli H.prob)

/--
The indicator specialization of `HyperFixedClusterComparison`.

This is the precise pre-Harris relay comparison needed for `HyperedgeGluing`; separating
it makes clear that neither the slab reduction nor any lattice geometry occurs in the
finite proof.
-/
def HyperFixedRelayComparison : Prop :=
  ∀ (W L : Type) [Fintype W] [Fintype L]
      (H : Hypergraph W L) (A : Finset W) (hA : A.Nonempty) (o b a : W),
    a ∈ A →
    (∀ x ∈ A,
      (prodBernoulli H.prob).real (hyperConn H a b) ≤
        (prodBernoulli H.prob).real (hyperConn H x b)) →
    (prodBernoulli H.prob).real
        (hyperConn H a b ∩ ⋃ x ∈ A, hyperConn H o x) ≤
      (prodBernoulli H.prob).real
        (hyperConn H o b ∩ ⋃ x ∈ A, hyperConn H o x)

/-- The fixed-cluster theorem implies its connection-indicator specialization. -/
theorem hyperFixedRelayComparison_of_fixedClusterComparison
    (hfixed : HyperFixedClusterComparison) : HyperFixedRelayComparison := by
  intro W L _ _ H A _hA o b a haA hmin
  let F : Set W → ℝ := fun K => if b ∈ K then 1 else 0
  have hFmono : ∀ K K' : Set W, K ⊆ K' → F K ≤ F K' := by
    intro K K' hKK'
    simp only [F]
    by_cases hbK : b ∈ K
    · rw [if_pos hbK, if_pos (hKK' hbK)]
    · rw [if_neg hbK]
      split_ifs <;> norm_num
  have hFind : ∀ x : W,
      (fun ω : Set L => F (hyperVertexCluster H ω x)) =
        (hyperConn H x b).indicator 1 := by
    intro x
    funext ω
    simp only [F]
    by_cases hω : ω ∈ hyperConn H x b
    · rw [Set.indicator_of_mem hω, Pi.one_apply,
        if_pos ((mem_hyperVertexCluster_iff H ω x b).2 hω)]
    · rw [Set.indicator_of_notMem hω,
        if_neg (fun hb => hω ((mem_hyperVertexCluster_iff H ω x b).1 hb))]
  have hmean : ∀ x ∈ A,
      (∫ ω, F (hyperVertexCluster H ω a) ∂(prodBernoulli H.prob)) ≤
        ∫ ω, F (hyperVertexCluster H ω x) ∂(prodBernoulli H.prob) := by
    intro x hx
    rw [hFind a, hFind x,
      integral_indicator_one (measurableSet_hyperConn H a b),
      integral_indicator_one (measurableSet_hyperConn H x b)]
    exact hmin x hx
  have hrestricted : ∀ x : W,
      (∫ ω in ⋃ y ∈ A, hyperConn H o y,
          F (hyperVertexCluster H ω x) ∂(prodBernoulli H.prob)) =
        (prodBernoulli H.prob).real
          (hyperConn H x b ∩ ⋃ y ∈ A, hyperConn H o y) := by
    intro x
    have hmeas : MeasurableSet (⋃ y ∈ A, hyperConn H o y) := MeasurableSet.of_discrete
    rw [hFind x, ← integral_indicator hmeas, Set.indicator_indicator,
      Set.inter_comm (⋃ y ∈ A, hyperConn H o y) (hyperConn H x b),
      integral_indicator_one
        ((measurableSet_hyperConn H x b).inter hmeas)]
  have h := hfixed W L H A o a F haA hFmono hmean
  rw [hrestricted a, hrestricted o] at h
  exact h

/-- The fixed relay comparison plus Harris proves the localized finite inequality. -/
theorem hyperedgeGluing_of_fixedRelayComparison
    (hfixed : HyperFixedRelayComparison) : HyperedgeGluing := by
  intro W L _ _ H A hA o b
  obtain ⟨a, haA, hmin⟩ :=
    Finset.exists_min_image A
      (fun x => (prodBernoulli H.prob).real (hyperConn H x b)) hA
  have hinf :
      A.inf' hA (fun x => (prodBernoulli H.prob).real (hyperConn H x b)) =
        (prodBernoulli H.prob).real (hyperConn H a b) :=
    le_antisymm (Finset.inf'_le _ haA)
      (Finset.le_inf' hA _ fun x hx => hmin x hx)
  have hUup : IsUpperSet (⋃ x ∈ A, hyperConn H o x) := by
    intro ω ω' hsub hω
    obtain ⟨x, hx, hox⟩ := Set.mem_iUnion₂.1 hω
    exact Set.mem_iUnion₂.2
      ⟨x, hx, (isUpperSet_hyperConn H o x) hsub hox⟩
  have hUmeas : MeasurableSet (⋃ x ∈ A, hyperConn H o x) :=
    MeasurableSet.of_discrete
  have hharris :
      (prodBernoulli H.prob).real (⋃ x ∈ A, hyperConn H o x) *
          (prodBernoulli H.prob).real (hyperConn H a b) ≤
        (prodBernoulli H.prob).real
          (hyperConn H a b ∩ ⋃ x ∈ A, hyperConn H o x) :=
    (mul_comm ((prodBernoulli H.prob).real (⋃ x ∈ A, hyperConn H o x))
        ((prodBernoulli H.prob).real (hyperConn H a b))).trans_le
      (prodBernoulli_harris_upper H.prob
        (isUpperSet_hyperConn H a b) hUup
        (measurableSet_hyperConn H a b) hUmeas)
  rw [hinf]
  exact hharris.trans (hfixed W L H A hA o b a haA hmin)

/-- The complete short tail from the single fixed-minimizer theorem to `HyperedgeGluing`. -/
theorem hyperedgeGluing_of_fixedClusterComparison
    (hfixed : HyperFixedClusterComparison) : HyperedgeGluing :=
  hyperedgeGluing_of_fixedRelayComparison
    (hyperFixedRelayComparison_of_fixedClusterComparison hfixed)

end KNAll.Site

end
