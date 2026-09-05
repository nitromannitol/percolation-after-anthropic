import Hypergraph.HyperAvoid
import Hypergraph.HyperPartition

/-!
# Cluster means as totally defined functions of the record

The two-cluster step of the gluing argument compares a functional of the cluster of a source set
`S` with a functional of the cluster of a second set, conditionally on the first cluster avoiding
the second.  Positive association is applied to those two functionals, so they have to be
increasing, respectively decreasing, functions on the whole lattice of records: on every subset of
labels, not only on the subsets that occur with positive probability.

That is what this module supplies.  For a set `J` of labels, `supportFromRecord H S J` is the
cluster of `S` in the configuration whose open labels are exactly `J`, and `fibreMean H S F J` is
the value of `F` there.  Both are defined for every `J`, with no feasibility and no positivity
condition, so `supportFromRecord_mono` and `fibreMean_mono` are ordinary statements about totally
defined functions.  The values on the records that actually occur are recovered from
`fibreMean_eq_on_clusterEvent`, which is a pointwise identity on the event that the cluster of `S`
is exactly `K`, again with no positivity of that event assumed.

* `supportFromRecord`, `supportFromRecord_mono` — the cluster as a monotone map from records to
  vertex sets;
* `fibreMean`, `fibreMean_mono`, `fibreMean_anti` — the value of a functional there, increasing for
  increasing `F` and decreasing for decreasing `F`;
* `fibreMean_eq_on_clusterEvent` — on the event that the cluster of `S` is `K`, the value is `F K`;
* `setIntegral_fibreMean_eq_sum`, `integral_fibreMean_eq_sum`,
  `avoidIntegral_eq_sum_clusterEvent` — the expectation of `F` at the cluster as a finite sum over
  the possible clusters, weighted by the probabilities of the cluster events.

The last group is the form in which conditioning on a cluster is used downstream.  A conditional
expectation given the event that the cluster is `K` would need that event to have positive
probability; the weighted sums below carry the same information with no denominator, the cluster
events of probability zero contributing zero.  `real_eq_sum_clusterEvent` of `KN/HyperPartition.lean`
is the case `F = 1`.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## The cluster of a record -/

/-- The cluster of `S` in the configuration whose open labels are exactly `J`.  Defined for every
set `J` of labels. -/
def supportFromRecord (H : Hypergraph V E) (S : Set V) (J : Set E) : Set V :=
  hyperClusterSet H J S

@[simp] theorem supportFromRecord_eq (H : Hypergraph V E) (S : Set V) (J : Set E) :
    supportFromRecord H S J = hyperClusterSet H J S := rfl

/-- The source lies in its own cluster. -/
theorem subset_supportFromRecord (H : Hypergraph V E) (S : Set V) (J : Set E) :
    S ⊆ supportFromRecord H S J :=
  subset_hyperClusterSet H J S

/-- **Target 2.**  Opening more labels only grows the cluster, so the cluster of `S` is a monotone
function of the record.  No feasibility hypothesis: the statement is about all subsets of labels. -/
theorem supportFromRecord_mono (H : Hypergraph V E) (S : Set V) :
    Monotone (supportFromRecord H S) :=
  fun _ _ hsub => hyperClusterSet_mono H S hsub

/-- The cluster of a larger source is larger. -/
theorem supportFromRecord_mono_source (H : Hypergraph V E) {S T : Set V} (hST : S ⊆ T)
    (J : Set E) : supportFromRecord H S J ⊆ supportFromRecord H T J := by
  rintro y ⟨x, hx, hr⟩
  exact ⟨x, hST hx, hr⟩

/-! ## The value of a functional at the cluster of a record -/

/-- The value of `F` at the cluster of `S` in the configuration whose open labels are exactly `J`.
Defined for every `J`. -/
def fibreMean (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ) (J : Set E) : ℝ :=
  F (supportFromRecord H S J)

@[simp] theorem fibreMean_eq (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ) (J : Set E) :
    fibreMean H S F J = F (hyperClusterSet H J S) := rfl

/-- **Target 3.**  An increasing functional of the cluster is an increasing function of the record.
The proof is the composition of two monotone maps, and it is available on every record because
`fibreMean` is. -/
theorem fibreMean_mono (H : Hypergraph V E) (S : Set V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (fibreMean H S F) :=
  fun _ _ hsub => hF (supportFromRecord_mono H S hsub)

/-- The companion for a decreasing functional: this is the second of the two factors the two-cluster
statement pairs. -/
theorem fibreMean_anti (H : Hypergraph V E) (S : Set V) {F : Set V → ℝ} (hF : Antitone F) :
    Antitone (fibreMean H S F) :=
  fun _ _ hsub => hF (supportFromRecord_mono H S hsub)

theorem fibreMean_nonneg (H : Hypergraph V E) (S : Set V) {F : Set V → ℝ} (hF : ∀ K, 0 ≤ F K)
    (J : Set E) : 0 ≤ fibreMean H S F J := hF _

theorem fibreMean_const (H : Hypergraph V E) (S : Set V) (c : ℝ) (J : Set E) :
    fibreMean H S (fun _ => c) J = c := rfl

theorem fibreMean_mul (H : Hypergraph V E) (S : Set V) (F G : Set V → ℝ) (J : Set E) :
    fibreMean H S (fun K => F K * G K) J = fibreMean H S F J * fibreMean H S G J := rfl

theorem fibreMean_le_fibreMean (H : Hypergraph V E) (S : Set V) {F G : Set V → ℝ}
    (hFG : ∀ K, F K ≤ G K) (J : Set E) : fibreMean H S F J ≤ fibreMean H S G J := hFG _

/-! ## The feasible records -/

/-- **Target 4.**  On the event that the cluster of `S` is exactly `K`, the value of `F` at the
actual cluster is `F K`.  This is a pointwise identity at a single configuration, so the event is
not required to have positive probability, nor even to be nonempty. -/
theorem fibreMean_eq_on_clusterEvent (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ) (K : Set V)
    {ω : Set E} (hω : ω ∈ clusterEvent H S K) :
    F (hyperClusterSet H ω S) = F K := by
  have h : hyperClusterSet H ω S = K := hω
  rw [h]

/-- The same identity written through `fibreMean`, which is how the two-cluster argument reads
it. -/
theorem fibreMean_eq_of_mem_clusterEvent (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ)
    (K : Set V) {ω : Set E} (hω : ω ∈ clusterEvent H S K) :
    fibreMean H S F ω = F K :=
  fibreMean_eq_on_clusterEvent H S F K hω

/-- Conversely every record is feasible for the cluster it produces, so the identity above covers
every configuration. -/
theorem fibreMean_eq_self (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ) (ω : Set E) :
    fibreMean H S F ω = F (hyperClusterSet H ω S) :=
  fibreMean_eq_of_mem_clusterEvent H S F _ (mem_clusterEvent_self H S ω)

/-- A record avoids `X` exactly when the cluster it determines does. -/
theorem mem_avoidEvent_iff_supportFromRecord (H : Hypergraph V E) (S X : Set V) (J : Set E) :
    J ∈ avoidEvent H S X ↔ Disjoint (supportFromRecord H S J) X := Iff.rfl

/-! ## The expansion over the possible clusters

Over a finite vertex type the cluster of `S` is the coercion of a finset, and the cluster events
indexed by finsets are pairwise disjoint and cover the configuration space
(`KN/HyperPartition.lean`).  So a function of the cluster is a finite linear combination of the
indicators of those events, and its integral is the matching finite weighted sum.
-/

/-- **The decomposition.**  A function of the cluster of `S`, restricted to an event `D`, is the
finite sum over possible clusters of the constant `F K` carried by the part of `D` on which the
cluster is `K`. -/
theorem indicator_fibreMean_eq_sum [Fintype V] (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ)
    (D : Set (Set E)) (ω : Set E) :
    D.indicator (fibreMean H S F) ω
      = ∑ K : Finset V,
          (clusterEvent H S (↑K : Set V) ∩ D).indicator (fun _ => F (↑K : Set V)) ω := by
  obtain ⟨K₀, hK₀⟩ : ∃ K : Finset V, (↑K : Set V) = hyperClusterSet H ω S :=
    (Set.toFinite (hyperClusterSet H ω S)).exists_finset_coe
  have hmem₀ : ω ∈ clusterEvent H S (↑K₀ : Set V) := hK₀.symm
  have hzero : ∀ K : Finset V, K ≠ K₀ →
      (clusterEvent H S (↑K : Set V) ∩ D).indicator (fun _ => F (↑K : Set V)) ω = 0 := by
    intro K hK
    refine Set.indicator_of_notMem (fun hcon => hK ?_) _
    have h1 : hyperClusterSet H ω S = (↑K : Set V) := hcon.1
    exact Finset.coe_injective (h1.symm.trans hK₀.symm)
  have key : ∑ K : Finset V,
        (clusterEvent H S (↑K : Set V) ∩ D).indicator (fun _ => F (↑K : Set V)) ω
      = (clusterEvent H S (↑K₀ : Set V) ∩ D).indicator (fun _ => F (↑K₀ : Set V)) ω :=
    Finset.sum_eq_single K₀ (fun K _ hK => hzero K hK) (fun h => absurd (Finset.mem_univ _) h)
  rw [key]
  by_cases hω : ω ∈ D
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_inter hmem₀ hω)]
    show F (hyperClusterSet H ω S) = F (↑K₀ : Set V)
    rw [hK₀]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem fun h => hω h.2]

/-- **Target 5.**  The integral of `F` at the cluster of `S` over a measurable event `D` is the
finite sum over possible clusters `K` of `F K` weighted by the probability that the cluster is `K`
and `D` occurs.  No conditional expectation and no positivity hypothesis: a cluster event of
probability zero contributes zero. -/
theorem setIntegral_fibreMean_eq_sum [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (F : Set V → ℝ) {D : Set (Set E)} (hD : MeasurableSet D) :
    (∫ ω in D, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob))
      = ∑ K : Finset V, F (↑K : Set V) *
          (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V) ∩ D) := by
  have hmeas : ∀ K : Finset V, MeasurableSet (clusterEvent H S (↑K : Set V) ∩ D) := fun K =>
    (measurableSet_clusterEvent H S (↑K : Set V)).inter hD
  calc (∫ ω in D, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob))
      = ∫ ω, ∑ K : Finset V,
          (clusterEvent H S (↑K : Set V) ∩ D).indicator (fun _ => F (↑K : Set V)) ω
            ∂(prodBernoulli H.prob) := by
        rw [← integral_indicator hD]
        exact integral_congr_ae
          (Filter.Eventually.of_forall (indicator_fibreMean_eq_sum H S F D))
    _ = ∑ K : Finset V, ∫ ω,
          (clusterEvent H S (↑K : Set V) ∩ D).indicator (fun _ => F (↑K : Set V)) ω
            ∂(prodBernoulli H.prob) :=
        integral_finsetSum _ fun K _ => (integrable_const (F (↑K : Set V))).indicator (hmeas K)
    _ = ∑ K : Finset V, F (↑K : Set V) *
          (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V) ∩ D) := by
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [integral_indicator_const _ (hmeas K), smul_eq_mul, mul_comm]

/-- **Target 5, the unrestricted form.**  The expectation of `F` at the cluster of `S` is the sum
over possible clusters of `F K` weighted by the probability that the cluster is `K`. -/
theorem integral_fibreMean_eq_sum [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (F : Set V → ℝ) :
    (∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob))
      = ∑ K : Finset V, F (↑K : Set V) *
          (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V)) := by
  have h := setIntegral_fibreMean_eq_sum H S F (D := Set.univ) MeasurableSet.univ
  rw [Measure.restrict_univ] at h
  simp only [Set.inter_univ] at h
  exact h

/-- The avoidance functional of `KN/HyperAvoid.lean` in the same form: the sum over possible
clusters of `F K` weighted by the probability that the cluster is `K` and avoids `X`. -/
theorem avoidIntegral_eq_sum_clusterEvent [Fintype V] [Fintype E] (H : Hypergraph V E)
    (S X : Set V) (F : Set V → ℝ) :
    avoidIntegral H S X F
      = ∑ K : Finset V, F (↑K : Set V) *
          (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S X) :=
  setIntegral_fibreMean_eq_sum H S F (measurableSet_avoidEvent H S X)

/-- **The weights of the expansion add up.**  Summing the weights of `setIntegral_fibreMean_eq_sum`
against a constant returns the probability of the event conditioned on: this is
`real_eq_sum_clusterEvent`, and it is the statement that replaces the normalization a conditional
expectation would need. -/
theorem sum_clusterEvent_const [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V) (c : ℝ)
    {D : Set (Set E)} (hD : MeasurableSet D) :
    ∑ K : Finset V, c * (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V) ∩ D)
      = c * (prodBernoulli H.prob).real D := by
  rw [← Finset.mul_sum, ← real_eq_sum_clusterEvent H S D hD]

/-- **The case of a constant integrand**, which fixes the orientation of the expansion. -/
theorem setIntegral_fibreMean_const [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (c : ℝ) {D : Set (Set E)} (hD : MeasurableSet D) :
    (∫ _ω in D, c ∂(prodBernoulli H.prob)) = c * (prodBernoulli H.prob).real D :=
  (setIntegral_fibreMean_eq_sum H S (fun _ => c) hD).trans (sum_clusterEvent_const H S c hD)

/-- **Monotonicity of the expansion in the integrand.**  Termwise comparison of the two weighted
sums, the weights being nonnegative.  Together with `fibreMean_mono` this is the elementary half of
the two-cluster statement: an increasing functional gives a larger expansion. -/
theorem integral_fibreMean_mono [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    {F G : Set V → ℝ} (hFG : ∀ K, F K ≤ G K) :
    (∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob))
      ≤ ∫ ω, G (hyperClusterSet H ω S) ∂(prodBernoulli H.prob) := by
  rw [integral_fibreMean_eq_sum H S F, integral_fibreMean_eq_sum H S G]
  exact Finset.sum_le_sum fun K _ =>
    mul_le_mul_of_nonneg_right (hFG _) measureReal_nonneg

end KNAll.Site

end
