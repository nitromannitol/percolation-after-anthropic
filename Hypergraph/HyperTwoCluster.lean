import Hypergraph.HyperFibre
import Hypergraph.HyperExchange
import Hypergraph.ProdBernoulliFKG

/-!
# The two-cluster inequality: the cluster of `S` and the cluster of `T`, given that the first
avoids the second

Conditionally on the cluster of a source set `S` avoiding a set `T`, a functional increasing in the
record of the `S`-cluster and a functional decreasing in the record of the `T`-cluster are
positively associated.  This is van den Berg–Häggström–Kahn's Theorem 1.5 for the hyperedge model,
in the same denominator-free shape as everything else in this development: the conditioning event
`avoidEvent H S T` is never divided by, and every function handed to a correlation inequality is
defined on the whole lattice of records.

## What is proved

* `deleteHyper_integral_mul_le_mono_anti`, `deleteHyper_integral_mul_le_anti` — **the residual
  model**.  On the event that the cluster of `S` is exactly `K`, the labels still free are those
  avoiding `K`, and they carry the parameters of `deleteHyper H K`.  Harris' inequality there says
  that an increasing and a decreasing functional of the remaining configuration are negatively
  correlated, and that two decreasing ones are positively correlated.
  `deleteHyper_cluster_mul_le` and `deleteHyper_residual_mul_le` are the two cases for functionals
  of a cluster.
* `condMean` — the conditional mean of a functional of the pair of clusters given that the cluster
  of `S` is `K`, written as an integral in fresh labels off `K`.  It is defined for **every**
  `K : Set V`, with no feasibility and no positivity condition, and
  `condMean_eq_deleteHyper_integral` identifies it with the integral in the residual model.
  `condMean_mono` is the monotonicity in `K` that the one-cluster inequality consumes, and
  `condMean_mul_le` is the residual Harris inequality transported to it.
* `setIntegral_avoid_eq_sum` — **the recombination**.  The integral of a functional of the two
  clusters over the avoidance event is the finite sum over the possible clusters `K` of the
  conditional mean at `K`, weighted by `avoidWeight H S T K`, the probability that the cluster of
  `S` is `K` and avoids `T`.  This is BHK's display (10) with no conditional expectation and no
  denominator: a cluster of probability zero contributes zero, and a cluster meeting `T`
  contributes zero because its weight vanishes.
* `avoid_covariance_decomposition` — **the total covariance identity**, exactly: the covariance
  over the whole space is the weighted sum of the residual covariances plus the covariance of the
  conditional means, all four terms being finite sums against `avoidWeight`.
* `avoid_twoCluster_le` — **the conclusion**, for functionals of the pair of clusters increasing in
  the first and decreasing in the second; and `avoid_cluster_association`, the statement in the
  form quoted at the head of this file, together with `avoid_cluster_negCorrelation`, the negative
  correlation of two increasing functionals of the two clusters.

## The one-cluster inequality

The last step of the argument is the one-cluster inequality of van den Berg–Häggström–Kahn
(Theorem 1.3), applied not to the two given functionals but to their conditional means, which are
increasing functions of the cluster of `S`.  It enters here as the hypothesis
`OneClusterInequality H S T`, which `KN/HyperOneCluster.lean` supplies as
`avoidIntegral_mul_le_inter H S T T` after `Set.inter_self` and `Set.union_self`.  The hypothesis
is stated with the sign condition those authors carry;
`OneClusterInequality.of_monotone` removes it, an increasing function on a finite vertex type
attaining its minimum at `∅` and the inequality being invariant under adding constants.

## Why the conditional means are defined everywhere

An earlier account of this result defined the conditional means only on the records of positive
probability and then applied a positive-association theorem to them as though they were monotone
on the whole lattice.  `condMean H T Φ K` is an integral over the whole configuration space of a
functional of `K` and of a cluster computed in the labels off `K`; it is a total function of `K`,
`condMean_mono` is monotonicity of a total function, and every appeal to a correlation inequality
below is to a totally defined monotone function.  `supportFromRecord_mono` of `KN/HyperFibre.lean`
is what makes the monotonicity in `K` work: enlarging `K` closes more labels, so the second cluster
shrinks.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006), Thms. 1.3–1.5.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## Harris' inequality for a mixed and for a decreasing pair

`KN/ProdBernoulliFKG.lean` carries the inequality for two increasing functions.  The two variants
used below follow by changing the sign of one or of both factors, the integral of the negative
being the negative of the integral.
-/

section Harris

variable {ι : Type*}

/-- **Harris for an increasing and a decreasing function**: they are negatively correlated,
`∫ f g ≤ (∫ f)(∫ g)`.  Apply `prodBernoulli_integral_mul_le` to `f` and `-g`.
[cite: HarrisPCPS1960, Lemma 4.1] -/
theorem prodBernoulli_integral_mul_le_mono_anti [Fintype ι] (p : ι → unitInterval)
    {f g : Set ι → ℝ} (hf : Monotone f) (hg : Antitone g) :
    (∫ ω, f ω * g ω ∂(prodBernoulli p))
      ≤ (∫ ω, f ω ∂(prodBernoulli p)) * ∫ ω, g ω ∂(prodBernoulli p) := by
  have h := prodBernoulli_integral_mul_le p (f := f) (g := fun ω => -g ω) hf
    (fun _ _ hab => neg_le_neg (hg hab))
  simp only [mul_neg, integral_neg] at h
  linarith

/-- **Harris for two decreasing functions**: they are positively correlated,
`(∫ f)(∫ g) ≤ ∫ f g`.  Apply `prodBernoulli_integral_mul_le` to `-f` and `-g`.
[cite: HarrisPCPS1960, Lemma 4.1] -/
theorem prodBernoulli_integral_mul_le_anti [Fintype ι] (p : ι → unitInterval)
    {f g : Set ι → ℝ} (hf : Antitone f) (hg : Antitone g) :
    (∫ ω, f ω ∂(prodBernoulli p)) * (∫ ω, g ω ∂(prodBernoulli p))
      ≤ ∫ ω, f ω * g ω ∂(prodBernoulli p) := by
  have h := prodBernoulli_integral_mul_le p (f := fun ω => -f ω) (g := fun ω => -g ω)
    (fun _ _ hab => neg_le_neg (hf hab)) (fun _ _ hab => neg_le_neg (hg hab))
  simp only [neg_mul_neg, integral_neg] at h
  linarith

end Harris

/-! ## Target 1: Harris' inequality in the deleted model

On the event that the cluster of `S` is exactly `K` the labels meeting `K` are frozen, and
`clusterFactorization` says that the free labels carry the parameters of `deleteHyper H K`.  The
inequalities below are Harris there.  They involve neither the source `S` nor the cluster event:
they are statements about the deleted model alone, which is what makes them usable one cluster at a
time.
-/

/-- **Target 1.**  In the residual model of a cluster `K`, an increasing and a decreasing
functional of the remaining configuration are negatively correlated.
[cite: HarrisPCPS1960, Lemma 4.1] -/
theorem deleteHyper_integral_mul_le_mono_anti [Fintype E] (H : Hypergraph V E) (K : Set V)
    {f g : Set E → ℝ} (hf : Monotone f) (hg : Antitone g) :
    (∫ ν, f ν * g ν ∂(prodBernoulli (deleteHyper H K).prob))
      ≤ (∫ ν, f ν ∂(prodBernoulli (deleteHyper H K).prob)) *
        ∫ ν, g ν ∂(prodBernoulli (deleteHyper H K).prob) :=
  prodBernoulli_integral_mul_le_mono_anti _ hf hg

/-- **Target 1, the decreasing pair.**  Two decreasing functionals of the remaining configuration
are positively correlated in the residual model.  This is the case the recombination uses: both of
the two functionals of the two-cluster statement are decreasing in the second cluster.
[cite: HarrisPCPS1960, Lemma 4.1] -/
theorem deleteHyper_integral_mul_le_anti [Fintype E] (H : Hypergraph V E) (K : Set V)
    {f g : Set E → ℝ} (hf : Antitone f) (hg : Antitone g) :
    (∫ ν, f ν ∂(prodBernoulli (deleteHyper H K).prob)) *
        (∫ ν, g ν ∂(prodBernoulli (deleteHyper H K).prob))
      ≤ ∫ ν, f ν * g ν ∂(prodBernoulli (deleteHyper H K).prob) :=
  prodBernoulli_integral_mul_le_anti _ hf hg

/-- **Target 1 for cluster functionals.**  An increasing functional of the cluster of one source
and a decreasing functional of the cluster of another are negatively correlated in the residual
model, the cluster of a source being an increasing function of the record
(`supportFromRecord_mono`). -/
theorem deleteHyper_cluster_mul_le [Fintype E] (H : Hypergraph V E) (K S' T' : Set V)
    {F G : Set V → ℝ} (hF : Monotone F) (hG : Antitone G) :
    (∫ ν, F (hyperClusterSet H ν S') * G (hyperClusterSet H ν T')
        ∂(prodBernoulli (deleteHyper H K).prob))
      ≤ (∫ ν, F (hyperClusterSet H ν S') ∂(prodBernoulli (deleteHyper H K).prob)) *
        ∫ ν, G (hyperClusterSet H ν T') ∂(prodBernoulli (deleteHyper H K).prob) :=
  deleteHyper_integral_mul_le_mono_anti H K
    (fun _ _ hab => hF (supportFromRecord_mono H S' hab))
    (fun _ _ hab => hG (supportFromRecord_mono H T' hab))

/-- **Target 1 for two decreasing cluster functionals.**  Two functionals decreasing in the cluster
of `T` are positively correlated in the residual model of `K`. -/
theorem deleteHyper_residual_mul_le [Fintype E] (H : Hypergraph V E) (T : Set V)
    {Φ Ψ : Set V → Set V → ℝ} (hΦ : ∀ C, Antitone fun D => Φ C D)
    (hΨ : ∀ C, Antitone fun D => Ψ C D) (K : Set V) :
    (∫ ν, Φ K (hyperClusterSet H ν T) ∂(prodBernoulli (deleteHyper H K).prob)) *
        (∫ ν, Ψ K (hyperClusterSet H ν T) ∂(prodBernoulli (deleteHyper H K).prob))
      ≤ ∫ ν, Φ K (hyperClusterSet H ν T) * Ψ K (hyperClusterSet H ν T)
          ∂(prodBernoulli (deleteHyper H K).prob) :=
  deleteHyper_integral_mul_le_anti H K
    (fun _ _ hab => hΦ K (supportFromRecord_mono H T hab))
    (fun _ _ hab => hΨ K (supportFromRecord_mono H T hab))

/-! ## Functions of the trace of a record on a set of labels

`clusterFactorization` factorizes the probability of the cluster event against an *event*
determined by the labels avoiding the cluster.  The recombination needs the same for a *function*.
Over a finite label type such a function is a finite linear combination of the indicators of the
events "the trace on those labels is `J`", so the factorization for events gives the factorization
for functions, with no measurability or integrability side condition.
-/

section Trace

variable [Fintype E]

omit [Fintype E] in
/-- The event that the trace of the record on `M` is `X` depends only on the labels of `M`. -/
theorem determinedBy_trace (M X : Set E) : DeterminedBy {ρ : Set E | ρ ∩ M = X} M := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_setOf_eq, h]

/-- **The decomposition of a function of the trace.**  A function of the record depending only on
its trace on `M`, restricted to an event `D`, is the finite sum over the possible traces `J` of the
constant `h J` carried by the part of `D` on which the trace is `J`. -/
theorem indicator_trace_eq_sum (M : Set E) {h : Set E → ℝ}
    (hdet : ∀ ν, h (ν ∩ M) = h ν) (D : Set (Set E)) (ν : Set E) :
    D.indicator h ν
      = ∑ J : Finset E,
          (D ∩ {ρ : Set E | ρ ∩ M = (↑J : Set E)}).indicator (fun _ => h (↑J : Set E)) ν := by
  obtain ⟨J₀, hJ₀⟩ : ∃ J : Finset E, (↑J : Set E) = ν ∩ M := (Set.toFinite _).exists_finset_coe
  have hmem₀ : ν ∈ {ρ : Set E | ρ ∩ M = (↑J₀ : Set E)} := hJ₀.symm
  have hzero : ∀ J : Finset E, J ≠ J₀ →
      (D ∩ {ρ : Set E | ρ ∩ M = (↑J : Set E)}).indicator (fun _ => h (↑J : Set E)) ν = 0 := by
    intro J hJ
    refine Set.indicator_of_notMem (fun hcon => hJ ?_) _
    have h1 : ν ∩ M = (↑J : Set E) := hcon.2
    exact Finset.coe_injective (h1.symm.trans hJ₀.symm)
  have key : ∑ J : Finset E,
        (D ∩ {ρ : Set E | ρ ∩ M = (↑J : Set E)}).indicator (fun _ => h (↑J : Set E)) ν
      = (D ∩ {ρ : Set E | ρ ∩ M = (↑J₀ : Set E)}).indicator (fun _ => h (↑J₀ : Set E)) ν :=
    Finset.sum_eq_single J₀ (fun J _ hJ => hzero J hJ) (fun hc => absurd (Finset.mem_univ _) hc)
  rw [key]
  by_cases hν : ν ∈ D
  · rw [Set.indicator_of_mem hν, Set.indicator_of_mem (Set.mem_inter hν hmem₀), hJ₀]
    exact (hdet ν).symm
  · rw [Set.indicator_of_notMem hν, Set.indicator_of_notMem fun hc => hν hc.1]

/-- The integral of a function of the trace on `M` over an event `D`, as a finite sum over the
possible traces. -/
theorem setIntegral_trace_eq_sum (μ : Measure (Set E)) [IsFiniteMeasure μ] (M : Set E)
    {h : Set E → ℝ} (hdet : ∀ ν, h (ν ∩ M) = h ν) (D : Set (Set E)) :
    (∫ ν in D, h ν ∂μ)
      = ∑ J : Finset E, h (↑J : Set E) * μ.real (D ∩ {ρ : Set E | ρ ∩ M = (↑J : Set E)}) := by
  calc (∫ ν in D, h ν ∂μ)
      = ∫ ν, ∑ J : Finset E,
          (D ∩ {ρ : Set E | ρ ∩ M = (↑J : Set E)}).indicator (fun _ => h (↑J : Set E)) ν ∂μ := by
        rw [← integral_indicator (measurableSet_of_fintype D)]
        exact integral_congr_ae (Filter.Eventually.of_forall (indicator_trace_eq_sum M hdet D))
    _ = ∑ J : Finset E, ∫ ν,
          (D ∩ {ρ : Set E | ρ ∩ M = (↑J : Set E)}).indicator (fun _ => h (↑J : Set E)) ν ∂μ :=
        integral_finsetSum _ fun J _ =>
          (integrable_const (h (↑J : Set E))).indicator (measurableSet_of_fintype _)
    _ = _ := by
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [integral_indicator_const _ (measurableSet_of_fintype _), smul_eq_mul, mul_comm]

/-- The unrestricted form of `setIntegral_trace_eq_sum`. -/
theorem integral_trace_eq_sum (μ : Measure (Set E)) [IsFiniteMeasure μ] (M : Set E)
    {h : Set E → ℝ} (hdet : ∀ ν, h (ν ∩ M) = h ν) :
    (∫ ν, h ν ∂μ)
      = ∑ J : Finset E, h (↑J : Set E) * μ.real {ρ : Set E | ρ ∩ M = (↑J : Set E)} := by
  have hh := setIntegral_trace_eq_sum μ M hdet Set.univ
  rw [Measure.restrict_univ] at hh
  simpa only [Set.univ_inter] using hh

/-- **Closing the labels that meet `K` is invisible to a function of the labels avoiding `K`.**
The functional form of `prodBernoulli_deleteHyper_real_eq`, obtained from it by expanding the
function over the possible traces. -/
theorem integral_deleteHyper_eq_of_trace (H : Hypergraph V E) (K : Set V) {h : Set E → ℝ}
    (hdet : ∀ ν, h (ν ∩ (labelsMeeting H K)ᶜ) = h ν) :
    (∫ ν, h ν ∂(prodBernoulli (deleteHyper H K).prob)) = ∫ ν, h ν ∂(prodBernoulli H.prob) := by
  rw [integral_trace_eq_sum _ _ hdet, integral_trace_eq_sum _ _ hdet]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [prodBernoulli_deleteHyper_real_eq H K (determinedBy_trace _ _)]

/-- **The cluster factorization for functions.**  The integral of a function of the labels avoiding
`K` over the event that the cluster of `S` is `K` is the probability of that event times the
unrestricted integral.  `clusterFactorization` is the case of an indicator; the general case
follows by expanding over the possible traces on the labels avoiding `K`, and the passage back from
the deleted parameters to the original ones is `integral_deleteHyper_eq_of_trace`. -/
theorem setIntegral_clusterEvent_of_trace (H : Hypergraph V E) (S K : Set V) {h : Set E → ℝ}
    (hdet : ∀ ν, h (ν ∩ (labelsMeeting H K)ᶜ) = h ν) :
    (∫ ν in clusterEvent H S K, h ν ∂(prodBernoulli H.prob))
      = (prodBernoulli H.prob).real (clusterEvent H S K) * ∫ ν, h ν ∂(prodBernoulli H.prob) := by
  rw [setIntegral_trace_eq_sum _ _ hdet, ← integral_deleteHyper_eq_of_trace H K hdet,
    integral_trace_eq_sum _ _ hdet, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [clusterFactorization H S K (determinedBy_trace _ _) (measurableSet_of_fintype _)]
  ring

end Trace

/-! ## The geometry of the avoidance event

Three facts.  Enlarging a vertex set enlarges the set of labels meeting it.  On the event that the
cluster of `S` avoids `T`, the cluster of `S` and the cluster of `T` are disjoint, because a common
vertex would join a vertex of `T` to `S`.  Hence, by `clusterEvent_inter_avoiding`, on that event
the cluster of `T` is unchanged when the labels meeting the cluster of `S` are discarded.
-/

/-- Enlarging a vertex set enlarges the set of labels meeting it. -/
theorem labelsMeeting_mono (H : Hypergraph V E) {K K' : Set V} (hKK' : K ⊆ K') :
    labelsMeeting H K ⊆ labelsMeeting H K' := by
  intro e he
  rw [mem_labelsMeeting] at he ⊢
  obtain ⟨v, hv, hvK⟩ := Set.not_disjoint_iff.1 he
  exact Set.not_disjoint_iff.2 ⟨v, hv, hKK' hvK⟩

/-- **The two clusters are disjoint on the avoidance event.**  A vertex in both is joined to a
vertex of `T` and to a vertex of `S`, so that vertex of `T` lies in the cluster of `S`, which the
avoidance event forbids. -/
theorem disjoint_cluster_of_avoid (H : Hypergraph V E) {S T K : Set V} {ω : Set E}
    (hK : ω ∈ clusterEvent H S K) (hA : ω ∈ avoidEvent H S T) :
    Disjoint K (hyperClusterSet H ω T) := by
  rw [Set.disjoint_left]
  intro v hvK hvT
  have hKeq : hyperClusterSet H ω S = K := hK
  obtain ⟨t, htT, hrt⟩ := hvT
  have hv : v ∈ hyperClusterSet H ω S := by rw [hKeq]; exact hvK
  obtain ⟨s, hsS, hrs⟩ := hv
  exact Set.disjoint_left.1 hA ⟨s, hsS, hrs.trans hrt.symm⟩ htT

/-- A cluster disjoint from `T` already avoids `T`. -/
theorem clusterEvent_inter_avoidEvent_of_disjoint (H : Hypergraph V E) (S T K : Set V)
    (hKT : Disjoint K T) :
    clusterEvent H S K ∩ avoidEvent H S T = clusterEvent H S K := by
  refine Set.inter_eq_left.2 fun ω hω => ?_
  have hKeq : hyperClusterSet H ω S = K := hω
  show Disjoint (hyperClusterSet H ω S) T
  rw [hKeq]
  exact hKT

/-- A cluster meeting `T` never avoids `T`. -/
theorem clusterEvent_inter_avoidEvent_of_not_disjoint (H : Hypergraph V E) (S T K : Set V)
    (hKT : ¬ Disjoint K T) :
    clusterEvent H S K ∩ avoidEvent H S T = ∅ := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hω hA
  have hKeq : hyperClusterSet H ω S = K := hω
  have hd : Disjoint (hyperClusterSet H ω S) T := hA
  rw [hKeq] at hd
  exact hKT hd

/-- **The cluster of `T` is read off the labels avoiding `K`.**  On the event that the cluster of
`S` is `K` and avoids `T`, discarding the labels meeting `K` leaves the cluster of `T` unchanged:
the two clusters are disjoint, so `clusterEvent_inter_avoiding` applies. -/
theorem hyperClusterSet_trace_eq (H : Hypergraph V E) (S T K : Set V) {ω : Set E}
    (hK : ω ∈ clusterEvent H S K) (hA : ω ∈ avoidEvent H S T) :
    hyperClusterSet H (ω ∩ (labelsMeeting H K)ᶜ) T = hyperClusterSet H ω T := by
  have hdisj := disjoint_cluster_of_avoid H hK hA
  have hmem : ω ∈ clusterEvent H S K ∩ clusterEvent H T (hyperClusterSet H ω T) :=
    ⟨hK, mem_clusterEvent_self H T ω⟩
  rw [clusterEvent_inter_avoiding H S K T (hyperClusterSet H ω T) hdisj] at hmem
  exact hmem.2

/-! ## The conditional mean given the cluster of `S`

`condMean H T Φ K` is the mean of `Φ K` at the cluster of `T` computed in fresh labels off `K`.
It is defined for every `K`, it is monotone in `K` because enlarging `K` closes more labels, and
`condMean_eq_deleteHyper_integral` identifies it with the mean in the residual model of `K`, which
is where Harris' inequality was applied.
-/

/-- The conditional mean of `Φ` given that the cluster of `S` is `K`: the mean of `Φ K` at the
cluster of `T` in the record with the labels meeting `K` discarded.  Defined for every `K`. -/
def condMean (H : Hypergraph V E) (T : Set V) (Φ : Set V → Set V → ℝ) (K : Set V) : ℝ :=
  ∫ η, Φ K (supportFromRecord H T (η ∩ (labelsMeeting H K)ᶜ)) ∂(prodBernoulli H.prob)

theorem condMean_eq (H : Hypergraph V E) (T : Set V) (Φ : Set V → Set V → ℝ) (K : Set V) :
    condMean H T Φ K
      = ∫ η, Φ K (hyperClusterSet H (η ∩ (labelsMeeting H K)ᶜ) T) ∂(prodBernoulli H.prob) := rfl

/-- **The conditional mean is the mean in the residual model.**  Discarding the labels that meet
`K` from the record is the same as closing them in the parameters: the integrand is a function of
the labels avoiding `K` (`integral_deleteHyper_eq_of_trace`), and under the deleted parameters the
labels meeting `K` are almost surely absent, so discarding them changes nothing. -/
theorem condMean_eq_deleteHyper_integral [Fintype E] (H : Hypergraph V E) (T : Set V)
    (Φ : Set V → Set V → ℝ) (K : Set V) :
    condMean H T Φ K
      = ∫ ν, Φ K (hyperClusterSet H ν T) ∂(prodBernoulli (deleteHyper H K).prob) := by
  have hdet := integral_deleteHyper_eq_of_trace H K
    (h := fun ν => Φ K (hyperClusterSet H (ν ∩ (labelsMeeting H K)ᶜ) T))
    (fun ν => by rw [Set.inter_assoc, Set.inter_self])
  have hae : (∫ ν, Φ K (hyperClusterSet H (ν ∩ (labelsMeeting H K)ᶜ) T)
        ∂(prodBernoulli (deleteHyper H K).prob))
      = ∫ ν, Φ K (hyperClusterSet H ν T) ∂(prodBernoulli (deleteHyper H K).prob) := by
    refine integral_congr_ae ?_
    have hzero : ∀ e ∈ labelsMeeting H K, (deleteHyper H K).prob e = 0 := by
      intro e he
      simp only [deleteHyper, if_pos he]
    filter_upwards [prodBernoulli_ae_forall_notMem (deleteHyper H K).prob
      (Z := labelsMeeting H K) (Set.toFinite _).countable hzero] with ν hν
    have hint : ν ∩ (labelsMeeting H K)ᶜ = ν :=
      Set.inter_eq_left.2 fun e he hmem => hν e hmem he
    rw [hint]
  calc condMean H T Φ K
      = ∫ ν, Φ K (hyperClusterSet H (ν ∩ (labelsMeeting H K)ᶜ) T)
          ∂(prodBernoulli H.prob) := condMean_eq H T Φ K
    _ = ∫ ν, Φ K (hyperClusterSet H (ν ∩ (labelsMeeting H K)ᶜ) T)
          ∂(prodBernoulli (deleteHyper H K).prob) := hdet.symm
    _ = ∫ ν, Φ K (hyperClusterSet H ν T) ∂(prodBernoulli (deleteHyper H K).prob) := hae

/-- **The conditional mean is increasing in the cluster.**  A larger cluster of `S` both raises the
first argument of `Φ`, which is increasing in it, and closes more labels, which shrinks the cluster
of `T`, in which `Φ` is decreasing.  Both effects push the mean up.  The statement is about a
totally defined function of `K`; no record is required to be feasible.
[cite: VandenbergHaggstromKahn2005, §1 p. 8] -/
theorem condMean_mono [Fintype E] (H : Hypergraph V E) (T : Set V) {Φ : Set V → Set V → ℝ}
    (hΦ1 : ∀ D, Monotone fun C => Φ C D) (hΦ2 : ∀ C, Antitone fun D => Φ C D) :
    Monotone (condMean H T Φ) := by
  intro K K' hKK'
  refine integral_mono (integrable_of_fintype _) (integrable_of_fintype _) fun η => ?_
  have hsub : η ∩ (labelsMeeting H K')ᶜ ⊆ η ∩ (labelsMeeting H K)ᶜ :=
    Set.inter_subset_inter (subset_refl η)
      (Set.compl_subset_compl.2 (labelsMeeting_mono H hKK'))
  calc Φ K (supportFromRecord H T (η ∩ (labelsMeeting H K)ᶜ))
      ≤ Φ K' (supportFromRecord H T (η ∩ (labelsMeeting H K)ᶜ)) := hΦ1 _ hKK'
    _ ≤ Φ K' (supportFromRecord H T (η ∩ (labelsMeeting H K')ᶜ)) :=
        hΦ2 K' (supportFromRecord_mono H T hsub)

/-- **The residual Harris inequality on the conditional means.**  Two functionals decreasing in the
cluster of `T` have conditional means whose product is at most the conditional mean of their
product: this is `deleteHyper_residual_mul_le`, transported along
`condMean_eq_deleteHyper_integral`.  It is the residual covariance term of the recombination, and
it is nonnegative.  [cite: HarrisPCPS1960, Lemma 4.1] -/
theorem condMean_mul_le [Fintype E] (H : Hypergraph V E) (T : Set V) {Φ Ψ : Set V → Set V → ℝ}
    (hΦ2 : ∀ C, Antitone fun D => Φ C D) (hΨ2 : ∀ C, Antitone fun D => Ψ C D) (K : Set V) :
    condMean H T Φ K * condMean H T Ψ K ≤ condMean H T (fun C D => Φ C D * Ψ C D) K := by
  rw [condMean_eq_deleteHyper_integral, condMean_eq_deleteHyper_integral,
    condMean_eq_deleteHyper_integral H T (fun C D => Φ C D * Ψ C D)]
  exact deleteHyper_residual_mul_le H T hΦ2 hΨ2 K

/-! ## Target 2: the recombination

The weights of the expansion are the probabilities `avoidWeight H S T K` that the cluster of `S` is
`K` and avoids `T`.  They sum to the probability of the avoidance event, and the integral of a
functional of the two clusters over that event is their weighted sum against the conditional means.
No conditional expectation appears, and no event is required to have positive probability: a
cluster of probability zero, and a cluster meeting `T`, both carry weight zero.
-/

/-- The weight of the cluster `K` in the expansion: the probability that the cluster of `S` is `K`
and avoids `T`. -/
def avoidWeight (H : Hypergraph V E) (S T : Set V) (K : Finset V) : ℝ :=
  (prodBernoulli H.prob).real (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T)

theorem avoidWeight_nonneg (H : Hypergraph V E) (S T : Set V) (K : Finset V) :
    0 ≤ avoidWeight H S T K := measureReal_nonneg

/-- The avoidance functional as a weighted sum, which is
`avoidIntegral_eq_sum_clusterEvent` of `KN/HyperFibre.lean`. -/
theorem avoidIntegral_eq_sum_avoidWeight [Fintype V] [Fintype E] (H : Hypergraph V E)
    (S T : Set V) (f : Set V → ℝ) :
    avoidIntegral H S T f = ∑ K : Finset V, f (↑K : Set V) * avoidWeight H S T K :=
  avoidIntegral_eq_sum_clusterEvent H S T f

/-- The weights sum to the probability of the avoidance event. -/
theorem real_avoidEvent_eq_sum_avoidWeight [Fintype V] [Fintype E] (H : Hypergraph V E)
    (S T : Set V) :
    (prodBernoulli H.prob).real (avoidEvent H S T) = ∑ K : Finset V, avoidWeight H S T K :=
  real_eq_sum_clusterEvent H S (avoidEvent H S T) (measurableSet_avoidEvent H S T)

/-- **One term of the recombination.**  The integral over the event that the cluster of `S` is `K`
and avoids `T` is the conditional mean at `K` times the weight of `K`.  When `K` meets `T` the
event is empty and both sides vanish; otherwise the event is the whole cluster event, on which the
cluster of `T` is read off the labels avoiding `K`, and
`setIntegral_clusterEvent_of_trace` factorizes. -/
theorem setIntegral_clusterEvent_avoid_eq [Fintype E] (H : Hypergraph V E) (S T K : Set V)
    (Φ : Set V → Set V → ℝ) :
    (∫ ν in clusterEvent H S K ∩ avoidEvent H S T, Φ K (hyperClusterSet H ν T)
        ∂(prodBernoulli H.prob))
      = condMean H T Φ K *
        (prodBernoulli H.prob).real (clusterEvent H S K ∩ avoidEvent H S T) := by
  by_cases hKT : Disjoint K T
  · rw [clusterEvent_inter_avoidEvent_of_disjoint H S T K hKT]
    have hcongr : (∫ ν in clusterEvent H S K, Φ K (hyperClusterSet H ν T)
          ∂(prodBernoulli H.prob))
        = ∫ ν in clusterEvent H S K,
            Φ K (hyperClusterSet H (ν ∩ (labelsMeeting H K)ᶜ) T) ∂(prodBernoulli H.prob) := by
      refine setIntegral_congr_fun (measurableSet_of_fintype _) fun ν hν => ?_
      have hA : ν ∈ avoidEvent H S T := by
        have hKeq : hyperClusterSet H ν S = K := hν
        show Disjoint (hyperClusterSet H ν S) T
        rw [hKeq]
        exact hKT
      rw [hyperClusterSet_trace_eq H S T K hν hA]
    rw [hcongr, setIntegral_clusterEvent_of_trace H S K
      (h := fun ν => Φ K (hyperClusterSet H (ν ∩ (labelsMeeting H K)ᶜ) T))
      (fun ν => by rw [Set.inter_assoc, Set.inter_self])]
    exact mul_comm _ _
  · rw [clusterEvent_inter_avoidEvent_of_not_disjoint H S T K hKT]
    simp

/-- **Target 2, the recombination.**  The integral of a functional of the two clusters over the
avoidance event is the finite sum over the possible clusters of `S` of the conditional mean there,
weighted by the probability that the cluster of `S` is that set and avoids `T`.  This is van den
Berg–Häggström–Kahn's display (10) with the denominators cleared.
[cite: VandenbergHaggstromKahn2005, §1 pp. 7–8, display (10)] -/
theorem setIntegral_avoid_eq_sum [Fintype V] [Fintype E] (H : Hypergraph V E) (S T : Set V)
    (Φ : Set V → Set V → ℝ) :
    (∫ ω in avoidEvent H S T,
        Φ (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      = ∑ K : Finset V, condMean H T Φ (↑K : Set V) * avoidWeight H S T K := by
  have hexp : ∀ ω : Set E, (avoidEvent H S T).indicator
        (fun ν => Φ (hyperClusterSet H ν S) (hyperClusterSet H ν T)) ω
      = ∑ K : Finset V, (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T)) ω := by
    intro ω
    obtain ⟨K₀, hK₀⟩ : ∃ K : Finset V, (↑K : Set V) = hyperClusterSet H ω S :=
      (Set.toFinite _).exists_finset_coe
    have hmem₀ : ω ∈ clusterEvent H S (↑K₀ : Set V) := hK₀.symm
    have hzero : ∀ K : Finset V, K ≠ K₀ →
        (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T)) ω = 0 := by
      intro K hK
      refine Set.indicator_of_notMem (fun hcon => hK ?_) _
      have h1 : hyperClusterSet H ω S = (↑K : Set V) := hcon.1
      exact Finset.coe_injective (h1.symm.trans hK₀.symm)
    have key : ∑ K : Finset V, (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T)) ω
        = (clusterEvent H S (↑K₀ : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K₀ : Set V) (hyperClusterSet H ν T)) ω :=
      Finset.sum_eq_single K₀ (fun K _ hK => hzero K hK) (fun hc => absurd (Finset.mem_univ _) hc)
    rw [key]
    by_cases hω : ω ∈ avoidEvent H S T
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_inter hmem₀ hω), hK₀]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem fun hc => hω hc.2]
  calc (∫ ω in avoidEvent H S T,
        Φ (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      = ∫ ω, ∑ K : Finset V, (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T)) ω ∂(prodBernoulli H.prob) := by
        rw [← integral_indicator (measurableSet_avoidEvent H S T)]
        exact integral_congr_ae (Filter.Eventually.of_forall hexp)
    _ = ∑ K : Finset V, ∫ ω, (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T)) ω ∂(prodBernoulli H.prob) :=
        integral_finsetSum _ fun K _ =>
          (integrable_of_fintype _).indicator (measurableSet_of_fintype _)
    _ = ∑ K : Finset V, ∫ ω in clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T,
          Φ (↑K : Set V) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob) :=
        Finset.sum_congr rfl fun K _ => integral_indicator (measurableSet_of_fintype _)
    _ = _ :=
        Finset.sum_congr rfl fun K _ => setIntegral_clusterEvent_avoid_eq H S T (↑K : Set V) Φ

/-- **The total covariance identity.**  The covariance of two functionals of the two clusters over
the avoidance event splits, exactly, into the weighted sum of the residual covariances and the
covariance of the conditional means.  Both summands are finite sums against `avoidWeight`; the
first is nonnegative by `condMean_mul_le`, the second by the one-cluster inequality applied to the
conditional means, and those are the two steps of `avoid_twoCluster_le`. -/
theorem avoid_covariance_decomposition [Fintype V] [Fintype E] (H : Hypergraph V E) (S T : Set V)
    (F G : Set V → Set V → ℝ) :
    (prodBernoulli H.prob).real (avoidEvent H S T) *
        (∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) (hyperClusterSet H ω T) *
            G (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      - (∫ ω in avoidEvent H S T,
            F (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob)) *
        (∫ ω in avoidEvent H S T,
            G (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      = (prodBernoulli H.prob).real (avoidEvent H S T) *
          (∑ K : Finset V,
            (condMean H T (fun C D => F C D * G C D) (↑K : Set V)
                - condMean H T F (↑K : Set V) * condMean H T G (↑K : Set V))
              * avoidWeight H S T K)
        + ((prodBernoulli H.prob).real (avoidEvent H S T) *
            (∑ K : Finset V,
              (condMean H T F (↑K : Set V) * condMean H T G (↑K : Set V)) * avoidWeight H S T K)
          - (∑ K : Finset V, condMean H T F (↑K : Set V) * avoidWeight H S T K) *
            ∑ K : Finset V, condMean H T G (↑K : Set V) * avoidWeight H S T K) := by
  have h1 := setIntegral_avoid_eq_sum H S T F
  have h2 := setIntegral_avoid_eq_sum H S T G
  have h3 : (∫ ω in avoidEvent H S T,
        F (hyperClusterSet H ω S) (hyperClusterSet H ω T) *
          G (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      = ∑ K : Finset V, condMean H T (fun C D => F C D * G C D) (↑K : Set V) *
          avoidWeight H S T K :=
    setIntegral_avoid_eq_sum H S T (fun C D => F C D * G C D)
  have hsplit : ∑ K : Finset V,
        (condMean H T (fun C D => F C D * G C D) (↑K : Set V)
            - condMean H T F (↑K : Set V) * condMean H T G (↑K : Set V))
          * avoidWeight H S T K
      = (∑ K : Finset V, condMean H T (fun C D => F C D * G C D) (↑K : Set V) *
            avoidWeight H S T K)
        - ∑ K : Finset V,
            (condMean H T F (↑K : Set V) * condMean H T G (↑K : Set V)) * avoidWeight H S T K := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun K _ => by ring
  rw [h1, h2, h3, hsplit]
  ring

/-! ## The one-cluster inequality as a hypothesis

The last step needs positive association of increasing functionals of the cluster of `S`
conditionally on that cluster avoiding `T`.  That is the one-cluster inequality of van den
Berg–Häggström–Kahn, proved for this model in `KN/HyperOneCluster.lean`
(`avoidIntegral_mul_le_inter` with both avoided sets equal to `T`); it enters here as a hypothesis
so that this file does not depend on that one.
-/

/-- **The one-cluster inequality** for the source `S` and the avoided set `T`, denominator-free.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1] -/
def OneClusterInequality (H : Hypergraph V E) (S T : Set V) : Prop :=
  ∀ f g : Set V → ℝ, Monotone f → Monotone g → (∀ K, 0 ≤ f K) → (∀ K, 0 ≤ g K) →
    avoidIntegral H S T f * avoidIntegral H S T g
      ≤ avoidIntegral H S T (fun K => f K * g K) *
          (prodBernoulli H.prob).real (avoidEvent H S T)

/-- Adding constants to the two factors changes neither side of the one-cluster inequality: with
`W` the total weight, both sides move by the same amount. -/
private theorem shift_sum_le {n : Type*} [Fintype n] (w f g : n → ℝ) (a b : ℝ)
    (key : (∑ i, (f i - a) * w i) * (∑ i, (g i - b) * w i)
        ≤ (∑ i, ((f i - a) * (g i - b)) * w i) * ∑ i, w i) :
    (∑ i, f i * w i) * (∑ i, g i * w i) ≤ (∑ i, f i * g i * w i) * ∑ i, w i := by
  have h1 : ∑ i, (f i - a) * w i = (∑ i, f i * w i) - a * ∑ i, w i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, (g i - b) * w i = (∑ i, g i * w i) - b * ∑ i, w i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ i, ((f i - a) * (g i - b)) * w i
      = (∑ i, f i * g i * w i) - b * (∑ i, f i * w i) - a * (∑ i, g i * w i)
        + a * b * ∑ i, w i := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, h3] at key
  nlinarith [key]

/-- **The one-cluster inequality without the sign condition.**  On a finite vertex type an
increasing function attains its minimum at `∅`, and the inequality is unchanged when a constant is
added to either factor, so the hypothesis of nonnegativity can be dropped. -/
theorem OneClusterInequality.of_monotone [Fintype V] [Fintype E] {H : Hypergraph V E}
    {S T : Set V} (hOne : OneClusterInequality H S T) {f g : Set V → ℝ}
    (hf : Monotone f) (hg : Monotone g) :
    avoidIntegral H S T f * avoidIntegral H S T g
      ≤ avoidIntegral H S T (fun K => f K * g K) *
          (prodBernoulli H.prob).real (avoidEvent H S T) := by
  have key := hOne (fun K => f K - f ∅) (fun K => g K - g ∅)
    (fun _ _ hab => sub_le_sub_right (hf hab) _) (fun _ _ hab => sub_le_sub_right (hg hab) _)
    (fun K => sub_nonneg.2 (hf (Set.empty_subset K)))
    (fun K => sub_nonneg.2 (hg (Set.empty_subset K)))
  rw [avoidIntegral_eq_sum_avoidWeight, avoidIntegral_eq_sum_avoidWeight,
    avoidIntegral_eq_sum_avoidWeight, real_avoidEvent_eq_sum_avoidWeight] at key
  rw [avoidIntegral_eq_sum_avoidWeight, avoidIntegral_eq_sum_avoidWeight,
    avoidIntegral_eq_sum_avoidWeight, real_avoidEvent_eq_sum_avoidWeight]
  exact shift_sum_le (avoidWeight H S T) (fun K => f (↑K : Set V)) (fun K => g (↑K : Set V))
    (f ∅) (g ∅) key

/-! ## Target 3: the conclusion -/

/-- **The two-cluster inequality.**  Conditionally on the cluster of `S` avoiding `T`, two
functionals of the pair of clusters that are increasing in the cluster of `S` and decreasing in the
cluster of `T` are positively associated, in the denominator-free form
`(∫_A F)(∫_A G) ≤ P(A) ∫_A F G` with `A` the avoidance event.

The proof is the three steps of the printed one: the recombination `setIntegral_avoid_eq_sum`
rewrites each of the three integrals as a weighted sum of conditional means; the one-cluster
inequality applied to the two conditional means, which are increasing functions of the cluster of
`S` by `condMean_mono`, moves the product of sums past the sum of products; and the residual Harris
inequality `condMean_mul_le` compares the product of the conditional means with the conditional
mean of the product, one cluster at a time.
[cite: VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9)), proof pp. 7–8] -/
theorem avoid_twoCluster_le [Fintype V] [Fintype E] (H : Hypergraph V E) (S T : Set V)
    (hOne : OneClusterInequality H S T) {F G : Set V → Set V → ℝ}
    (hF1 : ∀ D, Monotone fun C => F C D) (hF2 : ∀ C, Antitone fun D => F C D)
    (hG1 : ∀ D, Monotone fun C => G C D) (hG2 : ∀ C, Antitone fun D => G C D) :
    (∫ ω in avoidEvent H S T,
        F (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob)) *
      (∫ ω in avoidEvent H S T,
        G (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      ≤ (prodBernoulli H.prob).real (avoidEvent H S T) *
        ∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) (hyperClusterSet H ω T) *
            G (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob) := by
  have h1 := setIntegral_avoid_eq_sum H S T F
  have h2 := setIntegral_avoid_eq_sum H S T G
  have h3 : (∫ ω in avoidEvent H S T,
        F (hyperClusterSet H ω S) (hyperClusterSet H ω T) *
          G (hyperClusterSet H ω S) (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      = ∑ K : Finset V, condMean H T (fun C D => F C D * G C D) (↑K : Set V) *
          avoidWeight H S T K :=
    setIntegral_avoid_eq_sum H S T (fun C D => F C D * G C D)
  have hP := real_avoidEvent_eq_sum_avoidWeight H S T
  rw [h1, h2, h3, hP]
  have hone := hOne.of_monotone (f := condMean H T F) (g := condMean H T G)
    (condMean_mono H T hF1 hF2) (condMean_mono H T hG1 hG2)
  rw [avoidIntegral_eq_sum_avoidWeight, avoidIntegral_eq_sum_avoidWeight,
    avoidIntegral_eq_sum_avoidWeight, real_avoidEvent_eq_sum_avoidWeight] at hone
  have hterm : ∑ K : Finset V,
        (condMean H T F (↑K : Set V) * condMean H T G (↑K : Set V)) * avoidWeight H S T K
      ≤ ∑ K : Finset V, condMean H T (fun C D => F C D * G C D) (↑K : Set V) *
          avoidWeight H S T K :=
    Finset.sum_le_sum fun K _ =>
      mul_le_mul_of_nonneg_right (condMean_mul_le H T hF2 hG2 (↑K : Set V))
        (avoidWeight_nonneg H S T K)
  have hW : 0 ≤ ∑ K : Finset V, avoidWeight H S T K :=
    Finset.sum_nonneg fun K _ => avoidWeight_nonneg H S T K
  calc (∑ K : Finset V, condMean H T F (↑K : Set V) * avoidWeight H S T K) *
        ∑ K : Finset V, condMean H T G (↑K : Set V) * avoidWeight H S T K
      ≤ (∑ K : Finset V,
            (condMean H T F (↑K : Set V) * condMean H T G (↑K : Set V)) * avoidWeight H S T K) *
          ∑ K : Finset V, avoidWeight H S T K := hone
    _ ≤ (∑ K : Finset V, condMean H T (fun C D => F C D * G C D) (↑K : Set V) *
            avoidWeight H S T K) * ∑ K : Finset V, avoidWeight H S T K :=
        mul_le_mul_of_nonneg_right hterm hW
    _ = _ := mul_comm _ _

/-- **The statement.**  Conditionally on the cluster of `S` avoiding `T`, a functional increasing
in the cluster of `S` and a functional decreasing in the cluster of `T` are positively associated.
The case of `avoid_twoCluster_le` where each of the two functionals ignores one of the two
clusters. [cite: VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9))] -/
theorem avoid_cluster_association [Fintype V] [Fintype E] (H : Hypergraph V E) (S T : Set V)
    (hOne : OneClusterInequality H S T) {F G : Set V → ℝ} (hF : Monotone F) (hG : Antitone G) :
    (∫ ω in avoidEvent H S T, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) *
      (∫ ω in avoidEvent H S T, G (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      ≤ (prodBernoulli H.prob).real (avoidEvent H S T) *
        ∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) * G (hyperClusterSet H ω T) ∂(prodBernoulli H.prob) :=
  avoid_twoCluster_le H S T hOne (F := fun C _ => F C) (G := fun _ D => G D)
    (fun _ => hF) (fun _ => antitone_const) (fun _ => monotone_const) (fun _ => hG)

/-- **The two clusters are negatively correlated.**  Conditionally on the cluster of `S` avoiding
`T`, an increasing functional of the cluster of `S` and an increasing functional of the cluster of
`T` are negatively correlated: `avoid_cluster_association` applied to the second functional with
the opposite sign.  [cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7)] -/
theorem avoid_cluster_negCorrelation [Fintype V] [Fintype E] (H : Hypergraph V E) (S T : Set V)
    (hOne : OneClusterInequality H S T) {F G : Set V → ℝ} (hF : Monotone F) (hG : Monotone G) :
    (prodBernoulli H.prob).real (avoidEvent H S T) *
        (∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) * G (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      ≤ (∫ ω in avoidEvent H S T, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) *
        ∫ ω in avoidEvent H S T, G (hyperClusterSet H ω T) ∂(prodBernoulli H.prob) := by
  have key := avoid_cluster_association H S T hOne (F := F) (G := fun D => -G D) hF
    (fun _ _ hab => neg_le_neg (hG hab))
  simp only [mul_neg, integral_neg] at key
  linarith

end KNAll.Site

end
