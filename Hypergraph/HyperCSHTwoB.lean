import Hypergraph.HyperCTOne
import Hypergraph.HyperCSHDefs
import Hypergraph.HyperTransfer
import Hypergraph.HyperCSHTwoA

/-!
# Layer two of the correlation core, for hyperedges: the covariance and hull-port half

The hyperedge port of seven modules of the bond development:
`Percolation/Continuity/CovTau/StarNReal.lean`,
`Percolation/Continuity/CovTau/A2Star.lean`,
`Percolation/Continuity/CovTau/A2Push.lean`,
`Percolation/Continuity/HullPort/TAStep.lean`,
`Percolation/Continuity/HullPort/SelectionThreeTA.lean`,
`Percolation/Continuity/HullPort/TASections.lean` and
`Percolation/Continuity/HullPort/TACond.lean`.

Everything is stated for a `Hypergraph V E` with arbitrary incidence sets over arbitrary types,
finiteness being assumed only where it is used.  The functionals are those of
`KN/HyperCTBase.lean` (`delE`, `cut`, `avoidEv`, `taC`, `taN`, `taNW`, `taB`, `taA`, `tab`,
`taa`, `taQ`), the restricted model is that of `KN/HyperOneCluster.lean` (`labelsIn`, `rCluster`,
`rAvoid`, `rTrace`) with `rest` of `KN/HyperCTOne.lean`, and the conditional expectation `cE` is
that of `KN/HyperCTBase.lean`.

## The `cE` calculus (`StarNReal`)

`cE_mul_of_splice_invariant` and `cE_cE`.  The bond `ED_congr_on` and `ED_sub` are Mathlib's
`integral_congr_ae` and `integral_sub` here; the bond `nr_eq_ite` reads the event `{v ↔ N}` off
the open EDGE cluster of `v`, and its hyperedge form `nr_eq_indMem` reads it off the vertex
cluster of `N`.  The bond file cites the decision-tree Harris inequality for real functions in
prose only; it is `treeHarris_real_general` of `KN/HyperTreeHK.lean`.

## The star decomposition (`A2Star`)

`reach_split`, `rCluster_restrict_source`, `rest_restrict`, `rest_sdiff_meeting`, `setStep_sum`:
van den Berg–Häggström–Kahn's identity (6) for a functional of the world `U ∖ C_N` left after the
cluster of a source SET `N ⊇ Z` is deleted.  The record of the exposed labels is the vertex trace
`rTrace` of `KN/HyperOneCluster.lean`, and the one place hyperedges differ from edges is the walk
splitting: a label crossed by a walk can meet `Z` at a vertex other than the two it joins, and then
it is not a label of the model on `U ∖ Z`; such a label is exposed, and the vertex it reaches lies
in the trace, which is where the walk restarts.

## The law of the record (`A2Push`)

The bond file proves that the law of BHK's neighbour set `S ⊆ U ∖ Z` is a PRODUCT law on `Set V`
and pushes the four functionals forward to it.  That statement is false for hyperedges:
`exists_rTrace_law_not_product` exhibits one label incident to three vertices whose trace has no
product law at all.  The mechanism is the one named in `KN/HyperLabelled.lean`: the bond proof
runs an induction over the vertices `u ∈ U ∖ Z`, whose stars `{s(u, z) : z ∈ Z}` are pairwise
disjoint blocks of coordinates because the map `(u, z) ↦ s(u, z)` is injective, and a label
incident to two outside vertices breaks the disjointness.  What survives, and what the four
functions step downstream has to consume, is the law of the LABEL record: `sum_weight_inter`
pushes the product weight forward along `ω ↦ ω ∩ A` to the product weight with the parameters off
`A` switched off, and `sum_weight_rTrace` reads the trace off that record.  So at the measure
transfer the label indexing is forced, through the injectivity that the bond argument uses
silently; the four functions step itself is indifferent, as `KN/HyperLabelled.lean` records.

## The one-label Bernstein step and Lemma 2 (`TAStep`)

`bernstein_step`, `bernstein_step_degenerate` (pure algebra, unchanged), `avoidEv_insert_insert_eq`,
`ind_inter_compl`, and `lemma2_avoidance`, which is `real_avoid_conn_not_conn` of
`KN/HyperCTOne.lean` for the cluster of `y`; the bond statement carries the nondegeneracy `s ≠ y`
because the conditional association theorem it invokes does, and the hyperedge theorem does not.

## The averaged inequality and marker dominance with an avoided set (`SelectionThreeTA`)

The bond theorem `markerDominanceAvoid_of_TA` has two halves: a pointwise comparison, for each
configuration of the cluster of `X`, of the integrand of the averaged inequality `T_A ≥ 0` with the
integrand of the reduction theorem's hypothesis, and the reduction theorem itself,
`BHK2006_clusterConditionalCov_nonneg_of_within_of_forall_nondegenerate` of
`Percolation/Literature/TwoClusterGibbsCovariance.lean`, the two-block Gibbs sampler of van den
Berg–Häggström–Kahn's §2.1.  The first half is ported: `markerDominance_cut` is the `X = ∅` marker
dominance lemma in the model with the labels meeting the cluster of `X` deleted, and
`R1_nonneg_of_taQ_nonneg` integrates it against the configuration of that cluster.  The second half
has no hyperedge form in this development: the Gibbs sampler of
`Percolation/Literature/TwoClusterGibbsSampler.lean` is written for pairs, and its hyperedge form
needs the uniform minorization by the event that every label incident to the second block is
closed.  That is the obstruction, and `markerDominanceAvoid_of_TA` is not stated here.

## The one-label sections (`TASections`)

`sum_weight_resample` and `sum_weight_mul_comp_sdiff_singleton_of_zero` mention no graph and are
unchanged.  The bond section identities deform ONE EDGE `{x₀, v}` with `x₀ ∈ X`, and the open
endpoint of the deformation is the state "`v` added to `X`".  A label `e` with `x₀ ∈ X` incident to
it has several other vertices, and opening it adds ALL of them: the open endpoint is the state
`X ∪ H.incidence e` (`reachable_insert_label_iff`, `insert_mem_avoidEv_iff`, `cut_insert_label`,
`section_generic`, `taB_section`, `taA_section`, `avoid_conn_section`, `taa_section`,
`tab_section`).  The parameter vector with the label switched off is carried by `withProb` of
`KN/HyperTransfer.lean`.

## Conditioning on the cluster of the avoided set and step (II) (`TACond`)

`set_sum_cond_sdiff` (BHK's Lemma 2.4: given the cluster of `X`, the configuration off the labels
meeting it is fresh; the cluster event is determined by those labels by `determinedBy_clusterEvent`
of `KN/HyperImplA.lean`), `cut_insert_vertex`, `mem_avoidEv_insert_iff`, `delE_union`, the
reading of the functionals at `X ∪ {v}` in the configuration with the cut of `X` deleted, and step
(II) `taB_insert_le`.  The bond `cut_insert_vertex` reads the cluster of `v` off the edge cluster
through the Gibbs-sampler bookkeeping `setCl_eq_sdiff_barOf`; here the cluster of `v` off the cut
of `X` is compared with its cluster in `ω` through `hyperClusterSet_off_subset` of
`KN/HyperCSHDefs.lean` and monotonicity.

## Where the two facts about label indexing were needed

The four functions step (the induction of `MetaA2`, a later layer) is not in this file.  Of the
steps here, `setStep_sum` and `set_sum_cond_sdiff` are block-Fubini identities and are indifferent
to the indexing: both carry the vertex record.  The measure transfer `sum_weight_rTrace` is the one
step where the label indexing is forced, and `exists_rTrace_law_not_product` is the proof that it
is.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Struct. Alg. 29 (2006), §1 identity (6), Thm. 1.3,
  §2.1 Lemma 2.4.
* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), Thm. 3.2.
* G. Kozma, S. Nitzan, *Kozma–Nitzan Conjecture 1*.
-/

noncomputable section

namespace KNAll.Site.CSHTwoB

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.CTBase KNAll.Site.CTOne KNAll.Site.CSHDefs
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open Percolation.Literature.BHK2006 (weight weight_nonneg blockFubini ind_inter ind_le_one
  integral_prodBernoulli_eq_sum)
open scoped Classical

variable {V E : Type*}

/-! ## The `cE` calculus

The bond `StarNReal.lean` records four facts about the weighted-cube expectation `ED` and the
conditional expectation `cE` along the exploration.  `ED_congr_on` and `ED_sub` are, for the
integral `cE` of `KN/HyperCTBase.lean`, the congruence and subtraction rules of the Bochner
integral; the two pull-out rules are stated below.
-/

section CECalc

variable [Fintype E]

omit [Fintype E] in
/-- The bond `ED_congr_on`: expectations of pointwise equal functions agree. -/
theorem integral_congr_of_forall (μ : Measure (Set E)) {φ ψ : Set E → ℝ}
    (h : ∀ ω, φ ω = ψ ω) : ∫ ω, φ ω ∂μ = ∫ ω, ψ ω ∂μ :=
  integral_congr_ae (Filter.Eventually.of_forall h)

/-- The bond `ED_sub`: differences. -/
theorem integral_sub_of_fintype (μ : Measure (Set E)) [IsFiniteMeasure μ] (φ ψ : Set E → ℝ) :
    ∫ ω, (φ ω - ψ ω) ∂μ = (∫ ω, φ ω ∂μ) - ∫ ω, ψ ω ∂μ :=
  integral_sub (integrable_of_fintype _) (integrable_of_fintype _)

omit [Fintype E] in
/-- **Pull-out of a splice-invariant factor** (the bond `cE_mul_of_local_on`): a factor which does
not change when the labels the exploration did not query are resampled comes out of the
conditional expectation at that configuration. -/
theorem cE_mul_of_splice_invariant (H : Hypergraph V E) (S : Set V) {Z : Set E → ℝ} {ω : Set E}
    (hZ : ∀ η : Set E, Z (spliceRecord (recordAt H S ω) η) = Z ω) (f : Set E → ℝ) :
    cE H S (fun ν => Z ν * f ν) ω = Z ω * cE H S f ω := by
  show (∫ η, Z (spliceRecord (recordAt H S ω) η) * f (spliceRecord (recordAt H S ω) η)
      ∂(prodBernoulli H.prob)) = _
  simp only [hZ]
  exact integral_const_mul _ _

/-- **The conditional expectation is idempotent** (the bond `cE_cE`): `cE f` is read off the
record, so it is its own conditional expectation. -/
theorem cE_cE (H : Hypergraph V E) (S : Set V) (f : Set E → ℝ) (ω : Set E) :
    cE H S (cE H S f) ω = cE H S f ω :=
  cE_eq_self_of_recordDetermined H S (fun _ _ h => cE_congr H S f h) ω

end CECalc

/-- The indicator of `{v ↔ N}`: some vertex of `N` is joined to `v`.  The bond `nr`. -/
def nr (H : Hypergraph V E) (N : Set V) (v : V) (ω : Set E) : ℝ :=
  ind {ω : Set E | ∃ s ∈ N, (openHyperGraph H ω).Reachable s v} ω

/-- `{v ↔ N}` read on the vertex cluster of `N`: the bond `nr_eq_ite`, which reads it on the open
EDGE cluster of `v`. -/
theorem nr_eq_indMem (H : Hypergraph V E) (N : Set V) (v : V) (ω : Set E) :
    nr H N v ω = AGBase.indMem v (hyperClusterSet H ω N) := by
  unfold nr AGBase.indMem
  by_cases h : ∃ s ∈ N, (openHyperGraph H ω).Reachable s v
  · rw [ind_of_mem (show ω ∈ {ω : Set E | ∃ s ∈ N, (openHyperGraph H ω).Reachable s v} from h),
      if_pos (show v ∈ hyperClusterSet H ω N from h)]
  · rw [ind_of_not_mem
      (show ω ∉ {ω : Set E | ∃ s ∈ N, (openHyperGraph H ω).Reachable s v} from h),
      if_neg (show v ∉ hyperClusterSet H ω N from h)]

/-- `0 ≤ nr ≤ 1`. -/
theorem nr_nonneg_le_one (H : Hypergraph V E) (N : Set V) (v : V) (ω : Set E) :
    0 ≤ nr H N v ω ∧ nr H N v ω ≤ 1 :=
  ⟨ind_nonneg _ _, ind_le_one _ _⟩

/-! ## The star decomposition of the world functionals

The cluster of a source set `N ⊇ Z` in the model on `U` splits at `Z`: it is `Z` together with the
cluster, in the model on `U ∖ Z`, of the sources outside `Z` and the vertices of the trace.
-/

section Star

/-- **Walk splitting.**  An open walk inside `U` from `y` to `c ∉ Z` either crosses no label
meeting `Z`, in which case `y ∉ Z` and the walk lies in the model on `U ∖ Z`, or has a last label
meeting `Z`, after which it starts at a vertex of the trace and stays in the model on `U ∖ Z`.
The bond `reach_split` splits at the last vertex of `Z`; here a label can meet `Z` at a vertex
the walk does not visit, so the split is at the last label meeting `Z`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem reach_split {H : Hypergraph V E} {U Z : Finset V} {ω : Set E} {y c : V}
    (h : (openHyperGraph H (ω ∩ labelsIn H U)).Reachable y c) (hc : c ∉ (↑Z : Set V)) :
    (y ∉ (↑Z : Set V) ∧ (openHyperGraph H (ω ∩ labelsIn H (U \ Z))).Reachable y c) ∨
      ∃ n ∈ rTrace H U Z ω, (openHyperGraph H (ω ∩ labelsIn H (U \ Z))).Reachable n c := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl ⟨hc, SimpleGraph.Reachable.refl y⟩
  | @tail b c hyb hbc ih =>
    obtain ⟨hne, e, ⟨heω, heU⟩, hbe, hce⟩ := (openHyperGraph_adj_iff H _ b c).1 hbc
    by_cases hmeet : e ∈ labelsMeeting H (↑Z : Set V)
    · refine Or.inr ⟨c, ?_, SimpleGraph.Reachable.refl c⟩
      exact (mem_traceOutside_iff H (↑Z) _ c).2 ⟨e, ⟨⟨heω, heU⟩, hmeet⟩, hce, hc⟩
    · have hdisj : Disjoint (H.incidence e) (↑Z : Set V) := by
        by_contra hcon
        exact hmeet hcon
      have heUZ : e ∈ labelsIn H (U \ Z) := fun v hv =>
        Finset.mem_sdiff.2 ⟨heU v hv, fun hvZ =>
          Set.disjoint_left.1 hdisj hv (Finset.mem_coe.2 hvZ)⟩
      have hadj : (openHyperGraph H (ω ∩ labelsIn H (U \ Z))).Adj b c :=
        (openHyperGraph_adj_iff H _ b c).2 ⟨hne, e, ⟨heω, heUZ⟩, hbe, hce⟩
      have hbZ : b ∉ (↑Z : Set V) := fun hb => Set.disjoint_left.1 hdisj hbe hb
      rcases ih hbZ with ⟨hyZ, hr⟩ | ⟨n, hn, hr⟩
      · exact Or.inl ⟨hyZ, hr.trans hadj.reachable⟩
      · exact Or.inr ⟨n, hn, hr.trans hadj.reachable⟩

/-- **The cluster of a source set splits at `Z ⊆ N`**: `C^U_N = Z ∪ C^{U∖Z}_{(N ∖ Z) ∪ T(ω)}`,
`T` the trace.  The bond `sC_restrict`, without its hypothesis `Z ⊆ U`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem rCluster_restrict_source (H : Hypergraph V E) {U Z : Finset V} {N : Set V}
    (hZN : (↑Z : Set V) ⊆ N) (ω : Set E) :
    rCluster H U N ω = ↑Z ∪ rCluster H (U \ Z) ((N \ ↑Z) ∪ rTrace H U Z ω) ω := by
  ext u
  constructor
  · rintro ⟨y, hyN, hr⟩
    by_cases hu : u ∈ (↑Z : Set V)
    · exact Or.inl hu
    · rcases reach_split hr hu with ⟨hyZ, hr'⟩ | ⟨n, hn, hr'⟩
      · exact Or.inr ⟨y, Or.inl ⟨hyN, hyZ⟩, hr'⟩
      · exact Or.inr ⟨n, Or.inr hn, hr'⟩
  · rintro (hu | ⟨y, hy, hr⟩)
    · exact subset_rCluster H U N ω (hZN hu)
    · have hr' : (openHyperGraph H (ω ∩ labelsIn H U)).Reachable y u :=
        hr.mono (openHyperGraph_le_of_subset H
          (Set.inter_subset_inter_right _ (labelsIn_mono H Finset.sdiff_subset)))
      rcases hy with ⟨hyN, -⟩ | hyT
      · exact ⟨y, hyN, hr'⟩
      · obtain ⟨e, ⟨⟨heω, heU⟩, hmeet⟩, hye, hyZ⟩ := (mem_traceOutside_iff H (↑Z) _ y).1 hyT
        obtain ⟨z, hze, hzZ⟩ := Set.not_disjoint_iff.1 hmeet
        refine ⟨z, hZN hzZ, ?_⟩
        by_cases hzy : z = y
        · exact hzy ▸ hr'
        · exact ((openHyperGraph_adj_iff H (ω ∩ labelsIn H U) z y).2
            ⟨hzy, e, ⟨heω, heU⟩, hze, hye⟩).reachable.trans hr'

/-- Consequently `U ∖ C^U_N = (U ∖ Z) ∖ C^{U∖Z}_{(N∖Z) ∪ T(ω)}`.  The bond `rest_restrict`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem rest_restrict (H : Hypergraph V E) {U Z : Finset V} {N : Set V}
    (hZN : (↑Z : Set V) ⊆ N) (ω : Set E) :
    rest H U N ω = rest H (U \ Z) ((N \ ↑Z) ∪ rTrace H U Z ω) ω := by
  ext u
  rw [mem_rest, mem_rest, rCluster_restrict_source H hZN ω, Finset.mem_sdiff, Set.mem_union,
    Finset.mem_coe]
  tauto

/-- The worlds of the model on `U ∖ Z` do not depend on the labels meeting `Z`.  The bond
`rest_diff_meeting`; the cluster form is `rCluster_sdiff_meeting` of `KN/HyperOneCluster.lean`. -/
theorem rest_sdiff_meeting (H : Hypergraph V E) (U Z : Finset V) (M : Set V) (ω : Set E) :
    rest H (U \ Z) M (ω \ labelsMeeting H (↑Z : Set V)) = rest H (U \ Z) M ω := by
  ext u
  rw [mem_rest, mem_rest, rCluster_sdiff_meeting]

variable [Fintype E]

/-- **BHK's (6) for world functionals**: for `Z ⊆ N`, `x ∉ Z` and any
`G : Finset V → ℝ`,
`E[G(U ∖ C_N) ; x ↮ N] = Σ_ω weight(ω) · E'[G((U∖Z) ∖ C'_{(N∖Z) ∪ T(ω)}) ; x ↮ (N∖Z) ∪ T(ω)]`,
primes denoting the model on `U ∖ Z` with fresh variables.  The bond `setStep_sum`, with the
neighbour set replaced by the trace.  The record carried is the vertex trace: a block-Fubini
identity is indifferent to the indexing of the record.  The bond hypothesis `Z ⊆ U` is not needed:
the labels of the restricted model are those with every vertex in `U`, so a label meeting `Z` and
open in the model on `U` already places `Z` inside `U` wherever it matters.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem setStep_sum (H : Hypergraph V E) {U Z : Finset V} {x : V}
    (hx : x ∉ (↑Z : Set V)) {N : Set V} (hZN : (↑Z : Set V) ⊆ N) (w : E → ℝ)
    (hm : ∑ ω : Set E, weight w ω = 1) (G : Finset V → ℝ) :
    ∑ ω : Set E, weight w ω * (G (rest H U N ω) * ind (rAvoid H U ({x} : Set V) N) ω) =
      ∑ ω : Set E, weight w ω * ∑ ω' : Set E, weight w ω' *
        (G (rest H (U \ Z) ((N \ ↑Z) ∪ rTrace H U Z ω) ω') *
          ind (rAvoid H (U \ Z) ({x} : Set V) ((N \ ↑Z) ∪ rTrace H U Z ω)) ω') := by
  have hSZ : ∀ y ∈ ({x} : Set V), y ∉ (↑Z : Set V) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hx
  set A := labelsMeeting H (↑Z : Set V) with hA
  set Φ : Set E → Set E → ℝ := fun ζ η =>
    G (rest H (U \ Z) ((N \ ↑Z) ∪ rTrace H U Z ζ) η) *
      ind (rAvoid H (U \ Z) ({x} : Set V) ((N \ ↑Z) ∪ rTrace H U Z ζ)) η with hΦ
  have hind : ∀ (M : Set V) (η : Set E),
      ind (rAvoid H (U \ Z) ({x} : Set V) M) (η \ labelsMeeting H (↑Z : Set V))
        = ind (rAvoid H (U \ Z) ({x} : Set V) M) η := by
    intro M η
    by_cases h : η ∈ rAvoid H (U \ Z) ({x} : Set V) M
    · rw [ind_of_mem h, ind_of_mem ((mem_rAvoid_sdiff_meeting H U Z _ M η).2 h)]
    · rw [ind_of_not_mem h,
        ind_of_not_mem fun h' => h ((mem_rAvoid_sdiff_meeting H U Z _ M η).1 h')]
  have hind' : ∀ ω : Set E, ind (rAvoid H U ({x} : Set V) N) ω
      = ind (rAvoid H (U \ Z) ({x} : Set V) ((N \ ↑Z) ∪ rTrace H U Z ω)) ω := by
    intro ω
    by_cases h : ω ∈ rAvoid H U ({x} : Set V) N
    · rw [ind_of_mem h, ind_of_mem ((mem_rAvoid_iff_restrict hSZ hZN ω).1 h)]
    · rw [ind_of_not_mem h, ind_of_not_mem fun h' => h ((mem_rAvoid_iff_restrict hSZ hZN ω).2 h')]
  have h1 : ∀ ω : Set E, G (rest H U N ω) * ind (rAvoid H U ({x} : Set V) N) ω
      = Φ (ω ∩ A) (ω \ A) := by
    intro ω
    simp only [hΦ, hA, rTrace_inter_meeting, rest_sdiff_meeting, hind,
      ← rest_restrict H hZN, hind']
  have h2 : ∀ ω ω' : Set E, Φ (ω ∩ A) (ω' \ A) =
      G (rest H (U \ Z) ((N \ ↑Z) ∪ rTrace H U Z ω) ω') *
        ind (rAvoid H (U \ Z) ({x} : Set V) ((N \ ↑Z) ∪ rTrace H U Z ω)) ω' := by
    intro ω ω'
    simp only [hΦ, hA, rTrace_inter_meeting, rest_sdiff_meeting, hind]
  calc ∑ ω : Set E, weight w ω * (G (rest H U N ω) * ind (rAvoid H U ({x} : Set V) N) ω)
      = (∑ ω : Set E, weight w ω) * ∑ ω : Set E, weight w ω * Φ (ω ∩ A) (ω \ A) := by
        rw [hm, one_mul]; simp_rw [h1]
    _ = ∑ ω : Set E, weight w ω * ∑ ω' : Set E, weight w ω' * Φ (ω ∩ A) (ω' \ A) :=
        blockFubini w A Φ
    _ = _ := by simp_rw [h2]

end Star

/-! ## The law of the record is a product law on the labels

The bond `A2Push.lean` pushes the four functionals forward along the neighbour set `S(ω)` to a
product law on `Set V`.  Here the push-forward is along the label record `ω ∩ A`, whose law is the
product law with the parameters off `A` switched off; the trace is read off the record.
-/

section Push

variable [Fintype E]

/-- **The law of the label record is a product law**: for every `Γ : Set E → ℝ`,
`Σ_ω weight_w(ω) Γ(ω ∩ A) = Σ_η weight_{w_A}(η) Γ(η)`, `w_A = w` on `A` and `0` off `A`.  The
hyperedge form of the bond `sum_weight_rS`; the record is the set of exposed labels found open, not
the set of vertices they reach. -/
theorem sum_weight_inter (w : E → ℝ) (A : Set E) (Γ : Set E → ℝ) :
    ∑ ω : Set E, weight w ω * Γ (ω ∩ A)
      = ∑ η : Set E, weight (fun e => if e ∈ A then w e else 0) η * Γ η := by
  have h : ∀ ω : Set E, ω ∩ A = ω \ Aᶜ := fun ω => (Set.sdiff_compl).symm
  simp_rw [h]
  rw [sum_weight_mul_comp_sdiff w Aᶜ Γ]
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 2
  funext e
  by_cases he : e ∈ A
  · simp [he]
  · simp [he]

omit [Fintype E] in
/-- The parameters of the pushed-forward law lie in `[0, 1]`.  The bond `pZ_mem`. -/
theorem param_inter_mem {w : E → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (A : Set E)
    (e : E) : 0 ≤ (if e ∈ A then w e else 0) ∧ (if e ∈ A then w e else 0) ≤ 1 := by
  split_ifs
  · exact ⟨hw0 e, hw1 e⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- **The trace is read off the record**: for every `Γ : Set V → ℝ`,
`Σ_ω weight_w(ω) Γ(T(ω)) = Σ_η weight_{w_A}(η) Γ(T(η))` with `A` the labels meeting `Z`.  This is
the form in which a four functions step downstream can consume the trace: as a function on the
lattice `Set E` of label records, against a product weight. -/
theorem sum_weight_rTrace (H : Hypergraph V E) (w : E → ℝ) (U Z : Finset V) (Γ : Set V → ℝ) :
    ∑ ω : Set E, weight w ω * Γ (rTrace H U Z ω)
      = ∑ η : Set E, weight (fun e => if e ∈ labelsMeeting H (↑Z : Set V) then w e else 0) η *
          Γ (rTrace H U Z η) := by
  rw [← sum_weight_inter w (labelsMeeting H (↑Z : Set V)) (fun η => Γ (rTrace H U Z η))]
  simp only [rTrace_inter_meeting]

end Push

/-! ## The one-label Bernstein step and Lemma 2 -/

section TAStep

/-- **The identity (★) and the Bernstein step**: if `Q₀₀, Q₁₁ ≥ 0`, `B₀b₁ − B₁b₀ ≥ 0`,
`a₀b₁ − a₁b₀ ≥ 0` and `b₀, b₁ > 0`, then `Q(t) = A(t)b(t) − a(t)B(t) ≥ 0` for the affine
interpolations at `t ∈ [0,1]`, because `b₀b₁·MIX = b₁²Q₀₀ + b₀²Q₁₁ + (B₀b₁ − B₁b₀)(a₀b₁ − a₁b₀)`.
Pure algebra, unchanged from the bond `bernstein_step`. -/
theorem bernstein_step (A₀ A₁ B₀ B₁ a₀ a₁ b₀ b₁ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hQ0 : 0 ≤ A₀ * b₀ - a₀ * B₀) (hQ1 : 0 ≤ A₁ * b₁ - a₁ * B₁) (hΔ : 0 ≤ B₀ * b₁ - B₁ * b₀)
    (hL : 0 ≤ a₀ * b₁ - a₁ * b₀) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) :
    0 ≤ ((1 - t) * A₀ + t * A₁) * ((1 - t) * b₀ + t * b₁) -
      ((1 - t) * a₀ + t * a₁) * ((1 - t) * B₀ + t * B₁) := by
  have hstar : b₀ * b₁ * (A₀ * b₁ + A₁ * b₀ - a₀ * B₁ - a₁ * B₀) =
      b₁ ^ 2 * (A₀ * b₀ - a₀ * B₀) + b₀ ^ 2 * (A₁ * b₁ - a₁ * B₁) +
        (B₀ * b₁ - B₁ * b₀) * (a₀ * b₁ - a₁ * b₀) := by
    ring
  have hmix0 : 0 ≤ b₀ * b₁ * (A₀ * b₁ + A₁ * b₀ - a₀ * B₁ - a₁ * B₀) := by
    rw [hstar]
    have h1 := mul_nonneg (sq_nonneg b₁) hQ0
    have h2 := mul_nonneg (sq_nonneg b₀) hQ1
    have h3 := mul_nonneg hΔ hL
    linarith
  have hmix : 0 ≤ A₀ * b₁ + A₁ * b₀ - a₀ * B₁ - a₁ * B₀ :=
    (mul_nonneg_iff_of_pos_left (mul_pos hb₀ hb₁)).1 hmix0
  have hexp : ((1 - t) * A₀ + t * A₁) * ((1 - t) * b₀ + t * b₁) -
      ((1 - t) * a₀ + t * a₁) * ((1 - t) * B₀ + t * B₁) =
      (1 - t) ^ 2 * (A₀ * b₀ - a₀ * B₀) + t * (1 - t) * (A₀ * b₁ + A₁ * b₀ - a₀ * B₁ - a₁ * B₀) +
        t ^ 2 * (A₁ * b₁ - a₁ * B₁) := by
    ring
  rw [hexp]
  have h1t : 0 ≤ 1 - t := by linarith
  have k1 := mul_nonneg (sq_nonneg (1 - t)) hQ0
  have k2 := mul_nonneg (mul_nonneg ht0 h1t) hmix
  have k3 := mul_nonneg (sq_nonneg t) hQ1
  linarith

/-- Degenerate Bernstein step: if the `t = 1` endpoint vanishes identically then
`Q(t) = (1 − t)² Q₀₀ ≥ 0`.  Unchanged from the bond. -/
theorem bernstein_step_degenerate (A₀ A₁ B₀ B₁ a₀ a₁ b₀ b₁ t : ℝ)
    (hQ0 : 0 ≤ A₀ * b₀ - a₀ * B₀) (hA₁ : A₁ = 0) (hB₁ : B₁ = 0) (ha₁ : a₁ = 0) (hb₁ : b₁ = 0) :
    0 ≤ ((1 - t) * A₀ + t * A₁) * ((1 - t) * b₀ + t * b₁) -
      ((1 - t) * a₀ + t * a₁) * ((1 - t) * B₀ + t * B₁) := by
  subst hA₁ hB₁ ha₁ hb₁
  have hexp : ((1 - t) * A₀ + t * 0) * ((1 - t) * b₀ + t * 0) -
      ((1 - t) * a₀ + t * 0) * ((1 - t) * B₀ + t * 0) = (1 - t) ^ 2 * (A₀ * b₀ - a₀ * B₀) := by
    ring
  rw [hexp]
  exact mul_nonneg (sq_nonneg _) hQ0

/-- `{y ↮ s, v, X} = {y ↮ s, X} ∖ {y ↔ v}`. -/
theorem avoidEv_insert_insert_eq (H : Hypergraph V E) (s y v : V) (X : Set V) :
    avoidEv H y (insert s (insert v X)) = avoidEv H y (insert s X) ∩ (hyperConn H y v)ᶜ := by
  have h : insert s (insert v X) = insert s X ∪ {v} := by
    ext u
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  rw [avoidEv_eq, avoidEv_eq, h, avoidEvent_union, avoidEvent_singleton_eq_compl]

/-- `1_{E ∩ Fᶜ} = 1_E (1 − 1_F)`.  Unchanged from the bond. -/
theorem ind_inter_compl {α : Type*} (A B : Set α) (a : α) :
    ind (A ∩ Bᶜ) a = ind A a * (1 - ind B a) := by
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B
  · rw [ind_of_not_mem (fun h => h.2 hB), ind_of_mem hA, ind_of_mem hB]; ring
  · rw [ind_of_mem (Set.mem_inter hA hB), ind_of_mem hA, ind_of_not_mem hB]; ring
  · rw [ind_of_not_mem (fun h => hA h.1), ind_of_not_mem hA]; ring
  · rw [ind_of_not_mem (fun h => hA h.1), ind_of_not_mem hA]; ring

variable [Fintype V] [Fintype E]

/-- **Lemma 2 (avoidance monotonicity)**: `μ(y↔z | y↮s,X) ≥ μ(y↔z | y↮s,X,v)`, that is
`a₁ b₀ ≤ a₀ b₁` for the `y`-side masses at the states `X` and `X ∪ {v}`: conditionally on the
cluster of `y` avoiding `{s} ∪ X`, the connection `{y ↔ z}` and the non-connection `{y ↮ v}` are
negatively correlated.  This is `real_avoid_conn_not_conn` of `KN/HyperCTOne.lean` for the cluster
of `y`.  The bond statement assumes `s ≠ y`, which the hyperedge conditional association theorem
does not need.  [cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] -/
theorem lemma2_avoidance (H : Hypergraph V E) (s y z v : V) (X : Set V) :
    taa H s y z (insert v X) * tab H s y X ≤ taa H s y z X * tab H s y (insert v X) := by
  have key := real_avoid_conn_not_conn H y (insert s X) z v
  have e1 : taa H s y z (insert v X) = (prodBernoulli H.prob).real
      (avoidEvent H ({y} : Set V) (insert s X) ∩ (hyperConn H z y ∩ (hyperConn H v y)ᶜ)) := by
    unfold taa
    rw [avoidEv_insert_insert_eq, avoidEv_eq, hyperConn_comm H y z, hyperConn_comm H y v]
    congr 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  have e2 : tab H s y X = (prodBernoulli H.prob).real (avoidEvent H ({y} : Set V) (insert s X)) :=
    rfl
  have e3 : taa H s y z X = (prodBernoulli H.prob).real
      (avoidEvent H ({y} : Set V) (insert s X) ∩ hyperConn H z y) := by
    unfold taa
    rw [avoidEv_eq, hyperConn_comm H y z]
  have e4 : tab H s y (insert v X) = (prodBernoulli H.prob).real
      (avoidEvent H ({y} : Set V) (insert s X) ∩ (hyperConn H v y)ᶜ) := by
    unfold tab
    rw [avoidEv_insert_insert_eq, avoidEv_eq, hyperConn_comm H y v]
  rw [e1, e2, e3, e4]
  exact key

end TAStep

/-! ## Marker dominance with an avoided set, from the averaged inequality `T_A ≥ 0`

The chain of the bond `SelectionThreeTA.lean`: `T_A ≥ 0` ⟹ `R_1 ≥ 0` ⟹ MDL(X).  The second
implication is the reduction theorem `CSHTwoA.clusterCov_nonneg_of_within`; the first is the
`X = ∅` marker dominance lemma `markerDominance_noAvoid` of `KN/HyperCTBase.lean` applied, for
each configuration of the cluster of `X`, in the model with the labels meeting that cluster
deleted.
-/

section Selection

variable [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem hyperConn_deleteHyper (H : Hypergraph V E) (K : Set V) (x y : V) :
    hyperConn (deleteHyper H K) x y = hyperConn H x y := rfl

omit [Fintype V] [Fintype E] in
theorem hyperClusterSet_deleteHyper (H : Hypergraph V E) (K : Set V) (ω : Set E) (S : Set V) :
    hyperClusterSet (deleteHyper H K) ω S = hyperClusterSet H ω S := rfl

/-- **Marker dominance in the model with the cut of `X` deleted**: for a monotone `g` and every
configuration `ω`, `μ'(s ↮ y, y ↔ z)/μ'(s ↮ y) · Cov'(g(C_s), 1{s ↔ y}) ≤ Cov'(g(C_s), 1{s ↔ z})`,
primes denoting the model `H − cut_X(ω)`; when `μ'(s ↮ y) = 0` the left side is `0` and the right
side is nonnegative by Harris.  The per-configuration step of the bond
`markerDominanceAvoid_of_TA`. -/
theorem markerDominance_cut (H : Hypergraph V E) (s y z : V) (X : Set V) {g : Set V → ℝ}
    (hg : Monotone g) (ω : Set E) :
    taNW H s y z X ω / taN H s y X ω * taC H s y X g ω ≤ taC H s z X g ω := by
  have hd : ∀ φ : Set E → ℝ, delE H (cut H X ω) φ
      = ∫ ν, φ ν ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω X)).prob) :=
    fun φ => delE_cut_eq_integral_deleteHyper H X ω φ
  simp only [taNW, taN, taC, hd, AGBase.integral_ind, AGBase.integral_mul_ind]
  have mdl := markerDominance_noAvoid (deleteHyper H (hyperClusterSet H ω X)) s y z hg
  simp only [hyperConn_deleteHyper, hyperClusterSet_deleteHyper] at mdl
  have hgC : Monotone fun η : Set E => g (hyperClusterSet H η ({s} : Set V)) :=
    fun _ _ hle => hg (hyperClusterSet_mono H _ hle)
  have harris := integral_harris (deleteHyper H (hyperClusterSet H ω X)) hgC
    (monotone_ind_of_isUpperSet (isUpperSet_hyperConn H s z))
  rw [AGBase.integral_ind, AGBase.integral_mul_ind] at harris
  by_cases hN : (prodBernoulli (deleteHyper H (hyperClusterSet H ω X)).prob).real
      (hyperConn H s y)ᶜ = 0
  · rw [hN, div_zero, zero_mul]
    linarith
  · have hpos : 0 < (prodBernoulli (deleteHyper H (hyperClusterSet H ω X)).prob).real
        (hyperConn H s y)ᶜ := lt_of_le_of_ne measureReal_nonneg (Ne.symm hN)
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith

omit [Fintype V] in
/-- `T_A` as one integral against the indicator of `{s ↮ X}`: `Q = A·b − a·B` is
`∫ 1{s ↮ X}·(b·(taNW/taN)·c − a·c)`.  The bond `TA_integral_eq_taQ`, read at the functionals. -/
theorem taQ_eq_integral (H : Hypergraph V E) (s y z : V) (X : Set V) (g : Set V → ℝ) :
    taQ H s y z X g = ∫ ω, ind (avoidEv H s X) ω *
      (tab H s y X * (taNW H s y z X ω / taN H s y X ω * taC H s y X g ω) -
        taa H s y z X * taC H s y X g ω) ∂(prodBernoulli H.prob) := by
  unfold taQ taA taB
  rw [mul_comm, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (integrable_of_fintype _) (integrable_of_fintype _)]
  refine integral_congr_of_forall _ fun ω => ?_
  ring

/-- **`R_1 ≥ 0` from `T_A ≥ 0`**: the integrand of the reduction theorem's hypothesis dominates the
integrand of `T_A` configuration by configuration (`markerDominance_cut`), so
`0 ≤ ∫ 1{s ↮ X}·(b·Cov'(g, 1{s ↔ z}) − a·Cov'(g, 1{s ↔ y}))` whenever `0 ≤ taQ`. -/
theorem R1_nonneg_of_taQ_nonneg (H : Hypergraph V E) (s y z : V) (X : Set V) {g : Set V → ℝ}
    (hg : Monotone g) (hTA : 0 ≤ taQ H s y z X g) :
    0 ≤ ∫ ω, ind (avoidEv H s X) ω *
      (tab H s y X * taC H s z X g ω - taa H s y z X * taC H s y X g ω)
        ∂(prodBernoulli H.prob) := by
  rw [taQ_eq_integral] at hTA
  refine hTA.trans (integral_mono (integrable_of_fintype _) (integrable_of_fintype _)
    fun ω => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (ind_nonneg _ _)
  have htab0 : 0 ≤ tab H s y X := measureReal_nonneg
  have h := mul_le_mul_of_nonneg_left (markerDominance_cut H s y z X hg ω) htab0
  linarith

omit [Fintype V] [Fintype E] in
/-- The world mean of `KN/HyperCSHTwoA.lean` at an explored cluster is the deleted-labels mean at
the cut. -/
theorem worldMean_eq_delE (H : Hypergraph V E) (s : V) (g : Set V → ℝ) (X : Set V) (ω : Set E) :
    CSHTwoA.worldMean H s g (hyperClusterSet H ω X)
      = delE H (cut H X ω) (fun η => g (hyperClusterSet H η ({s} : Set V))) := rfl

omit [Fintype V] [Fintype E] in
/-- The world mean of `g · 1{u ∈ C}` is the deleted-labels mean of `g(C_s)·1{s ↔ u}`. -/
theorem worldMean_mul_indMem (H : Hypergraph V E) (s u : V) (g : Set V → ℝ) (X : Set V)
    (ω : Set E) :
    CSHTwoA.worldMean H s (fun C => g C * AGBase.indMem u C) (hyperClusterSet H ω X)
      = delE H (cut H X ω)
          (fun η => g (hyperClusterSet H η ({s} : Set V)) * ind (hyperConn H s u) η) := by
  show (∫ η, g (hyperClusterSet H (η \ labelsMeeting H (hyperClusterSet H ω X)) ({s} : Set V)) *
      AGBase.indMem u (hyperClusterSet H (η \ labelsMeeting H (hyperClusterSet H ω X))
        ({s} : Set V)) ∂(prodBernoulli H.prob)) = _
  simp only [AGBase.indMem_hyperClusterSet, hyperConn_comm H u s]
  rfl

omit [Fintype V] [Fintype E] in
theorem worldMean_indMem (H : Hypergraph V E) (s u : V) (X : Set V) (ω : Set E) :
    CSHTwoA.worldMean H s (AGBase.indMem u) (hyperClusterSet H ω X)
      = delE H (cut H X ω) (fun η => ind (hyperConn H s u) η) := by
  show (∫ η, AGBase.indMem u (hyperClusterSet H (η \ labelsMeeting H (hyperClusterSet H ω X))
      ({s} : Set V)) ∂(prodBernoulli H.prob)) = _
  simp only [AGBase.indMem_hyperClusterSet, hyperConn_comm H u s]
  rfl

/-- The test function of the reduction: `h(C) = b·1{z ∈ C} − a·1{y ∈ C}`, with
`b = μ(y ↮ s, X)` and `a = μ(y ↮ s, X, y ↔ z)`. -/
def testFun (H : Hypergraph V E) (s y z : V) (X : Set V) : Set V → ℝ :=
  fun C => tab H s y X * AGBase.indMem z C - taa H s y z X * AGBase.indMem y C

omit [Fintype V] in
/-- The world covariance of `g` with the test function is the combination of the two marker
covariances `c` of the functionals, configuration by configuration. -/
theorem worldCov_testFun (H : Hypergraph V E) (s y z : V) (X : Set V) (g : Set V → ℝ)
    (ω : Set E) :
    CSHTwoA.worldMean H s (fun C => g C * testFun H s y z X C) (hyperClusterSet H ω X) -
        CSHTwoA.worldMean H s g (hyperClusterSet H ω X) *
          CSHTwoA.worldMean H s (testFun H s y z X) (hyperClusterSet H ω X)
      = tab H s y X * taC H s z X g ω - taa H s y z X * taC H s y X g ω := by
  have hlin : ∀ (φ₁ φ₂ : Set V → ℝ) (a b : ℝ),
      CSHTwoA.worldMean H s (fun C => a * φ₁ C - b * φ₂ C) (hyperClusterSet H ω X)
        = a * CSHTwoA.worldMean H s φ₁ (hyperClusterSet H ω X) -
          b * CSHTwoA.worldMean H s φ₂ (hyperClusterSet H ω X) := by
    intro φ₁ φ₂ a b
    unfold CSHTwoA.worldMean
    rw [integral_sub (integrable_of_fintype _) (integrable_of_fintype _), integral_const_mul,
      integral_const_mul]
  have h1 : (fun C => g C * testFun H s y z X C)
      = fun C => tab H s y X * (g C * AGBase.indMem z C) -
          taa H s y z X * (g C * AGBase.indMem y C) := by
    funext C
    unfold testFun
    ring
  rw [h1, hlin, show testFun H s y z X
      = fun C => tab H s y X * AGBase.indMem z C - taa H s y z X * AGBase.indMem y C from rfl,
    hlin, worldMean_mul_indMem, worldMean_mul_indMem, worldMean_indMem, worldMean_indMem,
    worldMean_eq_delE]
  unfold taC
  ring

/-- **MDL(X) from `T_A ≥ 0`.**  For an owner `s`, a marker `z`, an avoided set `X` every label
meeting which has `p_e < 1`, `D = {s ↮ X}`, `A = {y ↮ s, X}`, `W = {y ↔ z}`, `Y = {s ↔ y}`,
`Z = {s ↔ z}`: if the averaged inequality `T_A ≥ 0` holds for every monotone nonnegative `g`, then
for every monotone `F` of the vertex cluster of `s`,
`μ(A ∩ W)·[μ(D)∫_{D∩Y} F − (∫_D F) μ(D∩Y)] ≤ μ(A)·[μ(D)∫_{D∩Z} F − (∫_D F) μ(D∩Z)]`.

Proof: the reduction theorem `CSHTwoA.clusterCov_nonneg_of_within` with the test function
`h = μ(A)·1{z ∈ C} − μ(A∩W)·1{y ∈ C}`; its hypothesis is, configuration by configuration,
`μ(A)·Cov'(g,1_Z) − μ(A∩W)·Cov'(g,1_Y) ≥ (μ(A) μ'(N∩W)/μ'(N) − μ(A∩W))·Cov'(g,1_Y)` under the
deleted labels, which is `markerDominance_cut`.  The bond template quantifies `T_A ≥ 0` over all
non-degenerate weights and reaches arbitrary weights by continuity inside its reduction theorem;
the hyperedge reduction is stated at one model, so the hypothesis is asked at that model and the
non-degeneracy is carried explicitly.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6), §2.1 pp. 10–13] -/
theorem markerDominanceAvoid_of_TA (H : Hypergraph V E) (s y z : V) (X : Set V)
    (hX : ∀ e ∈ labelsMeeting H X, (H.prob e : ℝ) < 1)
    (hTA : ∀ g : Set V → ℝ, Monotone g → (∀ C, 0 ≤ g C) → 0 ≤ taQ H s y z X g)
    {F : Set V → ℝ} (hF : Monotone F) :
    (prodBernoulli H.prob).real (avoidEv H y (insert s X) ∩ hyperConn H y z) *
        ((prodBernoulli H.prob).real (avoidEv H s X) *
            (∫ ω in avoidEv H s X ∩ hyperConn H s y, F (hyperClusterSet H ω ({s} : Set V))
              ∂(prodBernoulli H.prob)) -
          (∫ ω in avoidEv H s X, F (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob)) *
            (prodBernoulli H.prob).real (avoidEv H s X ∩ hyperConn H s y))
      ≤ (prodBernoulli H.prob).real (avoidEv H y (insert s X)) *
        ((prodBernoulli H.prob).real (avoidEv H s X) *
            (∫ ω in avoidEv H s X ∩ hyperConn H s z, F (hyperClusterSet H ω ({s} : Set V))
              ∂(prodBernoulli H.prob)) -
          (∫ ω in avoidEv H s X, F (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob)) *
            (prodBernoulli H.prob).real (avoidEv H s X ∩ hyperConn H s z)) := by
  -- the reduction theorem at the test function
  have main := CSHTwoA.clusterCov_nonneg_of_within H s X hX (testFun H s y z X)
    (fun g hg hg0 => by
      have h := R1_nonneg_of_taQ_nonneg H s y z X hg (hTA g hg hg0)
      rw [← avoidEv_eq, CSHTwoA.setIntegral_eq_integral_ind_mul]
      refine h.trans (le_of_eq (integral_congr_of_forall _ fun ω => ?_))
      rw [worldCov_testFun]) hF
  unfold CSHTwoA.covDF at main
  have hpt : ∀ ω : Set E, testFun H s y z X (hyperClusterSet H ω ({s} : Set V))
      = tab H s y X * ind (hyperConn H s z) ω - taa H s y z X * ind (hyperConn H s y) ω := by
    intro ω
    unfold testFun
    rw [AGBase.indMem_hyperClusterSet, AGBase.indMem_hyperClusterSet, hyperConn_comm H z s,
      hyperConn_comm H y s]
  simp only [hpt] at main
  rw [← avoidEv_eq] at main
  have e1 : (∫ ω in avoidEv H s X, F (hyperClusterSet H ω ({s} : Set V)) *
        (tab H s y X * ind (hyperConn H s z) ω - taa H s y z X * ind (hyperConn H s y) ω)
        ∂(prodBernoulli H.prob))
      = tab H s y X * (∫ ω in avoidEv H s X ∩ hyperConn H s z,
            F (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob)) -
        taa H s y z X * (∫ ω in avoidEv H s X ∩ hyperConn H s y,
            F (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob)) := by
    rw [← AGBase.setIntegral_mul_ind, ← AGBase.setIntegral_mul_ind, ← integral_const_mul,
      ← integral_const_mul, ← integral_sub (integrable_of_fintype _) (integrable_of_fintype _)]
    refine integral_congr_of_forall _ fun ω => ?_
    ring
  have e2 : (∫ ω in avoidEv H s X,
        (tab H s y X * ind (hyperConn H s z) ω - taa H s y z X * ind (hyperConn H s y) ω)
        ∂(prodBernoulli H.prob))
      = tab H s y X * (prodBernoulli H.prob).real (avoidEv H s X ∩ hyperConn H s z) -
        taa H s y z X * (prodBernoulli H.prob).real (avoidEv H s X ∩ hyperConn H s y) := by
    rw [← AGBase.setIntegral_ind, ← AGBase.setIntegral_ind, ← integral_const_mul,
      ← integral_const_mul, ← integral_sub (integrable_of_fintype _) (integrable_of_fintype _)]
  rw [e1, e2] at main
  have htab : tab H s y X = (prodBernoulli H.prob).real (avoidEv H y (insert s X)) := rfl
  have htaa : taa H s y z X
      = (prodBernoulli H.prob).real (avoidEv H y (insert s X) ∩ hyperConn H y z) := rfl
  rw [htab, htaa] at main
  linarith [main]

end Selection

/-! ## The one-label sections of the `T_A` functionals -/

section Resample

variable {ι : Type*} [Fintype ι]

/-- **One-coordinate resampling**: `Σ_η weight(w) η F(η) = Σ_η weight(w₀) η [(1 − w e) F(η ∖ {e}) +
(w e) F(η ∪ {e})]` whenever `w₀ = w` off `e` and `w₀ e = 0`.  Unchanged from the bond. -/
theorem sum_weight_resample (w w₀ : ι → ℝ) (e : ι) (he0 : w₀ e = 0)
    (hoff : ∀ i, i ≠ e → w₀ i = w i) (F : Set ι → ℝ) :
    ∑ η, weight w η * F η
      = ∑ η, weight w₀ η * ((1 - w e) * F (η \ {e}) + w e * F (insert e η)) := by
  classical
  set R : Set ι → ℝ := fun η => ∏ i ∈ Finset.univ.erase e, (if i ∈ η then w i else 1 - w i)
    with hR
  have hfac : ∀ η : Set ι, weight w η = (if e ∈ η then w e else 1 - w e) * R η := fun η =>
    (Finset.mul_prod_erase Finset.univ (fun i => if i ∈ η then w i else 1 - w i)
      (Finset.mem_univ e)).symm
  have hfac₀ : ∀ η : Set ι, weight w₀ η = (if e ∈ η then 0 else 1) * R η := by
    intro η
    have h := (Finset.mul_prod_erase Finset.univ (fun i => if i ∈ η then w₀ i else 1 - w₀ i)
      (Finset.mem_univ e)).symm
    have hRe : ∏ i ∈ Finset.univ.erase e, (if i ∈ η then w₀ i else 1 - w₀ i) = R η := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hie : i ≠ e := Finset.ne_of_mem_erase hi
      simp only [hoff i hie]
    rw [hRe, he0] at h
    rw [show weight w₀ η = ∏ i, (if i ∈ η then w₀ i else 1 - w₀ i) from rfl, h]
    split_ifs <;> ring
  have hRins : ∀ η : Set ι, R (insert e η) = R η := fun η =>
    Finset.prod_congr rfl fun i hi => by
      have hie : i ≠ e := Finset.ne_of_mem_erase hi
      simp only [Set.mem_insert_iff, hie, false_or]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun η : Set ι => e ∈ η),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun η : Set ι => e ∈ η)
      (fun η => weight w₀ η * ((1 - w e) * F (η \ {e}) + w e * F (insert e η)))]
  have hzero : ∑ η ∈ Finset.univ.filter (fun η : Set ι => e ∈ η),
      weight w₀ η * ((1 - w e) * F (η \ {e}) + w e * F (insert e η)) = 0 := by
    refine Finset.sum_eq_zero fun η hη => ?_
    have he : e ∈ η := (Finset.mem_filter.1 hη).2
    rw [hfac₀ η, if_pos he]; ring
  have hreidx : ∑ η ∈ Finset.univ.filter (fun η : Set ι => e ∈ η), weight w η * F η =
      ∑ η ∈ Finset.univ.filter (fun η : Set ι => ¬ e ∈ η),
        weight w (insert e η) * F (insert e η) := by
    refine Finset.sum_nbij' (fun η => η \ {e}) (fun η => insert e η) ?_ ?_ ?_ ?_ ?_
    · intro η hη
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
        Set.mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true]
    · intro η hη
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_insert_iff, true_or]
    · intro η hη
      have he : e ∈ η := (Finset.mem_filter.1 hη).2
      simp only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem he]
    · intro η hη
      have he : e ∉ η := (Finset.mem_filter.1 hη).2
      show insert e η \ {e} = η
      rw [← Set.union_singleton, Set.union_sdiff_right, Set.sdiff_singleton_eq_self he]
    · intro η hη
      have he : e ∈ η := (Finset.mem_filter.1 hη).2
      simp only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem he]
  rw [hreidx, hzero, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun η hη => ?_
  have he : e ∉ η := (Finset.mem_filter.1 hη).2
  rw [hfac (insert e η), hfac η, hfac₀ η, hRins η, if_pos (Set.mem_insert e η), if_neg he,
    if_neg he, Set.sdiff_singleton_eq_self he]
  ring

/-- Deleting a coordinate of weight `0` changes nothing.  Unchanged from the bond. -/
theorem sum_weight_mul_comp_sdiff_singleton_of_zero (w₀ : ι → ℝ) (e : ι) (he0 : w₀ e = 0)
    (φ : Set ι → ℝ) : ∑ η, weight w₀ η * φ (η \ {e}) = ∑ η, weight w₀ η * φ η := by
  classical
  refine Finset.sum_congr rfl fun η _ => ?_
  by_cases he : e ∈ η
  · have h0 : weight w₀ η = 0 := by
      have h := (Finset.mul_prod_erase Finset.univ (fun i => if i ∈ η then w₀ i else 1 - w₀ i)
        (Finset.mem_univ e)).symm
      rw [show weight w₀ η = ∏ i, (if i ∈ η then w₀ i else 1 - w₀ i) from rfl, h, if_pos he,
        he0, zero_mul]
    rw [h0, zero_mul, zero_mul]
  · rw [Set.sdiff_singleton_eq_self he]

end Resample

section Sections

/-! ### Combinatorics of one added label `e` with a vertex `x₀ ∈ X` -/

/-- **One extra label.**  Reachability in the open graph of `insert e ω`: either `x ↔ y` already
in `ω`, or `x` reaches a vertex of `e` and a vertex of `e` reaches `y`, both in `ω`.  The bond
`reachable_insert_iff` names the two endpoints of the extra edge; a label has an incidence set
instead. -/
theorem reachable_insert_label_iff (H : Hypergraph V E) (ω : Set E) (e : E) (x y : V) :
    (openHyperGraph H (insert e ω)).Reachable x y ↔
      (openHyperGraph H ω).Reachable x y ∨
        ((∃ a ∈ H.incidence e, (openHyperGraph H ω).Reachable x a) ∧
          ∃ b ∈ H.incidence e, (openHyperGraph H ω).Reachable b y) := by
  constructor
  · intro hxy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
    induction hxy with
    | refl => exact Or.inl (SimpleGraph.Reachable.refl x)
    | @tail b c _ hbc ih =>
      obtain ⟨hne, e', he', hbe', hce'⟩ := (openHyperGraph_adj_iff H _ b c).1 hbc
      rcases Set.mem_insert_iff.1 he' with rfl | hω
      · rcases ih with h | ⟨ha, -⟩
        · exact Or.inr ⟨⟨b, hbe', h⟩, c, hce', SimpleGraph.Reachable.refl c⟩
        · exact Or.inr ⟨ha, c, hce', SimpleGraph.Reachable.refl c⟩
      · have hadj : (openHyperGraph H ω).Adj b c :=
          (openHyperGraph_adj_iff H ω b c).2 ⟨hne, e', hω, hbe', hce'⟩
        rcases ih with h | ⟨ha, b', hb', hb'b⟩
        · exact Or.inl (h.trans hadj.reachable)
        · exact Or.inr ⟨ha, b', hb', hb'b.trans hadj.reachable⟩
  · rintro (h | ⟨⟨a, ha, hxa⟩, b, hb, hby⟩)
    · exact h.mono (openHyperGraph_le_of_subset H (Set.subset_insert e ω))
    · have hle := openHyperGraph_le_of_subset H (Set.subset_insert e ω)
      have hab : (openHyperGraph H (insert e ω)).Reachable a b := by
        by_cases hab : a = b
        · exact hab ▸ SimpleGraph.Reachable.refl a
        · exact ((openHyperGraph_adj_iff H (insert e ω) a b).2
            ⟨hab, e, Set.mem_insert e ω, ha, hb⟩).reachable
      exact (hxa.mono hle).trans (hab.trans (hby.mono hle))

/-- Adding a label incident to `x₀ ∈ T`: `r ↮ T` afterwards iff `r ↮ T ∪ inc(e)` before.  The
bond `insert_mem_avoidEv_iff`, with the second endpoint `v` replaced by the whole incidence set. -/
theorem insert_mem_avoidEv_iff (H : Hypergraph V E) (r x₀ : V) (e : E) (T : Set V) (hx₀T : x₀ ∈ T)
    (hx₀e : x₀ ∈ H.incidence e) (ω : Set E) :
    insert e ω ∈ avoidEv H r T ↔ ω ∈ avoidEv H r (T ∪ H.incidence e) := by
  rw [avoidEv_eq, avoidEv_eq, mem_avoidEvent_singleton, mem_avoidEvent_singleton]
  constructor
  · intro h t ht hrt
    rcases ht with htT | hte
    · exact h t htT (hrt.mono (openHyperGraph_le_of_subset H (Set.subset_insert e ω)))
    · exact h x₀ hx₀T ((reachable_insert_label_iff H ω e r x₀).2
        (Or.inr ⟨⟨t, hte, hrt⟩, x₀, hx₀e, SimpleGraph.Reachable.refl x₀⟩))
  · intro h t ht hrt
    rcases (reachable_insert_label_iff H ω e r t).1 hrt with h1 | ⟨⟨a, ha, hra⟩, -⟩
    · exact h t (Or.inl ht) h1
    · exact h a (Or.inr ha) hra

/-- Adding a label incident to `x₀ ∈ X`: the cluster of `X` afterwards is the cluster of
`X ∪ inc(e)` before. -/
theorem hyperClusterSet_insert_label (H : Hypergraph V E) (X : Set V) (e : E) (x₀ : V)
    (hx₀X : x₀ ∈ X) (hx₀e : x₀ ∈ H.incidence e) (ω : Set E) :
    hyperClusterSet H (insert e ω) X = hyperClusterSet H ω (X ∪ H.incidence e) := by
  ext u
  constructor
  · rintro ⟨x, hx, hxu⟩
    rcases (reachable_insert_label_iff H ω e x u).1 hxu with h1 | ⟨-, b, hb, hbu⟩
    · exact ⟨x, Or.inl hx, h1⟩
    · exact ⟨b, Or.inr hb, hbu⟩
  · rintro ⟨y, hy, hyu⟩
    have hle := openHyperGraph_le_of_subset H (Set.subset_insert e ω)
    rcases hy with hyX | hye
    · exact ⟨y, hyX, hyu.mono hle⟩
    · refine ⟨x₀, hx₀X, ?_⟩
      have h0y : (openHyperGraph H (insert e ω)).Reachable x₀ y := by
        by_cases hxy : x₀ = y
        · exact hxy ▸ SimpleGraph.Reachable.refl x₀
        · exact ((openHyperGraph_adj_iff H (insert e ω) x₀ y).2
            ⟨hxy, e, Set.mem_insert e ω, hx₀e, hye⟩).reachable
      exact h0y.trans (hyu.mono hle)

/-- Adding a label incident to `x₀ ∈ X`: the cut of `X` afterwards is the cut of `X ∪ inc(e)`
before.  The bond `cut_insert_edge`. -/
theorem cut_insert_label (H : Hypergraph V E) (X : Set V) (e : E) (x₀ : V) (hx₀X : x₀ ∈ X)
    (hx₀e : x₀ ∈ H.incidence e) (ω : Set E) :
    cut H X (insert e ω) = cut H (X ∪ H.incidence e) ω := by
  rw [cut_eq, cut_eq, hyperClusterSet_insert_label H X e x₀ hx₀X hx₀e ω]

/-- On `{r ↮ T ∪ inc(e)}`, adding the label `e` does not change the connections of `r`. -/
theorem reachable_insert_label_iff_of_avoid (H : Hypergraph V E) (r : V) (e : E) (T : Set V)
    (z : V) (ω : Set E) (hω : ω ∈ avoidEv H r (T ∪ H.incidence e)) :
    (openHyperGraph H (insert e ω)).Reachable r z ↔ (openHyperGraph H ω).Reachable r z := by
  rw [avoidEv_eq, mem_avoidEvent_singleton] at hω
  constructor
  · intro h
    rcases (reachable_insert_label_iff H ω e r z).1 h with h1 | ⟨⟨a, ha, hra⟩, -⟩
    · exact h1
    · exact absurd hra (hω a (Or.inr ha))
  · exact fun h => h.mono (openHyperGraph_le_of_subset H (Set.subset_insert e ω))

/-- A label incident to a vertex of `X` lies in every cut of `X`.  The bond `edge_mem_cut`. -/
theorem label_mem_cut (H : Hypergraph V E) (X : Set V) (e : E) (x₀ : V) (hx₀X : x₀ ∈ X)
    (hx₀e : x₀ ∈ H.incidence e) (ω : Set E) : e ∈ cut H X ω := by
  rw [cut_eq, mem_labelsMeeting]
  exact Set.not_disjoint_iff.2 ⟨x₀, hx₀e, subset_hyperClusterSet H ω X hx₀X⟩

/-- The cut and the avoidance events do not see the label probabilities. -/
theorem cut_withProb (H : Hypergraph V E) (p : E → unitInterval) (X : Set V) (ω : Set E) :
    cut (withProb H p) X ω = cut H X ω := rfl

theorem avoidEv_withProb (H : Hypergraph V E) (p : E → unitInterval) (r : V) (T : Set V) :
    avoidEv (withProb H p) r T = avoidEv H r T := rfl

variable [Fintype E]

/-- A deleted-labels expectation does not see the probabilities of the deleted labels.  The bond
`delE_congr_of_mem`. -/
theorem delE_congr_of_prob {H H' : Hypergraph V E} {B : Set E}
    (h : ∀ e ∉ B, H.prob e = H'.prob e) (φ : Set E → ℝ) : delE H B φ = delE H' B φ := by
  simp only [delE]
  rw [integral_comp_sdiff_prodBernoulli H.prob B φ, integral_comp_sdiff_prodBernoulli H'.prob B φ]
  congr 2
  funext e
  by_cases he : e ∈ B
  · simp only [if_pos he]
  · simp only [if_neg he, h e he]

/-! ### The section identities

The label `e` has `x₀ ∈ X` among its vertices; `p₀` is the parameter vector with `e` switched
off.  Opening `e` adds all of `inc(e)` to the avoided set.
-/

/-- Generic section identity: for a functional `∫ 1_{D_X}·Φ(p, cut_X ω)` whose integrand depends
on `ω` only through the cut and on the parameters only off the cut,
`F_X(p) = (1 − p_e) F_X(p₀) + p_e F_{X ∪ inc(e)}(p₀)`.  The bond `section_generic`. -/
theorem section_generic (H : Hypergraph V E) (p₀ : E → unitInterval) (s x₀ : V) (e : E)
    (X : Set V) (hx₀X : x₀ ∈ X) (hx₀e : x₀ ∈ H.incidence e) (he0 : p₀ e = 0)
    (hoff : ∀ f, f ≠ e → p₀ f = H.prob f) (Φ : (E → unitInterval) → Set E → ℝ)
    (hΦ : ∀ (p p' : E → unitInterval) (B : Set E), (∀ f ∉ B, p f = p' f) → Φ p B = Φ p' B) :
    ∫ ω, ind (avoidEv H s X) ω * Φ H.prob (cut H X ω) ∂(prodBernoulli H.prob) =
      (1 - (H.prob e : ℝ)) *
          ∫ ω, ind (avoidEv H s X) ω * Φ p₀ (cut H X ω) ∂(prodBernoulli p₀) +
        (H.prob e : ℝ) * ∫ ω, ind (avoidEv H s (X ∪ H.incidence e)) ω *
          Φ p₀ (cut H (X ∪ H.incidence e) ω) ∂(prodBernoulli p₀) := by
  have hΦw : ∀ (Y : Set V) (ω : Set E), x₀ ∈ Y → Φ H.prob (cut H Y ω) = Φ p₀ (cut H Y ω) := by
    intro Y ω hY
    refine hΦ H.prob p₀ (cut H Y ω) fun f hf => ?_
    have hfe : f ≠ e := fun h => hf (h ▸ label_mem_cut H Y e x₀ hY hx₀e ω)
    rw [hoff f hfe]
  have he0' : (fun f => (p₀ f : ℝ)) e = 0 := by simp [he0]
  have hoff' : ∀ f, f ≠ e → (fun f => (p₀ f : ℝ)) f = (fun f => (H.prob f : ℝ)) f := by
    intro f hf
    simp only [hoff f hf]
  rw [integral_prodBernoulli_eq_sum, integral_prodBernoulli_eq_sum, integral_prodBernoulli_eq_sum,
    sum_weight_resample (fun f => (H.prob f : ℝ)) (fun f => (p₀ f : ℝ)) e he0' hoff']
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · have h1 := sum_weight_mul_comp_sdiff_singleton_of_zero (fun f => (p₀ f : ℝ)) e he0'
      (fun ζ => (1 - (H.prob e : ℝ)) * (ind (avoidEv H s X) ζ * Φ H.prob (cut H X ζ)))
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [hΦw X _ hx₀X]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    have hD : ind (avoidEv H s X) (insert e η) = ind (avoidEv H s (X ∪ H.incidence e)) η := by
      by_cases h : insert e η ∈ avoidEv H s X
      · rw [ind_of_mem h, ind_of_mem ((insert_mem_avoidEv_iff H s x₀ e X hx₀X hx₀e η).1 h)]
      · rw [ind_of_not_mem h,
          ind_of_not_mem fun h' => h ((insert_mem_avoidEv_iff H s x₀ e X hx₀X hx₀e η).2 h')]
    rw [hD, cut_insert_label H X e x₀ hx₀X hx₀e η, hΦw (X ∪ H.incidence e) η (Or.inl hx₀X)]
    ring

/-- **Section identity for `B`**: `B_X(p) = (1 − p_e) B_X(p₀) + p_e B_{X ∪ inc(e)}(p₀)`. -/
theorem taB_section (H : Hypergraph V E) (p₀ : E → unitInterval) (s y x₀ : V) (e : E) (X : Set V)
    (hx₀X : x₀ ∈ X) (hx₀e : x₀ ∈ H.incidence e) (he0 : p₀ e = 0)
    (hoff : ∀ f, f ≠ e → p₀ f = H.prob f) (g : Set V → ℝ) :
    taB H s y X g = (1 - (H.prob e : ℝ)) * taB (withProb H p₀) s y X g +
      (H.prob e : ℝ) * taB (withProb H p₀) s y (X ∪ H.incidence e) g := by
  have key := section_generic H p₀ s x₀ e X hx₀X hx₀e he0 hoff
    (fun p B => delE (withProb H p) B
        (fun η => g (hyperClusterSet H η ({s} : Set V)) * ind (hyperConn H s y) η) -
      delE (withProb H p) B (fun η => g (hyperClusterSet H η ({s} : Set V))) *
        delE (withProb H p) B (fun η => ind (hyperConn H s y) η))
    (fun p p' B h => by
      simp only [delE_congr_of_prob (H := withProb H p) (H' := withProb H p') (B := B) h])
  simpa only [taB, taC, cut_withProb, avoidEv_withProb, hyperClusterSet_withProb,
    hyperConn_withProb, withProb_prob, withProb_self] using key

/-- **Section identity for `A`**. -/
theorem taA_section (H : Hypergraph V E) (p₀ : E → unitInterval) (s y z x₀ : V) (e : E)
    (X : Set V) (hx₀X : x₀ ∈ X) (hx₀e : x₀ ∈ H.incidence e) (he0 : p₀ e = 0)
    (hoff : ∀ f, f ≠ e → p₀ f = H.prob f) (g : Set V → ℝ) :
    taA H s y z X g = (1 - (H.prob e : ℝ)) * taA (withProb H p₀) s y z X g +
      (H.prob e : ℝ) * taA (withProb H p₀) s y z (X ∪ H.incidence e) g := by
  have key := section_generic H p₀ s x₀ e X hx₀X hx₀e he0 hoff
    (fun p B => delE (withProb H p) B
          (fun η => ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η) /
        delE (withProb H p) B (fun η => ind (hyperConn H s y)ᶜ η) *
      (delE (withProb H p) B
          (fun η => g (hyperClusterSet H η ({s} : Set V)) * ind (hyperConn H s y) η) -
        delE (withProb H p) B (fun η => g (hyperClusterSet H η ({s} : Set V))) *
          delE (withProb H p) B (fun η => ind (hyperConn H s y) η)))
    (fun p p' B h => by
      simp only [delE_congr_of_prob (H := withProb H p) (H' := withProb H p') (B := B) h])
  simpa only [taA, taC, taN, taNW, cut_withProb, avoidEv_withProb, hyperClusterSet_withProb,
    hyperConn_withProb, withProb_prob, withProb_self] using key

/-- Section identity for an event of the root `y` avoiding `T ∋ x₀`, intersected with a
connection of `y`:
`μ_p(y ↮ T, y ↔ z) = (1 − p_e) μ_{p₀}(y ↮ T, y ↔ z) + p_e μ_{p₀}(y ↮ T ∪ inc(e), y ↔ z)`. -/
theorem avoid_conn_section (H : Hypergraph V E) (p₀ : E → unitInterval) (y z x₀ : V) (e : E)
    (T : Set V) (hx₀T : x₀ ∈ T) (hx₀e : x₀ ∈ H.incidence e) (he0 : p₀ e = 0)
    (hoff : ∀ f, f ≠ e → p₀ f = H.prob f) :
    (prodBernoulli H.prob).real (avoidEv H y T ∩ hyperConn H y z) =
      (1 - (H.prob e : ℝ)) * (prodBernoulli p₀).real (avoidEv H y T ∩ hyperConn H y z) +
        (H.prob e : ℝ) *
          (prodBernoulli p₀).real (avoidEv H y (T ∪ H.incidence e) ∩ hyperConn H y z) := by
  have he0' : (fun f => (p₀ f : ℝ)) e = 0 := by simp [he0]
  have hoff' : ∀ f, f ≠ e → (fun f => (p₀ f : ℝ)) f = (fun f => (H.prob f : ℝ)) f := by
    intro f hf
    simp only [hoff f hf]
  rw [prodBernoulli_real_eq_sum, prodBernoulli_real_eq_sum, prodBernoulli_real_eq_sum,
    sum_weight_resample (fun f => (H.prob f : ℝ)) (fun f => (p₀ f : ℝ)) e he0' hoff']
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · have h1 := sum_weight_mul_comp_sdiff_singleton_of_zero (fun f => (p₀ f : ℝ)) e he0'
      (fun ζ => (1 - (H.prob e : ℝ)) * ind (avoidEv H y T ∩ hyperConn H y z) ζ)
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    have hD : ind (avoidEv H y T ∩ hyperConn H y z) (insert e η) =
        ind (avoidEv H y (T ∪ H.incidence e) ∩ hyperConn H y z) η := by
      by_cases h : η ∈ avoidEv H y (T ∪ H.incidence e)
      · have h' : insert e η ∈ avoidEv H y T :=
          (insert_mem_avoidEv_iff H y x₀ e T hx₀T hx₀e η).2 h
        have hz : insert e η ∈ hyperConn H y z ↔ η ∈ hyperConn H y z :=
          reachable_insert_label_iff_of_avoid H y e T z η h
        by_cases hzz : η ∈ hyperConn H y z
        · rw [ind_of_mem (Set.mem_inter h' (hz.2 hzz)), ind_of_mem (Set.mem_inter h hzz)]
        · rw [ind_of_not_mem fun hh => hzz (hz.1 hh.2), ind_of_not_mem fun hh => hzz hh.2]
      · have h' : insert e η ∉ avoidEv H y T :=
          fun hh => h ((insert_mem_avoidEv_iff H y x₀ e T hx₀T hx₀e η).1 hh)
        rw [ind_of_not_mem fun hh => h' hh.1, ind_of_not_mem fun hh => h hh.1]
    rw [hD]
    ring

/-- **Section identity for `a`**. -/
theorem taa_section (H : Hypergraph V E) (p₀ : E → unitInterval) (s y z x₀ : V) (e : E)
    (X : Set V) (hx₀X : x₀ ∈ X) (hx₀e : x₀ ∈ H.incidence e) (he0 : p₀ e = 0)
    (hoff : ∀ f, f ≠ e → p₀ f = H.prob f) :
    taa H s y z X = (1 - (H.prob e : ℝ)) * taa (withProb H p₀) s y z X +
      (H.prob e : ℝ) * taa (withProb H p₀) s y z (X ∪ H.incidence e) := by
  have key := avoid_conn_section H p₀ y z x₀ e (insert s X) (Set.mem_insert_of_mem _ hx₀X) hx₀e
    he0 hoff
  rw [Set.insert_union] at key
  simpa only [taa, avoidEv_withProb, hyperConn_withProb, withProb_prob] using key

/-- **Section identity for `b`**. -/
theorem tab_section (H : Hypergraph V E) (p₀ : E → unitInterval) (s y x₀ : V) (e : E)
    (X : Set V) (hx₀X : x₀ ∈ X) (hx₀e : x₀ ∈ H.incidence e) (he0 : p₀ e = 0)
    (hoff : ∀ f, f ≠ e → p₀ f = H.prob f) :
    tab H s y X = (1 - (H.prob e : ℝ)) * tab (withProb H p₀) s y X +
      (H.prob e : ℝ) * tab (withProb H p₀) s y (X ∪ H.incidence e) := by
  have key := avoid_conn_section H p₀ y y x₀ e (insert s X) (Set.mem_insert_of_mem _ hx₀X) hx₀e
    he0 hoff
  rw [Set.insert_union] at key
  have hyy : ∀ T : Set V, avoidEv H y T ∩ hyperConn H y y = avoidEv H y T := by
    intro T
    ext ω
    simp only [Set.mem_inter_iff, and_iff_left_iff_imp]
    exact fun _ => SimpleGraph.Reachable.refl _
  simp only [hyy] at key
  simpa only [tab, avoidEv_withProb, withProb_prob] using key

end Sections

/-! ## Conditioning on the cluster of the avoided set, and step (II) -/

section Cond

variable [Fintype V] [Fintype E]

/-- **Conditioning on `C_X`** (van den Berg–Häggström–Kahn's Lemma 2.4 for a vertex set `X` and an
arbitrary kernel): given `{C_X = W}`, the configuration off the labels meeting `W` is a fresh
product configuration.  The cluster event is determined by the labels meeting `W`
(`determinedBy_clusterEvent` of `KN/HyperImplA.lean`), and the rest is block Fubini.  The bond
`set_sum_cond_sdiff`.  [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10)] -/
theorem set_sum_cond_sdiff (H : Hypergraph V E) (w : E → ℝ) (hm : ∑ ω : Set E, weight w ω = 1)
    (X : Set V) (K : Set V → Set E → ℝ) :
    ∑ ω : Set E, weight w ω * K (hyperClusterSet H ω X) (ω \ cut H X ω) =
      ∑ ω : Set E, weight w ω *
        ∑ η : Set E, weight w η * K (hyperClusterSet H ω X) (η \ cut H X ω) := by
  have hsd : ∀ (A ω : Set E), (ω \ A) \ A = ω \ A := fun A ω => by
    rw [Set.sdiff_sdiff, Set.union_self]
  have hdet : ∀ (W : Set V) (ω : Set E),
      hyperClusterSet H (ω ∩ labelsMeeting H W) X = W ↔ hyperClusterSet H ω X = W := by
    intro W ω
    have h := (determinedBy_iff _ _).1 (determinedBy_clusterEvent H X W)
      (ω ∩ labelsMeeting H W) ω (by rw [Set.inter_assoc, Set.inter_self])
    exact h
  have key : ∀ W : Set V,
      ∑ ω : Set E, (if hyperClusterSet H ω X = W then
          weight w ω * K W (ω \ labelsMeeting H W) else 0) =
      ∑ ω : Set E, (if hyperClusterSet H ω X = W then
          weight w ω * ∑ η : Set E, weight w η * K W (η \ labelsMeeting H W) else 0) := by
    intro W
    set A : Set E := labelsMeeting H W with hA
    set Φ : Set E → Set E → ℝ := fun ζ η =>
      if hyperClusterSet H ζ X = W then K W (η \ A) else 0 with hΦ
    have h1 : ∀ ω : Set E, (if hyperClusterSet H ω X = W then weight w ω * K W (ω \ A) else 0)
        = weight w ω * Φ (ω ∩ A) (ω \ A) := by
      intro ω
      simp only [hΦ, hA, hdet]
      split_ifs with hW
      · rw [← hA, hsd]
      · rw [mul_zero]
    have h2 : ∀ ω : Set E, weight w ω * ∑ ω' : Set E, weight w ω' * Φ (ω ∩ A) (ω' \ A) =
        (if hyperClusterSet H ω X = W then
          weight w ω * ∑ η : Set E, weight w η * K W (η \ A) else 0) := by
      intro ω
      simp only [hΦ, hA, hdet]
      split_ifs with hW
      · rw [← hA]
        refine congrArg (weight w ω * ·) (Finset.sum_congr rfl fun η _ => ?_)
        rw [hsd]
      · simp
    calc ∑ ω : Set E, (if hyperClusterSet H ω X = W then weight w ω * K W (ω \ A) else 0)
        = (∑ ω : Set E, weight w ω) * ∑ ω : Set E, weight w ω * Φ (ω ∩ A) (ω \ A) := by
          rw [hm, one_mul]; exact Finset.sum_congr rfl fun ω _ => h1 ω
      _ = ∑ ω : Set E, weight w ω * ∑ ω' : Set E, weight w ω' * Φ (ω ∩ A) (ω' \ A) :=
          blockFubini w A Φ
      _ = _ := Finset.sum_congr rfl fun ω _ => h2 ω
  calc ∑ ω : Set E, weight w ω * K (hyperClusterSet H ω X) (ω \ cut H X ω)
      = ∑ ω : Set E, ∑ W : Set V, (if hyperClusterSet H ω X = W then
          weight w ω * K W (ω \ labelsMeeting H W) else 0) :=
        Finset.sum_congr rfl fun ω _ =>
          (Fintype.sum_ite_eq (hyperClusterSet H ω X)
            fun W => weight w ω * K W (ω \ labelsMeeting H W)).symm
    _ = ∑ W : Set V, ∑ ω : Set E, (if hyperClusterSet H ω X = W then
          weight w ω * K W (ω \ labelsMeeting H W) else 0) := Finset.sum_comm
    _ = ∑ W : Set V, ∑ ω : Set E, (if hyperClusterSet H ω X = W then
          weight w ω * ∑ η : Set E, weight w η * K W (η \ labelsMeeting H W) else 0) :=
        Finset.sum_congr rfl fun W _ => key W
    _ = ∑ ω : Set E, ∑ W : Set V, (if hyperClusterSet H ω X = W then
          weight w ω * ∑ η : Set E, weight w η * K W (η \ labelsMeeting H W) else 0) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun ω _ =>
        Fintype.sum_ite_eq (hyperClusterSet H ω X)
          fun W => weight w ω * ∑ η : Set E, weight w η * K W (η \ labelsMeeting H W)

omit [Fintype V] [Fintype E] in
/-- `C_{X ∪ Y} = C_X ∪ C_Y`. -/
theorem hyperClusterSet_union (H : Hypergraph V E) (ω : Set E) (X Y : Set V) :
    hyperClusterSet H ω (X ∪ Y) = hyperClusterSet H ω X ∪ hyperClusterSet H ω Y := by
  ext u
  constructor
  · rintro ⟨x, hx | hx, hr⟩
    · exact Or.inl ⟨x, hx, hr⟩
    · exact Or.inr ⟨x, hx, hr⟩
  · rintro (⟨x, hx, hr⟩ | ⟨x, hx, hr⟩)
    · exact ⟨x, Or.inl hx, hr⟩
    · exact ⟨x, Or.inr hx, hr⟩

omit [Fintype V] [Fintype E] in
/-- The labels meeting a union. -/
theorem labelsMeeting_union (H : Hypergraph V E) (K L : Set V) :
    labelsMeeting H (K ∪ L) = labelsMeeting H K ∪ labelsMeeting H L := by
  ext e
  simp only [mem_labelsMeeting, Set.mem_union, Set.disjoint_union_right, not_and_or]

omit [Fintype V] [Fintype E] in
/-- **Adding a vertex to the avoided set**: the cut of `X ∪ {v}` is the cut of `X` together with
the cut of `{v}` in the configuration with the cut of `X` deleted.  The bond `cut_insert_vertex`
reads the cluster of `v` off the edge cluster through the Gibbs-sampler bookkeeping; here the
cluster of `v` off the cut of `X` is compared with its cluster in `ω` through
`hyperClusterSet_off_subset` of `KN/HyperCSHDefs.lean` and monotonicity. -/
theorem cut_insert_vertex (H : Hypergraph V E) (X : Set V) (v : V) (ω : Set E) :
    cut H (insert v X) ω = cut H X ω ∪ cut H ({v} : Set V) (ω \ cut H X ω) := by
  have hins : insert v X = X ∪ {v} := by
    ext u
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  by_cases hv : v ∈ hyperClusterSet H ω X
  · -- `v` lies in the cluster of `X`: both sides are the cut of `X`
    have h1 : hyperClusterSet H ω (insert v X) = hyperClusterSet H ω X := by
      rw [hins, hyperClusterSet_union]
      refine Set.union_eq_left.2 ?_
      rintro u ⟨x, hx, hr⟩
      rw [Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨x', hx', hr'⟩ := hv
      exact ⟨x', hx', hr'.trans hr⟩
    -- `v` is isolated off the cut of `X`
    have hiso : ∀ c, (openHyperGraph H (ω \ cut H X ω)).Reachable v c → c = v := by
      intro c hvc
      rw [SimpleGraph.reachable_iff_reflTransGen] at hvc
      induction hvc with
      | refl => rfl
      | @tail b c _ hbc ih =>
        subst ih
        obtain ⟨-, e, ⟨-, hnot⟩, hbe, -⟩ := (openHyperGraph_adj_iff H _ b c).1 hbc
        exact absurd (by
          rw [cut_eq, mem_labelsMeeting]
          exact Set.not_disjoint_iff.2 ⟨b, hbe, hv⟩) hnot
    have h2 : cut H ({v} : Set V) (ω \ cut H X ω) ⊆ cut H X ω := by
      intro e he
      rw [cut_eq, mem_labelsMeeting] at he ⊢
      obtain ⟨u, hue, t, ht, htu⟩ := Set.not_disjoint_iff.1 he
      rw [Set.mem_singleton_iff] at ht
      subst ht
      have huv := hiso u htu
      subst huv
      exact Set.not_disjoint_iff.2 ⟨u, hue, hv⟩
    show labelsMeeting H (hyperClusterSet H ω (insert v X)) = _
    rw [h1]
    exact (Set.union_eq_left.2 h2).symm
  · -- `v ∉ C_X`: the cluster of `v` lives off the cut of `X`
    have havoid : ∀ x ∈ X, ¬ (openHyperGraph H ω).Reachable v x :=
      fun x hx hr => hv ⟨x, hx, hr.symm⟩
    have hcl : hyperClusterSet H ω ({v} : Set V)
        = hyperClusterSet H (ω \ cut H X ω) ({v} : Set V) :=
      Set.Subset.antisymm (hyperClusterSet_off_subset H v X (subset_refl ω) havoid)
        (hyperClusterSet_mono H _ Set.sdiff_subset)
    show labelsMeeting H (hyperClusterSet H ω (insert v X))
      = labelsMeeting H (hyperClusterSet H ω X) ∪
        labelsMeeting H (hyperClusterSet H (ω \ cut H X ω) ({v} : Set V))
    rw [hins, hyperClusterSet_union, labelsMeeting_union, ← hcl]

omit [Fintype V] [Fintype E] in
/-- On `{s ↮ X}`: `s ↮ X ∪ {v}` iff `s ↮ v` in the configuration with the cut of `X` deleted. -/
theorem mem_avoidEv_insert_iff (H : Hypergraph V E) (s v : V) (X : Set V) (ω : Set E)
    (hω : ω ∈ avoidEv H s X) :
    ω ∈ avoidEv H s (insert v X) ↔ ω \ cut H X ω ∈ avoidEv H s ({v} : Set V) := by
  rw [avoidEv_eq, mem_avoidEvent_singleton] at hω
  rw [avoidEv_eq, avoidEv_eq, mem_avoidEvent_singleton, mem_avoidEvent_singleton]
  have hreach : ∀ t, (openHyperGraph H ω).Reachable s t ↔
      (openHyperGraph H (ω \ cut H X ω)).Reachable s t := fun t =>
    ⟨fun h => reachable_lift_of_avoid H (subset_refl ω) hω h,
      fun h => h.mono (openHyperGraph_le_of_subset H Set.sdiff_subset)⟩
  constructor
  · intro h t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    rw [← hreach]
    exact h t (Set.mem_insert _ _)
  · intro h t ht
    rcases Set.mem_insert_iff.1 ht with rfl | ht
    · rw [hreach]
      exact h t rfl
    · exact hω t ht

omit [Fintype V] in
/-- **Deleting in two stages**: `E_p[φ(η ∖ (B ∪ B'))] = E_{p_B}[φ(η ∖ B')]` whenever `p_B = p` off
`B` and `p_B = 0` on `B`.  The bond `delE_union`. -/
theorem delE_union (H : Hypergraph V E) (pB : E → unitInterval) (B B' : Set E)
    (hB : ∀ e ∈ B, pB e = 0) (hoff : ∀ e ∉ B, pB e = H.prob e) (φ : Set E → ℝ) :
    delE H (B ∪ B') φ = delE (withProb H pB) B' φ := by
  have hfun : (fun i => if i ∈ B then (0 : unitInterval) else H.prob i) = pB := by
    funext i
    by_cases hi : i ∈ B
    · rw [if_pos hi, hB i hi]
    · rw [if_neg hi, hoff i hi]
  simp only [delE, withProb_prob]
  have h1 : ∀ η : Set E, η \ (B ∪ B') = (η \ B) \ B' := fun η => by rw [Set.sdiff_sdiff]
  simp only [h1]
  rw [integral_comp_sdiff_prodBernoulli H.prob B (fun ζ => φ (ζ \ B')), hfun]

omit [Fintype V] in
/-- `E_p[φ(η ∖ B)] = E_{p_B}[φ]`. -/
theorem delE_eq_delE_empty (H : Hypergraph V E) (pB : E → unitInterval) (B : Set E)
    (hB : ∀ e ∈ B, pB e = 0) (hoff : ∀ e ∉ B, pB e = H.prob e) (φ : Set E → ℝ) :
    delE H B φ = delE (withProb H pB) ∅ φ := by
  have := delE_union H pB B ∅ hB hoff φ
  rwa [Set.union_empty] at this

omit [Fintype V] [Fintype E] in
/-- The cut of the empty avoided set is empty. -/
theorem cut_empty (H : Hypergraph V E) (ω : Set E) : cut H (∅ : Set V) ω = ∅ := by
  rw [cut_eq, hyperClusterSet_empty_source, labelsMeeting_empty]

omit [Fintype V] in
/-- The functional `c` at `X ∪ {v}`, read in the configuration with the cut of `X` deleted. -/
theorem taC_insert_eq (H : Hypergraph V E) (pB : E → unitInterval) (s y v : V) (X : Set V)
    (g : Set V → ℝ) (ω : Set E) (hB : ∀ e ∈ cut H X ω, pB e = 0)
    (hoff : ∀ e ∉ cut H X ω, pB e = H.prob e) :
    taC H s y (insert v X) g ω = taC (withProb H pB) s y ({v} : Set V) g (ω \ cut H X ω) := by
  have hdu : ∀ (B' : Set E) (φ : Set E → ℝ),
      delE H (cut H X ω ∪ B') φ = delE (withProb H pB) B' φ :=
    fun B' φ => delE_union H pB _ B' hB hoff φ
  simp only [taC, cut_insert_vertex H X v ω, hdu, cut_withProb, hyperClusterSet_withProb,
    hyperConn_withProb]

omit [Fintype V] in
/-- The functional `c` at `X`, read in the configuration with the cut of `X` deleted (empty avoided
set). -/
theorem taC_eq_empty (H : Hypergraph V E) (pB : E → unitInterval) (s y : V) (X : Set V)
    (g : Set V → ℝ) (ω ζ : Set E) (hB : ∀ e ∈ cut H X ω, pB e = 0)
    (hoff : ∀ e ∉ cut H X ω, pB e = H.prob e) :
    taC H s y X g ω = taC (withProb H pB) s y (∅ : Set V) g ζ := by
  have hdel : ∀ φ : Set E → ℝ, delE H (cut H X ω) φ = delE (withProb H pB) ∅ φ :=
    fun φ => delE_eq_delE_empty H pB _ hB hoff φ
  simp only [taC, cut_empty, hdel, hyperClusterSet_withProb, hyperConn_withProb]

omit [Fintype V] in
/-- Same for `taN`. -/
theorem taN_eq_empty (H : Hypergraph V E) (pB : E → unitInterval) (s y : V) (X : Set V)
    (ω ζ : Set E) (hB : ∀ e ∈ cut H X ω, pB e = 0) (hoff : ∀ e ∉ cut H X ω, pB e = H.prob e) :
    taN H s y X ω = taN (withProb H pB) s y (∅ : Set V) ζ := by
  have hdel : ∀ φ : Set E → ℝ, delE H (cut H X ω) φ = delE (withProb H pB) ∅ φ :=
    fun φ => delE_eq_delE_empty H pB _ hB hoff φ
  simp only [taN, cut_empty, hdel, hyperConn_withProb]

omit [Fintype V] in
/-- Same for `taNW`. -/
theorem taNW_eq_empty (H : Hypergraph V E) (pB : E → unitInterval) (s y z : V) (X : Set V)
    (ω ζ : Set E) (hB : ∀ e ∈ cut H X ω, pB e = 0) (hoff : ∀ e ∉ cut H X ω, pB e = H.prob e) :
    taNW H s y z X ω = taNW (withProb H pB) s y z (∅ : Set V) ζ := by
  have hdel : ∀ φ : Set E → ℝ, delE H (cut H X ω) φ = delE (withProb H pB) ∅ φ :=
    fun φ => delE_eq_delE_empty H pB _ hB hoff φ
  simp only [taNW, cut_empty, hdel, hyperConn_withProb]

omit [Fintype V] [Fintype E] in
/-- `1_{s ↮ X}` read off the cluster of `X`.  The bond `ind_avoidEv_eq_ite` reads it off the edge
cluster. -/
theorem ind_avoidEv_eq_ite (H : Hypergraph V E) (s : V) (X : Set V) (ω : Set E) :
    ind (avoidEv H s X) ω = if s ∈ hyperClusterSet H ω X then 0 else 1 := by
  by_cases h : s ∈ hyperClusterSet H ω X
  · rw [if_pos h]
    obtain ⟨x, hx, hxs⟩ := h
    exact ind_of_not_mem fun hω => (mem_avoidEvent_singleton H s X ω).1 hω x hx hxs.symm
  · rw [if_neg h]
    exact ind_of_mem
      ((mem_avoidEvent_singleton H s X ω).2 fun x hx hsx => h ⟨x, hx, hsx.symm⟩)

/-- **Step (II)**: `B_{X ∪ {v}} ≤ B_X − A^{(v)}_X`, that is
`∫ 1{s↮X,v} c_{X∪v} ≤ ∫ 1{s↮X} c_X · μ_{H−cut_X}(y ↮ v | s ↮ y)`, given Lemma `P_v` (hypothesis
`hPv`, "conditioning on the cluster of `v` explains at most the fraction `μ(y↮v | s↮y)` of
`Cov(g, 1{s↔y})`") in every model with the same incidence and labels switched off: apply `P_v` in
`H − cut_X(ω)` for each `ω` and recombine with `set_sum_cond_sdiff`.  The bond `taB_insert_le`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10)] -/
theorem taB_insert_le (H : Hypergraph V E) (hw : ∀ e, (H.prob e : ℝ) < 1) (s y v : V)
    (X : Set V) (g : Set V → ℝ)
    (hPv : ∀ (q : E → unitInterval), (∀ e, (q e : ℝ) < 1) → ∀ v' : V,
      taB (withProb H q) s y ({v'} : Set V) g ≤
        (1 - delE (withProb H q) ∅
              (fun η => ind ((hyperConn H s y)ᶜ ∩ hyperConn H y v') η) /
            delE (withProb H q) ∅ (fun η => ind (hyperConn H s y)ᶜ η)) *
          (delE (withProb H q) ∅
              (fun η => g (hyperClusterSet H η ({s} : Set V)) * ind (hyperConn H s y) η) -
            delE (withProb H q) ∅ (fun η => g (hyperClusterSet H η ({s} : Set V))) *
              delE (withProb H q) ∅ (fun η => ind (hyperConn H s y) η))) :
    taB H s y (insert v X) g ≤ taB H s y X g - taA H s y v X g := by
  have hw0 : ∀ e, 0 ≤ (H.prob e : ℝ) := fun e => (H.prob e).2.1
  have hw1 : ∀ e, (H.prob e : ℝ) ≤ 1 := fun e => (H.prob e).2.2
  -- the parameters with the labels meeting `W` switched off
  set qB : Set V → E → unitInterval :=
    fun W e => if e ∈ labelsMeeting H W then 0 else H.prob e with hqB
  have hB : ∀ ω : Set E, ∀ e ∈ cut H X ω, qB (hyperClusterSet H ω X) e = 0 := by
    intro ω e he
    rw [cut_eq] at he
    simp only [hqB]
    rw [if_pos he]
  have hoff : ∀ ω : Set E, ∀ e ∉ cut H X ω, qB (hyperClusterSet H ω X) e = H.prob e := by
    intro ω e he
    rw [cut_eq] at he
    simp only [hqB]
    rw [if_neg he]
  have hqlt : ∀ (W : Set V) (e : E), (qB W e : ℝ) < 1 := by
    intro W e
    show (((if e ∈ labelsMeeting H W then (0 : unitInterval) else H.prob e) : unitInterval) : ℝ)
      < 1
    by_cases h : e ∈ labelsMeeting H W
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      exact hw e
  -- the kernel expressing `1{s ↮ X, v} c_{X∪v}` through `(C_X, configuration off the cut)`
  set KK : Set V → Set E → ℝ := fun W ζ =>
    (if s ∈ W then 0 else 1) *
      (ind (avoidEv H s ({v} : Set V)) ζ * taC (withProb H (qB W)) s y ({v} : Set V) g ζ)
    with hKK
  have lhs : taB H s y (insert v X) g = ∑ ω : Set E, weight (fun e => (H.prob e : ℝ)) ω *
      KK (hyperClusterSet H ω X) (ω \ cut H X ω) := by
    rw [taB, integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [hKK]
    rw [← ind_avoidEv_eq_ite]
    by_cases hω : ω ∈ avoidEv H s X
    · have h1 : ind (avoidEv H s (insert v X)) ω =
          ind (avoidEv H s X) ω * ind (avoidEv H s ({v} : Set V)) (ω \ cut H X ω) := by
        rw [ind_of_mem hω, one_mul]
        by_cases h' : ω ∈ avoidEv H s (insert v X)
        · rw [ind_of_mem h', ind_of_mem ((mem_avoidEv_insert_iff H s v X ω hω).1 h')]
        · rw [ind_of_not_mem h',
            ind_of_not_mem fun hh => h' ((mem_avoidEv_insert_iff H s v X ω hω).2 hh)]
      rw [h1, taC_insert_eq H (qB (hyperClusterSet H ω X)) s y v X g ω (hB ω) (hoff ω)]
      ring
    · have h' : ω ∉ avoidEv H s (insert v X) := fun hh =>
        hω ((mem_avoidEvent_singleton H s X ω).2 fun x hx =>
          (mem_avoidEvent_singleton H s _ ω).1 hh x (Set.mem_insert_of_mem _ hx))
      rw [ind_of_not_mem h', ind_of_not_mem hω]
      ring
  rw [lhs, set_sum_cond_sdiff H (fun e => (H.prob e : ℝ)) (sum_weight_eq_one H.prob) X KK]
  -- the right-hand side, configuration by configuration
  have rhs : taB H s y X g - taA H s y v X g =
      ∑ ω : Set E, weight (fun e => (H.prob e : ℝ)) ω * (ind (avoidEv H s X) ω *
        ((1 - taNW H s y v X ω / taN H s y X ω) * taC H s y X g ω)) := by
    simp only [taB, taA]
    rw [integral_prodBernoulli_eq_sum, integral_prodBernoulli_eq_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  rw [rhs]
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hw0 hw1 ω)
  simp only [hKK]
  rw [← ind_avoidEv_eq_ite]
  by_cases hω : ω ∈ avoidEv H s X
  swap
  · rw [ind_of_not_mem hω]
    simp
  rw [ind_of_mem hω, one_mul]
  -- in `H − cut_X(ω)`: the inner sum is `taB` at the switched-off parameters
  have inner : ∑ η : Set E, weight (fun e => (H.prob e : ℝ)) η *
      (1 * (ind (avoidEv H s ({v} : Set V)) (η \ cut H X ω) *
        taC (withProb H (qB (hyperClusterSet H ω X))) s y ({v} : Set V) g (η \ cut H X ω))) =
      taB (withProb H (qB (hyperClusterSet H ω X))) s y ({v} : Set V) g := by
    have hfun : (fun j => if j ∈ cut H X ω then (0 : ℝ) else (H.prob j : ℝ))
        = fun e => ((withProb H (qB (hyperClusterSet H ω X))).prob e : ℝ) := by
      funext e
      by_cases he : e ∈ cut H X ω
      · rw [if_pos he, withProb_prob, hB ω e he]
        simp
      · rw [if_neg he, withProb_prob, hoff ω e he]
    simp only [one_mul]
    rw [sum_weight_mul_comp_sdiff (fun e => (H.prob e : ℝ)) (cut H X ω)
      (fun ζ => ind (avoidEv H s ({v} : Set V)) ζ *
        taC (withProb H (qB (hyperClusterSet H ω X))) s y ({v} : Set V) g ζ),
      hfun, taB, integral_prodBernoulli_eq_sum]
    rfl
  rw [inner]
  have e1 := taC_eq_empty H (qB (hyperClusterSet H ω X)) s y X g ω ∅ (hB ω) (hoff ω)
  have e2 := taN_eq_empty H (qB (hyperClusterSet H ω X)) s y X ω ∅ (hB ω) (hoff ω)
  have e3 := taNW_eq_empty H (qB (hyperClusterSet H ω X)) s y v X ω ∅ (hB ω) (hoff ω)
  rw [e1, e2, e3]
  have key := hPv (qB (hyperClusterSet H ω X)) (hqlt (hyperClusterSet H ω X)) v
  simp only [taC, taN, taNW, cut_empty, hyperClusterSet_withProb, hyperConn_withProb] at key ⊢
  exact key

end Cond

/-! ## Checks

Two readings that guard against degenerate statements.  `exists_rTrace_law_not_product` is the
reason the port of `A2Push` changes shape: the vertex-indexed product law of the bond file fails
for one label incident to three vertices.  `markerDominanceAvoid_self` reads
`markerDominanceAvoid_of_TA` at `y = s`, where the averaged inequality is the identity `0 ≤ 0`, and
recovers the conditional one-cluster inequality `0 ≤ μ(A)·Cov_{s ↮ X}(F(C_s), 1{s ↔ z})`.
-/

section Checks

/-- One label incident to three vertices, opening probability `1/2`. -/
def threeVertexHypergraph : Hypergraph (Fin 3) Unit where
  incidence := fun _ => Set.univ
  prob := fun _ => ⟨1 / 2, by norm_num [Set.mem_Icc]⟩

/-- The trace of `Z = {2}` in `threeVertexHypergraph`: the two other vertices when the label is
open, nothing otherwise. -/
theorem mem_rTrace_threeVertex (ω : Set Unit) (x : Fin 3) :
    x ∈ rTrace threeVertexHypergraph Finset.univ ({2} : Finset (Fin 3)) ω
      ↔ () ∈ ω ∧ x ≠ 2 := by
  show x ∈ traceOutside threeVertexHypergraph (↑({2} : Finset (Fin 3)))
    (ω ∩ labelsIn threeVertexHypergraph Finset.univ ∩
      labelsMeeting threeVertexHypergraph (↑({2} : Finset (Fin 3)))) ↔ _
  rw [mem_traceOutside_iff]
  constructor
  · rintro ⟨e, ⟨⟨he, -⟩, -⟩, -, hx⟩
    refine ⟨by cases e; exact he, fun h => hx ?_⟩
    rw [h]
    exact Finset.mem_coe.2 (Finset.mem_singleton_self 2)
  · rintro ⟨hω, hx⟩
    refine ⟨(), ⟨⟨hω, fun v _ => Finset.mem_univ v⟩, ?_⟩, Set.mem_univ x, fun h => hx ?_⟩
    · rw [mem_labelsMeeting]
      exact Set.not_disjoint_iff.2 ⟨2, Set.mem_univ _, Finset.mem_coe.2 (Finset.mem_singleton_self 2)⟩
    · exact Finset.mem_singleton.1 (Finset.mem_coe.1 h)

/-- Every configuration of `threeVertexHypergraph` has weight `1/2`. -/
theorem weight_threeVertex (ω : Set Unit) :
    weight (fun e => (threeVertexHypergraph.prob e : ℝ)) ω = 1 / 2 := by
  unfold weight
  rw [Fintype.prod_unique]
  show (if (default : Unit) ∈ ω then (1 : ℝ) / 2 else 1 - (1 : ℝ) / 2) = 1 / 2
  split_ifs <;> norm_num

/-- **The vertex-indexed product law of the bond `A2Push` fails for hyperedges.**  In
`threeVertexHypergraph` with `Z = {2}`, the trace is `{0, 1}` or `∅` with probability `1/2` each,
and no product law on `Set (Fin 3)` has that push-forward: a product law giving mass to `{0, 1}`
and to `∅` gives mass to `{0}` as well.  The bond argument needs the stars of distinct outside
vertices to be disjoint blocks of coordinates, which is the injectivity of `(u, z) ↦ s(u, z)`; one
label incident to two outside vertices breaks it. -/
theorem exists_rTrace_law_not_product :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (H : Hypergraph V E) (U Z : Finset V)
      (w : E → ℝ), (∀ e, 0 ≤ w e) ∧ (∀ e, w e ≤ 1) ∧ (∑ ω : Set E, weight w ω = 1) ∧
      ¬ ∃ p : V → ℝ, ∀ Γ : Set V → ℝ,
        ∑ ω : Set E, weight w ω * Γ (rTrace H U Z ω) = ∑ η : Set V, weight p η * Γ η := by
  refine ⟨Fin 3, Unit, inferInstance, inferInstance, threeVertexHypergraph, Finset.univ,
    ({2} : Finset (Fin 3)), fun e => (threeVertexHypergraph.prob e : ℝ),
    fun e => (threeVertexHypergraph.prob e).2.1, fun e => (threeVertexHypergraph.prob e).2.2,
    sum_weight_eq_one threeVertexHypergraph.prob, ?_⟩
  rintro ⟨p, hp⟩
  set T : Set Unit → Set (Fin 3) :=
    fun ω => rTrace threeVertexHypergraph Finset.univ ({2} : Finset (Fin 3)) ω with hT
  -- the push-forward of a point mass: `Σ_η weight_p(η) 1{η = S} = weight_p(S)`
  have hpoint : ∀ S : Set (Fin 3),
      ∑ η : Set (Fin 3), weight p η * ind ({S} : Set (Set (Fin 3))) η = weight p S := by
    intro S
    rw [Finset.sum_eq_single S]
    · rw [ind_of_mem (Set.mem_singleton S), mul_one]
    · intro η _ hη
      rw [ind_of_not_mem (fun h => hη (Set.mem_singleton_iff.1 h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ S) h
  have hnn : ∀ (S : Set (Fin 3)) (ω : Set Unit),
      0 ≤ weight (fun e => (threeVertexHypergraph.prob e : ℝ)) ω * ind ({S} : Set (Set (Fin 3))) (T ω) :=
    fun S ω => by rw [weight_threeVertex]; exact mul_nonneg (by norm_num) (ind_nonneg _ _)
  -- the trace of the open configuration contains `0`, the trace of the closed one is empty
  have h0T : (0 : Fin 3) ∈ T Set.univ := (mem_rTrace_threeVertex _ _).2 ⟨Set.mem_univ _, by decide⟩
  have hTempty : T ∅ = ∅ := Set.eq_empty_of_forall_notMem fun x hx =>
    ((mem_rTrace_threeVertex _ _).1 hx).1
  -- (1) the set `{0}` is never a trace
  have hno : ∀ ω : Set Unit, T ω ≠ ({0} : Set (Fin 3)) := by
    intro ω h
    have h0 : (0 : Fin 3) ∈ T ω := h ▸ Set.mem_singleton 0
    have h1 : (1 : Fin 3) ∈ T ω :=
      (mem_rTrace_threeVertex _ _).2 ⟨((mem_rTrace_threeVertex _ _).1 h0).1, by decide⟩
    rw [h] at h1
    exact absurd (Set.mem_singleton_iff.1 h1) (by decide)
  have e1 : weight p ({0} : Set (Fin 3)) = 0 := by
    rw [← hpoint, ← hp (ind ({({0} : Set (Fin 3))} : Set (Set (Fin 3))))]
    refine Finset.sum_eq_zero fun ω _ => ?_
    rw [ind_of_not_mem (fun h => hno ω (Set.mem_singleton_iff.1 h)), mul_zero]
  -- (2) the trace of the open configuration, and (3) the empty set, have positive mass
  have hpos : ∀ (S : Set (Fin 3)) (ω₀ : Set Unit), T ω₀ = S → 0 < weight p S := by
    intro S ω₀ hS
    rw [← hpoint, ← hp]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun ω _ => hnn S ω) (Finset.mem_univ ω₀))
    rw [weight_threeVertex, hS, ind_of_mem (Set.mem_singleton S)]
    norm_num
  have e2 := hpos (T Set.univ) Set.univ rfl
  have e3 := hpos ∅ ∅ hTempty
  -- a zero product has a zero factor, which the two positive products forbid
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 e1
  have hne2 := Finset.prod_ne_zero_iff.1 e2.ne' i (Finset.mem_univ i)
  have hne3 := Finset.prod_ne_zero_iff.1 e3.ne' i (Finset.mem_univ i)
  by_cases hi0 : i ∈ ({0} : Set (Fin 3))
  · rw [if_pos hi0] at hi
    rw [Set.mem_singleton_iff] at hi0
    subst hi0
    rw [if_pos h0T] at hne2
    exact hne2 hi
  · rw [if_neg hi0] at hi
    rw [if_neg (Set.notMem_empty i)] at hne3
    exact hne3 hi

/-- `{y ↮ s}` as the complement of the connection event. -/
theorem avoidEv_insert_empty (H : Hypergraph V E) (s y : V) :
    avoidEv H y (insert s (∅ : Set V)) = (hyperConn H s y)ᶜ := by
  ext ω
  rw [avoidEv_eq, mem_avoidEvent_singleton, Set.mem_compl_iff]
  constructor
  · intro h hsy
    exact h s (Set.mem_insert s ∅) (hsy : (openHyperGraph H ω).Reachable s y).symm
  · intro h t ht hyt
    rcases Set.mem_insert_iff.1 ht with rfl | ht
    · exact h hyt.symm
    · exact absurd ht (Set.notMem_empty t)

variable [Fintype V] [Fintype E]

omit [Fintype V] in
/-- With no avoided set the averaged inequality is the identity `0 ≤ 0`: the cut is empty, the
functionals do not depend on the configuration, and `A·b − a·B` is `(m/n)·c·n − m·c` with
`m ≤ n`. -/
theorem taQ_empty (H : Hypergraph V E) (s y z : V) (g : Set V → ℝ) :
    taQ H s y z (∅ : Set V) g = 0 := by
  have hdel : ∀ (ω : Set E) (φ : Set E → ℝ),
      delE H (cut H (∅ : Set V) ω) φ = ∫ η, φ η ∂(prodBernoulli H.prob) := by
    intro ω φ
    simp only [delE, cut_empty, Set.sdiff_empty]
  have hC : ∀ ω, taC H s y (∅ : Set V) g ω =
      (∫ η, g (hyperClusterSet H η ({s} : Set V)) * ind (hyperConn H s y) η
          ∂(prodBernoulli H.prob)) -
        (∫ η, g (hyperClusterSet H η ({s} : Set V)) ∂(prodBernoulli H.prob)) *
          ∫ η, ind (hyperConn H s y) η ∂(prodBernoulli H.prob) :=
    fun ω => by simp only [taC, hdel]
  have hN : ∀ ω, taN H s y (∅ : Set V) ω =
      ∫ η, ind (hyperConn H s y)ᶜ η ∂(prodBernoulli H.prob) :=
    fun ω => by simp only [taN, hdel]
  have hNW : ∀ ω, taNW H s y z (∅ : Set V) ω =
      ∫ η, ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η ∂(prodBernoulli H.prob) :=
    fun ω => by simp only [taNW, hdel]
  have hD : avoidEv H s (∅ : Set V) = Set.univ := avoidEvent_empty H _
  have hind : ∀ ω : Set E, ind (Set.univ : Set (Set E)) ω = 1 :=
    fun ω => ind_of_mem (Set.mem_univ ω)
  have hB : taB H s y (∅ : Set V) g =
      (∫ η, g (hyperClusterSet H η ({s} : Set V)) * ind (hyperConn H s y) η
          ∂(prodBernoulli H.prob)) -
        (∫ η, g (hyperClusterSet H η ({s} : Set V)) ∂(prodBernoulli H.prob)) *
          ∫ η, ind (hyperConn H s y) η ∂(prodBernoulli H.prob) := by
    simp only [taB, hC, hD, hind, one_mul]
    exact CSHTwoA.integral_const_prob (prodBernoulli H.prob) _
  have hA : taA H s y z (∅ : Set V) g =
      (∫ η, ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η ∂(prodBernoulli H.prob)) /
          (∫ η, ind (hyperConn H s y)ᶜ η ∂(prodBernoulli H.prob)) *
        ((∫ η, g (hyperClusterSet H η ({s} : Set V)) * ind (hyperConn H s y) η
            ∂(prodBernoulli H.prob)) -
          (∫ η, g (hyperClusterSet H η ({s} : Set V)) ∂(prodBernoulli H.prob)) *
            ∫ η, ind (hyperConn H s y) η ∂(prodBernoulli H.prob)) := by
    simp only [taA, hC, hN, hNW, hD, hind, one_mul]
    exact CSHTwoA.integral_const_prob (prodBernoulli H.prob) _
  have htab : tab H s y (∅ : Set V) = ∫ η, ind (hyperConn H s y)ᶜ η ∂(prodBernoulli H.prob) := by
    unfold tab
    rw [avoidEv_insert_empty, AGBase.integral_ind]
  have htaa : taa H s y z (∅ : Set V) =
      ∫ η, ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η ∂(prodBernoulli H.prob) := by
    unfold taa
    rw [avoidEv_insert_empty, AGBase.integral_ind]
  have hmn : (∫ η, ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η ∂(prodBernoulli H.prob))
      ≤ ∫ η, ind (hyperConn H s y)ᶜ η ∂(prodBernoulli H.prob) :=
    integral_mono (integrable_of_fintype _) (integrable_of_fintype _)
      fun η => BHK2006.ind_mono Set.inter_subset_left η
  have hm0 : 0 ≤ ∫ η, ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η ∂(prodBernoulli H.prob) :=
    integral_nonneg fun _ => ind_nonneg _ _
  unfold taQ
  rw [hA, hB, htab, htaa]
  by_cases hn0 : (∫ η, ind (hyperConn H s y)ᶜ η ∂(prodBernoulli H.prob)) = 0
  · have hm : (∫ η, ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η ∂(prodBernoulli H.prob)) = 0 :=
      le_antisymm (hmn.trans hn0.le) hm0
    rw [hn0, hm]
    simp
  · rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hn0, sub_self]

/-- **Non-vacuity of `markerDominanceAvoid_of_TA`**: with no avoided set both hypotheses are
discharged (`taQ_empty`, and no label meets `∅`), and the theorem returns
`markerDominance_noAvoid` of `KN/HyperCTBase.lean`, the marker dominance lemma
`μ(s ↮ y, y ↔ z)·Cov(F(C_s), 1{s ↔ y}) ≤ μ(s ↮ y)·Cov(F(C_s), 1{s ↔ z})`. -/
theorem markerDominanceAvoid_empty (H : Hypergraph V E) (s y z : V) {F : Set V → ℝ}
    (hF : Monotone F) :
    (prodBernoulli H.prob).real ((hyperConn H s y)ᶜ ∩ hyperConn H y z) *
        ((∫ ω in hyperConn H s y, F (hyperClusterSet H ω ({s} : Set V))
              ∂(prodBernoulli H.prob)) -
          (∫ ω, F (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob)) *
            (prodBernoulli H.prob).real (hyperConn H s y))
      ≤ (prodBernoulli H.prob).real ((hyperConn H s y)ᶜ) *
          ((∫ ω in hyperConn H s z, F (hyperClusterSet H ω ({s} : Set V))
                ∂(prodBernoulli H.prob)) -
            (∫ ω, F (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob)) *
              (prodBernoulli H.prob).real (hyperConn H s z)) := by
  have key := markerDominanceAvoid_of_TA H s y z (∅ : Set V)
    (fun e he => by
      rw [labelsMeeting_empty] at he
      exact absurd he (Set.notMem_empty e))
    (fun g _ _ => (taQ_empty H s y z g).symm.le) hF
  have hD : avoidEv H s (∅ : Set V) = Set.univ := avoidEvent_empty H _
  rw [hD, avoidEv_insert_empty, Set.univ_inter, Set.univ_inter, Measure.restrict_univ,
    probReal_univ, one_mul, one_mul] at key
  exact key

end Checks

end KNAll.Site.CSHTwoB

end
