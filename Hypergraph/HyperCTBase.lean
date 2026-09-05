import Hypergraph.HyperDecisionTree
import Hypergraph.HyperProjGen

/-!
# The base layer of the correlation core, for hyperedges

The hyperedge port of five modules of the bond development:
`Percolation/Continuity/LowerTail/TreeHarrisReal.lean`,
`Percolation/Continuity/CovTau/Transfer.lean`,
`Percolation/Continuity/HullPort/MarkerDominanceTools.lean`,
`Percolation/Continuity/LowerTail/MarkerDominancePv.lean` and
`Percolation/Continuity/HullPort/TADefs.lean`.  Everything is stated for a `Hypergraph V E` with
arbitrary incidence sets over arbitrary types, finiteness being assumed only where it is used.

## The conditional expectation given the exploration record

The bond `TreeHarris.cE D p Fm φ K = Σ_{K₂} wt(K₂) φ(K →_{Fm K} K₂)` becomes `cE H S f`, the mean
of `f` at the splice `spliceRecord (recordAt H S ω)` of `KN/HyperDecisionTree.lean`, written as an
ordinary integral: no record event has to have positive probability, or to be nonempty.

* `setIntegral_recordEvent_eq` — `∫_{record = r} f = P(record = r) · E_r[f]` for EVERY `f`.  This is
  `real_recordEvent_inter` of `KN/HyperDecisionTree.lean` with the indicator replaced by a function,
  obtained from it by expanding `f ∘ spliceRecord r` over the traces on the labels the exploration
  did not query (`setIntegral_trace_eq_sum` of `KN/HyperTwoCluster.lean`).
* `integral_eq_sum_recordEvent` — the record events partition the configuration space.
* `cE_const`, `cE_congr`, `cE_mul_of_local`, `integral_cE` (the tower `E[cE f] = E[f]`) and
  `integral_mul_cE_comm` (the symmetry `E[f · cE g] = E[cE f · g]`).  The bond file gets the last two
  from Gladkov's swap Lemma 3.1 on the product space; here both are the partition together with
  `setIntegral_recordEvent_eq`, which already contains the swap.
* `sum_mul_nonneg_of_upperSet` — the layer-cake extension, a statement about a preorder and a finite
  set, ported unchanged.

## What `treeHarris_hyper` already covers, and what it does not

`treeHarris_hyper` of `KN/HyperDecisionTree.lean` is the inequality for a functional of the explored
cluster.  `TreeHarris.treeHarris_real` has exactly two call sites in the bond development,
`Continuity/CovTau/StarH.lean` lines 114 and 260, and both instantiate the monotone function at
`fcl Ψ x`, a functional of the open cluster of a vertex; the other `CovTau` modules only cite it in
prose.  For those two instances the bond theorem is covered.  The bond statement itself is more
general: it is about an arbitrary monotone `f ≥ 0` of the configuration.

`cE_eq_self_of_recordDetermined` explains the gap.  A function read off the record is its own
conditional expectation, so for it the bond right side `E[E[f ∣ ℱ] · 1_Y]` collapses to `E[f · 1_Y]`
and the statement is Harris' inequality (`treeHarris_real_recordDetermined`, which also drops the
sign hypothesis the bond statement carries).  For an `f` not read off the record there is no
collapse, and the inequality is the genuine decision-tree one.  Nothing here proves that; it needs
Gladkov's induction over a decision tree presenting the hyperedge exploration, which this
development does not build — the record of `KN/HyperDecisionTree.lean` is defined directly, not as
the revealed set of a tree.  The obstruction is concrete: the residual probability
`ω ↦ condRecord H (recordAt H S ω) Y` of an increasing `Y` is not a monotone function of `ω`,
because a larger configuration queries labels the smaller one did not, and those extra labels are
resampled rather than found open.

The same gap is the one in the port of `MarkerDominancePv.sum_condSumW_ge`:
`sum_condRecord_ge_of_recordDetermined` proves it for an increasing event read off the record, which
is the case the hyperedge gluing argument uses, and not for an arbitrary increasing event.

## The conditioned covariance transfer

`KN/HyperProjGen.lean` already carries `projFun`, `monotone_projFun` and the projection identities
`setIntegral_clusterFamily_eq` (the hyperedge form of the bond `CovTau.tower_clusterFun`) and
`setIntegral_sub_eq_projFun`.  Added here: `antitone_condMean`, the monotonicity of the subtracted
conditional mean on its own, and `covTransfer_of_covTau`, the transfer statement in the shape the
two-relay surplus step consumes.

## Marker dominance

`integral_harris` is `prodBernoulli_integral_mul_le` of `KN/ProdBernoulliFKG.lean`, which needs no
sign hypothesis.  `markerDominance_noAvoid` is the bond argument with one substitution: the bond
proof calls the "off-cluster" form of van den Berg–Häggström–Kahn's Theorem 1.3, and here the same
step is `avoid_cluster_negCorrelation` of `KN/HyperTwoCluster.lean` for the cluster of `s` and the
cluster of `y`, with its hypothesis discharged by `oneClusterInequality_holds`.  The hyperedge
statement carries neither the nonnegativity of the functional nor the nondegeneracy `s ≠ y`.

## The avoided-set functionals

`delE`, `cut`, `avoidEv`, `taC`, `taN`, `taNW`, `taB`, `taA`, `tab`, `taa`, `taQ` — the definitions
of the bond `HullPort` bookkeeping, with sums against `BHK2006.weight` replaced by integrals against
`prodBernoulli`, the pairs meeting a cluster replaced by `labelsMeeting`, and the edge cluster
replaced by the vertex cluster.

## References

* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), Lemma 3.1,
  Theorem 3.2.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation
  and related processes*, Random Struct. Alg. 29 (2006), Thms. 1.3–1.5.
-/

noncomputable section

namespace KNAll.Site.CTBase

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {V E : Type*}

/-! ## The conditional expectation given the exploration record -/

/-- The conditional expectation of a real function of the configuration given the record `r`. -/
def condRecordFun (H : Hypergraph V E) (r : ExplorationRecord V E) (f : Set E → ℝ) : ℝ :=
  ∫ ω, f (spliceRecord r ω) ∂(prodBernoulli H.prob)

/-- The conditional expectation of `f` given the record left by the exploration of `S`. -/
def cE (H : Hypergraph V E) (S : Set V) (f : Set E → ℝ) (ω : Set E) : ℝ :=
  condRecordFun H (recordAt H S ω) f

theorem cE_eq (H : Hypergraph V E) (S : Set V) (f : Set E → ℝ) (ω : Set E) :
    cE H S f ω = condRecordFun H (recordAt H S ω) f := rfl

/-- At an indicator the conditional expectation is `condRecord`. -/
theorem condRecordFun_ind [Fintype E] (H : Hypergraph V E) (r : ExplorationRecord V E)
    (Y : Set (Set E)) :
    condRecordFun H r (fun ν => DecisionTree.ind Y ν) = condRecord H r Y := by
  have hfun : (fun ω : Set E => DecisionTree.ind Y (spliceRecord r ω))
      = (residualEvent r Y).indicator (1 : Set E → ℝ) := by
    funext ω
    by_cases h : spliceRecord r ω ∈ Y
    · rw [DecisionTree.ind_of_mem h,
        Set.indicator_of_mem (show ω ∈ residualEvent r Y from h), Pi.one_apply]
    · rw [DecisionTree.ind_of_not_mem h,
        Set.indicator_of_notMem (show ω ∉ residualEvent r Y from h)]
  show ∫ ω, DecisionTree.ind Y (spliceRecord r ω) ∂(prodBernoulli H.prob) = _
  rw [hfun, integral_indicator_one (measurableSet_of_fintype _)]
  rfl

/-- The conditional expectation is linear in its argument. -/
theorem condRecordFun_add [Fintype E] (H : Hypergraph V E) (r : ExplorationRecord V E)
    (f g : Set E → ℝ) :
    condRecordFun H r (fun ν => f ν + g ν)
      = condRecordFun H r f + condRecordFun H r g :=
  integral_add (integrable_of_fintype _) (integrable_of_fintype _)

theorem condRecordFun_const (H : Hypergraph V E) (r : ExplorationRecord V E) (c : ℝ) :
    condRecordFun H r (fun _ => c) = c := by
  simp [condRecordFun]

/-- **The exact conditional expectation identity for a real function.**  The mean of `f` on the
event that the exploration stops with the record `r` is the probability of that event times the
residual mean of `f`, for *every* `f`.  This is `real_recordEvent_inter` of
`KN/HyperDecisionTree.lean` with the indicator replaced by an arbitrary function, obtained from it
by expanding `f ∘ spliceRecord r` over the possible traces on the labels the exploration did not
query.  It carries no denominator and no positivity requirement. -/
theorem setIntegral_recordEvent_eq [Fintype E] (H : Hypergraph V E) (S : Set V)
    (r : ExplorationRecord V E) (f : Set E → ℝ) :
    (∫ ω in recordEvent H S r, f ω ∂(prodBernoulli H.prob))
      = (prodBernoulli H.prob).real (recordEvent H S r) * condRecordFun H r f := by
  classical
  set μ := prodBernoulli H.prob with hμ
  set h : Set E → ℝ := fun ν => f (spliceRecord r ν) with hh
  have hdet : ∀ ν : Set E, h (ν ∩ (r.queried)ᶜ) = h ν := by
    intro ν
    simp only [hh]
    rw [spliceRecord_congr r (ω := ν ∩ (r.queried)ᶜ) (ω' := ν)
      (by rw [Set.inter_assoc, Set.inter_self])]
  have hself : (∫ ω in recordEvent H S r, f ω ∂μ) = ∫ ω in recordEvent H S r, h ω ∂μ := by
    refine setIntegral_congr_fun (measurableSet_recordEvent H S r) fun ω hω => ?_
    simp only [hh]
    rw [spliceRecord_eq_self H S hω]
  have hfac : ∀ J : Finset E,
      μ.real (recordEvent H S r ∩ {ρ : Set E | ρ ∩ (r.queried)ᶜ = (↑J : Set E)})
        = μ.real (recordEvent H S r) * μ.real {ρ : Set E | ρ ∩ (r.queried)ᶜ = (↑J : Set E)} := by
    intro J
    rw [real_recordEvent_inter H S r,
      condRecord_eq_real_of_determinedBy H r (determinedBy_trace (r.queried)ᶜ (↑J : Set E))]
  rw [hself, setIntegral_trace_eq_sum μ (r.queried)ᶜ hdet (recordEvent H S r)]
  have hres : condRecordFun H r f = ∑ J : Finset E,
      h (↑J : Set E) * μ.real {ρ : Set E | ρ ∩ (r.queried)ᶜ = (↑J : Set E)} :=
    integral_trace_eq_sum μ (r.queried)ᶜ hdet
  rw [hres, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [hfac J]
  ring

/-! ## The partition into record events -/

open Classical in
/-- The records the exploration can leave behind: the image of the configuration space under
`recordAt`.  Over a finite label type this is a finite set, and the record events it indexes
partition the configuration space. -/
def recordSet [Fintype E] (H : Hypergraph V E) (S : Set V) : Finset (ExplorationRecord V E) :=
  Finset.image (recordAt H S) (Finset.univ : Finset (Set E))

theorem recordAt_mem_recordSet [Fintype E] (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    recordAt H S ω ∈ recordSet H S := by
  classical
  exact Finset.mem_image.2 ⟨ω, Finset.mem_univ ω, rfl⟩

/-- **The partition.**  Every configuration lies on exactly one record event, so the integral of any
function is the sum of its integrals over the record events. -/
theorem integral_eq_sum_recordEvent [Fintype E] (H : Hypergraph V E) (S : Set V) (g : Set E → ℝ) :
    (∫ ω, g ω ∂(prodBernoulli H.prob))
      = ∑ r ∈ recordSet H S, ∫ ω in recordEvent H S r, g ω ∂(prodBernoulli H.prob) := by
  classical
  have hpart : ∀ ω : Set E,
      ∑ r ∈ recordSet H S, (recordEvent H S r).indicator g ω = g ω := by
    intro ω
    have hterm : ∀ r ∈ recordSet H S, r ≠ recordAt H S ω →
        (recordEvent H S r).indicator g ω = 0 := by
      intro r _ hr
      have hnot : ω ∉ recordEvent H S r := fun hmem => hr (hmem : recordAt H S ω = r).symm
      exact Set.indicator_of_notMem hnot g
    rw [Finset.sum_eq_single (recordAt H S ω) hterm
      (fun hc => absurd (recordAt_mem_recordSet H S ω) hc)]
    exact Set.indicator_of_mem (mem_recordEvent_self H S ω) _
  have hsum : ∀ r : ExplorationRecord V E,
      (∫ ω in recordEvent H S r, g ω ∂(prodBernoulli H.prob))
        = ∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
            (recordEvent H S r).indicator g ω := by
    intro r
    rw [← integral_indicator (measurableSet_recordEvent H S r),
      BHK2006.integral_prodBernoulli_eq_sum]
  rw [BHK2006.integral_prodBernoulli_eq_sum]
  simp only [hsum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← Finset.mul_sum, hpart ω]

/-! ## The calculus of `cE` -/

theorem cE_const (H : Hypergraph V E) (S : Set V) (c : ℝ) (ω : Set E) :
    cE H S (fun _ => c) ω = c := condRecordFun_const H _ c

/-- `cE f` is read off the record, hence off the labels the exploration queried. -/
theorem cE_congr (H : Hypergraph V E) (S : Set V) (f : Set E → ℝ) {ω ω' : Set E}
    (h : recordAt H S ω = recordAt H S ω') : cE H S f ω = cE H S f ω' := by
  simp only [cE, h]

theorem cE_eq_of_mem_recordEvent (H : Hypergraph V E) (S : Set V) (f : Set E → ℝ)
    {r : ExplorationRecord V E} {ω : Set E} (hω : ω ∈ recordEvent H S r) :
    cE H S f ω = condRecordFun H r f := by
  have h : recordAt H S ω = r := hω
  show condRecordFun H (recordAt H S ω) f = condRecordFun H r f
  rw [h]

/-- **The splice lands on the record event it splices at.**  The trace of `spliceRecord r η` on the
queried labels is the recorded one, and a record event is exactly that cylinder
(`recordEvent_eq_cylinder`). -/
theorem spliceRecord_mem_recordEvent (H : Hypergraph V E) (S : Set V) (ω η : Set E) :
    spliceRecord (recordAt H S ω) η ∈ recordEvent H S (recordAt H S ω) := by
  set r := recordAt H S ω with hr
  rw [recordEvent_eq_cylinder H S (mem_recordEvent_self H S ω)]
  show spliceRecord r η ∩ r.queried = r.openLabels
  rw [spliceRecord, Set.union_inter_distrib_right,
    Set.inter_eq_self_of_subset_left (ExplorationRecord.openLabels_subset_queried r)]
  simp

/-- **A function of the record is its own conditional expectation.**  This is why the hyperedge
inequality needs no tower step for a cluster functional: the splice reproduces the record, so the
conditional expectation collapses. -/
theorem cE_eq_self_of_recordDetermined [Fintype E] (H : Hypergraph V E) (S : Set V)
    {f : Set E → ℝ} (hf : ∀ ν ν' : Set E, recordAt H S ν = recordAt H S ν' → f ν = f ν')
    (ω : Set E) : cE H S f ω = f ω := by
  have hpt : ∀ η : Set E, f (spliceRecord (recordAt H S ω) η) = f ω := by
    intro η
    exact hf _ _ (spliceRecord_mem_recordEvent H S ω η : _ = recordAt H S ω)
  show (∫ η, f (spliceRecord (recordAt H S ω) η) ∂(prodBernoulli H.prob)) = f ω
  simp only [hpt]
  simp

/-- A functional of the explored cluster is its own conditional expectation. -/
theorem cE_clusterFun [Fintype E] (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ) (ω : Set E) :
    cE H S (fun ν => F (hyperClusterSet H ν S)) ω = F (hyperClusterSet H ω S) := by
  refine cE_eq_self_of_recordDetermined H S (fun ν ν' hν => ?_) ω
  have h : hyperClusterSet H ν S = hyperClusterSet H ν' S := by
    have := congrArg ExplorationRecord.reached hν
    simpa using this
  rw [h]

/-- **Pull-out**: a factor read off the record comes out of the conditional expectation. -/
theorem cE_mul_of_local [Fintype E] (H : Hypergraph V E) (S : Set V) {Z : Set E → ℝ}
    (hZ : ∀ ν ν' : Set E, recordAt H S ν = recordAt H S ν' → Z ν = Z ν') (f : Set E → ℝ)
    (ω : Set E) : cE H S (fun ν => Z ν * f ν) ω = Z ω * cE H S f ω := by
  have hpt : ∀ η : Set E, Z (spliceRecord (recordAt H S ω) η) = Z ω := fun η =>
    hZ _ _ (spliceRecord_mem_recordEvent H S ω η : _ = recordAt H S ω)
  show (∫ η, Z (spliceRecord (recordAt H S ω) η) * f (spliceRecord (recordAt H S ω) η)
      ∂(prodBernoulli H.prob)) = _
  simp only [hpt]
  exact integral_const_mul _ _

/-- **The tower property** `E[cE f] = E[f]`. -/
theorem integral_cE [Fintype E] (H : Hypergraph V E) (S : Set V) (f : Set E → ℝ) :
    (∫ ω, cE H S f ω ∂(prodBernoulli H.prob)) = ∫ ω, f ω ∂(prodBernoulli H.prob) := by
  classical
  rw [integral_eq_sum_recordEvent H S (fun ω => cE H S f ω),
    integral_eq_sum_recordEvent H S f]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [setIntegral_recordEvent_eq H S r f]
  rw [setIntegral_congr_fun (measurableSet_recordEvent H S r)
    (g := fun _ => condRecordFun H r f) fun ω hω => cE_eq_of_mem_recordEvent H S f hω,
    setIntegral_const, smul_eq_mul]

/-- **Symmetry** `E[f · cE g] = E[cE f · g]`: both are the sum over records of
`P(record = r) · cE_r f · cE_r g`. -/
theorem integral_mul_cE_comm [Fintype E] (H : Hypergraph V E) (S : Set V) (f g : Set E → ℝ) :
    (∫ ω, f ω * cE H S g ω ∂(prodBernoulli H.prob))
      = ∫ ω, cE H S f ω * g ω ∂(prodBernoulli H.prob) := by
  classical
  have hone : ∀ (u v : Set E → ℝ) (r : ExplorationRecord V E),
      (∫ ω in recordEvent H S r, u ω * cE H S v ω ∂(prodBernoulli H.prob))
        = (prodBernoulli H.prob).real (recordEvent H S r) *
            (condRecordFun H r u * condRecordFun H r v) := by
    intro u v r
    rw [setIntegral_congr_fun (measurableSet_recordEvent H S r)
      (g := fun ω => u ω * condRecordFun H r v)
      fun ω hω => by rw [cE_eq_of_mem_recordEvent H S v hω]]
    rw [integral_mul_const, setIntegral_recordEvent_eq H S r u]
    ring
  rw [integral_eq_sum_recordEvent H S (fun ω => f ω * cE H S g ω),
    integral_eq_sum_recordEvent H S (fun ω => cE H S f ω * g ω)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hone f g r]
  rw [setIntegral_congr_fun (measurableSet_recordEvent H S r)
    (g := fun ω => g ω * cE H S f ω) fun ω hω => by ring]
  rw [hone g f r]
  ring

/-! ## Layer-cake extension: from up-set indicators to monotone functions -/

/-- **Layer-cake extension.**  On a finite set `s` of elements of a preorder, a linear functional
`f ↦ Σ_{K ∈ s} a_K f(K)` that is nonnegative on the indicator of every up-set is nonnegative on
every monotone `f ≥ 0`: peel off `m · 1_{f > 0}` with `m` the least positive value and induct on the
support.  The statement mentions no percolation model, and the proof is the one of
`Percolation.Continuity.TreeHarris.sum_mul_nonneg_of_upperSet`. -/
theorem sum_mul_nonneg_of_upperSet {α : Type*} [Preorder α] (s : Finset α) (a : α → ℝ)
    (ha : ∀ U : Set α, IsUpperSet U → 0 ≤ ∑ K ∈ s, a K * DecisionTree.ind U K) :
    ∀ f : α → ℝ, Monotone f → (∀ K, 0 ≤ f K) → 0 ≤ ∑ K ∈ s, a K * f K := by
  classical
  intro f hf hf0
  induction hn : (s.filter fun K => 0 < f K).card using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    by_cases hsupp : (s.filter fun K => 0 < f K) = ∅
    · have h0 : ∀ K ∈ s, f K = 0 := fun K hK => by
        have : K ∉ s.filter fun K => 0 < f K := by rw [hsupp]; exact Finset.notMem_empty K
        rw [Finset.mem_filter, not_and, not_lt] at this
        exact le_antisymm (this hK) (hf0 K)
      rw [Finset.sum_eq_zero fun K hK => by rw [h0 K hK, mul_zero]]
    · have hne : (s.filter fun K => 0 < f K).Nonempty := Finset.nonempty_iff_ne_empty.2 hsupp
      set m₀ : ℝ := ((s.filter fun K => 0 < f K).image f).min' (hne.image f) with hm₀
      set U : Set α := {K | 0 < f K} with hU
      have hUup : IsUpperSet U := fun K K' hKK' hK => lt_of_lt_of_le hK (hf hKK')
      have hm₀pos : 0 < m₀ := by
        obtain ⟨K, hK, hKm⟩ := Finset.mem_image.1 (Finset.min'_mem _ (hne.image f))
        rw [← hm₀] at hKm
        rw [← hKm]; exact (Finset.mem_filter.1 hK).2
      have hm₀le : ∀ K ∈ s, 0 < f K → m₀ ≤ f K := fun K hK hfK =>
        Finset.min'_le _ _ (Finset.mem_image.2 ⟨K, Finset.mem_filter.2 ⟨hK, hfK⟩, rfl⟩)
      set f' : α → ℝ := fun K => f K - m₀ * DecisionTree.ind U K with hf'
      have hf'U : ∀ K, 0 < f K → f' K = f K - m₀ := fun K hK => by
        simp only [hf']; rw [DecisionTree.ind_of_mem (show K ∈ U from hK), mul_one]
      have hf'nU : ∀ K, ¬ 0 < f K → f' K = f K := fun K hK => by
        simp only [hf']; rw [DecisionTree.ind_of_not_mem (show K ∉ U from hK), mul_zero, sub_zero]
      have hfz : ∀ K, ¬ 0 < f K → f K = 0 := fun K hK => le_antisymm (not_lt.1 hK) (hf0 K)
      have hf'0s : ∀ K ∈ s, 0 ≤ f' K := fun K hK => by
        by_cases hfK : 0 < f K
        · rw [hf'U K hfK]; linarith [hm₀le K hK hfK]
        · rw [hf'nU K hfK]; exact hf0 K
      set f'' : α → ℝ := fun K => max (f' K) 0 with hf''
      have hf''mono : Monotone f'' := by
        intro K K' hKK'
        simp only [hf'', hf']
        by_cases hK : 0 < f K
        · have hK' : 0 < f K' := lt_of_lt_of_le hK (hf hKK')
          rw [DecisionTree.ind_of_mem (show K ∈ U from hK),
            DecisionTree.ind_of_mem (show K' ∈ U from hK')]
          exact max_le_max (by linarith [hf hKK']) le_rfl
        · rw [hfz K hK, DecisionTree.ind_of_not_mem (show K ∉ U from hK)]
          simp only [mul_zero, sub_zero, max_self]
          exact le_max_right _ _
      have hf''0 : ∀ K, 0 ≤ f'' K := fun K => le_max_right _ _
      have hf''s : ∀ K ∈ s, f'' K = f' K := fun K hK => max_eq_left (hf'0s K hK)
      obtain ⟨K₀, hK₀, hK₀m⟩ := Finset.mem_image.1 (Finset.min'_mem _ (hne.image f))
      have hlt : (s.filter fun K => 0 < f'' K).card < n := by
        rw [← hn]
        refine Finset.card_lt_card ⟨fun K hK => ?_, fun hsub => ?_⟩
        · rw [Finset.mem_filter] at hK ⊢
          refine ⟨hK.1, ?_⟩
          by_contra hfK
          rw [hf''s K hK.1, hf'nU K hfK, hfz K hfK] at hK
          exact lt_irrefl _ hK.2
        · have h1 : K₀ ∈ s.filter fun K => 0 < f'' K := hsub hK₀
          rw [Finset.mem_filter] at h1
          have hs₀ := (Finset.mem_filter.1 hK₀)
          rw [hf''s K₀ hs₀.1, hf'U K₀ hs₀.2, hK₀m, ← hm₀] at h1
          exact lt_irrefl _ (by linarith [h1.2] : m₀ < m₀)
      have hrec := ih _ hlt f'' hf''mono hf''0 rfl
      have hsplit : ∑ K ∈ s, a K * f K
          = ∑ K ∈ s, a K * f'' K + m₀ * ∑ K ∈ s, a K * DecisionTree.ind U K := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun K hK => ?_
        rw [hf''s K hK]
        simp only [hf']; ring
      rw [hsplit]
      exact add_nonneg hrec (mul_nonneg hm₀pos.le (ha U hUup))

/-! ## Decision-tree Harris along the exploration

The bond `TreeHarris.treeHarris_real` states `E[f]·P(Y) ≤ E[E[f ∣ ℱ_T]·1_Y]` for a monotone
`f ≥ 0` of the whole configuration and an increasing `Y`; it needs Gladkov's induction over the
decision tree, and the layer-cake extension above to pass from up-set indicators to a real `f`.

Every bond consumer of that theorem (`Continuity/CovTau/StarH.lean`, `StarNReal.lean`,
`StarBridge*.lean`) instantiates `f` at `fcl Ψ x`, a functional of the open cluster of a vertex, and
such an `f` is read off the exploration record.  For those `f` the conditional expectation is the
function itself (`cE_eq_self_of_recordDetermined`), so the statement collapses to Harris' inequality
for `f` and `1_Y`, with no tree induction and no sign hypothesis.  That is the content of the two
theorems here.  For an `f` that is NOT read off the record the collapse fails, and the statement is
the genuine decision-tree inequality; nothing in this file proves it.
-/

/-- The mean of an indicator over an event is the probability of the intersection. -/
theorem setIntegral_ind_eq_real [Fintype E] (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (A X : Set (Set E)) : (∫ ω in A, DecisionTree.ind X ω ∂μ) = μ.real (A ∩ X) := by
  have hfun : (fun ω : Set E => DecisionTree.ind X ω) = X.indicator (1 : Set E → ℝ) := by
    funext ω; simp only [DecisionTree.indicator_eq_mul_ind, Pi.one_apply, one_mul]
  rw [hfun, setIntegral_indicator (measurableSet_of_fintype X), Set.inter_comm]
  simp

/-- The mean of an indicator is the probability. -/
theorem integral_ind_eq_real [Fintype E] (μ : Measure (Set E)) [IsFiniteMeasure μ] (X : Set (Set E)) :
    (∫ ω, DecisionTree.ind X ω ∂μ) = μ.real X := by
  have h := setIntegral_ind_eq_real μ (Set.univ : Set (Set E)) X
  rwa [Measure.restrict_univ, Set.univ_inter] at h

/-- **Lemma TH for the hyperedge exploration**, for a monotone function of the configuration that is
read off the exploration record: `E[f]·P(Y) ≤ E[E[f ∣ ℱ]·1_Y]`.  The conditional expectation is the
function itself, so this is Harris' inequality for `f` against the increasing indicator `1_Y`.
Bond template: `TreeHarris.treeHarris_real`, which carries `f ≥ 0`; that hypothesis is not needed
here. -/
theorem treeHarris_real_recordDetermined [Fintype E] (H : Hypergraph V E) (S : Set V)
    {f : Set E → ℝ} (hf : Monotone f)
    (hfrec : ∀ ν ν' : Set E, recordAt H S ν = recordAt H S ν' → f ν = f ν')
    {Y : Set (Set E)} (hY : IsUpperSet Y) :
    (∫ ω, f ω ∂(prodBernoulli H.prob)) * (prodBernoulli H.prob).real Y
      ≤ ∫ ω, cE H S f ω * DecisionTree.ind Y ω ∂(prodBernoulli H.prob) := by
  have hcE : ∀ ω : Set E, cE H S f ω = f ω := cE_eq_self_of_recordDetermined H S hfrec
  simp only [hcE]
  have h := prodBernoulli_integral_mul_le H.prob hf (monotone_ind_of_isUpperSet hY)
  rwa [integral_ind_eq_real] at h

/-- **The cluster case**, the one every bond consumer of `treeHarris_real` uses: `F` increasing on
vertex sets and `f = F(C_S)`.  The same inequality also follows from
`integral_fibreMean_mul_real_le` of `KN/HyperDecisionTree.lean`, which is where the hyperedge
development records Harris for a cluster functional against an increasing event. -/
theorem treeHarris_real_cluster [Fintype E] (H : Hypergraph V E) (S : Set V)
    {F : Set V → ℝ} (hF : Monotone F) {Y : Set (Set E)} (hY : IsUpperSet Y) :
    (∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) * (prodBernoulli H.prob).real Y
      ≤ ∫ ω, cE H S (fun ν => F (hyperClusterSet H ν S)) ω * DecisionTree.ind Y ω
          ∂(prodBernoulli H.prob) := by
  refine treeHarris_real_recordDetermined H S
    (fun _ _ h => hF (hyperClusterSet_mono H S h)) (fun ν ν' hν => ?_) hY
  have h : hyperClusterSet H ν S = hyperClusterSet H ν' S := by
    have := congrArg ExplorationRecord.reached hν
    simpa using this
  rw [h]

/-- The same inequality with the conditional expectation on the indicator instead, the shape of the
bond `ED_mul_PrW_le_ED_mul_cE_ind`.  It is `treeHarris_real_cluster` moved across
`integral_mul_cE_comm`. -/
theorem integral_mul_condRecord_ind_ge [Fintype E] (H : Hypergraph V E) (S : Set V)
    {F : Set V → ℝ} (hF : Monotone F) {Y : Set (Set E)} (hY : IsUpperSet Y) :
    (∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) * (prodBernoulli H.prob).real Y
      ≤ ∫ ω, F (hyperClusterSet H ω S) * cE H S (fun ν => DecisionTree.ind Y ν) ω
          ∂(prodBernoulli H.prob) := by
  have hcomm := integral_mul_cE_comm H S (fun ν => F (hyperClusterSet H ν S))
    (fun ν => DecisionTree.ind Y ν)
  rw [hcomm]
  exact treeHarris_real_cluster H S hF hY

/-- The conditional expectation on the indicator of `Y` is the residual probability of `Y`. -/
theorem cE_ind_eq_condRecord [Fintype E] (H : Hypergraph V E) (S : Set V) (Y : Set (Set E))
    (ω : Set E) :
    cE H S (fun ν => DecisionTree.ind Y ν) ω = condRecord H (recordAt H S ω) Y :=
  condRecordFun_ind H (recordAt H S ω) Y

/-! ## The conditioned covariance transfer

`KN/HyperProjGen.lean` already carries the projection of `F(C_b) − F(C_a)` onto the explored
cluster of `b` (`projFun`, `monotone_projFun`) and the projection identities
(`setIntegral_clusterFamily_eq`, which is the hyperedge form of the bond `CovTau.tower_clusterFun`,
and `setIntegral_sub_eq_projFun`).  What is added here is the monotonicity of the subtracted
conditional mean on its own, and the transfer statement the two-relay surplus step consumes.
-/

/-- **The conditional mean `E[F(C_a) | C_b = K]` is decreasing in `K`.**  A larger explored cluster
closes more labels, so the recomputed cluster of `a` shrinks.  This is the second half of
`monotone_projFun` of `KN/HyperProjGen.lean`, isolated; the bond template is
`CovTau.antitone_condMean`. -/
theorem antitone_condMean [Fintype E] (H : Hypergraph V E) (a : V) {F : Set V → ℝ}
    (hF : ∀ K L : Set V, K ⊆ L → F K ≤ F L) :
    Antitone fun K : Set V =>
      ∫ η, F (hyperClusterSet H (η \ labelsMeeting H K) ({a} : Set V)) ∂(prodBernoulli H.prob) := by
  intro K K' hKK'
  refine integral_mono (integrable_of_fintype _) (integrable_of_fintype _) fun η => ?_
  refine hF _ _ (hyperClusterSet_mono H ({a} : Set V) ?_)
  exact fun e he => ⟨he.1, fun hmem => he.2 (labelsMeeting_mono H hKK' hmem)⟩

/-- **The conditioned covariance transfer.**  The two-relay surplus step consumes the transfer
inequality for the functional `F(C_b) − F(C_a)`, which is not a functional of the explored cluster
of `b`; the covariance transfer itself is available for a monotone functional of that cluster.  On
the event that `b` avoids `a` the two agree in mean, cluster event by cluster event
(`setIntegral_sub_eq_projFun` and `setIntegral_sub_eq_projFun_conn` of `KN/HyperProjGen.lean`), so
the inequality for the projection is the inequality for the difference.  Bond template:
`CovTau.covTransfer_of_covTau`. -/
theorem covTransfer_of_covTau [Fintype V] [Fintype E] (H : Hypergraph V E) (o v a b : V)
    (F : Set V → ℝ)
    (hCT :
      (prodBernoulli H.prob).real
            (avoidEvent H ({v} : Set V) ({b, a} : Set V) ∩ hyperConn H v o) *
          ((prodBernoulli H.prob).real (avoidEvent H ({b} : Set V) ({a} : Set V)) *
              (∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b v,
                projFun H a F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob)) -
            (prodBernoulli H.prob).real
                (avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b v) *
              ∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V),
                projFun H a F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob))
        ≤ (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({b, a} : Set V)) *
            ((prodBernoulli H.prob).real (avoidEvent H ({b} : Set V) ({a} : Set V)) *
                (∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b o,
                  projFun H a F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob)) -
              (prodBernoulli H.prob).real
                  (avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b o) *
                ∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V),
                  projFun H a F (hyperClusterSet H ω ({b} : Set V))
                    ∂(prodBernoulli H.prob))) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) ({b, a} : Set V) ∩ hyperConn H v o) *
        ((prodBernoulli H.prob).real (avoidEvent H ({b} : Set V) ({a} : Set V)) *
            (∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b v,
              (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
                ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real
              (avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b v) *
            ∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V),
              (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
                ∂(prodBernoulli H.prob))
      ≤ (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({b, a} : Set V)) *
          ((prodBernoulli H.prob).real (avoidEvent H ({b} : Set V) ({a} : Set V)) *
              (∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b o,
                (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
                  ∂(prodBernoulli H.prob)) -
            (prodBernoulli H.prob).real
                (avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b o) *
              ∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V),
                (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
                  ∂(prodBernoulli H.prob)) := by
  classical
  have hconn : ∀ x : V, (⋃ t ∈ ({x} : Finset V), hyperConn H b t) = hyperConn H b x := by
    intro x; simp
  have iO : ∀ x : V,
      (∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b x,
          (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
            ∂(prodBernoulli H.prob))
        = ∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V) ∩ hyperConn H b x,
            projFun H a F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob) := by
    intro x
    have h := setIntegral_sub_eq_projFun_conn H a b F ({x} : Finset V)
    rwa [hconn x] at h
  have iD : (∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V),
        (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
          ∂(prodBernoulli H.prob))
      = ∫ ω in avoidEvent H ({b} : Set V) ({a} : Set V),
          projFun H a F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob) := by
    have h := setIntegral_sub_eq_projFun H a b F (Set.univ : Set (Set V))
    simpa using h
  rw [iO v, iO o, iD]
  exact hCT

/-! ## Marker dominance -/

/-- **Harris' inequality, functional form**, for the hyperedge model.  The bond template
`HullPort.integral_harris` carries a nonnegativity hypothesis on both factors;
`prodBernoulli_integral_mul_le` of `KN/ProdBernoulliFKG.lean` does not need it. -/
theorem integral_harris [Fintype E] (H : Hypergraph V E) {f g : Set E → ℝ}
    (hf : Monotone f) (hg : Monotone g) :
    (∫ ω, f ω ∂(prodBernoulli H.prob)) * (∫ ω, g ω ∂(prodBernoulli H.prob))
      ≤ ∫ ω, f ω * g ω ∂(prodBernoulli H.prob) :=
  prodBernoulli_integral_mul_le H.prob hf hg

/-- Two indicators with the same truth value agree. -/
theorem ind_congr_of_iff {ι κ : Type*} {P : Set ι} {Q : Set κ} {x : ι} {u : κ}
    (h : x ∈ P ↔ u ∈ Q) : DecisionTree.ind P x = DecisionTree.ind Q u := by
  by_cases hx : x ∈ P
  · rw [DecisionTree.ind_of_mem hx, DecisionTree.ind_of_mem (h.1 hx)]
  · rw [DecisionTree.ind_of_not_mem hx, DecisionTree.ind_of_not_mem (fun hu => hx (h.2 hu))]

/-- The event that the cluster of `s` avoids `{y}` is the complement of `{s ↔ y}`. -/
theorem avoidEvent_singleton_eq_compl (H : Hypergraph V E) (s y : V) :
    avoidEvent H ({s} : Set V) ({y} : Set V) = (hyperConn H s y)ᶜ := by
  ext ω
  simp only [mem_avoidEvent, Set.disjoint_singleton_right, hyperClusterSet, Set.mem_compl_iff,
    hyperConn, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h hr; exact h ⟨s, rfl, hr⟩
  · rintro h ⟨x, rfl, hr⟩; exact h hr

/-- **Marker dominance, no avoided set.**  For a monotone functional `F` of the cluster of `s` and
vertices `y`, `z`,

  `μ(s ↮ y, y ↔ z) · Cov(F(C_s), 1{s ↔ y}) ≤ μ(s ↮ y) · Cov(F(C_s), 1{s ↔ z})`,

that is, the marker `z` is at least `μ(y ↔ z ∣ s ↮ y)` times as correlated with every increasing
functional of the cluster of `s` as `y` is.  The proof is the bond one: with `B = Z ∪ W` the
identity

  `μ(N)Cov(F,1_Z) − μ(WN)Cov(F,1_Y) = μ(N)[∫_B F − (∫F)μ(B)] + [μ(WN)∫_N F − μ(N)∫_{W∩N} F]`,

whose first bracket is nonnegative by Harris and whose second is nonnegative because, conditionally
on `{s ↮ y}`, an increasing functional of the cluster of `s` and the increasing functional
`K ↦ 1{z ∈ K}` of the cluster of `y` are negatively correlated
(`avoid_cluster_negCorrelation` of `KN/HyperTwoCluster.lean` with the hypothesis discharged by
`oneClusterInequality_holds`).  The bond template gets the second bracket from the "off-cluster"
form of van den Berg–Häggström–Kahn's Theorem 1.3 and carries a nonnegativity hypothesis on `F` and
the nondegeneracy `s ≠ y`; neither is needed here. -/
theorem markerDominance_noAvoid [Fintype V] [Fintype E] (H : Hypergraph V E) (s y z : V)
    {F : Set V → ℝ} (hF : Monotone F) :
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
  classical
  set μ := prodBernoulli H.prob with hμ
  have hmeas : ∀ A : Set (Set E), MeasurableSet A := fun A => measurableSet_of_fintype A
  set Y : Set (Set E) := hyperConn H s y with hY
  set Z : Set (Set E) := hyperConn H s z with hZ
  set W : Set (Set E) := hyperConn H y z with hW
  set N : Set (Set E) := Yᶜ with hN
  set f : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({s} : Set V)) with hf
  have hfmono : Monotone f := fun _ _ h => hF (hyperClusterSet_mono H ({s} : Set V) h)
  have hint : ∀ A : Set (Set E), IntegrableOn f A μ := fun A => integrable_of_fintype f
  -- `W ∩ N = W ∖ Z`
  have hWN : W ∩ N = W \ Z := by
    ext ω
    simp only [hW, hN, hZ, hY, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff, hyperConn,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hyz, hsy⟩
      exact ⟨hyz, fun hsz => hsy (hsz.trans hyz.symm)⟩
    · rintro ⟨hyz, hsz⟩
      exact ⟨hyz, fun hsy => hsz (hsy.trans hyz)⟩
  have hBdisj : Disjoint Z (W ∩ N) := by rw [hWN]; exact disjoint_sdiff_right
  have hBunion : Z ∪ W = Z ∪ (W ∩ N) := by rw [hWN, Set.union_sdiff_self]
  have hBup : IsUpperSet (Z ∪ W) :=
    (isUpperSet_hyperConn H s z).union (isUpperSet_hyperConn H y z)
  -- the four bookkeeping identities
  have iB : ∫ ω in Z ∪ W, f ω ∂μ = (∫ ω in Z, f ω ∂μ) + ∫ ω in W ∩ N, f ω ∂μ := by
    rw [hBunion]; exact setIntegral_union hBdisj (hmeas _) (hint _) (hint _)
  have mB : μ.real (Z ∪ W) = μ.real Z + μ.real (W ∩ N) := by
    rw [hBunion]; exact measureReal_union hBdisj (hmeas _)
  have iY : (∫ ω in Y, f ω ∂μ) + ∫ ω in N, f ω ∂μ = ∫ ω, f ω ∂μ :=
    integral_add_compl (hmeas Y) (integrable_of_fintype f)
  have mY : μ.real Y + μ.real N = 1 := by
    have h := measureReal_add_measureReal_compl (μ := μ) (hmeas Y)
    rwa [probReal_univ] at h
  -- (a) Harris: `(∫ f) μ(Z ∪ W) ≤ ∫_{Z ∪ W} f`
  have ha : (∫ ω, f ω ∂μ) * μ.real (Z ∪ W) ≤ ∫ ω in Z ∪ W, f ω ∂μ := by
    have h := integral_harris H hfmono (monotone_ind_of_isUpperSet hBup)
    have e1 : (∫ ω, DecisionTree.ind (Z ∪ W) ω ∂μ) = μ.real (Z ∪ W) := by
      have hfun : (fun ω : Set E => DecisionTree.ind (Z ∪ W) ω)
          = (Z ∪ W).indicator (1 : Set E → ℝ) := by
        funext ω; simp only [DecisionTree.indicator_eq_mul_ind, Pi.one_apply, one_mul]
      rw [hfun, integral_indicator_one (hmeas _)]
    have e2 : (∫ ω, f ω * DecisionTree.ind (Z ∪ W) ω ∂μ) = ∫ ω in Z ∪ W, f ω ∂μ := by
      have hfun : (fun ω : Set E => f ω * DecisionTree.ind (Z ∪ W) ω)
          = (Z ∪ W).indicator f := by
        funext ω; simp only [DecisionTree.indicator_eq_mul_ind]
      rw [hfun, integral_indicator (hmeas _)]
    rw [e1, e2] at h
    exact h
  -- (b) the two clusters are negatively correlated given `{s ↮ y}`
  have hGup : IsUpperSet {K : Set V | z ∈ K} := fun _ _ hKK' hz => hKK' hz
  have hAN : avoidEvent H ({s} : Set V) ({y} : Set V) = N := by
    rw [avoidEvent_singleton_eq_compl H s y]
  have hGW : ∀ ω : Set E,
      DecisionTree.ind {K : Set V | z ∈ K} (hyperClusterSet H ω ({y} : Set V))
        = DecisionTree.ind W ω := by
    intro ω
    refine ind_congr_of_iff ?_
    simp only [Set.mem_setOf_eq, hyperClusterSet, hW, hyperConn, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl, hr⟩; exact hr
    · intro hr; exact ⟨y, rfl, hr⟩
  have hb0 := avoid_cluster_negCorrelation H ({s} : Set V) ({y} : Set V)
    (oneClusterInequality_holds H ({s} : Set V) ({y} : Set V)) hF
    (monotone_ind_of_isUpperSet hGup)
  rw [hAN] at hb0
  simp only [hGW] at hb0
  -- rewrite the two `1_W` integrals over `N`
  have iWN : (∫ ω in N, f ω * DecisionTree.ind W ω ∂μ) = ∫ ω in W ∩ N, f ω ∂μ := by
    have hfun : (fun ω : Set E => f ω * DecisionTree.ind W ω) = W.indicator f := by
      funext ω; simp only [DecisionTree.indicator_eq_mul_ind]
    rw [hfun, setIntegral_indicator (hmeas W), Set.inter_comm]
  have iW : (∫ ω in N, DecisionTree.ind W ω ∂μ) = μ.real (W ∩ N) := by
    have hfun : (fun ω : Set E => DecisionTree.ind W ω) = W.indicator (1 : Set E → ℝ) := by
      funext ω; simp only [DecisionTree.indicator_eq_mul_ind, Pi.one_apply, one_mul]
    rw [hfun, setIntegral_indicator (hmeas W), Set.inter_comm]
    simp
  rw [iWN, iW] at hb0
  -- combine
  have hN0 : 0 ≤ μ.real N := measureReal_nonneg
  have mY' : μ.real Y = 1 - μ.real N := by linarith
  have ident : μ.real N * ((∫ ω in Z, f ω ∂μ) - (∫ ω, f ω ∂μ) * μ.real Z) -
      μ.real (W ∩ N) * ((∫ ω in Y, f ω ∂μ) - (∫ ω, f ω ∂μ) * μ.real Y) =
      μ.real N * ((∫ ω in Z ∪ W, f ω ∂μ) - (∫ ω, f ω ∂μ) * μ.real (Z ∪ W)) +
        (μ.real (W ∩ N) * (∫ ω in N, f ω ∂μ) - μ.real N * ∫ ω in W ∩ N, f ω ∂μ) := by
    rw [mY', ← iY, iB, mB]; ring
  have h1 : 0 ≤ μ.real N * ((∫ ω in Z ∪ W, f ω ∂μ) - (∫ ω, f ω ∂μ) * μ.real (Z ∪ W)) := by
    nlinarith [ha, hN0]
  have h2 : 0 ≤ μ.real (W ∩ N) * (∫ ω in N, f ω ∂μ) - μ.real N * ∫ ω in W ∩ N, f ω ∂μ := by
    nlinarith [hb0]
  have hgoal : μ.real (N ∩ W) = μ.real (W ∩ N) := by rw [Set.inter_comm]
  rw [hgoal]
  linarith [ident, h1, h2]

/-! ## The hybrid bookkeeping of the cluster-conditioning step -/

/-- **The hybrid event as a record average.**  `E[1_X · P(Y ∣ ℱ)]` is the sum over the possible
records of the probability that the exploration stops with that record inside `X`, times the
residual probability of `Y` at that record.  This is the hyperedge form of the bond
`MarkerDominancePv.Pr2W_hybrid_eq_sum_condSumW`, whose left-hand side is the probability that a
pair of independent configurations has the first in `X` and the splice in `Y`; here the splice is
integrated out into `condRecord`, so no product space is needed.  It is an identity of finite sums
with no positivity requirement on any record event. -/
theorem integral_ind_mul_cE_ind_eq_sum [Fintype E] (H : Hypergraph V E) (S : Set V)
    (X Y : Set (Set E)) :
    (∫ ω, DecisionTree.ind X ω * cE H S (fun ν => DecisionTree.ind Y ν) ω
        ∂(prodBernoulli H.prob))
      = ∑ r ∈ recordSet H S,
          (prodBernoulli H.prob).real (recordEvent H S r ∩ X) * condRecord H r Y := by
  classical
  rw [integral_eq_sum_recordEvent H S
    (fun ω => DecisionTree.ind X ω * cE H S (fun ν => DecisionTree.ind Y ν) ω)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [setIntegral_congr_fun (measurableSet_recordEvent H S r)
    (g := fun ω => DecisionTree.ind X ω * condRecord H r Y)
    fun ω hω => by rw [cE_eq_of_mem_recordEvent H S _ hω, condRecordFun_ind]]
  rw [integral_mul_const, setIntegral_ind_eq_real]

/-- **Cluster-conditional Harris**, in the case the hyperedge development uses: for an increasing
event `X` that is read off the exploration record and an increasing event `Y`,

  `P(X) · P(Y) ≤ Σ_r P(record = r, X) · P_r(Y)`.

Bond template: `MarkerDominancePv.sum_condSumW_ge`, which holds for an arbitrary increasing `X` and
is Gladkov's Theorem 3.2 for the stopped exploration.  Here `X` is required to be read off the
record; then `cE 1_X = 1_X`, the symmetry `integral_mul_cE_comm` turns the right-hand side into
`P(X ∩ Y)`, and the inequality is Harris' for two increasing events.  For an `X` not read off the
record the argument does not apply: the residual probability of an increasing `Y` is not a monotone
function of the configuration, which is exactly why the bond proof induces over the decision tree. -/
theorem sum_condRecord_ge_of_recordDetermined [Fintype E] (H : Hypergraph V E) (S : Set V)
    {X Y : Set (Set E)}
    (hXrec : ∀ ν ν' : Set E, recordAt H S ν = recordAt H S ν' → (ν ∈ X ↔ ν' ∈ X))
    (hX : IsUpperSet X) (hY : IsUpperSet Y) :
    (prodBernoulli H.prob).real X * (prodBernoulli H.prob).real Y
      ≤ ∑ r ∈ recordSet H S,
          (prodBernoulli H.prob).real (recordEvent H S r ∩ X) * condRecord H r Y := by
  rw [← integral_ind_mul_cE_ind_eq_sum H S X Y,
    integral_mul_cE_comm H S (fun ν => DecisionTree.ind X ν) (fun ν => DecisionTree.ind Y ν)]
  have hcE : ∀ ω : Set E, cE H S (fun ν => DecisionTree.ind X ν) ω = DecisionTree.ind X ω :=
    cE_eq_self_of_recordDetermined H S fun ν ν' hν => ind_congr_of_iff (hXrec ν ν' hν)
  simp only [hcE]
  have hinter : (fun ω : Set E => DecisionTree.ind X ω * DecisionTree.ind Y ω)
      = fun ω : Set E => DecisionTree.ind (X ∩ Y) ω := by
    funext ω; rw [BHK2006.ind_inter]
  rw [hinter, integral_ind_eq_real]
  exact prodBernoulli_harris_upper H.prob hX hY (measurableSet_of_fintype X)
    (measurableSet_of_fintype Y)

/-! ## The avoided-set functionals `T_A`

The objects of the averaged inequality `T_A ≥ 0`, in the hyperedge model.  `delE` is the mean in the
model with a set of labels deleted; `cut H X ω` is the set of labels meeting the open cluster of
`X`, which in the bond bookkeeping is written as a set of pairs; `avoidEv` is `{r ↮ T}`, which the
rest of this development writes `avoidEvent H {r} T`.
-/

/-- `E[φ(η ∖ B)]`: the mean of `φ` when the labels of `B` are deleted. -/
def delE (H : Hypergraph V E) (B : Set E) (φ : Set E → ℝ) : ℝ :=
  ∫ η, φ (η \ B) ∂(prodBernoulli H.prob)

/-- The labels meeting the open cluster of the set `X` in `ω`. -/
def cut (H : Hypergraph V E) (X : Set V) (ω : Set E) : Set E :=
  labelsMeeting H (hyperClusterSet H ω X)

/-- `{r ↮ T}`: the root `r` is joined to no vertex of `T`. -/
def avoidEv (H : Hypergraph V E) (r : V) (T : Set V) : Set (Set E) :=
  avoidEvent H ({r} : Set V) T

theorem avoidEv_eq (H : Hypergraph V E) (r : V) (T : Set V) :
    avoidEv H r T = avoidEvent H ({r} : Set V) T := rfl

theorem cut_eq (H : Hypergraph V E) (X : Set V) (ω : Set E) :
    cut H X ω = labelsMeeting H (hyperClusterSet H ω X) := rfl

theorem delE_const (H : Hypergraph V E) (B : Set E) (c : ℝ) :
    delE H B (fun _ => c) = c := by simp [delE]

/-- `c(ω) = Cov_{H − cut_X(ω)}(g(C_s), 1{s ↔ y})`. -/
def taC (H : Hypergraph V E) (s y : V) (X : Set V) (g : Set V → ℝ) (ω : Set E) : ℝ :=
  delE H (cut H X ω)
      (fun η => g (hyperClusterSet H η ({s} : Set V)) * DecisionTree.ind (hyperConn H s y) η) -
    delE H (cut H X ω) (fun η => g (hyperClusterSet H η ({s} : Set V))) *
      delE H (cut H X ω) (fun η => DecisionTree.ind (hyperConn H s y) η)

/-- `μ_{H − cut_X(ω)}(s ↮ y)`. -/
def taN (H : Hypergraph V E) (s y : V) (X : Set V) (ω : Set E) : ℝ :=
  delE H (cut H X ω) (fun η => DecisionTree.ind (hyperConn H s y)ᶜ η)

/-- `μ_{H − cut_X(ω)}(s ↮ y, y ↔ z)`. -/
def taNW (H : Hypergraph V E) (s y z : V) (X : Set V) (ω : Set E) : ℝ :=
  delE H (cut H X ω)
    (fun η => DecisionTree.ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η)

/-- `B = Σ_K m(K) c_K = E[1{s ↮ X} · c]`. -/
def taB (H : Hypergraph V E) (s y : V) (X : Set V) (g : Set V → ℝ) : ℝ :=
  ∫ ω, DecisionTree.ind (avoidEv H s X) ω * taC H s y X g ω ∂(prodBernoulli H.prob)

/-- `A = E[1{s ↮ X} · (taNW / taN) · c]`. -/
def taA (H : Hypergraph V E) (s y z : V) (X : Set V) (g : Set V → ℝ) : ℝ :=
  ∫ ω, DecisionTree.ind (avoidEv H s X) ω *
    (taNW H s y z X ω / taN H s y X ω * taC H s y X g ω) ∂(prodBernoulli H.prob)

/-- `b = μ(y ↮ s, y ↮ X)`. -/
def tab (H : Hypergraph V E) (s y : V) (X : Set V) : ℝ :=
  (prodBernoulli H.prob).real (avoidEv H y (insert s X))

/-- `a = μ(y ↮ s, y ↮ X, y ↔ z)`. -/
def taa (H : Hypergraph V E) (s y z : V) (X : Set V) : ℝ :=
  (prodBernoulli H.prob).real (avoidEv H y (insert s X) ∩ hyperConn H y z)

/-- `Q = A·b − a·B`, which is `b · T_A`. -/
def taQ (H : Hypergraph V E) (s y z : V) (X : Set V) (g : Set V → ℝ) : ℝ :=
  taA H s y z X g * tab H s y X - taa H s y z X * taB H s y X g

end KNAll.Site.CTBase

end
