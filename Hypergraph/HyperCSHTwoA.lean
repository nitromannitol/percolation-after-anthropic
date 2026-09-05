import Hypergraph.HyperTreeHK
import Hypergraph.HyperCTBase
import Hypergraph.HyperCTOne
import Hypergraph.HyperAGBase
import Hypergraph.HyperAGOne
import Hypergraph.HyperCSHDefs
import Hypergraph.HyperPeel
import Hypergraph.HyperProjGen
import Hypergraph.HyperTransfer
import Hypergraph.HyperTwoClusterClosed
import Percolation.Continuity.CSH.LemmaT

/-!
# Layer 2, first half: level forms, Lemma T, (GEN) from (S5) graded by the relay count, the glue,
and the two-relay surplus transfer from the conditioned covariance transfer, for hyperedges

The hyperedge form of five modules of the bond development:
`Percolation/Continuity/CSH/LevelForms.lean`, `Percolation/Continuity/CSH/LemmaT.lean`,
`Percolation/Continuity/AdditiveGluing/GenOfSurplusTransfer.lean`,
`Percolation/Continuity/AdditiveGluing/Glue.lean` and
`Percolation/Continuity/LowerTail/SurplusTransferPairOfCov.lean`.  Everything is stated for a
`Hypergraph V E` with arbitrary incidence sets over arbitrary types, finiteness being assumed only
where it is used.

## What is already available, and is used verbatim

* All of `CSH/LevelForms.lean` except its last model-specific line: `CSH.slForm_congr`,
  `CSH.slForm_finset_sum`, `CSH.eq_sum_smul_single`, `CSH.slForm_eq_sum_single`,
  `CSH.cshMarg_eq_sum_single`, the unfolding objects `CSH.chi`, `CSH.jn`, `CSH.av`,
  `CSH.unfoldT`, `CSH.unfoldK` and the pointwise unfolding identity `CSH.slForm_jn` are stated for
  an arbitrary evaluation type and an arbitrary symmetric transitive relation; they never mention
  a percolation model.  The model-specific line is `CSH.map_fst_decoyList`, ported here as
  `map_fst_decoyList`.
* The linearity bookkeeping of `CSH/LemmaT.lean`: `CSH.cshMarg_zero`, `CSH.cshMarg_finset_sum`
  and the coefficient representation `CSH.cshMarg_eq_sum` are model-independent and are imported
  from `Percolation.Continuity.CSH.LemmaT`.
* `AGloc.filter_erase_of_not` is `filter_erase_of_not` of `KN/HyperPeel.lean`;
  `additiveGluing_of_surplusTransfer` (the composite (S5) ⟹ `AdditiveGluing`, one model at a
  time) is `AGOne.additiveGluing_of_surplusTransfer`, built on the ungraded induction
  `genY_of_surplusTransferY` of `KN/HyperProjGen.lean`; `additiveGluingSuffices_proof` is
  `AGOne.hyperAdditiveGluingSuffices`.
* The three transfers consumed by the two-relay step, `SurplusTransfer.ordTransfer`,
  `SurplusTransfer.blockHarrisTransfer` and `SurplusTransfer.plusPiece_nonneg`, are
  `CTOne.ordTransfer`, `CTOne.blockHarrisTransfer` and `CTOne.plusPiece_nonneg`; the one-relay
  transfer and the three-relay assembly are `AGOne.surplusTransfer_single` and
  `AGOne.gen_triple_of_surplusTransfer_pair`.

## What is added

* `map_fst_decoyList`, `cshMargin_eq_sum`, `slForm_jn_reachable` — the model-specific readings of
  the level forms: the decoys of `decoyList H A D` are `D`, the CSH margin is the fixed linear
  combination `Σ_u Λ(u)·covD(u)` with `Λ(u) = Marg[δ_u]`, and the unfolding identity at the
  reachability relation of an open hypergraph.
* **Lemma T** (`cshMargin_nonneg_of_within`, `cshHolds_of_within`).  The bond proof consumes the
  multi-marker reduction `BHK2006_multiMarkerCov_nonneg_of_within`, which rests on the two-block
  Gibbs sampler of van den Berg–Häggström–Kahn (`Percolation/Literature/TwoClusterGibbsSampler.lean`
  and `TwoClusterGibbsCovariance.lean`, 1385 lines of bond Lean).  No hyperedge form of that
  sampler exists in this development, so the reduction is proved here from scratch, in the
  calculus of the conditional expectation `CTBase.cE` given an exploration record:
  - `covDF_eq_withinF_add` — the exact one-step decomposition
    `cov_D(φ, h) = P(D)·R(φ) + cov_D(𝑇φ, h)`, `𝑇 = E[·∣C_s] ∘ E[·∣C_X]`, which in the bond file is
    proved by explicit sums over configurations and here is the tower property, the pull-out of a
    record-determined factor and the symmetry `E[f·cE g] = E[cE f·g]` of `KN/HyperCTBase.lean`;
  - `gibbsT`, `gibbsT_mono`, `gibbsT_iterate_bounds` — the operator on functions of the owner's
    vertex cluster, its monotonicity, and the oscillation contraction by `1 − ε`, where
    `ε = P(every label meeting X is closed) = ∏_{e meets X} (1 − p_e)` (`real_regen`,
    `real_regen_pos`).  On the regeneration event the cluster of `X` is `X` whatever was deleted
    (`hyperClusterSet_eq_of_mem_regen`), which is the coupling that makes the iterates converge;
  - `clusterCov_nonneg_of_within` — the reduction: if the averaged conditional covariance is
    nonnegative for every monotone nonnegative `g`, then `cov_D(f(C_s), h(C_s)) ≥ 0` for every
    monotone `f` and EVERY `h`;
  - `multiMarkerCov_nonneg_of_within` — its reading at `h = Σ_u c(u)·1{u ∈ C_s}`, with the
    conditional covariances written as covariances under the model `deleteHyper H (C_X ω)`.
* `gen_firstRank_of_surplusTransfer` — (S5) for every relay set of size at most `K` implies (GEN)
  for every relay set of size at most `K + 1`.  The ungraded statement is
  `genY_of_surplusTransferY`; the grading is what the bond development consumes, and it is proved
  by the same induction with the cardinality carried along.  Unlike the bond statement the
  hypothesis is asked for one model at a time.  `hyperAdditiveGluing_of_surplusTransfer` names the
  composite.
* `HyperAdditiveGluingGlue`, `hyperAdditiveGluingGlue_proof` — the glue as a named statement.
* `surplusTransfer_pair_of_covTransfer` — the two-relay surplus transfer (S5)₂ from the conditioned
  covariance transfer (COV).  The bond template assumes `v ≠ a`, `v ≠ b` and `F ≥ 0` and splits off
  `a = b`; none of that is needed here, because the hyperedge forms of the three transfers carry
  no such hypotheses and the case `a = b` is the case `P(a ↮ b) = 0` of the general argument.
  `surplusTransfer_pair_of_covTau` consumes the shape `CTBase.covTransfer_of_covTau` produces, and
  `gen_triple_of_covTransfer`, `gen_triple_of_covTau` compose with the three-relay assembly.

## Non-vacuity

`covD_nonneg_of_within_harris` discharges the hypothesis of the reduction by Harris' inequality in
the deleted model and recovers the one-cluster inequality `0 ≤ covD H s X f u` of van den
Berg–Häggström–Kahn (`oneCluster_contact_le` of `KN/HyperProjGen.lean`, proved there by a different
route).  `gen_singleton` reads the graded theorem at `K = 0`, where its hypothesis is vacuous, and
recovers Harris' inequality `P(o ↔ a)·E F(C_a) ≤ E[F(C_o); o ↔ a]`.  `surplusTransfer_pair_self`
reads (S5)₂ at `a = b`, where (COV) is the identity `0 = 0`, and recovers the one-relay transfer.

## The two facts about labels

Neither of the two mechanisms singled out for this port is needed here.  No step uses the
four-functions argument; the only record used is the exploration record of `KN/HyperDecisionTree.lean`,
and every function handed to the `cE` calculus is a function of a vertex cluster.  No step
transfers a measure along a label map, so no injectivity is used.  The one place where labels are
intrinsic is the regeneration event, which is the event that every LABEL meeting `X` is closed.

## The repair points

Of the four places where the hypergraph case is said to need a repair relative to the graph
argument, Lemma T is the two-block Gibbs argument: the iterates converge by the one-step identity
(stationarity) together with the oscillation contraction, and the contraction needs the
minorization by the event that every label incident to `X` is closed, of probability
`∏ (1 − p_e) > 0`.  The bond Lean already contains exactly this repair (`BHK2006.regenT`,
`BHK2006.regenWeight_eq_prod`, `BHK2006.gibbsE_iterate_sub_le`,
`BHK2006.covD_eq_sum_withinD_add`), and it is reproduced here.  The other three points do not
arise in these five modules.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006), §2.1 pp. 9–13
  (the chain, Claim 2.5, Remark 2.8), Thms. 1.3–1.5.
* G. Kozma, S. Nitzan, Conj. 1 (p. 3), Conj. 4 (p. 32).
* N. Gladkov, *Percolation inequalities and decision trees*, arXiv:2408.08457, Thm. 3.2.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Site.CSHTwoA

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Continuity
open KNAll.Site KNAll.Site.CTBase KNAll.Site.CTOne KNAll.Site.AGBase KNAll.Site.AGOne
open KNAll.Site.CSHDefs
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

/-! ## The level forms: the model-specific readings -/

section LevelForms

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The decoys of `decoyList H A D` are `D`.  Hyperedge form of `CSH.map_fst_decoyList`. -/
theorem map_fst_decoyList (H : Hypergraph V E) (A : Set V) (D : List V) :
    (decoyList H A D).map Prod.fst = D := by
  induction D generalizing A with
  | nil => rfl
  | cons d ds ih => simp [decoyList, ih]

/-- **Coefficient representation of the CSH margin**: `cshMargin H x Y D o v f = Σ_u Λ(u)·covD(u)`
with `Λ(u) = Marg[δ_u]`, the fixed linear combination the multi-marker reduction consumes. -/
theorem cshMargin_eq_sum (H : Hypergraph V E) (x : V) (Y : Set V) (D : List V) (o v : V)
    (f : Set V → ℝ) :
    cshMargin H x Y D o v f =
      ∑ u, CSH.cshMarg (decoyList H (insert x Y) D) (obsConst H o v (insert x Y ∪ {d | d ∈ D}))
          o v (Pi.single u 1) * covD H x Y f u := by
  unfold cshMargin
  exact CSH.cshMarg_eq_sum _ _ o v _

/-- **The pointwise unfolding identity of Lemma U at an open hypergraph.**  Reachability in
`openHyperGraph H ω` is symmetric and transitive, so `CSH.slForm_jn` applies to it verbatim. -/
theorem slForm_jn_reachable (H : Hypergraph V E) (ω : Set E) (L : List (V × (V → ℝ))) (S : Set V)
    (u : V) :
    CSH.slForm L (CSH.jn (fun a b => (openHyperGraph H ω).Reachable a b) S) u =
      CSH.jn (fun a b => (openHyperGraph H ω).Reachable a b) (S ∪ {d | d ∈ L.map Prod.fst}) u -
        CSH.unfoldT (fun a b => (openHyperGraph H ω).Reachable a b) S L u + CSH.unfoldK L u :=
  CSH.slForm_jn _ (fun _ _ h => h.symm) (fun _ _ _ h h' => h.trans h') L S u

end LevelForms

/-! ## Lemma T: the two-block Gibbs reduction for hyperedges

Owner `s`, avoided set `X`, `D = {s ↮ X}`.  The two operators of van den Berg–Häggström–Kahn's
chain act on functions of the owner's vertex cluster: `worldMean g K = E[g(C_s)]` in the model with
every label meeting `K` deleted, and `bStep ψ C = E[ψ(C_X)]` in the model with every label meeting
`C` deleted; `gibbsT g = bStep (worldMean g)` is one full step.  The regeneration event is that
every label meeting `X` is closed.
-/

section Gibbs

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The mean of a constant against a probability measure. -/
theorem integral_const_prob (μ : Measure (Set E)) [IsProbabilityMeasure μ] (a : ℝ) :
    ∫ _ω, a ∂μ = a := by
  rw [integral_const, probReal_univ, one_smul]

/-- `E[g(C_s)]` in the model with every label meeting `K` deleted: the world `H − K`. -/
def worldMean (H : Hypergraph V E) (s : V) (g : Set V → ℝ) (K : Set V) : ℝ :=
  ∫ η, g (hyperClusterSet H (η \ labelsMeeting H K) ({s} : Set V)) ∂(prodBernoulli H.prob)

/-- The world mean is the mean under the deleted parameters. -/
theorem worldMean_eq_deleteHyper (H : Hypergraph V E) (s : V) (g : Set V → ℝ) (K : Set V) :
    worldMean H s g K =
      ∫ η, g (hyperClusterSet H η ({s} : Set V)) ∂(prodBernoulli (deleteHyper H K).prob) :=
  delE_eq_integral_deleteHyper H K (fun η => g (hyperClusterSet H η ({s} : Set V)))

/-- Deleting more labels shrinks the owner's cluster: the world mean of a monotone `g` decreases
in `K`. -/
theorem worldMean_antitone (H : Hypergraph V E) (s : V) {g : Set V → ℝ} (hg : Monotone g) :
    Antitone (worldMean H s g) := by
  intro K K' hKK'
  exact integral_mono (integrable_of_fintype _) (integrable_of_fintype _) fun η =>
    hg (hyperClusterSet_mono H _ (sdiff_labelsMeeting_anti H η hKK'))

theorem worldMean_bounds (H : Hypergraph V E) (s : V) {g : Set V → ℝ} {a b : ℝ}
    (hg : ∀ C, a ≤ g C ∧ g C ≤ b) (K : Set V) :
    a ≤ worldMean H s g K ∧ worldMean H s g K ≤ b := by
  constructor
  · have h := integral_mono (μ := prodBernoulli H.prob) (f := fun _ => a)
      (g := fun η => g (hyperClusterSet H (η \ labelsMeeting H K) ({s} : Set V)))
      (integrable_of_fintype _) (integrable_of_fintype _) (fun η => (hg _).1)
    rwa [integral_const_prob] at h
  · have h := integral_mono (μ := prodBernoulli H.prob) (g := fun _ => b)
      (f := fun η => g (hyperClusterSet H (η \ labelsMeeting H K) ({s} : Set V)))
      (integrable_of_fintype _) (integrable_of_fintype _) (fun η => (hg _).2)
    rwa [integral_const_prob] at h

theorem worldMean_nonneg (H : Hypergraph V E) (s : V) {g : Set V → ℝ} (hg0 : ∀ C, 0 ≤ g C)
    (K : Set V) : 0 ≤ worldMean H s g K :=
  integral_nonneg fun _ => hg0 _

/-- `E[ψ(C_X)]` in the model with every label meeting `C` deleted. -/
def bStep (H : Hypergraph V E) (X : Set V) (ψ : Set V → ℝ) (C : Set V) : ℝ :=
  ∫ η, ψ (hyperClusterSet H (η \ labelsMeeting H C) X) ∂(prodBernoulli H.prob)

/-- **One step of the chain** on functions of the owner's cluster. -/
def gibbsT (H : Hypergraph V E) (s : V) (X : Set V) (g : Set V → ℝ) : Set V → ℝ :=
  bStep H X (worldMean H s g)

theorem bStep_mono_of_antitone (H : Hypergraph V E) (X : Set V) {ψ : Set V → ℝ}
    (hψ : Antitone ψ) : Monotone (bStep H X ψ) := by
  intro C C' hCC'
  exact integral_mono (integrable_of_fintype _) (integrable_of_fintype _) fun η =>
    hψ (hyperClusterSet_mono H X (sdiff_labelsMeeting_anti H η hCC'))

theorem bStep_nonneg (H : Hypergraph V E) (X : Set V) {ψ : Set V → ℝ} (hψ : ∀ K, 0 ≤ ψ K)
    (C : Set V) : 0 ≤ bStep H X ψ C :=
  integral_nonneg fun _ => hψ _

/-- The step preserves monotonicity (Remark 2.8 of van den Berg–Häggström–Kahn): a decreasing
function of the explored cluster of `X`, resampled given the owner's cluster, increases in it. -/
theorem gibbsT_mono (H : Hypergraph V E) (s : V) (X : Set V) {g : Set V → ℝ} (hg : Monotone g) :
    Monotone (gibbsT H s X g) :=
  bStep_mono_of_antitone H X (worldMean_antitone H s hg)

theorem gibbsT_nonneg (H : Hypergraph V E) (s : V) (X : Set V) {g : Set V → ℝ}
    (hg0 : ∀ C, 0 ≤ g C) (C : Set V) : 0 ≤ gibbsT H s X g C :=
  bStep_nonneg H X (worldMean_nonneg H s hg0) C

theorem gibbsT_iterate_mono_nonneg (H : Hypergraph V E) (s : V) (X : Set V) {g : Set V → ℝ}
    (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) (n : ℕ) :
    Monotone ((gibbsT H s X)^[n] g) ∧ ∀ C, 0 ≤ (gibbsT H s X)^[n] g C := by
  induction n with
  | zero => exact ⟨hg, hg0⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨gibbsT_mono H s X ih.1, fun C => gibbsT_nonneg H s X ih.2 C⟩

/-! ### Regeneration -/

/-- The regeneration event: every label meeting `X` is closed. -/
def regen (H : Hypergraph V E) (X : Set V) : Set (Set E) :=
  {η | ∀ e ∈ labelsMeeting H X, e ∉ η}

/-- **The regeneration probability is `∏ (1 − p_e)` over the labels meeting `X`.** -/
theorem real_regen (H : Hypergraph V E) (X : Set V) :
    (prodBernoulli H.prob).real (regen H X) =
      ∏ e ∈ (labelsMeeting H X).toFinset, (1 - (H.prob e : ℝ)) := by
  rw [← prodBernoulli_real_forall_notMem H.prob (labelsMeeting H X).toFinset]
  congr 1
  ext η
  simp only [regen, Set.mem_setOf_eq, Set.mem_toFinset]

/-- It is positive as soon as every label meeting `X` has `p_e < 1`. -/
theorem real_regen_pos (H : Hypergraph V E) (X : Set V)
    (hX : ∀ e ∈ labelsMeeting H X, (H.prob e : ℝ) < 1) :
    0 < (prodBernoulli H.prob).real (regen H X) := by
  rw [real_regen]
  exact Finset.prod_pos fun e he => sub_pos.2 (hX e (Set.mem_toFinset.1 he))

/-- **On the regeneration event the cluster of `X` is `X`, whatever was deleted.**  This is the
coupling: the resampled cluster of `X` does not depend on the owner's cluster. -/
theorem hyperClusterSet_eq_of_mem_regen (H : Hypergraph V E) (X : Set V) {η : Set E}
    (hη : η ∈ regen H X) (B : Set E) : hyperClusterSet H (η \ B) X = X := by
  refine Set.Subset.antisymm ?_ (subset_hyperClusterSet H _ X)
  rintro y ⟨x, hx, hr⟩
  have hiso : ∀ e ∈ η \ B, x ∉ H.incidence e := fun e he hxe =>
    hη e ((mem_labelsMeeting H X e).2 (Set.not_disjoint_iff.2 ⟨x, hxe, hx⟩)) he.1
  rw [eq_of_reachable_of_isolated H hiso hr]
  exact hx

/-- **Oscillation contraction of the second half-step**: for `ψ` with values in `[a, b]`,
`bStep ψ C − bStep ψ C' ≤ (1 − ε)(b − a)`, `ε` the regeneration probability. -/
theorem bStep_sub_le (H : Hypergraph V E) (X : Set V) {ψ : Set V → ℝ} {a b : ℝ}
    (hψ : ∀ K, a ≤ ψ K ∧ ψ K ≤ b) (C C' : Set V) :
    bStep H X ψ C - bStep H X ψ C' ≤
      (1 - (prodBernoulli H.prob).real (regen H X)) * (b - a) := by
  unfold bStep
  rw [← integral_sub (integrable_of_fintype _) (integrable_of_fintype _)]
  have hpt : ∀ η : Set E,
      ψ (hyperClusterSet H (η \ labelsMeeting H C) X) -
          ψ (hyperClusterSet H (η \ labelsMeeting H C') X) ≤
        (b - a) * ind (regen H X)ᶜ η := by
    intro η
    by_cases hη : η ∈ regen H X
    · rw [ind_of_not_mem (Set.notMem_compl_iff.2 hη), mul_zero,
        hyperClusterSet_eq_of_mem_regen H X hη, hyperClusterSet_eq_of_mem_regen H X hη, sub_self]
    · rw [ind_of_mem (Set.mem_compl hη), mul_one]
      linarith [(hψ (hyperClusterSet H (η \ labelsMeeting H C) X)).2,
        (hψ (hyperClusterSet H (η \ labelsMeeting H C') X)).1]
  calc _ ≤ ∫ η, (b - a) * ind (regen H X)ᶜ η ∂(prodBernoulli H.prob) :=
        integral_mono (integrable_of_fintype _) (integrable_of_fintype _) hpt
    _ = (b - a) * (prodBernoulli H.prob).real (regen H X)ᶜ := by
        rw [integral_const_mul, integral_ind_eq_real]
    _ = _ := by
        rw [measureReal_compl (measurableSet_of_fintype _), probReal_univ]; ring

/-- **The iterates contract**: the `n`-th iterate of a function with values in `[a, b]` has
values in an interval of length at most `(1 − ε)ⁿ (b − a)`. -/
theorem gibbsT_iterate_bounds (H : Hypergraph V E) (s : V) (X : Set V) {g : Set V → ℝ}
    {a b : ℝ} (hg : ∀ C, a ≤ g C ∧ g C ≤ b) (n : ℕ) :
    ∃ a' b' : ℝ, (∀ C, a' ≤ (gibbsT H s X)^[n] g C ∧ (gibbsT H s X)^[n] g C ≤ b') ∧
      b' - a' ≤ (1 - (prodBernoulli H.prob).real (regen H X)) ^ n * (b - a) := by
  have hρ0 : 0 ≤ 1 - (prodBernoulli H.prob).real (regen H X) := sub_nonneg.2 measureReal_le_one
  induction n with
  | zero => exact ⟨a, b, by simpa using hg, by simp⟩
  | succ n ih =>
    obtain ⟨a', b', hab', hosc⟩ := ih
    have hw := fun K => worldMean_bounds H s hab' K
    have hφeq : (gibbsT H s X)^[n + 1] g =
        bStep H X (worldMean H s ((gibbsT H s X)^[n] g)) := by
      rw [Function.iterate_succ_apply']; rfl
    obtain ⟨C₀, hC₀⟩ := Finite.exists_min ((gibbsT H s X)^[n + 1] g)
    refine ⟨(gibbsT H s X)^[n + 1] g C₀,
      (gibbsT H s X)^[n + 1] g C₀ + (1 - (prodBernoulli H.prob).real (regen H X)) * (b' - a'),
      fun C => ⟨hC₀ C, ?_⟩, ?_⟩
    · have h := bStep_sub_le H X hw C C₀
      rw [← hφeq] at h
      linarith
    · calc (gibbsT H s X)^[n + 1] g C₀ +
            (1 - (prodBernoulli H.prob).real (regen H X)) * (b' - a') -
              (gibbsT H s X)^[n + 1] g C₀
          = (1 - (prodBernoulli H.prob).real (regen H X)) * (b' - a') := by ring
        _ ≤ (1 - (prodBernoulli H.prob).real (regen H X)) *
              ((1 - (prodBernoulli H.prob).real (regen H X)) ^ n * (b - a)) :=
            mul_le_mul_of_nonneg_left hosc hρ0
        _ = (1 - (prodBernoulli H.prob).real (regen H X)) ^ (n + 1) * (b - a) := by ring

/-! ### The one-step decomposition, in the calculus of `cE` -/

/-- `cov_D(φ, h) = P(D)·E[φ h; D] − E[φ; D]·E[h; D]`, for functions of the configuration. -/
def covDF (H : Hypergraph V E) (D : Set (Set E)) (φ h : Set E → ℝ) : ℝ :=
  (prodBernoulli H.prob).real D * (∫ ω in D, φ ω * h ω ∂(prodBernoulli H.prob)) -
    (∫ ω in D, φ ω ∂(prodBernoulli H.prob)) * ∫ ω in D, h ω ∂(prodBernoulli H.prob)

/-- `R(φ) = E[ E[φ h ∣ C_X] − E[φ ∣ C_X]·E[h ∣ C_X] ; D ]`, the averaged conditional covariance. -/
def withinF (H : Hypergraph V E) (X : Set V) (D : Set (Set E)) (φ h : Set E → ℝ) : ℝ :=
  ∫ ω in D, (cE H X (fun ν => φ ν * h ν) ω - cE H X φ ω * cE H X h ω) ∂(prodBernoulli H.prob)

theorem setIntegral_eq_integral_ind_mul (μ : Measure (Set E)) (D : Set (Set E))
    (g : Set E → ℝ) : ∫ ω in D, g ω ∂μ = ∫ ω, ind D ω * g ω ∂μ := by
  rw [← integral_mul_ind D g]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

/-- **The one-step decomposition** `cov_D(φ, h) = P(D)·R(φ) + cov_D(𝑇φ, h)` with
`𝑇 = E[·∣C_S] ∘ E[·∣C_X]`, for an event `D` read off both records and an `h` read off the record of
`S`.  The bond proof (`BHK2006.covD_eq_withinD_add`) is an explicit computation with sums over
configurations; here it is the tower property, the pull-out of a record-determined factor and the
symmetry `E[f·cE g] = E[cE f·g]`.  [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4] -/
theorem covDF_eq_withinF_add (H : Hypergraph V E) (S X : Set V) (D : Set (Set E))
    (hDX : ∀ ν ν' : Set E, recordAt H X ν = recordAt H X ν' → (ν ∈ D ↔ ν' ∈ D))
    (hDS : ∀ ν ν' : Set E, recordAt H S ν = recordAt H S ν' → (ν ∈ D ↔ ν' ∈ D))
    (φ h : Set E → ℝ) (hh : ∀ ν ν' : Set E, recordAt H S ν = recordAt H S ν' → h ν = h ν') :
    covDF H D φ h =
      (prodBernoulli H.prob).real D * withinF H X D φ h + covDF H D (cE H S (cE H X φ)) h := by
  set μ := prodBernoulli H.prob with hμ
  have hZX : ∀ ν ν' : Set E, recordAt H X ν = recordAt H X ν' → ind D ν = ind D ν' := by
    intro ν ν' hr
    by_cases hν : ν ∈ D
    · rw [ind_of_mem hν, ind_of_mem ((hDX ν ν' hr).1 hν)]
    · rw [ind_of_not_mem hν, ind_of_not_mem (fun h' => hν ((hDX ν ν' hr).2 h'))]
  have hZS : ∀ ν ν' : Set E, recordAt H S ν = recordAt H S ν' → ind D ν = ind D ν' := by
    intro ν ν' hr
    by_cases hν : ν ∈ D
    · rw [ind_of_mem hν, ind_of_mem ((hDS ν ν' hr).1 hν)]
    · rw [ind_of_not_mem hν, ind_of_not_mem (fun h' => hν ((hDS ν ν' hr).2 h'))]
  have hZh : ∀ ν ν' : Set E, recordAt H S ν = recordAt H S ν' →
      ind D ν * h ν = ind D ν' * h ν' :=
    fun ν ν' hr => by rw [hZS ν ν' hr, hh ν ν' hr]
  -- (A) `E[φ h; D] = E[1_D · cE_X(φ h)]`
  have hA : (∫ ω in D, φ ω * h ω ∂μ) = ∫ ω, ind D ω * cE H X (fun ν => φ ν * h ν) ω ∂μ := by
    rw [setIntegral_eq_integral_ind_mul μ D, ← integral_cE H X (fun ω => ind D ω * (φ ω * h ω))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      cE_mul_of_local H X hZX (fun ν => φ ν * h ν) ω)
  -- (B) `E[1_D · cE_X φ · cE_X h] = E[cE_S(cE_X φ) · 1_D h]`
  have hB : (∫ ω, ind D ω * (cE H X φ ω * cE H X h ω) ∂μ) =
      ∫ ω, cE H S (cE H X φ) ω * (ind D ω * h ω) ∂μ := by
    have e1 : (∫ ω, ind D ω * (cE H X φ ω * cE H X h ω) ∂μ) =
        ∫ ω, cE H X φ ω * cE H X (fun ν => ind D ν * h ν) ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [cE_mul_of_local H X hZX h ω]; ring)
    have e2 : (∫ ω, cE H X φ ω * cE H X (fun ν => ind D ν * h ν) ω ∂μ) =
        ∫ ω, cE H X (cE H X φ) ω * (ind D ω * h ω) ∂μ :=
      integral_mul_cE_comm H X (cE H X φ) (fun ν => ind D ν * h ν)
    have e3 : (∫ ω, cE H X (cE H X φ) ω * (ind D ω * h ω) ∂μ) =
        ∫ ω, cE H X φ ω * (ind D ω * h ω) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [cE_eq_self_of_recordDetermined H X (f := cE H X φ)
          (fun ν ν' hr => cE_congr H X φ hr) ω])
    have e4 : (∫ ω, cE H X φ ω * (ind D ω * h ω) ∂μ) =
        ∫ ω, cE H X φ ω * cE H S (fun ν => ind D ν * h ν) ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [cE_eq_self_of_recordDetermined H S hZh ω])
    have e5 := integral_mul_cE_comm H S (cE H X φ) (fun ν => ind D ν * h ν)
    rw [e1, e2, e3, e4, e5]
  -- (C) `E[φ; D] = E[cE_S(cE_X φ); D]`
  have hC : (∫ ω in D, φ ω ∂μ) = ∫ ω in D, cE H S (cE H X φ) ω ∂μ := by
    rw [setIntegral_eq_integral_ind_mul μ D φ, setIntegral_eq_integral_ind_mul μ D,
      ← integral_cE H X (fun ω => ind D ω * φ ω)]
    have e1 : (∫ ω, cE H X (fun ν => ind D ν * φ ν) ω ∂μ) = ∫ ω, cE H X φ ω * ind D ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [cE_mul_of_local H X hZX φ ω]; ring)
    have e2 : (∫ ω, cE H X φ ω * ind D ω ∂μ) =
        ∫ ω, cE H X φ ω * cE H S (fun ν => ind D ν) ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only
        rw [cE_eq_self_of_recordDetermined H S hZS ω])
    have e3 := integral_mul_cE_comm H S (cE H X φ) (fun ν => ind D ν)
    rw [e1, e2, e3]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  -- assemble
  have hsplit : (∫ ω, ind D ω * cE H X (fun ν => φ ν * h ν) ω ∂μ) =
      withinF H X D φ h + ∫ ω, ind D ω * (cE H X φ ω * cE H X h ω) ∂μ := by
    unfold withinF
    rw [setIntegral_eq_integral_ind_mul μ D,
      ← integral_add (integrable_of_fintype _) (integrable_of_fintype _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have hDh : (∫ ω in D, cE H S (cE H X φ) ω * h ω ∂μ) =
      ∫ ω, cE H S (cE H X φ) ω * (ind D ω * h ω) ∂μ := by
    rw [setIntegral_eq_integral_ind_mul μ D]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  unfold covDF
  rw [hA, hsplit, hB, ← hDh, hC]
  ring

/-- `cov_D(·, h)` reads its first argument on `D` only. -/
theorem covDF_congr_on (H : Hypergraph V E) (D : Set (Set E)) {φ φ' h : Set E → ℝ}
    (hφ : ∀ ω ∈ D, φ ω = φ' ω) : covDF H D φ h = covDF H D φ' h := by
  unfold covDF
  have e1 : (∫ ω in D, φ ω * h ω ∂(prodBernoulli H.prob)) =
      ∫ ω in D, φ' ω * h ω ∂(prodBernoulli H.prob) :=
    setIntegral_congr_fun (measurableSet_of_fintype D) fun ω hω => by rw [hφ ω hω]
  have e2 : (∫ ω in D, φ ω ∂(prodBernoulli H.prob)) = ∫ ω in D, φ' ω ∂(prodBernoulli H.prob) :=
    setIntegral_congr_fun (measurableSet_of_fintype D) fun ω hω => hφ ω hω
  rw [e1, e2]

/-- `cov_D` is invariant under adding a constant to the first argument. -/
theorem covDF_sub_const (H : Hypergraph V E) (D : Set (Set E)) (φ h : Set E → ℝ) (c : ℝ) :
    covDF H D (fun ω => φ ω - c) h = covDF H D φ h := by
  unfold covDF
  set μ := prodBernoulli H.prob with hμ
  have e1 : (∫ ω in D, (φ ω - c) * h ω ∂μ) =
      (∫ ω in D, φ ω * h ω ∂μ) - c * ∫ ω in D, h ω ∂μ := by
    rw [← integral_const_mul, ← integral_sub (integrable_of_fintype _) (integrable_of_fintype _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have e2 : (∫ ω in D, (φ ω - c) ∂μ) = (∫ ω in D, φ ω ∂μ) - c * μ.real D := by
    rw [integral_sub (integrable_of_fintype _) (integrable_of_fintype _), setIntegral_const,
      smul_eq_mul, mul_comm]
  rw [e1, e2]
  ring

/-- **The covariance is small when the first argument oscillates little**:
`|cov_D(φ, h)| ≤ 2 (b − a) M P(D)²` for `φ ∈ [a, b]` on `D` and `|h| ≤ M`. -/
theorem abs_covDF_le (H : Hypergraph V E) (D : Set (Set E)) {φ h : Set E → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hφ : ∀ ω ∈ D, a ≤ φ ω ∧ φ ω ≤ b) (hM : ∀ ω, |h ω| ≤ M) :
    |covDF H D φ h| ≤ 2 * ((b - a) * M) * (prodBernoulli H.prob).real D ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ∅)
  rw [← covDF_sub_const H D φ h a]
  unfold covDF
  set μ := prodBernoulli H.prob with hμ
  have hD : μ D < ⊤ := measure_lt_top _ _
  have hn : 0 ≤ μ.real D := measureReal_nonneg
  have h1 : |∫ ω in D, (φ ω - a) * h ω ∂μ| ≤ (b - a) * M * μ.real D := by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun ω => (φ ω - a) * h ω)
      (s := D) (C := (b - a) * M) hD (fun ω hω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (by rw [abs_of_nonneg (by linarith [(hφ ω hω).1])]; linarith [(hφ ω hω).2])
          (hM ω) (abs_nonneg _) (by linarith))
    rwa [Real.norm_eq_abs] at this
  have h2 : |∫ ω in D, (φ ω - a) ∂μ| ≤ (b - a) * μ.real D := by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := fun ω => φ ω - a) (s := D)
      (C := b - a) hD (fun ω hω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hφ ω hω).1])]
        linarith [(hφ ω hω).2])
    rwa [Real.norm_eq_abs] at this
  have h3 : |∫ ω in D, h ω ∂μ| ≤ M * μ.real D := by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) (f := h) (s := D) (C := M) hD
      (fun ω _ => by rw [Real.norm_eq_abs]; exact hM ω)
    rwa [Real.norm_eq_abs] at this
  calc |μ.real D * (∫ ω in D, (φ ω - a) * h ω ∂μ) -
          (∫ ω in D, (φ ω - a) ∂μ) * ∫ ω in D, h ω ∂μ|
      ≤ |μ.real D * ∫ ω in D, (φ ω - a) * h ω ∂μ| +
          |(∫ ω in D, (φ ω - a) ∂μ) * ∫ ω in D, h ω ∂μ| := abs_sub _ _
    _ = μ.real D * |∫ ω in D, (φ ω - a) * h ω ∂μ| +
          |∫ ω in D, (φ ω - a) ∂μ| * |∫ ω in D, h ω ∂μ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hn]
    _ ≤ μ.real D * ((b - a) * M * μ.real D) + ((b - a) * μ.real D) * (M * μ.real D) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hn)
          (mul_le_mul h2 h3 (abs_nonneg _) (mul_nonneg (by linarith) hn))
    _ = 2 * ((b - a) * M) * μ.real D ^ 2 := by ring

/-! ### Reading the operators on the avoidance event -/

/-- `s ↮ X` says that `s` is outside the cluster of `X`. -/
theorem mem_avoidEvent_iff_not_mem (H : Hypergraph V E) (s : V) (X : Set V) (ω : Set E) :
    ω ∈ avoidEvent H ({s} : Set V) X ↔ s ∉ hyperClusterSet H ω X := by
  rw [mem_avoidEvent_singleton]
  constructor
  · rintro h ⟨x, hx, hr⟩
    exact h x hx hr.symm
  · intro h x hx hr
    exact h ⟨x, hx, hr.symm⟩

/-- The avoidance event is read off the record of `X`. -/
theorem avoidEvent_recordDetermined_X (H : Hypergraph V E) (s : V) (X : Set V) :
    ∀ ν ν' : Set E, recordAt H X ν = recordAt H X ν' →
      (ν ∈ avoidEvent H ({s} : Set V) X ↔ ν' ∈ avoidEvent H ({s} : Set V) X) := by
  intro ν ν' hr
  have hc : hyperClusterSet H ν X = hyperClusterSet H ν' X := by
    have := congrArg ExplorationRecord.reached hr
    simpa using this
  rw [mem_avoidEvent_iff_not_mem, mem_avoidEvent_iff_not_mem, hc]

/-- The avoidance event is read off the record of `s`. -/
theorem avoidEvent_recordDetermined_s (H : Hypergraph V E) (s : V) (X : Set V) :
    ∀ ν ν' : Set E, recordAt H ({s} : Set V) ν = recordAt H ({s} : Set V) ν' →
      (ν ∈ avoidEvent H ({s} : Set V) X ↔ ν' ∈ avoidEvent H ({s} : Set V) X) := by
  intro ν ν' hr
  have hc : hyperClusterSet H ν ({s} : Set V) = hyperClusterSet H ν' ({s} : Set V) := by
    have := congrArg ExplorationRecord.reached hr
    simpa using this
  simp only [mem_avoidEvent, hc]

/-- A functional of the owner's cluster is read off the record of `s`. -/
theorem clusterFun_recordDetermined (H : Hypergraph V E) (s : V) (G : Set V → ℝ) :
    ∀ ν ν' : Set E, recordAt H ({s} : Set V) ν = recordAt H ({s} : Set V) ν' →
      G (hyperClusterSet H ν ({s} : Set V)) = G (hyperClusterSet H ν' ({s} : Set V)) := by
  intro ν ν' hr
  have hc : hyperClusterSet H ν ({s} : Set V) = hyperClusterSet H ν' ({s} : Set V) := by
    have := congrArg ExplorationRecord.reached hr
    simpa using this
  rw [hc]

/-- On `D`, the conditional expectation of `g(C_s)` given the record of `X` is the world mean. -/
theorem cE_X_clusterFun_eq (H : Hypergraph V E) (s : V) (X : Set V) (g : Set V → ℝ) {ω : Set E}
    (hω : ω ∈ avoidEvent H ({s} : Set V) X) :
    cE H X (fun ν => g (hyperClusterSet H ν ({s} : Set V))) ω =
      worldMean H s g (hyperClusterSet H ω X) := by
  rw [cE_clusterFun_of_not_mem H X g ω ((mem_avoidEvent_iff_not_mem H s X ω).1 hω)]
  rfl

theorem cE_X_mul_clusterFun_eq (H : Hypergraph V E) (s : V) (X : Set V) (g h : Set V → ℝ)
    {ω : Set E} (hω : ω ∈ avoidEvent H ({s} : Set V) X) :
    cE H X (fun ν => g (hyperClusterSet H ν ({s} : Set V)) * h (hyperClusterSet H ν ({s} : Set V)))
        ω = worldMean H s (fun C => g C * h C) (hyperClusterSet H ω X) :=
  cE_X_clusterFun_eq H s X (fun C => g C * h C) hω

/-- **The cluster of a vertex set disjoint from the explored cluster, read at the splice**, is its
cluster in the deleted configuration: `hyperClusterSet_spliceRecord_of_not_mem` vertex by
vertex. -/
theorem hyperClusterSet_spliceRecord_of_disjoint (H : Hypergraph V E) (S : Set V) (ω η : Set E)
    (Y : Set V) (hY : ∀ y ∈ Y, y ∉ hyperClusterSet H ω S) :
    hyperClusterSet H (spliceRecord (recordAt H S ω) η) Y =
      hyperClusterSet H (off H (hyperClusterSet H ω S) η) Y := by
  ext z
  simp only [hyperClusterSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, hr⟩
    exact ⟨y, hy, (reachable_spliceRecord_of_not_mem H S ω η (hY y hy) z).2 hr⟩
  · rintro ⟨y, hy, hr⟩
    exact ⟨y, hy, (reachable_spliceRecord_of_not_mem H S ω η (hY y hy) z).1 hr⟩

/-- On `D`, the conditional expectation of `ψ(C_X)` given the record of `s` is `bStep ψ (C_s)`. -/
theorem cE_s_clusterFunX_eq (H : Hypergraph V E) (s : V) (X : Set V) (ψ : Set V → ℝ) {ω : Set E}
    (hω : ω ∈ avoidEvent H ({s} : Set V) X) :
    cE H ({s} : Set V) (fun ν => ψ (hyperClusterSet H ν X)) ω =
      bStep H X ψ (hyperClusterSet H ω ({s} : Set V)) := by
  have hY : ∀ y ∈ X, y ∉ hyperClusterSet H ω ({s} : Set V) := fun y hy hmem =>
    Set.disjoint_left.1 ((mem_avoidEvent H ({s} : Set V) X ω).1 hω) hmem hy
  show (∫ η, ψ (hyperClusterSet H (spliceRecord (recordAt H ({s} : Set V) ω) η) X)
      ∂(prodBernoulli H.prob)) = _
  unfold bStep
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  dsimp only
  rw [hyperClusterSet_spliceRecord_of_disjoint H ({s} : Set V) ω η X hY]
  rfl

/-- **On `D`, one step of the abstract chain is one step of the concrete one**:
`E[E[g(C_s) ∣ C_X] ∣ C_s] = (𝑇g)(C_s)`. -/
theorem cE_cE_clusterFun_eq (H : Hypergraph V E) (s : V) (X : Set V) (g : Set V → ℝ) {ω : Set E}
    (hω : ω ∈ avoidEvent H ({s} : Set V) X) :
    cE H ({s} : Set V) (cE H X (fun ν => g (hyperClusterSet H ν ({s} : Set V)))) ω =
      gibbsT H s X g (hyperClusterSet H ω ({s} : Set V)) := by
  have hpt : ∀ η : Set E,
      cE H X (fun ν => g (hyperClusterSet H ν ({s} : Set V)))
          (spliceRecord (recordAt H ({s} : Set V) ω) η) =
        worldMean H s g (hyperClusterSet H (spliceRecord (recordAt H ({s} : Set V) ω) η) X) := by
    intro η
    have hrec : recordAt H ({s} : Set V) (spliceRecord (recordAt H ({s} : Set V) ω) η) =
        recordAt H ({s} : Set V) ω := spliceRecord_mem_recordEvent H ({s} : Set V) ω η
    exact cE_X_clusterFun_eq H s X g
      ((avoidEvent_recordDetermined_s H s X ω _ hrec.symm).1 hω)
  show (∫ η, cE H X (fun ν => g (hyperClusterSet H ν ({s} : Set V)))
      (spliceRecord (recordAt H ({s} : Set V) ω) η) ∂(prodBernoulli H.prob)) = _
  simp only [hpt]
  exact cE_s_clusterFunX_eq H s X (worldMean H s g) hω

/-- **The iterated decomposition**: `cov_D(g(C_s), h(C_s)) = P(D) Σ_{k<n} R(𝑇ᵏg) + cov_D(𝑇ⁿg, h)`. -/
theorem covDF_eq_sum_withinF_add (H : Hypergraph V E) (s : V) (X : Set V) (g h : Set V → ℝ)
    (n : ℕ) :
    covDF H (avoidEvent H ({s} : Set V) X) (fun ω => g (hyperClusterSet H ω ({s} : Set V)))
        (fun ω => h (hyperClusterSet H ω ({s} : Set V))) =
      (prodBernoulli H.prob).real (avoidEvent H ({s} : Set V) X) *
          ∑ k ∈ Finset.range n, withinF H X (avoidEvent H ({s} : Set V) X)
            (fun ω => (gibbsT H s X)^[k] g (hyperClusterSet H ω ({s} : Set V)))
            (fun ω => h (hyperClusterSet H ω ({s} : Set V))) +
        covDF H (avoidEvent H ({s} : Set V) X)
          (fun ω => (gibbsT H s X)^[n] g (hyperClusterSet H ω ({s} : Set V)))
          (fun ω => h (hyperClusterSet H ω ({s} : Set V))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, mul_add, add_assoc]
    congr 1
    rw [covDF_eq_withinF_add H ({s} : Set V) X (avoidEvent H ({s} : Set V) X)
      (avoidEvent_recordDetermined_X H s X) (avoidEvent_recordDetermined_s H s X) _ _
      (clusterFun_recordDetermined H s h)]
    congr 1
    apply covDF_congr_on
    intro ω hω
    rw [cE_cE_clusterFun_eq H s X _ hω, Function.iterate_succ_apply']

/-! ### The reduction theorem -/

/-- **Reduction of a conditional covariance sign to the averaged one-step covariances**, for
hyperedges.  Owner `s`, avoided set `X` every label meeting which has `p_e < 1`, `D = {s ↮ X}`,
`h` ANY function of vertex sets.  If `R(g) = E[Cov(g(C_s), h(C_s) ∣ C_X); D] ≥ 0` for every
monotone nonnegative `g`, then `cov_D(f(C_s), h(C_s)) ≥ 0` for every monotone `f`.  Proof:
`cov_D(f, h) = cov_D(f − f(∅), h) = P(D) Σ_{k<n} R(𝑇ᵏ(f − f ∅)) + cov_D(𝑇ⁿ(f − f ∅), h)`; the sum
is nonnegative because the iterates are monotone and nonnegative, and the last term is
`O((1 − ε)ⁿ)`.  Hyperedge form of `BHK2006.covD_nonneg_of_withinD_nonneg`.
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–13 (the chain, Claim 2.5, Remark 2.8)] -/
theorem clusterCov_nonneg_of_within (H : Hypergraph V E) (s : V) (X : Set V)
    (hX : ∀ e ∈ labelsMeeting H X, (H.prob e : ℝ) < 1) (h : Set V → ℝ)
    (hR : ∀ g : Set V → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in avoidEvent H ({s} : Set V) X,
        (worldMean H s (fun C => g C * h C) (hyperClusterSet H ω X) -
          worldMean H s g (hyperClusterSet H ω X) * worldMean H s h (hyperClusterSet H ω X))
          ∂(prodBernoulli H.prob))
    {f : Set V → ℝ} (hf : Monotone f) :
    0 ≤ covDF H (avoidEvent H ({s} : Set V) X) (fun ω => f (hyperClusterSet H ω ({s} : Set V)))
      (fun ω => h (hyperClusterSet H ω ({s} : Set V))) := by
  set μ := prodBernoulli H.prob with hμ
  set D := avoidEvent H ({s} : Set V) X with hD
  set f₀ : Set V → ℝ := fun C => f C - f ∅ with hf₀
  have hf₀m : Monotone f₀ := fun C C' hCC' => sub_le_sub_right (hf hCC') _
  have hf₀0 : ∀ C, 0 ≤ f₀ C := fun C => sub_nonneg.2 (hf (Set.empty_subset C))
  set c : ℝ := f Set.univ - f ∅ with hc
  have hf₀b : ∀ C, 0 ≤ f₀ C ∧ f₀ C ≤ c :=
    fun C => ⟨hf₀0 C, sub_le_sub_right (hf (Set.subset_univ C)) _⟩
  obtain ⟨C₀, hC₀⟩ := Finite.exists_max (fun C : Set V => |h C|)
  set M := |h C₀| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  have hεpos : 0 < μ.real (regen H X) := real_regen_pos H X hX
  set ρ := 1 - μ.real (regen H X) with hρ
  have hρ0 : 0 ≤ ρ := sub_nonneg.2 measureReal_le_one
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hn : 0 ≤ μ.real D := measureReal_nonneg
  -- the averaged one-step covariances of the iterates are nonnegative
  have hW : ∀ k : ℕ, 0 ≤ withinF H X D
      (fun ω => (gibbsT H s X)^[k] f₀ (hyperClusterSet H ω ({s} : Set V)))
      (fun ω => h (hyperClusterSet H ω ({s} : Set V))) := by
    intro k
    obtain ⟨hkm, hk0⟩ := gibbsT_iterate_mono_nonneg H s X hf₀m hf₀0 k
    have key := hR _ hkm hk0
    unfold withinF
    refine le_of_le_of_eq key (setIntegral_congr_fun (measurableSet_of_fintype D)
      fun ω hω => ?_)
    rw [cE_X_mul_clusterFun_eq H s X _ h hω, cE_X_clusterFun_eq H s X _ hω,
      cE_X_clusterFun_eq H s X h hω]
  -- the lower bound for every `n`
  have key : ∀ n : ℕ, -(2 * ((ρ ^ n * c) * M) * μ.real D ^ 2) ≤
      covDF H D (fun ω => f₀ (hyperClusterSet H ω ({s} : Set V)))
        (fun ω => h (hyperClusterSet H ω ({s} : Set V))) := by
    intro n
    rw [covDF_eq_sum_withinF_add H s X f₀ h n]
    have h1 : 0 ≤ μ.real D * ∑ k ∈ Finset.range n, withinF H X D
        (fun ω => (gibbsT H s X)^[k] f₀ (hyperClusterSet H ω ({s} : Set V)))
        (fun ω => h (hyperClusterSet H ω ({s} : Set V))) :=
      mul_nonneg hn (Finset.sum_nonneg fun k _ => hW k)
    obtain ⟨a', b', hab', hosc⟩ := gibbsT_iterate_bounds H s X hf₀b n
    have hosc' : b' - a' ≤ ρ ^ n * c := by
      rw [hρ]; simpa using hosc
    have hab : a' ≤ b' := (hab' ∅).1.trans (hab' ∅).2
    have h2 := abs_covDF_le H D hab (fun ω _ => hab' (hyperClusterSet H ω ({s} : Set V)))
      (fun ω => hC₀ (hyperClusterSet H ω ({s} : Set V)))
    have h3 : 2 * ((b' - a') * M) * μ.real D ^ 2 ≤ 2 * ((ρ ^ n * c) * M) * μ.real D ^ 2 := by
      have hh : (b' - a') * M ≤ (ρ ^ n * c) * M := mul_le_mul_of_nonneg_right hosc' hM0
      have hsq : 0 ≤ μ.real D ^ 2 := sq_nonneg _
      nlinarith [hh, hsq]
    linarith [neg_abs_le (covDF H D
      (fun ω => (gibbsT H s X)^[n] f₀ (hyperClusterSet H ω ({s} : Set V)))
      (fun ω => h (hyperClusterSet H ω ({s} : Set V))))]
  -- let `n → ∞`
  have hlim : Filter.Tendsto (fun n : ℕ => -(2 * ((ρ ^ n * c) * M) * μ.real D ^ 2))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ρ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have : Filter.Tendsto (fun n : ℕ => -(2 * ((ρ ^ n * c) * M) * μ.real D ^ 2)) Filter.atTop
        (nhds (-(2 * ((0 * c) * M) * μ.real D ^ 2))) :=
      ((((h0.mul_const c).mul_const M).const_mul 2).mul_const (μ.real D ^ 2)).neg
    simpa using this
  have hge : 0 ≤ covDF H D (fun ω => f₀ (hyperClusterSet H ω ({s} : Set V)))
      (fun ω => h (hyperClusterSet H ω ({s} : Set V))) := le_of_tendsto' hlim key
  have hfin : covDF H D (fun ω => f₀ (hyperClusterSet H ω ({s} : Set V)))
      (fun ω => h (hyperClusterSet H ω ({s} : Set V))) =
      covDF H D (fun ω => f (hyperClusterSet H ω ({s} : Set V)))
        (fun ω => h (hyperClusterSet H ω ({s} : Set V))) :=
    covDF_sub_const H D (fun ω => f (hyperClusterSet H ω ({s} : Set V)))
      (fun ω => h (hyperClusterSet H ω ({s} : Set V))) (f ∅)
  rwa [hfin] at hge

/-! ### The multi-marker form -/

/-- The marker sum `h = Σ_{u ∈ T} c(u)·1{u ∈ C}` splits a covariance into a sum of marker
covariances, under any finite measure and on any event. -/
theorem markerCov_eq_sum (H : Hypergraph V E) (s : V) (μ' : Measure (Set E))
    [IsFiniteMeasure μ'] (A : Set (Set E)) (g : Set V → ℝ) (T : Finset V) (c : V → ℝ) :
    μ'.real A * (∫ ω in A, g (hyperClusterSet H ω ({s} : Set V)) *
          (∑ u ∈ T, c u * indMem u (hyperClusterSet H ω ({s} : Set V))) ∂μ') -
        (∫ ω in A, g (hyperClusterSet H ω ({s} : Set V)) ∂μ') *
          ∫ ω in A, (∑ u ∈ T, c u * indMem u (hyperClusterSet H ω ({s} : Set V))) ∂μ' =
      ∑ u ∈ T, c u * (μ'.real A *
          (∫ ω in A ∩ hyperConn H s u, g (hyperClusterSet H ω ({s} : Set V)) ∂μ') -
        (∫ ω in A, g (hyperClusterSet H ω ({s} : Set V)) ∂μ') *
          μ'.real (A ∩ hyperConn H s u)) := by
  have e1 : (∫ ω in A, g (hyperClusterSet H ω ({s} : Set V)) *
      (∑ u ∈ T, c u * indMem u (hyperClusterSet H ω ({s} : Set V))) ∂μ') =
      ∑ u ∈ T, c u * ∫ ω in A ∩ hyperConn H s u, g (hyperClusterSet H ω ({s} : Set V)) ∂μ' := by
    have hpt : ∀ ω : Set E, g (hyperClusterSet H ω ({s} : Set V)) *
        (∑ u ∈ T, c u * indMem u (hyperClusterSet H ω ({s} : Set V))) =
        ∑ u ∈ T, c u * (g (hyperClusterSet H ω ({s} : Set V)) * ind (hyperConn H s u) ω) := by
      intro ω
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [indMem_hyperClusterSet H u s ω, hyperConn_comm H u s]; ring
    simp only [hpt]
    rw [integral_finsetSum _ fun u _ => integrable_of_fintype _]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_const_mul, setIntegral_mul_ind]
  have e2 : (∫ ω in A, (∑ u ∈ T, c u * indMem u (hyperClusterSet H ω ({s} : Set V))) ∂μ') =
      ∑ u ∈ T, c u * μ'.real (A ∩ hyperConn H s u) := by
    have hpt : ∀ ω : Set E, (∑ u ∈ T, c u * indMem u (hyperClusterSet H ω ({s} : Set V))) =
        ∑ u ∈ T, c u * ind (hyperConn H s u) ω := by
      intro ω
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [indMem_hyperClusterSet H u s ω, hyperConn_comm H u s]
    simp only [hpt]
    rw [integral_finsetSum _ fun u _ => integrable_of_fintype _]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_const_mul, setIntegral_ind]
  rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

/-- **The multi-marker reduction for hyperedges.**  Owner `s`, avoided set `X` every label meeting
which has `p_e < 1`, markers `T` with coefficients `c` of arbitrary sign.  If for every monotone
nonnegative `g` the `{s ↮ X}`-average of the world covariances
`Σ_u c(u)·Cov_{H − C_X(ω)}(g(C_s), 1{s ↔ u})` is nonnegative, then
`Σ_u c(u)·covD H s X f u ≥ 0` for every monotone `f`.  Hyperedge form of
`BHK2006_multiMarkerCov_nonneg_of_within`. -/
theorem multiMarkerCov_nonneg_of_within (H : Hypergraph V E) (s : V) (X : Set V)
    (hX : ∀ e ∈ labelsMeeting H X, (H.prob e : ℝ) < 1) (T : Finset V) (c : V → ℝ)
    (hR : ∀ g : Set V → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in avoidEvent H ({s} : Set V) X,
        (∑ u ∈ T, c u * ((∫ η in hyperConn H s u, g (hyperClusterSet H η ({s} : Set V))
                ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω X)).prob)) -
              (∫ η, g (hyperClusterSet H η ({s} : Set V))
                ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω X)).prob)) *
              (prodBernoulli (deleteHyper H (hyperClusterSet H ω X)).prob).real
                (hyperConn H s u))) ∂(prodBernoulli H.prob))
    {f : Set V → ℝ} (hf : Monotone f) :
    0 ≤ ∑ u ∈ T, c u * covD H s X f u := by
  set hc : Set V → ℝ := fun C => ∑ u ∈ T, c u * indMem u C with hhc
  -- the world covariances in marker form
  have hworld : ∀ (K : Set V) (g : Set V → ℝ),
      worldMean H s (fun C => g C * hc C) K - worldMean H s g K * worldMean H s hc K =
        ∑ u ∈ T, c u * ((∫ η in hyperConn H s u, g (hyperClusterSet H η ({s} : Set V))
              ∂(prodBernoulli (deleteHyper H K).prob)) -
            (∫ η, g (hyperClusterSet H η ({s} : Set V))
              ∂(prodBernoulli (deleteHyper H K).prob)) *
            (prodBernoulli (deleteHyper H K).prob).real (hyperConn H s u)) := by
    intro K g
    rw [worldMean_eq_deleteHyper, worldMean_eq_deleteHyper, worldMean_eq_deleteHyper]
    have h := markerCov_eq_sum H s (prodBernoulli (deleteHyper H K).prob) Set.univ g T c
    simp only [Measure.restrict_univ, Set.univ_inter, probReal_univ, one_mul] at h
    exact h
  have main := clusterCov_nonneg_of_within H s X hX hc (fun g hg hg0 => by
    have h := hR g hg hg0
    simp only [hworld]
    exact h) hf
  have hconc := markerCov_eq_sum H s (prodBernoulli H.prob) (avoidEvent H ({s} : Set V) X) f T c
  unfold covDF at main
  rw [hconc] at main
  exact main

/-! ### Lemma T -/

/-- **Lemma T for the conditioned slack hierarchy, hyperedge form.**  Owner `x`, avoided set `Y`
every label meeting which has `p_e < 1`, decoys `D`, observers `o, v`; `L`, `p` the decoy list and
observer constant of `cshMargin`.  IF for every monotone `g ≥ 0` the world-wise margin is
nonnegative,
`0 ≤ ∫_{x ↮ Y} Marg_{L,p}[u ↦ ∫_{x↔u} g(C_x) dμ_{H − C_Y(ω)} − (∫ g(C_x) dμ_{H − C_Y(ω)})·μ_{H − C_Y(ω)}(x ↔ u)] dμ(ω)`,
THEN `0 ≤ cshMargin H x Y D o v f` for every monotone `f`.  The world `H − C_Y(ω)` is
`deleteHyper H (hyperClusterSet H ω Y)`, the model with every label meeting the open cluster of
`Y` closed.  Hyperedge form of `CSH.cshMargin_nonneg_of_within`.
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–13, Lemma 2.4 (p. 10)] -/
theorem cshMargin_nonneg_of_within (H : Hypergraph V E) (x : V) (Y : Set V) (D : List V)
    (o v : V) (hY : ∀ e ∈ labelsMeeting H Y, (H.prob e : ℝ) < 1)
    (hW : ∀ g : Set V → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in avoidEvent H ({x} : Set V) Y,
        CSH.cshMarg (decoyList H (insert x Y) D) (obsConst H o v (insert x Y ∪ {d | d ∈ D})) o v
          (fun u => (∫ η in hyperConn H x u, g (hyperClusterSet H η ({x} : Set V))
                ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob)) -
              (∫ η, g (hyperClusterSet H η ({x} : Set V))
                ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob)) *
              (prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob).real
                (hyperConn H x u)) ∂(prodBernoulli H.prob))
    (f : Set V → ℝ) (hf : Monotone f) :
    0 ≤ cshMargin H x Y D o v f := by
  set L := decoyList H (insert x Y) D with hL
  set p := obsConst H o v (insert x Y ∪ {d | d ∈ D}) with hp
  set Λ : V → ℝ := fun u => CSH.cshMarg L p o v (Pi.single u 1) with hΛ
  have hmain := multiMarkerCov_nonneg_of_within H x Y hY Finset.univ Λ (fun g hg hg0 => by
    have h := hW g hg hg0
    have e : ∀ ω : Set E, CSH.cshMarg L p o v
        (fun u => (∫ η in hyperConn H x u, g (hyperClusterSet H η ({x} : Set V))
              ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob)) -
            (∫ η, g (hyperClusterSet H η ({x} : Set V))
              ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob)) *
            (prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob).real
              (hyperConn H x u)) =
        ∑ u, Λ u * ((∫ η in hyperConn H x u, g (hyperClusterSet H η ({x} : Set V))
              ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob)) -
            (∫ η, g (hyperClusterSet H η ({x} : Set V))
              ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob)) *
            (prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob).real
              (hyperConn H x u)) :=
      fun ω => CSH.cshMarg_eq_sum L p o v _
    simp only [e] at h
    exact h) hf
  rw [cshMargin_eq_sum]
  exact hmain

/-- **`CSHHolds` from the world-wise margins**: Lemma T quantified over the functional. -/
theorem cshHolds_of_within (H : Hypergraph V E) (x : V) (Y : Set V) (D : List V) (o v : V)
    (hY : ∀ e ∈ labelsMeeting H Y, (H.prob e : ℝ) < 1)
    (hW : ∀ g : Set V → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in avoidEvent H ({x} : Set V) Y,
        CSH.cshMarg (decoyList H (insert x Y) D) (obsConst H o v (insert x Y ∪ {d | d ∈ D})) o v
          (fun u => (∫ η in hyperConn H x u, g (hyperClusterSet H η ({x} : Set V))
                ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob)) -
              (∫ η, g (hyperClusterSet H η ({x} : Set V))
                ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob)) *
              (prodBernoulli (deleteHyper H (hyperClusterSet H ω Y)).prob).real
                (hyperConn H x u)) ∂(prodBernoulli H.prob)) :
    CSHHolds H x Y D o v :=
  fun f hf => cshMargin_nonneg_of_within H x Y D o v hY hW f hf

/-! ### Non-vacuity: the one-cluster inequality out of the reduction -/

/-- **The one-cluster inequality of van den Berg–Häggström–Kahn out of the reduction.**  At a
single marker the hypothesis of `multiMarkerCov_nonneg_of_within` is Harris' inequality in the
model `H − C_X(ω)` for the increasing functional `g(C_s)` and the increasing event `{s ↔ u}`, so
the reduction returns `0 ≤ covD H s X f u`: given `s ↮ X`, `f(C_s)` and `1{s ↔ u}` are positively
correlated.  This is `oneCluster_contact_le` of `KN/HyperProjGen.lean`, proved there by another
route.  [cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] -/
theorem covD_nonneg_of_within_harris (H : Hypergraph V E) (s : V) (X : Set V)
    (hX : ∀ e ∈ labelsMeeting H X, (H.prob e : ℝ) < 1) (u : V) {f : Set V → ℝ}
    (hf : Monotone f) : 0 ≤ covD H s X f u := by
  have key := multiMarkerCov_nonneg_of_within H s X hX ({u} : Finset V) (fun _ => 1)
    (fun g hg hg0 => by
      refine setIntegral_nonneg (measurableSet_of_fintype _) fun ω _ => ?_
      simp only [Finset.sum_singleton, one_mul]
      have hcl : hyperClusterSet (deleteHyper H (hyperClusterSet H ω X)) = hyperClusterSet H :=
        rfl
      have hharris := setIntegral_clusterFun_ge (deleteHyper H (hyperClusterSet H ω X))
        ({s} : Set V) g hg (hyperConn H s u) (isUpperSet_hyperConn H s u)
      rw [hcl] at hharris
      linarith) hf
  simpa using key

end Gibbs

/-! ## (GEN) from (S5), graded by the size of the relay set -/

section Graded

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **(S5) for relay sets of size `≤ K` implies (GEN) for relay sets of size `≤ K + 1`.**  For an
`m`-compatible injective rank on `A`, remove the rank-maximal relay `k`: `Sur_o(A) = Sur_o(T) −
deficit_k`, and the one-cluster inequality for `C(k)` given `k ↮ T` together with (S5) for
`(o, k, T)` bounds the deficit.  Hyperedge form of `AGloc.gen_firstRank_of_surplusTransfer`; the
hypothesis is asked for the given model only.  [cite: VandenbergHaggstromKahn2005, Thm. 1.3] -/
theorem gen_firstRank_of_surplusTransfer (H : Hypergraph V E) (K : ℕ)
    (hST : ∀ (T : Finset V) (o v : V) (F : Set V → ℝ) (r : V → ℕ),
      T.card ≤ K → v ∉ T → (∀ S S' : Set V, S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) →
      Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
          ∫ ω, F (hyperClusterSet H ω ({a'} : Set V)) ∂(prodBernoulli H.prob)) →
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V) ∩ hyperConn H o v) *
          surplus H T r F v ≤
        (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V)) *
          surplus H T r F o) :
    ∀ (A : Finset V) (o : V) (F : Set V → ℝ) (r : V → ℕ),
      A.card ≤ K + 1 → (∀ S S' : Set V, S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) →
      Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
          ∫ ω, F (hyperClusterSet H ω ({a'} : Set V)) ∂(prodBernoulli H.prob)) →
      ∑ a ∈ A, (prodBernoulli H.prob).real (firstPattern H A r o a) *
            ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) ≤
        ∫ ω in ⋃ a ∈ A, hyperConn H o a,
          F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) := by
  have main : ∀ (N : ℕ) (A : Finset V) (o : V) (F : Set V → ℝ) (r : V → ℕ), A.card = N →
      A.card ≤ K + 1 → (∀ S S' : Set V, S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) →
      Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
          ∫ ω, F (hyperClusterSet H ω ({a'} : Set V)) ∂(prodBernoulli H.prob)) →
      0 ≤ surplusY H (∅ : Set V) A r F o := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro A o F r hN hK hF hF0 hr hcompat
    set μ := prodBernoulli H.prob with hμ
    have hn := fun (S : Set (Set E)) => (measureReal_nonneg : 0 ≤ μ.real S)
    rcases A.eq_empty_or_nonempty with hA0 | hne
    · subst hA0; simp [surplusY]
    obtain ⟨k, hkA, hkmax⟩ := Finset.exists_max_image A r hne
    set T : Finset V := A.erase k with hT
    have hTcard : T.card < N := by
      have hpos : 0 < A.card := Finset.card_pos.2 hne
      rw [hT, Finset.card_erase_of_mem hkA]; omega
    have hTK : T.card ≤ K := by rw [hT, Finset.card_erase_of_mem hkA]; omega
    have hTA : ∀ a ∈ T, a ∈ A := fun a ha => Finset.mem_of_mem_erase ha
    have hkT : k ∉ T := Finset.notMem_erase k A
    have hlt : ∀ a ∈ T, r a < r k := by
      intro a ha
      rcases (hkmax a (hTA a ha)).lt_or_eq with h | h
      · exact h
      · exact absurd (hr (hTA a ha) hkA h) (Finset.ne_of_mem_erase ha)
    have hrT : Set.InjOn r ↑T := hr.mono (by intro a ha; exact hTA a ha)
    have hcompatT : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂μ) ≤
          ∫ ω, F (hyperClusterSet H ω ({a'} : Set V)) ∂μ :=
      fun a ha a' ha' h => hcompat a (hTA a ha) a' (hTA a' ha') h
    have hmle : ∀ a ∈ T, (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂μ) ≤
        ∫ ω, F (hyperClusterSet H ω ({k} : Set V)) ∂μ :=
      fun a ha => hcompat a (hTA a ha) k hkA (hlt a ha)
    have hIH : 0 ≤ surplusY H ∅ T r F o :=
      ih T.card hTcard T o F r rfl (hTK.trans (Nat.le_succ K)) hF hF0 hrT hcompatT
    have hS5 := hST T o k F r hTK hkT hF hF0 hrT hcompatT
    rw [← surplusY_empty H T r F k, ← surplusY_empty H T r F o, hyperConn_comm H o k] at hS5
    set Dk : Set (Set E) := avoidEvent H ({k} : Set V) (↑T : Set V) with hDk
    set Ok : Set (Set E) := hyperConn H k o with hOk
    set fk : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({k} : Set V)) with hfk
    set mk : ℝ := ∫ ω, fk ω ∂μ with hmk
    have hpeel : surplusY H ∅ A r F o = surplusY H ∅ T r F o +
        ((∫ ω in Dk ∩ Ok, fk ω ∂μ) - μ.real (Dk ∩ Ok) * mk) := by
      have h := surplusY_erase_add H (∅ : Set V) A r F hkA hlt o
      rw [Set.empty_union, condMeanY_empty] at h
      exact h
    have hBHK := oneCluster_contact_le H k o (↑T : Set V) hF
    have hκ : mk * μ.real Dk - ∫ ω in Dk, fk ω ∂μ ≤ surplusY H ∅ T r F k := by
      have h := kappaY_le_surplusY H (∅ : Set V) T r F k hrT
        (fun a ha => by rw [condMeanY_empty, condMeanY_empty]; exact hmle a ha)
      rw [Set.empty_union, condMeanY_empty] at h
      exact h
    have hkey : μ.real Dk * (mk * μ.real (Dk ∩ Ok) - ∫ ω in Dk ∩ Ok, fk ω ∂μ) ≤
        μ.real Dk * surplusY H ∅ T r F o := by
      have h1 : μ.real Dk * (mk * μ.real (Dk ∩ Ok) - ∫ ω in Dk ∩ Ok, fk ω ∂μ) ≤
          μ.real (Dk ∩ Ok) * (mk * μ.real Dk - ∫ ω in Dk, fk ω ∂μ) := by nlinarith [hBHK]
      have h2 := mul_le_mul_of_nonneg_left hκ (hn (Dk ∩ Ok))
      linarith
    rw [hpeel]
    by_cases hD0 : μ.real Dk = 0
    · have hP0 : μ.real (Dk ∩ Ok) = 0 :=
        le_antisymm (hD0 ▸ measureReal_mono Set.inter_subset_left (measure_ne_top _ _)) (hn _)
      have hnull : μ (Dk ∩ Ok) = 0 := by
        rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at hP0
      have hPint : ∫ ω in Dk ∩ Ok, fk ω ∂μ = 0 := by
        rw [Measure.restrict_eq_zero.2 hnull, integral_zero_measure]
      rw [hP0, zero_mul, sub_zero, hPint]
      linarith
    · have hDpos : 0 < μ.real Dk := lt_of_le_of_ne (hn _) (Ne.symm hD0)
      by_contra hneg
      have := mul_neg_of_pos_of_neg hDpos (lt_of_not_ge hneg)
      nlinarith [hkey]
  intro A o F r hK hF hF0 hr hcompat
  exact sum_le_setIntegral_of_gen H A r F o
    (by rw [← surplusY_empty]; exact main A.card A o F r rfl hK hF hF0 hr hcompat)

/-- **`HyperAdditiveGluing` from (S5)**, by name: if the surplus transfer inequality holds in every
finite model for every relay set, then additive gluing holds for hyperedges.  The composite
`(S5) ⟹ (GEN) ⟹ (AG-loc) ⟹ AdditiveGluing` is `AGOne.additiveGluing_of_surplusTransfer`, one model
at a time; this is its quantified form, the hyperedge reading of
`AGloc.additiveGluing_of_surplusTransfer`. -/
theorem hyperAdditiveGluing_of_surplusTransfer
    (hST : ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L) (F : Set W → ℝ),
      (∀ S S' : Set W, S ⊆ S' → F S ≤ F S') →
      ∀ (T : Finset W) (u v : W) (r : W → ℕ), v ∉ T → Set.InjOn r ↑T →
      (∀ c ∈ T, ∀ c' ∈ T, r c < r c' →
        condMeanY H (∅ : Set W) F c ≤ condMeanY H (∅ : Set W) F c') →
      (prodBernoulli H.prob).real
            (avoidEvent H ({v} : Set W) ((∅ : Set W) ∪ (↑T : Set W)) ∩ hyperConn H u v) *
          surplusY H (∅ : Set W) T r F v ≤
        (prodBernoulli H.prob).real (avoidEvent H ({v} : Set W) ((∅ : Set W) ∪ (↑T : Set W))) *
          surplusY H (∅ : Set W) T r F u) :
    HyperAdditiveGluing := by
  intro W L _ _ H A o b t ht hrel
  exact additiveGluing_of_surplusTransfer H A o b t ht hrel fun F hF => hST W L H F hF

end Graded

/-! ## The glue -/

section Glue

/-- **The glue as a named statement**: additive gluing for hyperedges implies near-one gluing for
hyperedges.  Hyperedge form of `Percolation.Continuity.Statements.AdditiveGluingGlue`. -/
def HyperAdditiveGluingGlue : Prop := HyperAdditiveGluing → HyperNearOneGluing

/-- **`HyperAdditiveGluingGlue` holds**, with `δ = ε / 2`: it is `AGOne.hyperAdditiveGluingSuffices`.
Hyperedge form of `Percolation.Continuity.additiveGluingGlue_proof`. -/
theorem hyperAdditiveGluingGlue_proof : HyperAdditiveGluingGlue := by
  unfold HyperAdditiveGluingGlue
  intro hAG
  exact hyperAdditiveGluingSuffices hAG

end Glue

/-! ## The two-relay surplus transfer from the conditioned covariance transfer -/

section Pair

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **(S5)₂ from (COV).**  `μ = prodBernoulli H.prob`, `F` monotone on vertex sets, relays `a, b`
with `m_a ≤ m_b`, observers `o, v`, `D = {v ↮ a} ∩ {v ↮ b}`, `Q = {a ↮ b}` and
`S15_x = μ(Q)·∫_{{x↔b}∩Q} (F(C_b) − F(C_a)) − μ({x↔b}∩Q)·∫_Q (F(C_b) − F(C_a))`.  IF (COV)
`μ(D ∩ {o↔v})·S15_v ≤ μ(D)·S15_o`, THEN the two-relay surplus transfer holds:
`μ(D ∩ {o↔v})·Sur_v({a,b}) ≤ μ(D)·Sur_o({a,b})`.

The bond template assumes `v ≠ a`, `v ≠ b` and `0 ≤ F`, and splits off the case `a = b`.  Here
`CTOne.blockHarrisTransfer` and `CTOne.plusPiece_nonneg` ask for none of that, and when `a = b` the
event `Q` is empty, which is the case `μ(Q) = 0` of the general argument.
[cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5] -/
theorem surplusTransfer_pair_of_covTransfer (H : Hypergraph V E) (o v a b : V) (F : Set V → ℝ)
    (hF : Monotone F)
    (hmab : (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob))
    (hCOV : (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) ({a, b} : Set V) ∩ hyperConn H o v) *
        ((prodBernoulli H.prob).real ((hyperConn H a b)ᶜ : Set (Set E)) *
            (∫ ω in hyperConn H v b ∩ (hyperConn H a b)ᶜ,
              (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
                ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (hyperConn H v b ∩ (hyperConn H a b)ᶜ) *
            ∫ ω in ((hyperConn H a b)ᶜ : Set (Set E)),
              (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
                ∂(prodBernoulli H.prob)) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a, b} : Set V)) *
        ((prodBernoulli H.prob).real ((hyperConn H a b)ᶜ : Set (Set E)) *
            (∫ ω in hyperConn H o b ∩ (hyperConn H a b)ᶜ,
              (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
                ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (hyperConn H o b ∩ (hyperConn H a b)ᶜ) *
            ∫ ω in ((hyperConn H a b)ᶜ : Set (Set E)),
              (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
                ∂(prodBernoulli H.prob))) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) ({a, b} : Set V) ∩ hyperConn H o v) *
        ((∫ ω in hyperConn H v a ∪ hyperConn H v b,
              F (hyperClusterSet H ω ({v} : Set V)) ∂(prodBernoulli H.prob)) -
          ((prodBernoulli H.prob).real (hyperConn H v a) *
              ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) +
            (prodBernoulli H.prob).real (hyperConn H v b ∩ (hyperConn H v a)ᶜ) *
              ∫ ω, F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob))) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a, b} : Set V)) *
        ((∫ ω in hyperConn H o a ∪ hyperConn H o b,
              F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob)) -
          ((prodBernoulli H.prob).real (hyperConn H o a) *
              ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) +
            (prodBernoulli H.prob).real (hyperConn H o b ∩ (hyperConn H o a)ᶜ) *
              ∫ ω, F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob))) := by
  have hmeas : ∀ T : Set (Set E), MeasurableSet T := fun _ => measurableSet_of_fintype _
  -- the three proved transfers, stated before the abbreviations so that `set` rewrites them too
  have hT1 := blockHarrisTransfer H o v a b F hF
  have hT4 := ordTransfer H o v a b
  have hpos := plusPiece_nonneg H v a b F hF
  set μ := prodBernoulli H.prob with hμ
  set fa : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({a} : Set V)) with hfa
  set fb : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({b} : Set V)) with hfb
  set ma : ℝ := ∫ ω, fa ω ∂μ with hma
  set mb : ℝ := ∫ ω, fb ω ∂μ with hmb
  have hint : ∀ (k : Set E → ℝ) (T : Set (Set E)), IntegrableOn k T μ :=
    fun k T => (integrable_of_fintype k).integrableOn
  have hn := fun (S : Set (Set E)) => (measureReal_nonneg : 0 ≤ μ.real S)
  set D : Set (Set E) := avoidEvent H ({v} : Set V) ({a, b} : Set V) with hD
  set Qc : Set (Set E) := (hyperConn H a b)ᶜ with hQc
  set Ov : Set (Set E) := hyperConn H o v with hOv
  -- cluster identities
  have hXbQ : ∀ x : V, (hyperConn H x b ∩ (hyperConn H x a)ᶜ : Set (Set E)) =
      hyperConn H x b ∩ Qc := by
    intro x; ext ω
    simp only [mem_inter_iff, mem_compl_iff, mem_hyperConn, hQc]
    constructor
    · rintro ⟨hxb, hxa⟩; exact ⟨hxb, fun h => hxa (hxb.trans h.symm)⟩
    · rintro ⟨hxb, hq⟩; exact ⟨hxb, fun hxa => hq (hxa.symm.trans hxb)⟩
  have hdiff : ∀ x : V, (hyperConn H x a ∪ hyperConn H x b : Set (Set E)) \ hyperConn H x a =
      hyperConn H x b ∩ Qc := by
    intro x; rw [← hXbQ x]; ext ω
    simp only [mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff]; tauto
  -- `Sur_x` in terms of `fa`, `fb`
  have hSur : ∀ x : V, (∫ ω in hyperConn H x a ∪ hyperConn H x b,
      F (hyperClusterSet H ω ({x} : Set V)) ∂μ) =
      (∫ ω in hyperConn H x a, fa ω ∂μ) + ∫ ω in hyperConn H x b ∩ Qc, fb ω ∂μ := by
    intro x
    rw [← integral_inter_add_sdiff (hmeas (hyperConn H x a)) (hint _ _),
      inter_eq_right.2 subset_union_left, hdiff x]
    congr 1
    · exact setIntegral_congr_fun (hmeas _) fun ω hω => by
        show F (hyperClusterSet H ω ({x} : Set V)) = F (hyperClusterSet H ω ({a} : Set V))
        rw [hyperClusterSet_singleton_eq_of_reachable H
          (hω : (openHyperGraph H ω).Reachable x a)]
    · exact setIntegral_congr_fun (hmeas _) fun ω hω => by
        show F (hyperClusterSet H ω ({x} : Set V)) = F (hyperClusterSet H ω ({b} : Set V))
        rw [hyperClusterSet_singleton_eq_of_reachable H
          (hω.1 : (openHyperGraph H ω).Reachable x b)]
  -- `SH_x` in terms of `fa`
  have hSH : ∀ x : V, (∫ ω in hyperConn H x a ∪ hyperConn H x b, fa ω ∂μ) =
      (∫ ω in hyperConn H x a, fa ω ∂μ) + ∫ ω in hyperConn H x b ∩ Qc, fa ω ∂μ := by
    intro x
    rw [← integral_inter_add_sdiff (hmeas (hyperConn H x a)) (hint _ _),
      inter_eq_right.2 subset_union_left, hdiff x]
  have hUμ : ∀ x : V, μ.real (hyperConn H x a ∪ hyperConn H x b : Set (Set E)) =
      μ.real (hyperConn H x a) + μ.real (hyperConn H x b ∩ Qc) := by
    intro x
    rw [← measureReal_inter_add_sdiff (s := (hyperConn H x a ∪ hyperConn H x b : Set (Set E)))
      (h := measure_ne_top _ _) (hmeas (hyperConn H x a)), inter_eq_right.2 subset_union_left,
      hdiff x]
  -- `∫_{Qc} (fb − fa) = mb − ma`
  have hQint : ∫ ω in Qc, (fb ω - fa ω) ∂μ = mb - ma := by
    have h1 := integral_add_compl (hmeas (hyperConn H a b : Set (Set E)))
      (integrable_of_fintype (μ := μ) (fun ω => fb ω - fa ω))
    have h2 : ∫ ω in (hyperConn H a b : Set (Set E)), (fb ω - fa ω) ∂μ = 0 := by
      refine (setIntegral_congr_fun (hmeas _) (g := fun _ => (0 : ℝ)) fun ω hω => ?_).trans
        (by simp)
      show F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)) = 0
      rw [hyperClusterSet_singleton_eq_of_reachable H (hω : (openHyperGraph H ω).Reachable a b),
        sub_self]
    rw [h2, zero_add] at h1
    rw [hQc, h1, integral_sub (integrable_of_fintype _) (integrable_of_fintype _)]
  have hsubint : ∀ S : Set (Set E), ∫ ω in S, (fb ω - fa ω) ∂μ =
      (∫ ω in S, fb ω ∂μ) - ∫ ω in S, fa ω ∂μ :=
    fun S => integral_sub (hint fb S) (hint fa S)
  have hmab' : ma ≤ mb := hmab
  have hQc1 : μ.real Qc ≤ 1 := measureReal_le_one
  -- rewrite everything in terms of the pieces
  rw [hSur v, hSur o, hXbQ v, hXbQ o]
  rw [hSH v, hSH o, hUμ v, hUμ o] at hT1
  rw [hQint, hsubint, hsubint] at hCOV
  rw [hQint, hsubint] at hpos
  -- real arithmetic
  set P := μ.real Qc with hP
  set d := μ.real D with hd
  set dov := μ.real (D ∩ Ov) with hdov
  set IaO := ∫ ω in hyperConn H o a, fa ω ∂μ
  set IaV := ∫ ω in hyperConn H v a, fa ω ∂μ
  set IbO := ∫ ω in hyperConn H o b ∩ Qc, fb ω ∂μ with hIbO
  set IbV := ∫ ω in hyperConn H v b ∩ Qc, fb ω ∂μ with hIbV
  set JaO := ∫ ω in hyperConn H o b ∩ Qc, fa ω ∂μ with hJaO
  set JaV := ∫ ω in hyperConn H v b ∩ Qc, fa ω ∂μ with hJaV
  set xO := μ.real (hyperConn H o b ∩ Qc) with hxO'
  set xV := μ.real (hyperConn H v b ∩ Qc) with hxV'
  set yO := μ.real (hyperConn H o a : Set (Set E))
  set yV := μ.real (hyperConn H v a : Set (Set E))
  set sO := P * (IbO - JaO) - xO * (mb - ma) with hsO
  set sV := P * (IbV - JaV) - xV * (mb - ma) with hsV
  have hsV0 : 0 ≤ sV := by rw [hsV]; linarith [hpos]
  have hkey : dov * sV ≤ d * sO := by
    rw [hsO, hsV]
    exact hCOV
  have hT4' : dov * xV ≤ d * xO := hT4
  by_cases hP0 : P = 0
  · have hxO : xO = 0 :=
      le_antisymm (hP0 ▸ measureReal_mono inter_subset_right (measure_ne_top _ _)) (hn _)
    have hxV : xV = 0 :=
      le_antisymm (hP0 ▸ measureReal_mono inter_subset_right (measure_ne_top _ _)) (hn _)
    have hI0 : ∀ (k : Set E → ℝ) (S : Set (Set E)), μ.real (S ∩ Qc) = 0 →
        ∫ ω in S ∩ Qc, k ω ∂μ = 0 :=
      fun k S h0 => setIntegral_measure_zero k ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0)
    have h1 : IbO = 0 := hI0 fb _ hxO
    have h2 : IbV = 0 := hI0 fb _ hxV
    have h3 : JaO = 0 := hI0 fa _ hxO
    have h4 : JaV = 0 := hI0 fa _ hxV
    rw [h1, h2, hxO, hxV]
    rw [h3, h4, hxO, hxV] at hT1
    simp only [add_zero, zero_mul] at hT1 ⊢
    exact hT1
  · have hPpos : 0 < P := lt_of_le_of_ne (hn _) (Ne.symm hP0)
    have hc : 0 ≤ (1 - P) * (mb - ma) := mul_nonneg (by linarith) (by linarith)
    have i1 : dov * (P * (IaV + JaV - (yV + xV) * ma)) ≤ d * (P * (IaO + JaO - (yO + xO) * ma)) :=
      calc dov * (P * (IaV + JaV - (yV + xV) * ma))
          = P * (dov * (IaV + JaV - (yV + xV) * ma)) := by ring
        _ ≤ P * (d * (IaO + JaO - (yO + xO) * ma)) := mul_le_mul_of_nonneg_left hT1 (hn Qc)
        _ = d * (P * (IaO + JaO - (yO + xO) * ma)) := by ring
    have i3 : dov * ((1 - P) * (mb - ma) * xV) ≤ d * ((1 - P) * (mb - ma) * xO) :=
      calc dov * ((1 - P) * (mb - ma) * xV) = (1 - P) * (mb - ma) * (dov * xV) := by ring
        _ ≤ (1 - P) * (mb - ma) * (d * xO) := mul_le_mul_of_nonneg_left hT4' hc
        _ = d * ((1 - P) * (mb - ma) * xO) := by ring
    have split : ∀ (Ia Ib Ja x y : ℝ), P * (Ia + Ib - (y * ma + x * mb)) =
        P * (Ia + Ja - (y + x) * ma) + (P * (Ib - Ja) - x * (mb - ma)) +
          (1 - P) * (mb - ma) * x := by
      intro Ia Ib Ja x y; ring
    have hfinal : P * (dov * (IaV + IbV - (yV * ma + xV * mb))) ≤
        P * (d * (IaO + IbO - (yO * ma + xO * mb))) :=
      calc P * (dov * (IaV + IbV - (yV * ma + xV * mb)))
          = dov * (P * (IaV + IbV - (yV * ma + xV * mb))) := by ring
        _ = dov * (P * (IaV + JaV - (yV + xV) * ma)) + dov * sV +
              dov * ((1 - P) * (mb - ma) * xV) := by
          rw [split IaV IbV JaV xV yV]; ring
        _ ≤ d * (P * (IaO + JaO - (yO + xO) * ma)) + d * sO +
              d * ((1 - P) * (mb - ma) * xO) := by
          linarith [i1, hkey, i3]
        _ = d * (P * (IaO + IbO - (yO * ma + xO * mb))) := by rw [split IaO IbO JaO xO yO]; ring
        _ = P * (d * (IaO + IbO - (yO * ma + xO * mb))) := by ring
    exact le_of_mul_le_mul_left hfinal hPpos

/-- **(GEN) for three relays from (COV).**  For `F` monotone nonnegative, an observer `o` and
relays `a₁, a₂, a₃` with `m₁ ≤ m₂ ≤ m₃`: IF (COV) holds with `(a, b, v) = (a₁, a₂, a₃)`, THEN
`μ(o↔a₁)·m₁ + μ(o↔a₂, o↮a₁)·m₂ + μ(o↔a₃, o↮a₁, o↮a₂)·m₃ ≤ ∫_{o ↔ {a₁,a₂,a₃}} F(C(o))`.
Hyperedge form of `SurplusTransfer.gen_triple_of_covTransfer`; the distinctness hypotheses of the
bond statement are absent.  [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem gen_triple_of_covTransfer (H : Hypergraph V E) (o a₁ a₂ a₃ : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hm12 : (∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob))
    (hm23 : (∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({a₃} : Set V)) ∂(prodBernoulli H.prob))
    (hCOV : (prodBernoulli H.prob).real
          (avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V) ∩ hyperConn H o a₃) *
        ((prodBernoulli H.prob).real ((hyperConn H a₁ a₂)ᶜ : Set (Set E)) *
            (∫ ω in hyperConn H a₃ a₂ ∩ (hyperConn H a₁ a₂)ᶜ,
              (F (hyperClusterSet H ω ({a₂} : Set V)) - F (hyperClusterSet H ω ({a₁} : Set V)))
                ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (hyperConn H a₃ a₂ ∩ (hyperConn H a₁ a₂)ᶜ) *
            ∫ ω in ((hyperConn H a₁ a₂)ᶜ : Set (Set E)),
              (F (hyperClusterSet H ω ({a₂} : Set V)) - F (hyperClusterSet H ω ({a₁} : Set V)))
                ∂(prodBernoulli H.prob)) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V)) *
        ((prodBernoulli H.prob).real ((hyperConn H a₁ a₂)ᶜ : Set (Set E)) *
            (∫ ω in hyperConn H o a₂ ∩ (hyperConn H a₁ a₂)ᶜ,
              (F (hyperClusterSet H ω ({a₂} : Set V)) - F (hyperClusterSet H ω ({a₁} : Set V)))
                ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (hyperConn H o a₂ ∩ (hyperConn H a₁ a₂)ᶜ) *
            ∫ ω in ((hyperConn H a₁ a₂)ᶜ : Set (Set E)),
              (F (hyperClusterSet H ω ({a₂} : Set V)) - F (hyperClusterSet H ω ({a₁} : Set V)))
                ∂(prodBernoulli H.prob))) :
    (prodBernoulli H.prob).real (hyperConn H o a₁) *
          (∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob)) +
        (prodBernoulli H.prob).real (hyperConn H o a₂ ∩ (hyperConn H o a₁)ᶜ) *
          (∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) +
        (prodBernoulli H.prob).real
            (hyperConn H o a₃ ∩ (hyperConn H o a₁ ∪ hyperConn H o a₂)ᶜ) *
          (∫ ω, F (hyperClusterSet H ω ({a₃} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω in hyperConn H o a₁ ∪ hyperConn H o a₂ ∪ hyperConn H o a₃,
        F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) :=
  gen_triple_of_surplusTransfer_pair H o a₁ a₂ a₃ F hF hF0 hm12 hm23
    (surplusTransfer_pair_of_covTransfer H o a₃ a₁ a₂ F (fun _ _ h => hF _ _ h) hm12 hCOV)

/-- **(S5)₂ in the shape `CTBase.covTransfer_of_covTau` produces.**  The conditioned covariance
transfer of `KN/HyperCTBase.lean` is stated with the events `{b ↮ a}`, `{b ↔ v}`, `{v ↮ {b, a}}`
and `{v ↔ o}`; this is `surplusTransfer_pair_of_covTransfer` read through the four identifications
`{b ↮ a} = {a ↔ b}ᶜ`, `{b ↔ x} = {x ↔ b}`, `{v ↮ {b,a}} = {v ↮ {a,b}}` and `{v ↔ o} = {o ↔ v}`. -/
theorem surplusTransfer_pair_of_covTau (H : Hypergraph V E) (o v a b : V) (F : Set V → ℝ)
    (hF : Monotone F)
    (hmab : (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob))
    (hCT : (prodBernoulli H.prob).real
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
          (avoidEvent H ({v} : Set V) ({a, b} : Set V) ∩ hyperConn H o v) *
        ((∫ ω in hyperConn H v a ∪ hyperConn H v b,
              F (hyperClusterSet H ω ({v} : Set V)) ∂(prodBernoulli H.prob)) -
          ((prodBernoulli H.prob).real (hyperConn H v a) *
              ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) +
            (prodBernoulli H.prob).real (hyperConn H v b ∩ (hyperConn H v a)ᶜ) *
              ∫ ω, F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob))) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a, b} : Set V)) *
        ((∫ ω in hyperConn H o a ∪ hyperConn H o b,
              F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob)) -
          ((prodBernoulli H.prob).real (hyperConn H o a) *
              ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) +
            (prodBernoulli H.prob).real (hyperConn H o b ∩ (hyperConn H o a)ᶜ) *
              ∫ ω, F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob))) := by
  have key := covTransfer_of_covTau H o v a b F hCT
  have hQ : avoidEvent H ({b} : Set V) ({a} : Set V) = ((hyperConn H a b)ᶜ : Set (Set E)) := by
    rw [avoidEvent_singleton_eq_compl H b a, hyperConn_comm H b a]
  rw [hQ, Set.pair_comm b a, hyperConn_comm H v o, hyperConn_comm H b v, hyperConn_comm H b o,
    Set.inter_comm ((hyperConn H a b)ᶜ) (hyperConn H v b),
    Set.inter_comm ((hyperConn H a b)ᶜ) (hyperConn H o b)] at key
  exact surplusTransfer_pair_of_covTransfer H o v a b F hF hmab key

/-- **(GEN) for three relays from the conditioned covariance transfer in `covTau` shape.** -/
theorem gen_triple_of_covTau (H : Hypergraph V E) (o a₁ a₂ a₃ : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hm12 : (∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob))
    (hm23 : (∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({a₃} : Set V)) ∂(prodBernoulli H.prob))
    (hCT : (prodBernoulli H.prob).real
          (avoidEvent H ({a₃} : Set V) ({a₂, a₁} : Set V) ∩ hyperConn H a₃ o) *
        ((prodBernoulli H.prob).real (avoidEvent H ({a₂} : Set V) ({a₁} : Set V)) *
            (∫ ω in avoidEvent H ({a₂} : Set V) ({a₁} : Set V) ∩ hyperConn H a₂ a₃,
              projFun H a₁ F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real
              (avoidEvent H ({a₂} : Set V) ({a₁} : Set V) ∩ hyperConn H a₂ a₃) *
            ∫ ω in avoidEvent H ({a₂} : Set V) ({a₁} : Set V),
              projFun H a₁ F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob))
        ≤ (prodBernoulli H.prob).real (avoidEvent H ({a₃} : Set V) ({a₂, a₁} : Set V)) *
            ((prodBernoulli H.prob).real (avoidEvent H ({a₂} : Set V) ({a₁} : Set V)) *
                (∫ ω in avoidEvent H ({a₂} : Set V) ({a₁} : Set V) ∩ hyperConn H a₂ o,
                  projFun H a₁ F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) -
              (prodBernoulli H.prob).real
                  (avoidEvent H ({a₂} : Set V) ({a₁} : Set V) ∩ hyperConn H a₂ o) *
                ∫ ω in avoidEvent H ({a₂} : Set V) ({a₁} : Set V),
                  projFun H a₁ F (hyperClusterSet H ω ({a₂} : Set V))
                    ∂(prodBernoulli H.prob))) :
    (prodBernoulli H.prob).real (hyperConn H o a₁) *
          (∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob)) +
        (prodBernoulli H.prob).real (hyperConn H o a₂ ∩ (hyperConn H o a₁)ᶜ) *
          (∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) +
        (prodBernoulli H.prob).real
            (hyperConn H o a₃ ∩ (hyperConn H o a₁ ∪ hyperConn H o a₂)ᶜ) *
          (∫ ω, F (hyperClusterSet H ω ({a₃} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω in hyperConn H o a₁ ∪ hyperConn H o a₂ ∪ hyperConn H o a₃,
        F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) :=
  gen_triple_of_surplusTransfer_pair H o a₁ a₂ a₃ F hF hF0 hm12 hm23
    (surplusTransfer_pair_of_covTau H o a₃ a₁ a₂ F (fun _ _ h => hF _ _ h) hm12 hCT)

end Pair

/-! ## Non-vacuity of the graded theorem and of the two-relay transfer -/

section Checks

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **Harris' inequality out of the graded theorem.**  At `K = 0` the hypothesis of
`gen_firstRank_of_surplusTransfer` is vacuous (the only relay set of size `≤ 0` is empty, and both
surpluses vanish), and the conclusion at the relay set `{a}` is
`P(o ↔ a) · E F(C_a) ≤ E[F(C_o); o ↔ a]`. -/
theorem gen_singleton (H : Hypergraph V E) (o a : V) (F : Set V → ℝ)
    (hF : ∀ S S' : Set V, S ⊆ S' → F S ≤ F S') (hF0 : ∀ S, 0 ≤ F S) :
    (prodBernoulli H.prob).real (hyperConn H o a) *
        (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω in hyperConn H o a, F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) := by
  have hvac : ∀ (T : Finset V) (o v : V) (F : Set V → ℝ) (r : V → ℕ),
      T.card ≤ 0 → v ∉ T → (∀ S S' : Set V, S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) →
      Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
          ∫ ω, F (hyperClusterSet H ω ({a'} : Set V)) ∂(prodBernoulli H.prob)) →
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V) ∩ hyperConn H o v) *
          surplus H T r F v ≤
        (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V)) *
          surplus H T r F o := by
    intro T o v F r hT _ _ _ _ _
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hT)
    subst hT0
    simp [surplus]
  have key := gen_firstRank_of_surplusTransfer H 0 hvac ({a} : Finset V) o F (fun _ => 0)
    (by simp) hF hF0 (by intro x hx y hy _; simp only [Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy; rw [hx, hy]) (by intro x hx y hy h; exact absurd h (lt_irrefl 0))
  have hfp : firstPattern H ({a} : Finset V) (fun _ => 0) o a = hyperConn H o a := by
    simp [firstPattern]
  simpa [hfp] using key

/-- **The one-relay transfer out of the two-relay one.**  At `a = b` the event `{a ↮ b}` is empty,
so (COV) reads `0 ≤ 0` and `surplusTransfer_pair_of_covTransfer` returns the one-relay surplus
transfer `μ(D ∩ {o ↔ v})·Sur_v({a}) ≤ μ(D)·Sur_o({a})`, in the two-relay notation. -/
theorem surplusTransfer_pair_self (H : Hypergraph V E) (o v a : V) (F : Set V → ℝ)
    (hF : Monotone F) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) ({a, a} : Set V) ∩ hyperConn H o v) *
        ((∫ ω in hyperConn H v a ∪ hyperConn H v a,
              F (hyperClusterSet H ω ({v} : Set V)) ∂(prodBernoulli H.prob)) -
          ((prodBernoulli H.prob).real (hyperConn H v a) *
              ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) +
            (prodBernoulli H.prob).real (hyperConn H v a ∩ (hyperConn H v a)ᶜ) *
              ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob))) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a, a} : Set V)) *
        ((∫ ω in hyperConn H o a ∪ hyperConn H o a,
              F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob)) -
          ((prodBernoulli H.prob).real (hyperConn H o a) *
              ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) +
            (prodBernoulli H.prob).real (hyperConn H o a ∩ (hyperConn H o a)ᶜ) *
              ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob))) := by
  refine surplusTransfer_pair_of_covTransfer H o v a a F hF le_rfl ?_
  have hQ : ((hyperConn H a a)ᶜ : Set (Set E)) = ∅ := by
    ext ω
    simp only [Set.mem_compl_iff, mem_hyperConn, Set.mem_empty_iff_false, iff_false, not_not]
    exact SimpleGraph.Reachable.refl a
  simp [hQ]

end Checks

end KNAll.Site.CSHTwoA

end

#print axioms KNAll.Site.CSHTwoA.map_fst_decoyList
#print axioms KNAll.Site.CSHTwoA.cshMargin_eq_sum
#print axioms KNAll.Site.CSHTwoA.slForm_jn_reachable
#print axioms KNAll.Site.CSHTwoA.covDF_eq_withinF_add
#print axioms KNAll.Site.CSHTwoA.gibbsT_iterate_bounds
#print axioms KNAll.Site.CSHTwoA.real_regen_pos
#print axioms KNAll.Site.CSHTwoA.clusterCov_nonneg_of_within
#print axioms KNAll.Site.CSHTwoA.multiMarkerCov_nonneg_of_within
#print axioms KNAll.Site.CSHTwoA.cshMargin_nonneg_of_within
#print axioms KNAll.Site.CSHTwoA.cshHolds_of_within
#print axioms KNAll.Site.CSHTwoA.covD_nonneg_of_within_harris
#print axioms KNAll.Site.CSHTwoA.gen_firstRank_of_surplusTransfer
#print axioms KNAll.Site.CSHTwoA.hyperAdditiveGluing_of_surplusTransfer
#print axioms KNAll.Site.CSHTwoA.hyperAdditiveGluingGlue_proof
#print axioms KNAll.Site.CSHTwoA.surplusTransfer_pair_of_covTransfer
#print axioms KNAll.Site.CSHTwoA.surplusTransfer_pair_of_covTau
#print axioms KNAll.Site.CSHTwoA.gen_triple_of_covTransfer
#print axioms KNAll.Site.CSHTwoA.gen_triple_of_covTau
#print axioms KNAll.Site.CSHTwoA.gen_singleton
#print axioms KNAll.Site.CSHTwoA.surplusTransfer_pair_self
