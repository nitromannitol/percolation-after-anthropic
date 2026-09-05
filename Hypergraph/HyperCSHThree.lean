import Hypergraph.HyperAGBase
import Hypergraph.HyperCTBase
import Hypergraph.HyperCSHDefs
import Hypergraph.HyperAGOne
import Hypergraph.HyperCTOne
import Hypergraph.HyperCSHTwoA
import Hypergraph.HyperCSHTwoB
import Hypergraph.HyperTreeHK
import Hypergraph.HyperPeel
import Hypergraph.HyperProjGen
import Hypergraph.HyperTransfer
import Hypergraph.HyperOneCluster
import Hypergraph.HyperTwoClusterClosed
import Hypergraph.HyperFibre
import Hypergraph.HyperExpose
import Hypergraph.HyperLabelled
import Hypergraph.HyperDecisionTree
import Percolation.Continuity.OfGluing
import Percolation.Continuity.CovTau.StarBridge
import Percolation.Continuity.CSH.PeelTools

/-!
# Layer three of the correlation core, for hyperedges

The nine modules of `Percolation/Continuity/` whose imports inside that subtree all lie in layers
zero to two: `AdditiveGluing/SurplusClosure.lean`, `CSH/PeelTools.lean`, `CSH/PhiMarkov.lean`,
`CovTau/A2EdgeDefs.lean`, `CovTau/A2Anti.lean`, `CovTau/StarBridge.lean`,
`CovTau/StarHPrelim.lean`, `HullPort/TABase.lean` and `Continuity/OfGluing.lean`.  Everything is
stated for a `Hypergraph V E` with arbitrary incidence sets over arbitrary types, finiteness being
assumed only where it is used.

## What the layer already had

Much of two of the nine files is in the development already, in a more general form.

* `CSH/PeelTools.lean`.  `KN/HyperPeel.lean` proves Lemma P and Lemma κ with a base avoided set,
  and carries `covD_topTerm_eq` against an arbitrary avoided set and an arbitrary subtracted
  constant, `covD_psiIso`, `mem_decoyList` and the `Ψ_iso` facts.  Only the decoy-free readings are
  added (Section 1), as the case `Y = ∅`.  `CSH.cshMarg_congr` of the bond file is stated for an
  arbitrary evaluation type and never mentions a percolation model, so it is imported and used.
* `AdditiveGluing/SurplusClosure.lean`.  `KN/HyperTransfer.lean` proves the whole closure with a
  base avoided set: the rank-free minimum form, its continuity at a probability vector at which
  every relay is active, and the passage from strictly interior probabilities to arbitrary ones.
  At `Y = ∅` the activity hypothesis is automatic, and Section 2 records the specializations.
* `Continuity/OfGluing.lean` is about `ℤ^d` and not about the model, so Section 3 only feeds it:
  `AGOne.additiveGluing_of_hyperAdditiveGluing` produces the bond statement and Kozma and Nitzan's
  Theorem 6 finishes.
* `CovTau/StarBridge.lean`.  Its marginal identity `ED_inter_eq` and its `sum_weight_mul_eq_ED` are
  stated for an arbitrary coordinate type; they are imported and used verbatim.  `KN/HyperTreeHK.lean`
  already carries the half of the dictionary that concerns the whole label set.

## What needed a new argument

* Section 4 (`A2EdgeDefs`).  The bond `tfE` reads a functional of the open EDGE cluster.  A
  functional of the vertex record will not do, by `CSHTwoB.exists_rTrace_law_not_product`, so `tfE`
  is defined at the LABEL cluster `rLabels`.
* Section 5 (`A2Anti`).  The locality of the event `{C_N = W}` and the domain Markov property go
  through as in the bond file.  `reach_rest_iff` does not: a step of a walk crosses a label, and for
  that label to belong to the model on `U ∖ C_N` EVERY one of its vertices has to avoid `C_N`, not
  only the two the step uses.  It does, because a vertex of the label lying in `C_N` would be
  adjacent to the walk's current vertex.
* Section 6 (`PhiMarkov`).  `CSHTwoB.set_sum_cond_sdiff` conditions on the cluster explored in the
  whole configuration; the peeling step needs the cluster explored in `ω ∖ B` for a fixed label set
  `B`, and `set_sum_cond_sdiff_off` is that.  `phiFun_eq_sum` then writes `Φ` as an exact finite sum
  against the product weight, with no conditioning event required to have positive probability.
* Section 8 (`TABase`).  Two hyperedge simplifications.  The bond boundary condition carries
  `¬ e.IsDiag`, because a diagonal pair is never open-adjacent; a label meeting both `X` and its
  complement automatically has two distinct vertices, so `taQ_eq_zero_of_noBoundary` carries no such
  clause.  And the bond hypothesis constrains the two endpoints of a pair where here it constrains
  every vertex of a label, which is what makes `cut_eq_of_noBoundary` come out as the labels meeting
  `X` exactly.
* Section 9 (`StarHPrelim`).  The union identity for the marker indicator, the functionals `covH`
  and `yH`, and the Markov bookkeeping `starH_markov` port.  The bond's Theorem 1.4 with a vertex
  SET does not; see below.

## Where layer three stops

`CovTauStarN.bhk14S_ED` reads the owner's functional as the value of `Ψ` at the open EDGE cluster
of `x`, and applies negative correlation with the source set `S`.  What licenses that is
`openEdgeCluster_biUnion_eq`: the edge cluster of a member is recovered from the edge cluster of the
set, so the owner's functional is an increasing functional of the cluster of the source set.  The
hyperedge development states its conditional association theorems for the VERTEX cluster, and
`exists_hyperClusterSet_eq_and_singleton_ne` proves that the vertex cluster of a source set does not
determine the cluster of a member.  So the bond statement has no transcription here.
`bhk14S_setFunctional` is the part that does port, for a functional of the cluster of the SET.
`hyperClusterSet_srcLabels` identifies the object that would license the full statement, the label
cluster of the source set; what is missing is van den Berg–Häggström–Kahn's Theorem 1.1 for
functionals of that label cluster, `KN/HyperOneCluster.lean` proving it for the vertex cluster only.

## The exchange identity

`clusterExchange` of `KN/HyperExchange.lean` is the ordered exchange of two prescribed clusters,
with the deletion of a vertex set realised as the closing of the labels that meet it.  It carries
`Disjoint K L`, and `exists_clusterExchange_ne_of_not_disjoint` of Section 10 shows the hypothesis
is not removable: one label incident to two vertices, the sources `{false}` and `{true}` and the
prescribed clusters `{false}` and `Set.univ` give `0` on the left and a positive number on the
right.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006), Thms. 1.1, 1.3–1.5,
  §1 pp. 3–5 and 7–8, §2.1 Lemma 2.4 p. 10.
* A. Gladkov, *A note on the Harris–Kesten theorem*, 2024, Thm. 3.2.
* G. Kozma, S. Nitzan, Conj. 1 (p. 3), Conj. 3 and Thm. 6 (p. 15), Conj. 4 (p. 32).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Site.CSHThree

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.AGBase KNAll.Site.AGOne KNAll.Site.CTBase KNAll.Site.CTOne
open KNAll.Site.CSHDefs KNAll.Site.CSHTwoA KNAll.Site.CSHTwoB KNAll.Site.TreeHK
open Percolation.Continuity Percolation.Continuity.Statements
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open Percolation.Literature.BHK2006 (weight weight_nonneg blockFubini ind_inter
  ind_le_one)
open scoped Classical

variable {V E : Type*}


/-! ## Section 1.  The peeling tools with no avoided set (`CSH/PeelTools.lean`)

`KN/HyperPeel.lean` proves Lemma P and Lemma κ with a base avoided set `Y`, and carries `covD`
against an arbitrary avoided set and an arbitrary subtracted constant (`covD_topTerm_eq`,
`covD_psiIso`), together with `mem_decoyList` and the `Ψ_iso` facts.  What the bond file
`Percolation/Continuity/CSH/PeelTools.lean` states is the decoy-free case, and that is what is
recorded here.  `CSH.cshMarg_congr` of that bond file is stated for an arbitrary evaluation type and
never mentions a percolation model, so it is imported and used verbatim. -/

section Peeling

variable [Fintype V] [Fintype E]

/-- **Lemma P, no avoided set**: peeling the rank-maximal relay `k` off `T`,
`Sur_u(T) = Sur_u(T ∖ {k}) + (∫_{D_k ∩ {k ↔ u}} F(C_k) − P(D_k ∩ {k ↔ u})·m_k)` with
`D_k = {k ↮ T ∖ {k}}`.  The bond `CSH.surplus_erase_add`; here it is `surplusY_erase_add` at
`Y = ∅`. -/
theorem surplus_erase_add (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ)
    {k : V} (hkT : k ∈ T) (hlt : ∀ a ∈ T.erase k, r a < r k) (u : V) :
    surplus H T r F u = surplus H (T.erase k) r F u +
      ((∫ ω in avoidEvent H ({k} : Set V) (↑(T.erase k) : Set V) ∩ hyperConn H k u,
          F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) -
        (prodBernoulli H.prob).real
            (avoidEvent H ({k} : Set V) (↑(T.erase k) : Set V) ∩ hyperConn H k u) *
          ∫ ω, F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) := by
  have h := surplusY_erase_add H (∅ : Set V) T r F hkT hlt u
  rwa [surplusY_empty, surplusY_empty, condMeanY_empty, Set.empty_union] at h

/-- **Lemma κ, no avoided set**: with `D_k = {k ↮ T'}` and the mean `m_k` maximal on `T' ∪ {k}`,
the deficit `κ_k = m_k·P(D_k) − ∫_{D_k} F(C_k)` is at most `Sur_k(T')`.  The bond
`CSH.kappa_le_surplus`; here it is `kappaY_le_surplusY` at `Y = ∅`. -/
theorem kappa_le_surplus (H : Hypergraph V E) (T' : Finset V) (r : V → ℕ) (F : Set V → ℝ)
    (k : V) (hrT : Set.InjOn r ↑T')
    (hmle : ∀ a ∈ T', (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) :
    (∫ ω, F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) *
        (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) (↑T' : Set V)) -
      (∫ ω in avoidEvent H ({k} : Set V) (↑T' : Set V),
        F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) ≤
      surplus H T' r F k := by
  have h := kappaY_le_surplusY H (∅ : Set V) T' r F k hrT
    (by simpa only [condMeanY_empty] using hmle)
  rwa [surplusY_empty, condMeanY_empty, Set.empty_union] at h

/-- **The top-relay term against `covD`, no avoided set**: the bond `CSH.covD_clusterFun_eq`.  It is
`covD_topTerm_eq` of `KN/HyperPeel.lean` at `A = ↑T'` and `m` the unconditional relay mean; the bond
file has to present the vertex functional as a functional `C ↦ F {a | a = k ∨ ∃ e ∈ C, a ∈ e}` of
the edge cluster, and here `covD` already reads a functional of the vertex cluster. -/
theorem covD_clusterFun_eq (H : Hypergraph V E) (T' : Finset V) (F : Set V → ℝ) (k u : V) :
    (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) (↑T' : Set V)) *
        ((∫ ω in avoidEvent H ({k} : Set V) (↑T' : Set V) ∩ hyperConn H k u,
            F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real
              (avoidEvent H ({k} : Set V) (↑T' : Set V) ∩ hyperConn H k u) *
            ∫ ω, F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) =
      covD H k (↑T' : Set V) F u -
        ((∫ ω, F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) *
            (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) (↑T' : Set V)) -
          ∫ ω in avoidEvent H ({k} : Set V) (↑T' : Set V),
            F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) *
          (prodBernoulli H.prob).real
            (avoidEvent H ({k} : Set V) (↑T' : Set V) ∩ hyperConn H k u) :=
  covD_topTerm_eq H (↑T' : Set V) F k u _

end Peeling

/-! ## Section 2.  The surplus transfer for all label probabilities, no avoided set
(`AdditiveGluing/SurplusClosure.lean`)

`KN/HyperTransfer.lean` proves the closure with a base avoided set `Y`: the ranked surplus equals
the rank-free minimum form (`avoidSurplus_eq_minForm`), the minimum form is continuous at a
probability vector at which every relay is active (`continuousAt_minForm`), and the transfer at
arbitrary probabilities follows from the transfer at strictly interior ones
(`avoidSurplusTransfer_of_nondegenerate`).  At `Y = ∅` the activity hypothesis is automatic, because
the avoidance event of the empty set is the whole space; the decoy-free statements of the bond file
are exactly those specializations, and `additiveGluing_of_surplusTransfer_nondegenerate` composes
them with `AGOne.additiveGluing_of_surplusTransfer`. -/

section Closure

variable [Fintype V] [Fintype E]

/-- The avoided surplus at `Y = ∅` is the plain surplus. -/
theorem avoidSurplus_empty (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ)
    (u : V) : avoidSurplus H (∅ : Set V) T r F u = surplus H T r F u :=
  surplusY_empty H T r F u

/-- With no avoided set the avoided conditional relay mean is the plain mean. -/
theorem avoidMean_empty (H : Hypergraph V E) (F : Set V → ℝ) (a : V) :
    avoidMean H (∅ : Set V) F a
      = ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) := by
  simp only [avoidMean, avoidIntegral, avoidEvent_empty, Measure.restrict_univ, probReal_univ,
    div_one]

/-- Every relay is active when there is nothing to avoid. -/
theorem avoidEvent_empty_pos (H : Hypergraph V E) (a : V) :
    0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) (∅ : Set V)) := by
  rw [avoidEvent_empty, probReal_univ]
  norm_num

/-- **The ranked surplus equals the pattern-free minimum form**, no avoided set: on the first-in-rank
pattern of `a` the relay `a` minimises the mean over the relays joined to `x`, so the ranked surplus
does not depend on the compatible injective rank.  The bond `CSH.surplus_eq_minForm`. -/
theorem surplus_eq_minForm (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (x : V)
    (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' →
      (∫ ω, F (hyperClusterSet H ω ({b} : Set V)) ∂(prodBernoulli H.prob)) ≤
        ∫ ω, F (hyperClusterSet H ω ({b'} : Set V)) ∂(prodBernoulli H.prob)) :
    surplus H T r F x =
      ∫ ω in ⋃ a ∈ T, hyperConn H x a,
        (F (hyperClusterSet H ω ({x} : Set V)) -
          (if h : (T.filter fun b => ω ∈ hyperConn H x b).Nonempty then
            (T.filter fun b => ω ∈ hyperConn H x b).inf' h
              (fun b => ∫ η, F (hyperClusterSet H η ({b} : Set V)) ∂(prodBernoulli H.prob))
          else 0)) ∂(prodBernoulli H.prob) := by
  have h := avoidSurplus_eq_minForm H (∅ : Set V) T r F x hr
    (by simpa only [avoidMean_empty] using hcompat)
  rw [avoidSurplus_empty] at h
  rw [h]
  simp only [avoidMean_empty, avoidEvent_empty, Set.univ_inter]

/-- **The surplus transfer at arbitrary label probabilities from the transfer at strictly interior
ones**, no avoided set.  The bond `CSH.surplusTransfer_of_nondegenerate`: the ranked surplus is not
a function of the probability vector alone, because a rank compatible at one vector need not be
compatible at a neighbouring one, whereas the minimum form is, and it is continuous. -/
theorem surplusTransfer_of_nondegenerate (H : Hypergraph V E) (T : Finset V) (o v : V)
    (F : Set V → ℝ)
    (h : ∀ p : E → unitInterval, (∀ e, 0 < p e ∧ p e < 1) → ∀ r : V → ℕ, Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli p)) ≤
          ∫ ω, F (hyperClusterSet H ω ({a'} : Set V)) ∂(prodBernoulli p)) →
      (prodBernoulli p).real (avoidEvent H ({v} : Set V) (↑T : Set V) ∩ hyperConn H o v) *
          surplus (withProb H p) T r F v ≤
        (prodBernoulli p).real (avoidEvent H ({v} : Set V) (↑T : Set V)) *
          surplus (withProb H p) T r F o)
    (r : V → ℕ) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
        ∫ ω, F (hyperClusterSet H ω ({a'} : Set V)) ∂(prodBernoulli H.prob)) :
    (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V) ∩ hyperConn H o v) *
        surplus H T r F v ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V)) * surplus H T r F o := by
  have hmean : ∀ (p : E → unitInterval) (a : V),
      avoidMean (withProb H p) (∅ : Set V) F a
        = ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli p) := by
    intro p a
    rw [avoidMean_empty]
    simp only [withProb_prob, hyperClusterSet_withProb]
  have key := avoidSurplusTransfer_of_nondegenerate H (∅ : Set V) T o v F
    (fun p hp r' hr' hc' => by
      have := h p hp r' hr' (by simpa only [hmean] using hc')
      simpa only [avoidSurplus_empty, Set.empty_union, avoidEvent_withProb] using this)
    (fun a _ => avoidEvent_empty_pos H a)
    r hr (by simpa only [avoidMean_empty] using hcompat)
  simpa only [avoidSurplus_empty, Set.empty_union] using key

/-- **`HyperAdditiveGluing` from the surplus transfer at strictly interior label probabilities
only.**  The peeling proof of (S5) divides by probabilities of conditioning events, so it gives the
transfer only at non-degenerate probabilities; `surplusTransfer_of_nondegenerate` closes over the
degenerate ones, and `AGOne.additiveGluing_of_surplusTransfer` composes
(S5) ⟹ (GEN) ⟹ (AG-loc) ⟹ additive gluing.  The bond
`CSH.additiveGluing_of_surplusTransfer_nondegenerate`. -/
theorem hyperAdditiveGluing_of_surplusTransfer_nondegenerate
    (hST : ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L) (p : L → unitInterval),
      (∀ e, 0 < p e ∧ p e < 1) →
      ∀ (T : Finset W) (o v : W) (F : Set W → ℝ) (r : W → ℕ),
      v ∉ T → (∀ S S' : Set W, S ⊆ S' → F S ≤ F S') → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        (∫ ω, F (hyperClusterSet H ω ({a} : Set W)) ∂(prodBernoulli p)) ≤
          ∫ ω, F (hyperClusterSet H ω ({a'} : Set W)) ∂(prodBernoulli p)) →
      (prodBernoulli p).real (avoidEvent H ({v} : Set W) (↑T : Set W) ∩ hyperConn H o v) *
          surplus (withProb H p) T r F v ≤
        (prodBernoulli p).real (avoidEvent H ({v} : Set W) (↑T : Set W)) *
          surplus (withProb H p) T r F o) :
    HyperAdditiveGluing := by
  refine hyperAdditiveGluing_of_surplusTransfer fun W L _ _ H F hF T u v r hvT hr hc => ?_
  have := surplusTransfer_of_nondegenerate H T u v F
    (fun p hp r' hr' hc' => hST W L H p hp T u v F r' hvT hF hr' hc') r hr
    (by simpa only [condMeanY_empty] using hc)
  simpa only [Set.empty_union, surplusY_empty] using this

end Closure

/-! ## Section 3.  The capstone (`Continuity/OfGluing.lean`)

The bond file turns near-one gluing into `θ_{ℤ^d}(p_c) = 0` for every `d ≥ 2`, through Kozma and
Nitzan's Theorem 6 and the Barsky–Grimmett–Newman half-space theorem.  Its hyperedge form is the
same statement fed by the hyperedge gluing inequality:
`AGOne.additiveGluing_of_hyperAdditiveGluing` produces the bond `AdditiveGluing` from
`HyperAdditiveGluing`, and `percolationContinuity_of_additiveGluing` finishes.  Nothing about the
lattice changes, since the lattice enters only through the bond statement. -/

section Capstone

/-- **Hyperedge additive gluing implies `θ_{ℤ^d}(p_c(ℤ^d)) = 0` for every `d ≥ 2`.** -/
theorem percolationContinuity_of_hyperAdditiveGluing (h : HyperAdditiveGluing) (d : ℕ)
    (hd : 2 ≤ d) : PercolationContinuity d :=
  percolationContinuity_of_additiveGluing (additiveGluing_of_hyperAdditiveGluing h) d hd

/-- **Hyperedge near-one gluing implies `θ_{ℤ^d}(p_c(ℤ^d)) = 0` for every `d ≥ 2`**, through
`AGOne.nearOneGluing_of_hyperNearOneGluing` and Kozma–Nitzan's Theorem 6. -/
theorem percolationContinuity_of_hyperNearOneGluing (h : HyperNearOneGluing) (d : ℕ)
    (hd : 2 ≤ d) : PercolationContinuity d :=
  percolationContinuity_of_nearOneGluing (nearOneGluing_of_hyperNearOneGluing h) d hd

end Capstone

/-! ## Section 4.  The fresh mean in the induced model (`CovTau/A2EdgeDefs.lean`)

The bond `CovTau.tfE w U x g = Σ_ω weight(ω)·g(C_x^{G[U]})` is the mean of a functional of the open
EDGE cluster of `x` in the model induced on `U`.  Its hyperedge form has to read a functional of the
open LABEL cluster: `KN/HyperCSHTwoB.lean` proves in `exists_rTrace_law_not_product` that the law of
the vertex record of a set of labels has no product law, so a quantity indexed by vertex sets is not
interchangeable with one indexed by label sets.  `rLabels` is the label cluster, and `tfE` the mean
of a functional of it. -/

section Fresh

variable [Fintype E]

/-- The open labels of the model induced on `U` incident to the cluster of `x`: the hyperedge form
of the bond open edge cluster `BHK2006.rC U x ω`. -/
def rLabels (H : Hypergraph V E) (U : Finset V) (x : V) (ω : Set E) : Set E :=
  ω ∩ labelsIn H U ∩ labelsMeeting H (rCluster H U ({x} : Set V) ω)

/-- Membership in the label cluster, unfolded. -/
theorem mem_rLabels {H : Hypergraph V E} {U : Finset V} {x : V} {ω : Set E} {e : E} :
    e ∈ rLabels H U x ω ↔ e ∈ ω ∧ (∀ v ∈ H.incidence e, v ∈ U) ∧
      ∃ v ∈ H.incidence e, (openHyperGraph H (ω ∩ labelsIn H U)).Reachable x v := by
  simp only [rLabels, Set.mem_inter_iff, mem_labelsIn, mem_labelsMeeting,
    Set.not_disjoint_iff, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact ⟨fun ⟨v, hv, hvc⟩ => ⟨v, hv, mem_rCluster_singleton.1 hvc⟩,
    fun ⟨v, hv, hr⟩ => ⟨v, hv, mem_rCluster_singleton.2 hr⟩⟩

/-- An open label of the induced model incident to `x` belongs to the label cluster of `x`. -/
theorem mem_rLabels_of_mem_incidence {H : Hypergraph V E} {U : Finset V} {x : V} {ω : Set E}
    {e : E} (he : e ∈ ω) (heU : ∀ v ∈ H.incidence e, v ∈ U) (hx : x ∈ H.incidence e) :
    e ∈ rLabels H U x ω :=
  mem_rLabels.2 ⟨he, heU, x, hx, SimpleGraph.Reachable.refl x⟩

/-- **`t = E_{H[U]} g(C_x)`**: the mean of a functional of the label cluster of `x` in the model
induced on `U`.  The bond `CovTau.tfE`. -/
def tfE (H : Hypergraph V E) (w : E → ℝ) (U : Finset V) (x : V) (g : Set E → ℝ) : ℝ :=
  ∑ ω : Set E, weight w ω * g (rLabels H U x ω)

/-- The fresh mean of a constant is that constant, when the weights are normalised. -/
theorem tfE_const (H : Hypergraph V E) {w : E → ℝ} (hm : ∑ ω : Set E, weight w ω = 1)
    (U : Finset V) (x : V) (c : ℝ) : tfE H w U x (fun _ => c) = c := by
  simp only [tfE, ← Finset.sum_mul, hm, one_mul]

/-- The fresh mean against the product measure is an integral. -/
theorem tfE_eq_integral (H : Hypergraph V E) (p : E → unitInterval) (U : Finset V) (x : V)
    (g : Set E → ℝ) :
    tfE H (fun e => (p e : ℝ)) U x g = ∫ ω, g (rLabels H U x ω) ∂(prodBernoulli p) := by
  rw [Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  rfl

end Fresh

/-! ## Section 5.  The cluster of a source set in the induced model (`CovTau/A2Anti.lean`)

The locality of the event that the cluster of a source SET has a prescribed value, the domain Markov
property in the finite weight-sum framework, and the effect of adding one source vertex.  The bond
proofs go through unchanged in structure; the one place where a hyperedge argument is needed is
`reach_rest_iff`, where the label crossed by a step of the walk has to be shown to lie inside the
world `U ∖ C_N`.  For an edge that is the statement that its two endpoints avoid `C_N`; for a label
it is the statement that EVERY incident vertex does, and it holds because a label open in the
induced model and incident both to a vertex of `C_N` and to a vertex outside it would make the two
adjacent, putting the outside vertex into `C_N`. -/

section SetCluster

/-- An open walk inside `U` starting in a set `W` closed under the open labels of `ω` inside `U`
stays in `W`.  The bond `CovTau.reach_stays`. -/
theorem reach_stays {H : Hypergraph V E} {U : Finset V} {ω : Set E} {W : Set V} {a b : V}
    (hW : ∀ p q : V, p ∈ W → (openHyperGraph H (ω ∩ labelsIn H U)).Adj p q → q ∈ W)
    (h : (openHyperGraph H (ω ∩ labelsIn H U)).Reachable a b) (ha : a ∈ W) : b ∈ W := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hW _ _ ih hbc

/-- **Locality of `{C_N = W}`**: if the cluster of `N` in the model induced on `U` is `W` in `ω`,
and `ω'` agrees with `ω` on every label meeting `W`, then it is `W` in `ω'` too.  The bond
`CovTau.sC_eq_of_agree`. -/
theorem rCluster_eq_of_agree {H : Hypergraph V E} {U : Finset V} {N : Set V} {ω ω' : Set E}
    {W : Set V} (hW : rCluster H U N ω = W)
    (hag : ∀ e : E, ¬ Disjoint (H.incidence e) W → (e ∈ ω ↔ e ∈ ω')) :
    rCluster H U N ω' = W := by
  have hcl : ∀ ξ : Set E, (∀ e : E, ¬ Disjoint (H.incidence e) W → (e ∈ ξ ↔ e ∈ ω)) →
      ∀ p q : V, p ∈ W → (openHyperGraph H (ξ ∩ labelsIn H U)).Adj p q → q ∈ W := by
    intro ξ hξ p q hp hpq
    obtain ⟨hne, e, ⟨heξ, heU⟩, hpe, hqe⟩ := (openHyperGraph_adj_iff H _ p q).1 hpq
    have hmeet : ¬ Disjoint (H.incidence e) W := Set.not_disjoint_iff.2 ⟨p, hpe, hp⟩
    have heω : e ∈ ω := (hξ e hmeet).1 heξ
    rw [← hW] at hp ⊢
    exact hyperClusterSet_mem_of_adj H _ N hp
      ((openHyperGraph_adj_iff H _ p q).2 ⟨hne, e, ⟨heω, heU⟩, hpe, hqe⟩)
  have hcl' := hcl ω' fun e he => (hag e he).symm
  have hclω := hcl ω fun _ _ => Iff.rfl
  have hNW : N ⊆ W := by rw [← hW]; exact subset_rCluster H U N ω
  ext u
  constructor
  · rintro ⟨z, hz, hr⟩
    exact reach_stays hcl' hr (hNW hz)
  · intro hu
    rw [← hW] at hu
    obtain ⟨z, hz, hr⟩ := hu
    refine ⟨z, hz, ?_⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr ⊢
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      refine ih.tail ?_
      obtain ⟨hne, e, ⟨heω, heU⟩, hbe, hce⟩ := (openHyperGraph_adj_iff H _ b c).1 hbc
      have hb : b ∈ W :=
        reach_stays hclω ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hab) (hNW hz)
      have hmeet : ¬ Disjoint (H.incidence e) W := Set.not_disjoint_iff.2 ⟨b, hbe, hb⟩
      exact (openHyperGraph_adj_iff H _ b c).2 ⟨hne, e, ⟨(hag e hmeet).1 heω, heU⟩, hbe, hce⟩

/-- `{C_N = W}` is decided by the labels meeting `W`.  The bond `CovTau.sC_inter_meet_eq_iff`. -/
theorem rCluster_inter_meeting_eq_iff (H : Hypergraph V E) (U : Finset V) (N : Set V) (ω : Set E)
    (W : Set V) :
    rCluster H U N (ω ∩ labelsMeeting H W) = W ↔ rCluster H U N ω = W :=
  ⟨fun h => rCluster_eq_of_agree h fun _ he => ⟨fun h' => h'.1, fun h' => ⟨h', he⟩⟩,
    fun h => rCluster_eq_of_agree h fun _ he => ⟨fun h' => ⟨h', he⟩, fun h' => h'.1⟩⟩

/-- The labels lying inside `U ∖ W` do not meet `W`.  For a hyperedge this asks that EVERY incident
vertex lie outside `W`, which is exactly what `labelsIn` supplies.  The bond
`CovTau.diff_meet_inter_edgesIn`. -/
theorem sdiff_meeting_inter_labelsIn (H : Hypergraph V E) (U : Finset V) (W : Set V) (ω : Set E) :
    (ω \ labelsMeeting H W) ∩ labelsIn H (U.filter fun u => u ∉ W) =
      ω ∩ labelsIn H (U.filter fun u => u ∉ W) := by
  ext e
  constructor
  · rintro ⟨⟨hω, -⟩, hU⟩; exact ⟨hω, hU⟩
  · rintro ⟨hω, hU⟩
    refine ⟨⟨hω, ?_⟩, hU⟩
    rw [mem_labelsMeeting, not_not]
    exact Set.disjoint_left.2 fun v hv => (Finset.mem_filter.1 (hU v hv)).2

/-- `rest H U N ω` is `U` filtered by `∉ C_N(ω)`.  The bond `CovTau.rest_eq_filter`. -/
theorem rest_eq_filter (H : Hypergraph V E) (U : Finset V) (N : Set V) (ω : Set E) :
    rest H U N ω = U.filter fun u => u ∉ rCluster H U N ω := rfl

variable [Fintype V] [Fintype E]

/-- **Conditioning on the value of the cluster of a source set** (the domain Markov property in the
finite weight-sum framework): for every kernel `Φ`,
`Σ_ω weight(ω)·Φ(C_N(ω), ω ∩ E(U ∖ C_N(ω))) = Σ_ω weight(ω)·Σ_η weight(η)·Φ(C_N(ω), η ∩ E(U ∖ C_N(ω)))`.
Given `C_N = W`, the labels lying inside `U ∖ W` are fresh.  The bond `CovTau.sum_cond_sC`. -/
theorem sum_cond_rCluster (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ ω : Set E, weight w ω = 1) (U : Finset V) (N : Set V) (Φ : Set V → Set E → ℝ) :
    ∑ ω : Set E, weight w ω * Φ (rCluster H U N ω) (ω ∩ labelsIn H (rest H U N ω)) =
      ∑ ω : Set E, weight w ω *
        ∑ η : Set E, weight w η * Φ (rCluster H U N ω) (η ∩ labelsIn H (rest H U N ω)) := by
  have key : ∀ W : Set V,
      ∑ ω : Set E, (if rCluster H U N ω = W then
          weight w ω * Φ W (ω ∩ labelsIn H (U.filter fun u => u ∉ W)) else 0) =
      ∑ ω : Set E, (if rCluster H U N ω = W then
          weight w ω * ∑ η : Set E, weight w η *
            Φ W (η ∩ labelsIn H (U.filter fun u => u ∉ W)) else 0) := by
    intro W
    set A : Set E := labelsMeeting H W with hA
    set Ψ : Set E → Set E → ℝ := fun ζ η =>
      if rCluster H U N ζ = W then Φ W (η ∩ labelsIn H (U.filter fun u => u ∉ W)) else 0 with hΨ
    have h1 : ∀ ω : Set E, (if rCluster H U N ω = W then
        weight w ω * Φ W (ω ∩ labelsIn H (U.filter fun u => u ∉ W)) else 0)
        = weight w ω * Ψ (ω ∩ A) (ω \ A) := by
      intro ω
      simp only [hΨ, hA, rCluster_inter_meeting_eq_iff, sdiff_meeting_inter_labelsIn]
      split_ifs <;> simp
    have h2 : ∀ ω ω' : Set E, Ψ (ω ∩ A) (ω' \ A) =
        if rCluster H U N ω = W then
          Φ W (ω' ∩ labelsIn H (U.filter fun u => u ∉ W)) else 0 := by
      intro ω ω'
      simp only [hΨ, hA, rCluster_inter_meeting_eq_iff, sdiff_meeting_inter_labelsIn]
    calc ∑ ω : Set E, (if rCluster H U N ω = W then
            weight w ω * Φ W (ω ∩ labelsIn H (U.filter fun u => u ∉ W)) else 0)
        = (∑ ω : Set E, weight w ω) * ∑ ω : Set E, weight w ω * Ψ (ω ∩ A) (ω \ A) := by
          rw [hm, one_mul]; simp_rw [h1]
      _ = ∑ ω : Set E, weight w ω * ∑ ω' : Set E, weight w ω' * Ψ (ω ∩ A) (ω' \ A) :=
          blockFubini w A Ψ
      _ = _ := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases hc : rCluster H U N ω = W <;> simp [h2, hc]
  have lhs : ∑ ω : Set E, weight w ω * Φ (rCluster H U N ω) (ω ∩ labelsIn H (rest H U N ω)) =
      ∑ ω : Set E, ∑ W : Set V, (if rCluster H U N ω = W then
        weight w ω * Φ W (ω ∩ labelsIn H (U.filter fun u => u ∉ W)) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (rCluster H U N ω)]
    simp [rest_eq_filter]
  have rhs : ∑ ω : Set E, weight w ω *
        ∑ η : Set E, weight w η * Φ (rCluster H U N ω) (η ∩ labelsIn H (rest H U N ω)) =
      ∑ ω : Set E, ∑ W : Set V, (if rCluster H U N ω = W then
        weight w ω * ∑ η : Set E, weight w η *
          Φ W (η ∩ labelsIn H (U.filter fun u => u ∉ W)) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (rCluster H U N ω)]
    simp [rest_eq_filter]
  rw [lhs, rhs, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun W _ => key W

end SetCluster

/-! ### Adding one source vertex -/

section AddSource

/-- Clusters computed from `ω ∩ E(U')` are the clusters of the model induced on `U'`. -/
theorem rCluster_inter_labelsIn (H : Hypergraph V E) (U' : Finset V) (M : Set V) (ω : Set E) :
    rCluster H U' M (ω ∩ labelsIn H U') = rCluster H U' M ω := by
  simp only [rCluster, Set.inter_assoc, Set.inter_self]

/-- Worlds computed from `ω ∩ E(U')` are the worlds of the model induced on `U'`. -/
theorem rest_inter_labelsIn (H : Hypergraph V E) (U' : Finset V) (M : Set V) (ω : Set E) :
    rest H U' M (ω ∩ labelsIn H U') = rest H U' M ω := by
  ext u; rw [mem_rest, mem_rest, rCluster_inter_labelsIn]

/-- Avoidance events computed from `ω ∩ E(U')`. -/
theorem mem_rAvoid_inter_labelsIn (H : Hypergraph V E) (U' : Finset V) (S M : Set V) (ω : Set E) :
    ω ∩ labelsIn H U' ∈ rAvoid H U' S M ↔ ω ∈ rAvoid H U' S M := by
  simp only [mem_rAvoid, rCluster_inter_labelsIn]

/-- If `u ∈ C_N` then `C_{N ∪ {u}} = C_N`.  The bond `CovTau.sC_insert_of_mem`. -/
theorem rCluster_insert_of_mem {H : Hypergraph V E} {U : Finset V} {N : Set V} {ω : Set E} {u : V}
    (hu : u ∈ rCluster H U N ω) :
    rCluster H U (insert u N) ω = rCluster H U N ω := by
  refine Set.Subset.antisymm ?_ (rCluster_mono_source H U (Set.subset_insert u N) ω)
  rintro a ⟨z, hz, hr⟩
  rcases hz with rfl | hz
  · obtain ⟨z', hz', hr'⟩ := hu
    exact ⟨z', hz', hr'.trans hr⟩
  · exact ⟨z, hz, hr⟩

/-- **A walk avoiding the cluster of `N` is a walk of the world `U ∖ C_N`**: if `a ∉ C_N(ω)` then
`a ↔ b` in the model on `U` iff `a ↔ b` in the model on `U ∖ C_N(ω)`.  The bond
`CovTau.reach_rest_iff`.  For a hyperedge the step needs more than the bond argument: the label
crossed must lie INSIDE `U ∖ C_N`, that is every one of its vertices must avoid `C_N`, and a vertex
of the label lying in `C_N` would be adjacent to the walk's current vertex and put it in `C_N`
too. -/
theorem reach_rest_iff {H : Hypergraph V E} {U : Finset V} {N : Set V} {ω : Set E} {a b : V}
    (ha : a ∉ rCluster H U N ω) :
    (openHyperGraph H (ω ∩ labelsIn H (rest H U N ω))).Reachable a b ↔
      (openHyperGraph H (ω ∩ labelsIn H U)).Reachable a b := by
  constructor
  · exact fun h => h.mono (openHyperGraph_le_of_subset H
      (Set.inter_subset_inter_right _ (labelsIn_mono H (rest_subset H U N ω))))
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      obtain ⟨hne, e, ⟨heω, heU⟩, hbe, hce⟩ := (openHyperGraph_adj_iff H _ b c).1 hbc
      have hb : b ∉ rCluster H U N ω := fun ⟨z, hz, hr⟩ =>
        ha ⟨z, hz, hr.trans ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hab).symm⟩
      have heU' : e ∈ labelsIn H (rest H U N ω) := by
        intro v hv
        refine mem_rest.2 ⟨heU v hv, fun hvC => hb ?_⟩
        by_cases hvb : v = b
        · exact hvb ▸ hvC
        · exact hyperClusterSet_mem_of_adj H _ N hvC
            ((openHyperGraph_adj_iff H _ v b).2 ⟨hvb, e, ⟨heω, heU⟩, hv, hbe⟩)
      exact ih.tail ((openHyperGraph_adj_iff H _ b c).2 ⟨hne, e, ⟨heω, heU'⟩, hbe, hce⟩)

/-- If `u ∉ C_N` then `C_{N ∪ {u}} = C_N ∪ C^{U ∖ C_N}_u`.  The bond
`CovTau.sC_insert_of_not_mem`. -/
theorem rCluster_insert_of_not_mem {H : Hypergraph V E} {U : Finset V} {N : Set V} {ω : Set E}
    {u : V} (hu : u ∉ rCluster H U N ω) :
    rCluster H U (insert u N) ω
      = rCluster H U N ω ∪ rCluster H (rest H U N ω) ({u} : Set V) ω := by
  ext a
  simp only [Set.mem_union, mem_rCluster_singleton, reach_rest_iff hu]
  constructor
  · rintro ⟨z, hz, hr⟩
    rcases hz with rfl | hz
    · exact Or.inr hr
    · exact Or.inl ⟨z, hz, hr⟩
  · rintro (⟨z, hz, hr⟩ | hr)
    · exact ⟨z, Set.mem_insert_of_mem u hz, hr⟩
    · exact ⟨u, Set.mem_insert u N, hr⟩

/-- If `u ∉ C_N` then `U ∖ C_{N ∪ {u}} = (U ∖ C_N) ∖ C^{U ∖ C_N}_u`.  The bond
`CovTau.rest_insert_of_not_mem`. -/
theorem rest_insert_of_not_mem {H : Hypergraph V E} {U : Finset V} {N : Set V} {ω : Set E} {u : V}
    (hu : u ∉ rCluster H U N ω) :
    rest H U (insert u N) ω = rest H (rest H U N ω) ({u} : Set V) ω := by
  ext a
  rw [mem_rest, mem_rest, mem_rest, rCluster_insert_of_not_mem hu, Set.mem_union]
  tauto

end AddSource

/-! ## Section 6.  The Markov property at the cluster explored off a fixed label set, and Lemma
`Φ`(a) (`CSH/PhiMarkov.lean`)

`KN/HyperCSHTwoB.lean` proves `set_sum_cond_sdiff`, the conditioning identity for the cluster of a
vertex set explored in the whole configuration.  The peeling step needs it for the cluster explored
in `ω ∖ B` for a fixed label set `B`, the world still being the full configuration off the cut, and
that is `set_sum_cond_sdiff_off` below; `B = ∅` recovers the imported statement.  Lemma `Φ`(a) is
its consequence: the first term of the integrand of `KN/HyperCSHDefs.lean` is, on average, the world
mean of `g(C_s)` given the cluster of `X`. -/

section PhiMarkov

variable [Fintype V] [Fintype E]

/-- The total weight is one. -/
theorem sum_weight_prob (H : Hypergraph V E) :
    ∑ ω : Set E, weight (fun e => (H.prob e : ℝ)) ω = 1 := by
  have h := Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum H.prob
    (fun _ : Set E => (1 : ℝ))
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  exact h.symm

/-- **Conditioning on the cluster of `X` explored off a fixed label set `B`.**  The event
`{C_X(ω ∖ B) = W}` reads only the labels meeting `W`, and the configuration off those labels is
fresh, so for every kernel `K`
`Σ_ω w(ω)·K(C_X(ω ∖ B), ω ∖ cut) = Σ_ω w(ω)·Σ_η w(η)·K(C_X(ω ∖ B), η ∖ cut)`.
The bond `CSH.set_sum_cond_sdiff_off`. -/
theorem set_sum_cond_sdiff_off (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ ω : Set E, weight w ω = 1) (X : Set V) (B : Set E) (K : Set V → Set E → ℝ) :
    ∑ ω : Set E, weight w ω *
        K (hyperClusterSet H (ω \ B) X) (ω \ cut H X (ω \ B)) =
      ∑ ω : Set E, weight w ω * ∑ η : Set E, weight w η *
        K (hyperClusterSet H (ω \ B) X) (η \ cut H X (ω \ B)) := by
  have hsd : ∀ (A ω : Set E), (ω \ A) \ A = ω \ A := fun A ω => by
    rw [Set.sdiff_sdiff, Set.union_self]
  have hdet : ∀ (W : Set V) (ω : Set E),
      hyperClusterSet H ((ω ∩ labelsMeeting H W) \ B) X = W
        ↔ hyperClusterSet H (ω \ B) X = W := by
    intro W ω
    have hrw : (ω ∩ labelsMeeting H W) \ B = (ω \ B) ∩ labelsMeeting H W := by
      ext e; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
    rw [hrw]
    exact (determinedBy_iff _ _).1 (determinedBy_clusterEvent H X W)
      ((ω \ B) ∩ labelsMeeting H W) (ω \ B) (by rw [Set.inter_assoc, Set.inter_self])
  have key : ∀ W : Set V,
      ∑ ω : Set E, (if hyperClusterSet H (ω \ B) X = W then
          weight w ω * K W (ω \ labelsMeeting H W) else 0) =
      ∑ ω : Set E, (if hyperClusterSet H (ω \ B) X = W then
          weight w ω * ∑ η : Set E, weight w η * K W (η \ labelsMeeting H W) else 0) := by
    intro W
    set A : Set E := labelsMeeting H W with hA
    set Φ : Set E → Set E → ℝ := fun ζ η =>
      if hyperClusterSet H (ζ \ B) X = W then K W (η \ A) else 0 with hΦ
    have h1 : ∀ ω : Set E,
        (if hyperClusterSet H (ω \ B) X = W then weight w ω * K W (ω \ A) else 0)
          = weight w ω * Φ (ω ∩ A) (ω \ A) := by
      intro ω
      simp only [hΦ, hA, hdet]
      split_ifs with hW
      · rw [← hA, hsd]
      · rw [mul_zero]
    have h2 : ∀ ω : Set E, weight w ω * ∑ ω' : Set E, weight w ω' * Φ (ω ∩ A) (ω' \ A) =
        (if hyperClusterSet H (ω \ B) X = W then
          weight w ω * ∑ η : Set E, weight w η * K W (η \ A) else 0) := by
      intro ω
      simp only [hΦ, hA, hdet]
      split_ifs with hW
      · rw [← hA]
        refine congrArg (weight w ω * ·) (Finset.sum_congr rfl fun η _ => ?_)
        rw [hsd]
      · simp
    calc ∑ ω : Set E, (if hyperClusterSet H (ω \ B) X = W then
            weight w ω * K W (ω \ A) else 0)
        = (∑ ω : Set E, weight w ω) * ∑ ω : Set E, weight w ω * Φ (ω ∩ A) (ω \ A) := by
          rw [hm, one_mul]; exact Finset.sum_congr rfl fun ω _ => h1 ω
      _ = ∑ ω : Set E, weight w ω * ∑ ω' : Set E, weight w ω' * Φ (ω ∩ A) (ω' \ A) :=
          blockFubini w A Φ
      _ = _ := Finset.sum_congr rfl fun ω _ => h2 ω
  calc ∑ ω : Set E, weight w ω * K (hyperClusterSet H (ω \ B) X) (ω \ cut H X (ω \ B))
      = ∑ ω : Set E, ∑ W : Set V, (if hyperClusterSet H (ω \ B) X = W then
          weight w ω * K W (ω \ labelsMeeting H W) else 0) :=
        Finset.sum_congr rfl fun ω _ =>
          (Fintype.sum_ite_eq (hyperClusterSet H (ω \ B) X)
            fun W => weight w ω * K W (ω \ labelsMeeting H W)).symm
    _ = ∑ W : Set V, ∑ ω : Set E, (if hyperClusterSet H (ω \ B) X = W then
          weight w ω * K W (ω \ labelsMeeting H W) else 0) := Finset.sum_comm
    _ = ∑ W : Set V, ∑ ω : Set E, (if hyperClusterSet H (ω \ B) X = W then
          weight w ω * ∑ η : Set E, weight w η * K W (η \ labelsMeeting H W) else 0) :=
        Finset.sum_congr rfl fun W _ => key W
    _ = ∑ ω : Set E, ∑ W : Set V, (if hyperClusterSet H (ω \ B) X = W then
          weight w ω * ∑ η : Set E, weight w η * K W (η \ labelsMeeting H W) else 0) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun ω _ =>
        Fintype.sum_ite_eq (hyperClusterSet H (ω \ B) X)
          fun W => weight w ω * ∑ η : Set E, weight w η * K W (η \ labelsMeeting H W)

/-- `set_sum_cond_sdiff` of `KN/HyperCSHTwoB.lean` is the case `B = ∅`. -/
theorem set_sum_cond_sdiff_off_empty (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ ω : Set E, weight w ω = 1) (X : Set V) (K : Set V → Set E → ℝ) :
    ∑ ω : Set E, weight w ω * K (hyperClusterSet H ω X) (ω \ cut H X ω) =
      ∑ ω : Set E, weight w ω * ∑ η : Set E, weight w η * K (hyperClusterSet H ω X) (η \ cut H X ω)
    := by
  simpa only [Set.sdiff_empty] using set_sum_cond_sdiff_off H w hm X (∅ : Set E) K

/-- **The world mean at the sum level**: `ḡ(ζ) = Σ_η w(η)·φ(η ∖ cut_X(ζ))`, the mean of `φ` after
deleting the labels meeting the cluster of `X` in `ζ`.  The bond `CSH.wmeanOff`. -/
def wmeanOff (H : Hypergraph V E) (w : E → ℝ) (X : Set V) (φ : Set E → ℝ) (ζ : Set E) : ℝ :=
  ∑ η : Set E, weight w η * φ (η \ cut H X ζ)

/-- The world mean at the sum level is `CTBase.delE` at the cut, hence the `worldMean` of
`KN/HyperCSHTwoA.lean`, when the weight comes from the model's own probabilities. -/
theorem wmeanOff_eq_worldMean (H : Hypergraph V E) (s : V) (g : Set V → ℝ) (X : Set V)
    (ζ : Set E) :
    wmeanOff H (fun e => (H.prob e : ℝ)) X
        (fun β => g (hyperClusterSet H β ({s} : Set V))) ζ
      = CSHTwoA.worldMean H s g (hyperClusterSet H ζ X) := by
  rw [worldMean_eq_delE H s g X ζ, delE, wmeanOff,
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]

/-- **Lemma `Φ`(a)**, sum level: the first term of the `Φ`-integrand is, on average, the world mean
of `g(C_s)` given the cluster of `X`, so
`Σ_η w(η)·I_K(η) = Σ_η w(η)·1{s ↮ X off K}·( ḡ(η off K) − g(C_s(η off K)) )`.  The bond
`CSH.sum_phiIntegrand_eq`.  The bond file has to say "`s ∉ X ∪ V(C_X)`" because its avoidance event
is stated through the edge cluster; here `ind_avoidEv_eq_ite` of `KN/HyperCSHTwoB.lean` reads it off
the vertex cluster directly. -/
theorem sum_phiIntegrand_eq (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ ω : Set E, weight w ω = 1) (s : V) (X K : Set V) (g : Set V → ℝ) :
    ∑ η : Set E, weight w η * CSHDefs.phiIntegrand H s X K g η =
      ∑ η : Set E, weight w η * (ind (avoidEv H s X) (η \ labelsMeeting H K) *
        (wmeanOff H w X (fun β => g (hyperClusterSet H β ({s} : Set V)))
            (η \ labelsMeeting H K) -
          g (hyperClusterSet H (η \ labelsMeeting H K) ({s} : Set V)))) := by
  have hI : ∀ η : Set E, CSHDefs.phiIntegrand H s X K g η
      = ind (avoidEv H s X) (η \ labelsMeeting H K) *
        (g (hyperClusterSet H (η \ cut H X (η \ labelsMeeting H K)) ({s} : Set V)) -
          g (hyperClusterSet H (η \ labelsMeeting H K) ({s} : Set V))) := by
    intro η
    unfold CSHDefs.phiIntegrand
    rw [avoidEv_eq]
    by_cases h : ∀ x ∈ X, ¬ (openHyperGraph H (η \ labelsMeeting H K)).Reachable s x
    · rw [if_pos h, ind_of_mem
        ((mem_avoidEvent_singleton H s X (η \ labelsMeeting H K)).2 h), one_mul]
    · rw [if_neg h, ind_of_not_mem
        (fun hm' => h ((mem_avoidEvent_singleton H s X (η \ labelsMeeting H K)).1 hm')), zero_mul]
  simp_rw [hI, mul_sub, Finset.sum_sub_distrib]
  congr 1
  set Kk : Set V → Set E → ℝ := fun W β =>
    (if s ∈ W then 0 else 1) * g (hyperClusterSet H β ({s} : Set V)) with hKk
  have key := set_sum_cond_sdiff_off H w hm X (labelsMeeting H K) Kk
  have lhs : ∀ η : Set E, weight w η * (ind (avoidEv H s X) (η \ labelsMeeting H K) *
      g (hyperClusterSet H (η \ cut H X (η \ labelsMeeting H K)) ({s} : Set V)))
      = weight w η * Kk (hyperClusterSet H (η \ labelsMeeting H K) X)
          (η \ cut H X (η \ labelsMeeting H K)) := by
    intro η
    rw [hKk, ind_avoidEv_eq_ite]
  have rhs : ∀ η : Set E, weight w η * (ind (avoidEv H s X) (η \ labelsMeeting H K) *
      wmeanOff H w X (fun β => g (hyperClusterSet H β ({s} : Set V))) (η \ labelsMeeting H K))
      = weight w η * ∑ η' : Set E, weight w η' *
          Kk (hyperClusterSet H (η \ labelsMeeting H K) X)
            (η' \ cut H X (η \ labelsMeeting H K)) := by
    intro η
    rw [ind_avoidEv_eq_ite, wmeanOff, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun η' _ => ?_
    rw [hKk]; ring
  rw [Finset.sum_congr rfl fun η _ => lhs η, key]
  exact (Finset.sum_congr rfl fun η _ => rhs η).symm

/-- **The residual functional `Φ` as an exact finite sum.**  Together with `phiFun_nonneg` and
`phiFun_mono` of `KN/HyperCSHDefs.lean` this is the deletion commutator in the form the peeling step
consumes: `Φ(K)` is the average, over the configurations avoiding `X` off `K`, of the amount by
which the world mean of `g(C_s)` given the cluster of `X` exceeds the value of `g` at the cluster of
`s` itself.  Every term is an explicit finite sum against the product weight; no conditioning event
has to have positive probability, and no expectation is interchanged. -/
theorem phiFun_eq_sum (H : Hypergraph V E) (s : V) (X K : Set V) (g : Set V → ℝ) :
    CSHDefs.phiFun H s X g K
      = ∑ η : Set E, weight (fun e => (H.prob e : ℝ)) η *
          (ind (avoidEv H s X) (η \ labelsMeeting H K) *
            (CSHTwoA.worldMean H s g
                (hyperClusterSet H (η \ labelsMeeting H K) X) -
              g (hyperClusterSet H (η \ labelsMeeting H K) ({s} : Set V)))) := by
  rw [CSHDefs.phiFun, Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum,
    sum_phiIntegrand_eq H (fun e => (H.prob e : ℝ)) (sum_weight_prob H) s X K g]
  exact Finset.sum_congr rfl fun η _ => by
    rw [wmeanOff_eq_worldMean H s g X (η \ labelsMeeting H K)]

end PhiMarkov

/-! ## Section 7.  The dictionary between weight sums and the weighted cube (`CovTau/StarBridge.lean`)

The bond file translates between the finite weight sums of `BHK2006` and the expectations `ED` of
`Percolation/Literature/GladkovZiminKernel.lean`, whose configurations are finsets of coordinates.
Two of its lemmas, the marginal identity `CovTauStarN.ED_inter_eq` and
`CovTauStarN.sum_weight_mul_eq_ED`, are stated for an arbitrary coordinate type and never mention a
graph, so they are imported and used verbatim; the rest of the file is the dictionary between the
model induced on a vertex set and the coordinates `pairsIn U`, and that is what is ported here.

`KN/HyperTreeHK.lean` already carries the half of the dictionary that concerns the whole label set
(`finEvent`, `sum_set_eq_sum_finset`, `wtW_univ_eq_weight`, `integral_eq_sum_wtW`,
`PrW_univ_eq_real`).  What is added is the restriction to `labelsIn H U` and the identification of
the cluster of a source set in the induced model with the set the exploration of
`KN/HyperTreeHK.lean` reaches.  The bond `srcF`, which presents the source set as a `Finset`, has no
counterpart: the hyperedge exploration takes a `Set V` source. -/

section Bridge

variable [DecidableEq E]

/-- The labels lying inside `U`, as a finite set of coordinates.  The bond `CovTauStarN.pairsIn`. -/
def labelsInF [Fintype E] (H : Hypergraph V E) (U : Finset V) : Finset E :=
  Finset.univ.filter fun e => e ∈ labelsIn H U

variable [Fintype E]

@[simp] theorem mem_labelsInF {H : Hypergraph V E} {U : Finset V} {e : E} :
    e ∈ labelsInF H U ↔ e ∈ labelsIn H U := by simp [labelsInF]

theorem coe_inter_labelsInF (H : Hypergraph V E) (U : Finset V) (K : Finset E) :
    (↑(K ∩ labelsInF H U) : Set E) = ↑K ∩ labelsIn H U := by
  ext e; simp [labelsInF]

theorem coe_inter_labelsIn_of_subset {H : Hypergraph V E} {U : Finset V} {K : Finset E}
    (hK : K ⊆ labelsInF H U) : (↑K : Set E) ∩ labelsIn H U = ↑K :=
  Set.inter_eq_left.2 fun _ he => mem_labelsInF.1 (hK (Finset.mem_coe.1 he))

/-- **Restriction**: a weight sum of a functional that reads only the labels inside `U` is an
`ED (labelsInF H U)`-expectation.  The bond `CovTauStarN.sum_weight_restrict`. -/
theorem sum_weight_restrict (H : Hypergraph V E) (w : E → ℝ) (U : Finset V) (g : Set E → ℝ)
    (hg : ∀ ω, g ω = g (ω ∩ labelsIn H U)) :
    ∑ ω : Set E, weight w ω * g ω
      = Percolation.Literature.DecisionTree.ED (labelsInF H U) w (fun K => g ↑K) := by
  rw [CovTauStarN.sum_weight_mul_eq_ED]
  have hfun : (fun K : Finset E => g ↑K)
      = fun K => (fun K' : Finset E => g ↑K') (K ∩ labelsInF H U) := by
    funext K; dsimp only; rw [coe_inter_labelsInF, ← hg]
  have h2 := CovTauStarN.ED_inter_eq (Finset.subset_univ (labelsInF H U)) w
    (fun K' : Finset E => g ↑K')
  rw [← hfun] at h2
  exact h2

/-- The labels inside `U ∖ W` are the labels inside `U` that miss `W`.  The bond
`CovTauStarN.pairsIn_sdiff`; for a hyperedge "misses `W`" is a condition on every incident vertex,
not on two of them. -/
theorem labelsInF_sdiff (H : Hypergraph V E) (U W : Finset V) :
    labelsInF H (U \ W) = (labelsInF H U).filter fun e => Disjoint (H.incidence e) (↑W : Set V) := by
  ext e
  simp only [Finset.mem_filter, mem_labelsInF, mem_labelsIn, Finset.mem_sdiff,
    Set.disjoint_left, Finset.mem_coe]
  exact ⟨fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩,
    fun h v hv => ⟨h.1 v hv, h.2 hv⟩⟩

/-- **The cluster of a source set is the set the exploration reaches**: for `K ⊆ labelsInF H U`,
`rCluster H U N ↑K = reachedBy H N K`.  The bond `CovTauStarN.mem_sC_iff_mem_reached`. -/
theorem mem_rCluster_iff_mem_reachedBy {H : Hypergraph V E} {U : Finset V} {N : Set V}
    {K : Finset E} (hK : K ⊆ labelsInF H U) (u : V) :
    u ∈ rCluster H U N (↑K : Set E) ↔ u ∈ TreeHK.reachedBy H N K := by
  rw [TreeHK.reachedBy_eq]
  show u ∈ hyperClusterSet H ((↑K : Set E) ∩ labelsIn H U) N ↔ _
  rw [coe_inter_labelsIn_of_subset hK]

/-- `rest H U N ↑K = U ∖ reached` for `K ⊆ labelsInF H U`.  The bond
`CovTauStarN.rest_eq_sdiff`. -/
theorem rest_eq_sdiff {H : Hypergraph V E} {U : Finset V} {N : Set V} {K : Finset E}
    (hK : K ⊆ labelsInF H U) (u : V) :
    u ∈ rest H U N (↑K : Set E) ↔ u ∈ U ∧ u ∉ TreeHK.reachedBy H N K := by
  rw [mem_rest, mem_rCluster_iff_mem_reachedBy hK]

/-- `1{x ↮ N in H[U]}` at a configuration inside `U` is `1{x ∉ reached}`.  The bond
`CovTauStarN.ind_rD_eq`. -/
theorem ind_rAvoid_eq {H : Hypergraph V E} {U : Finset V} (x : V) (N : Set V) {K : Finset E}
    (hK : K ⊆ labelsInF H U) :
    ind (rAvoid H U ({x} : Set V) N) (↑K : Set E)
      = ind {L : Finset E | x ∉ TreeHK.reachedBy H N L} K := by
  by_cases h : x ∈ TreeHK.reachedBy H N K
  · rw [ind_of_not_mem (show K ∉ {L : Finset E | x ∉ TreeHK.reachedBy H N L} from fun h' => h' h),
      ind_of_not_mem]
    intro hmem
    exact ((notMem_rCluster_iff_rAvoid H U N (↑K : Set E) x).2 hmem)
      ((mem_rCluster_iff_mem_reachedBy hK x).2 h)
  · rw [ind_of_mem (show K ∈ {L : Finset E | x ∉ TreeHK.reachedBy H N L} from h),
      ind_of_mem ((notMem_rCluster_iff_rAvoid H U N (↑K : Set E) x).1
        (fun hc => h ((mem_rCluster_iff_mem_reachedBy hK x).1 hc)))]

end Bridge

/-! ## Section 8.  Marker dominance with an avoided set: base and degenerate cases
(`HullPort/TABase.lean`)

The functionals `taC`, `taN`, `taNW`, `taB`, `taA`, `tab`, `taa`, `taQ` are those of
`KN/HyperCTBase.lean`, and the one-label step and the section lemmas that consume this file are in
`KN/HyperCSHTwoB.lean`.  What is added is the degenerate positions of the marker and the root, and
the base case of the induction on `X`.

Two things simplify for hyperedges.  The bond boundary condition carries `¬ e.IsDiag`, because a
diagonal pair is never open-adjacent and so has to be excluded from the hypothesis by hand; a label
meeting both `X` and its complement automatically has two distinct vertices, so `noBoundary` below
carries no such clause.  And the bond hypothesis constrains the two endpoints of a pair, whereas
here it constrains every vertex of a label, which is what makes `cut_eq_of_noBoundary` come out as
the labels meeting `X` on the nose. -/

section TABase

variable [Fintype E]

/-- In the empty configuration only trivial connections exist. -/
theorem reachable_empty_iff (H : Hypergraph V E) (a b : V) :
    (openHyperGraph H (∅ : Set E)).Reachable a b ↔ a = b := by
  constructor
  · intro h
    exact (eq_of_reachable_of_isolated H (fun e he => absurd he (Set.notMem_empty e)) h).symm
  · rintro rfl; exact SimpleGraph.Reachable.refl _

/-- The weight of the empty configuration is positive when every label probability is `< 1`. -/
theorem weight_empty_pos {w : E → ℝ} (hw : ∀ e, w e < 1) :
    0 < weight w (∅ : Set E) := by
  unfold Percolation.Literature.BHK2006.weight
  refine Finset.prod_pos fun e _ => ?_
  split_ifs with h
  · exact absurd h (Set.notMem_empty e)
  · linarith [hw e]

/-- `b_X > 0` when `y ∉ X ∪ {s}` and every label probability is `< 1`: the empty configuration
already contributes. -/
theorem tab_pos (H : Hypergraph V E) (hw : ∀ e, (H.prob e : ℝ) < 1) (s y : V) (X : Set V)
    (hy : y ∉ insert s X) : 0 < tab H s y X := by
  set w : E → ℝ := fun e => (H.prob e : ℝ) with hwdef
  have hw0 : ∀ e, 0 ≤ w e := fun e => (H.prob e).2.1
  have hw1 : ∀ e, w e ≤ 1 := fun e => (hw e).le
  have hmem : (∅ : Set E) ∈ avoidEv H y (insert s X) :=
    empty_mem_avoidEvent_singleton H hy
  have hsum : tab H s y X = ∑ ω : Set E, weight w ω * ind (avoidEv H y (insert s X)) ω := by
    rw [tab, ← CTBase.integral_ind_eq_real (prodBernoulli H.prob),
      Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  rw [hsum]
  calc 0 < weight w (∅ : Set E) * ind (avoidEv H y (insert s X)) ∅ := by
        rw [ind_of_mem hmem, mul_one]; exact weight_empty_pos hw
    _ ≤ _ :=
        Finset.single_le_sum (f := fun ω => weight w ω * ind (avoidEv H y (insert s X)) ω)
          (fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)) (Finset.mem_univ _)

/-- Every label incident to a vertex of `X` lies in the cut of `X`. -/
theorem mem_cut_of_mem (H : Hypergraph V E) {X : Set V} {y : V} (hy : y ∈ X) {e : E}
    (hye : y ∈ H.incidence e) (ω : Set E) : e ∈ cut H X ω :=
  Set.not_disjoint_iff.2 ⟨y, hye, mem_hyperClusterSet_self H ω hy⟩

/-- If `y ∈ X` then `c ≡ 0`: in `H − cut_X` the marker `y` is isolated, so `{s ↔ y}` is impossible
for `s ≠ y`. -/
theorem taC_eq_zero_of_mem (H : Hypergraph V E) (s y : V) (hsy : s ≠ y) (X : Set V) (hy : y ∈ X)
    (g : Set V → ℝ) (ω : Set E) : taC H s y X g ω = 0 := by
  have hY : ∀ η : Set E, ind (hyperConn H s y) (η \ cut H X ω) = 0 := by
    intro η
    refine ind_of_not_mem fun h => hsy ?_
    have hiso : ∀ e ∈ η \ cut H X ω, y ∉ H.incidence e :=
      fun e he hye => he.2 (mem_cut_of_mem H hy hye ω)
    exact eq_of_reachable_of_isolated H hiso
      ((h : (openHyperGraph H (η \ cut H X ω)).Reachable s y).symm)
  simp only [taC, delE, hY, mul_zero, integral_zero, sub_zero]

/-- If `y ∈ X` then `B = 0`. -/
theorem taB_eq_zero_of_mem (H : Hypergraph V E) (s y : V) (hsy : s ≠ y) (X : Set V) (hy : y ∈ X)
    (g : Set V → ℝ) : taB H s y X g = 0 := by
  simp only [taB, taC_eq_zero_of_mem H s y hsy X hy g, mul_zero, integral_zero]

/-- If `y ∈ X` then `A = 0`. -/
theorem taA_eq_zero_of_mem (H : Hypergraph V E) (s y z : V) (hsy : s ≠ y) (X : Set V) (hy : y ∈ X)
    (g : Set V → ℝ) : taA H s y z X g = 0 := by
  simp only [taA, taC_eq_zero_of_mem H s y hsy X hy g, mul_zero, integral_zero]

/-- If `y ∈ X ∪ {s}` then `b = 0`. -/
theorem tab_eq_zero_of_mem (H : Hypergraph V E) (s y : V) (X : Set V) (hy : y ∈ insert s X) :
    tab H s y X = 0 := by
  rw [tab, avoidEv_eq, avoidEvent_singleton_eq_empty H hy, measureReal_empty]

/-- If `y ∈ X ∪ {s}` then `a = 0`. -/
theorem taa_eq_zero_of_mem (H : Hypergraph V E) (s y z : V) (X : Set V) (hy : y ∈ insert s X) :
    taa H s y z X = 0 := by
  rw [taa, avoidEv_eq, avoidEvent_singleton_eq_empty H hy, Set.empty_inter, measureReal_empty]

/-- If `s ∈ X` then `B = 0`, because `{s ↮ X}` is empty. -/
theorem taB_eq_zero_of_root_mem (H : Hypergraph V E) (s y : V) (X : Set V) (hs : s ∈ X)
    (g : Set V → ℝ) : taB H s y X g = 0 := by
  have h0 : ∀ ω : Set E, ind (avoidEv H s X) ω = 0 := fun ω =>
    ind_of_not_mem (by rw [avoidEv_eq, avoidEvent_singleton_eq_empty H hs]; exact Set.notMem_empty ω)
  simp only [taB, h0, zero_mul, integral_zero]

/-- If `s ∈ X` then `A = 0`. -/
theorem taA_eq_zero_of_root_mem (H : Hypergraph V E) (s y z : V) (X : Set V) (hs : s ∈ X)
    (g : Set V → ℝ) : taA H s y z X g = 0 := by
  have h0 : ∀ ω : Set E, ind (avoidEv H s X) ω = 0 := fun ω =>
    ind_of_not_mem (by rw [avoidEv_eq, avoidEvent_singleton_eq_empty H hs]; exact Set.notMem_empty ω)
  simp only [taA, h0, zero_mul, integral_zero]

/-! ### The base case: no label of positive probability joins `X` to its complement -/

/-- An open walk in a configuration with no label joining `X` to its complement does not leave
`X`. -/
theorem mem_of_reachable_of_noBoundary {H : Hypergraph V E} {X : Set V} {ζ : Set E}
    (hζ : ∀ e ∈ ζ, ∀ a ∈ H.incidence e, ∀ b ∈ H.incidence e, a ∈ X → b ∈ X) {x u : V}
    (hx : x ∈ X) (h : (openHyperGraph H ζ).Reachable x u) : u ∈ X := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hx
  | @tail b c _ hbc ih =>
    obtain ⟨-, e, he, hbe, hce⟩ := (openHyperGraph_adj_iff H ζ b c).1 hbc
    exact hζ e he b hbe c hce ih

/-- … nor enter `X`. -/
theorem notMem_of_reachable_of_noBoundary {H : Hypergraph V E} {X : Set V} {ζ : Set E}
    (hζ : ∀ e ∈ ζ, ∀ a ∈ H.incidence e, ∀ b ∈ H.incidence e, a ∈ X → b ∈ X) {x u : V}
    (hu : u ∉ X) (h : (openHyperGraph H ζ).Reachable u x) : x ∉ X := fun hx =>
  hu (mem_of_reachable_of_noBoundary hζ hx h.symm)

/-- With no open boundary label, the cluster of `X` is `X` and the cut of `X` is the set of labels
meeting `X`. -/
theorem cut_eq_of_noBoundary {H : Hypergraph V E} {X : Set V} {ζ : Set E}
    (hζ : ∀ e ∈ ζ, ∀ a ∈ H.incidence e, ∀ b ∈ H.incidence e, a ∈ X → b ∈ X) :
    cut H X ζ = labelsMeeting H X := by
  have hcl : hyperClusterSet H ζ X = X :=
    Set.Subset.antisymm (fun u ⟨x, hx, hr⟩ => mem_of_reachable_of_noBoundary hζ hx hr)
      (subset_hyperClusterSet H ζ X)
  rw [cut_eq, hcl]

/-- With no open boundary label, deleting the labels meeting `X` does not change connections
outside `X`. -/
theorem reachable_sdiff_iff_of_noBoundary {H : Hypergraph V E} {X : Set V} {ζ : Set E}
    (hζ : ∀ e ∈ ζ, ∀ a ∈ H.incidence e, ∀ b ∈ H.incidence e, a ∈ X → b ∈ X) {a : V}
    (ha : a ∉ X) (b : V) :
    (openHyperGraph H (ζ \ labelsMeeting H X)).Reachable a b
      ↔ (openHyperGraph H ζ).Reachable a b := by
  refine ⟨fun h => h.mono (openHyperGraph_le_of_subset H Set.sdiff_subset), fun h => ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c hab hbc ih =>
    obtain ⟨hne, e, he, hbe, hce⟩ := (openHyperGraph_adj_iff H ζ b c).1 hbc
    have hb : b ∉ X := notMem_of_reachable_of_noBoundary hζ ha
      ((SimpleGraph.reachable_iff_reflTransGen a b).2 hab)
    have hdisj : Disjoint (H.incidence e) X := by
      rw [Set.disjoint_left]
      intro u hu huX
      exact hb (hζ e he u hu b hbe huX)
    refine ih.trans (SimpleGraph.Adj.reachable
      ((openHyperGraph_adj_iff H _ b c).2 ⟨hne, e, ⟨he, ?_⟩, hbe, hce⟩))
    rw [mem_labelsMeeting, not_not]
    exact hdisj

/-- Removing labels of probability `0` from the configuration does not change any mean. -/
theorem integral_eq_integral_sdiff_of_zero (H : Hypergraph V E) (Z : Set E)
    (hZ : ∀ e ∈ Z, (H.prob e : ℝ) = 0) (F : Set E → ℝ) :
    (∫ η, F η ∂(prodBernoulli H.prob))
      = ∫ η, F (η \ Z) ∂(prodBernoulli H.prob) := by
  have hp : (fun j => if j ∈ Z then (0 : unitInterval) else H.prob j) = H.prob := by
    funext e
    by_cases he : e ∈ Z
    · rw [if_pos he]
      exact Subtype.ext (hZ e he).symm
    · rw [if_neg he]
  rw [CTOne.integral_comp_sdiff_prodBernoulli H.prob Z F, hp]

/-- **The base case of the induction on `X`**: if every label incident both to `X` and to its
complement has probability `0`, then `Q = A·b − a·B = 0`.  The cluster of `X` is `X`, the cut is the
constant set of labels meeting `X`, the event `{s ↮ X}` is sure, and the ratio `taNW / taN` is the
constant `a / b`.  The bond `HullPort.taQ_eq_zero_of_noBoundary`. -/
theorem taQ_eq_zero_of_noBoundary (H : Hypergraph V E) (s y z : V) (hsy : s ≠ y) (X : Set V)
    (g : Set V → ℝ)
    (hbd : ∀ e : E, ∀ a ∈ H.incidence e, ∀ b ∈ H.incidence e, a ∈ X → b ∉ X →
      (H.prob e : ℝ) = 0) :
    taQ H s y z X g = 0 := by
  classical
  by_cases hs : s ∈ X
  · simp only [taQ, taA_eq_zero_of_root_mem H s y z X hs, taB_eq_zero_of_root_mem H s y X hs]
    ring
  by_cases hyX : y ∈ X
  · simp only [taQ, tab_eq_zero_of_mem H s y X (Set.mem_insert_of_mem _ hyX),
      taa_eq_zero_of_mem H s y z X (Set.mem_insert_of_mem _ hyX)]
    ring
  set Z : Set E := {e | (H.prob e : ℝ) = 0} with hZ
  have hZzero : ∀ e ∈ Z, (H.prob e : ℝ) = 0 := fun e he => he
  have hnb : ∀ η : Set E, ∀ e ∈ η \ Z,
      ∀ a ∈ H.incidence e, ∀ b ∈ H.incidence e, a ∈ X → b ∈ X := by
    intro η e he a ha b hb haX
    by_contra hbX
    exact he.2 (hbd e a ha b hb haX hbX)
  have hcut : ∀ η : Set E, cut H X (η \ Z) = labelsMeeting H X :=
    fun η => cut_eq_of_noBoundary (hnb η)
  have hD : ∀ η : Set E, η \ Z ∈ avoidEv H s X := fun η =>
    (mem_avoidEvent_singleton H s X (η \ Z)).2 fun x hx hsx =>
      hs (mem_of_reachable_of_noBoundary (hnb η) hx hsx.symm)
  set c₀ : ℝ := delE H (labelsMeeting H X)
      (fun η => g (hyperClusterSet H η ({s} : Set V)) * ind (hyperConn H s y) η) -
    delE H (labelsMeeting H X) (fun η => g (hyperClusterSet H η ({s} : Set V))) *
      delE H (labelsMeeting H X) (fun η => ind (hyperConn H s y) η) with hc₀
  set n₀ : ℝ := delE H (labelsMeeting H X) (fun η => ind (hyperConn H s y)ᶜ η) with hn₀
  set nw₀ : ℝ :=
    delE H (labelsMeeting H X)
      (fun η => ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) η) with hnw₀
  have hB : taB H s y X g = c₀ := by
    rw [taB, integral_eq_integral_sdiff_of_zero H Z hZzero
      (fun ω => ind (avoidEv H s X) ω * taC H s y X g ω)]
    have h1 : ∀ η : Set E, ind (avoidEv H s X) (η \ Z) * taC H s y X g (η \ Z) = c₀ := by
      intro η
      rw [ind_of_mem (hD η), one_mul, taC, hcut η]
    rw [integral_congr_ae (Filter.Eventually.of_forall
        (fun η => h1 η : ∀ η : Set E, _ = c₀)),
      integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hA : taA H s y z X g = nw₀ / n₀ * c₀ := by
    rw [taA, integral_eq_integral_sdiff_of_zero H Z hZzero
      (fun ω => ind (avoidEv H s X) ω * (taNW H s y z X ω / taN H s y X ω * taC H s y X g ω))]
    have h1 : ∀ η : Set E, ind (avoidEv H s X) (η \ Z) *
        (taNW H s y z X (η \ Z) / taN H s y X (η \ Z) * taC H s y X g (η \ Z))
        = nw₀ / n₀ * c₀ := by
      intro η
      rw [ind_of_mem (hD η), one_mul, taC, taN, taNW, hcut η]
    rw [integral_congr_ae (Filter.Eventually.of_forall
        (fun η => h1 η : ∀ η : Set E, _ = nw₀ / n₀ * c₀)),
      integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hconn : ∀ (η : Set E) (t : V),
      (openHyperGraph H ((η \ Z) \ labelsMeeting H X)).Reachable y t
        ↔ (openHyperGraph H (η \ Z)).Reachable y t :=
    fun η t => reachable_sdiff_iff_of_noBoundary (hnb η) hyX t
  have hE : ∀ η : Set E, ind (avoidEv H y (insert s X)) (η \ Z)
      = ind (hyperConn H s y)ᶜ ((η \ Z) \ labelsMeeting H X) := by
    intro η
    by_cases h : η \ Z ∈ avoidEv H y (insert s X)
    · rw [ind_of_mem h, ind_of_mem]
      intro hsy'
      exact (mem_avoidEvent_singleton H y (insert s X) (η \ Z)).1 h s (Set.mem_insert _ _)
        ((hconn η s).1 (hsy' : (openHyperGraph H _).Reachable s y).symm)
    · rw [ind_of_not_mem h, ind_of_not_mem]
      intro hN
      refine h ((mem_avoidEvent_singleton H y (insert s X) (η \ Z)).2 fun t ht hyt => ?_)
      rcases Set.mem_insert_iff.1 ht with rfl | ht
      · exact hN (((hconn η t).2 hyt).symm : (openHyperGraph H _).Reachable t y)
      · exact hyX (mem_of_reachable_of_noBoundary (hnb η) ht hyt.symm)
  have hb : tab H s y X = n₀ := by
    have h1 : tab H s y X
        = ∫ η, ind (avoidEv H y (insert s X)) (η \ Z) ∂(prodBernoulli H.prob) := by
      rw [tab, ← CTBase.integral_ind_eq_real (prodBernoulli H.prob)]
      exact integral_eq_integral_sdiff_of_zero H Z hZzero
        (fun ω => ind (avoidEv H y (insert s X)) ω)
    have h2 : n₀
        = ∫ η, ind (hyperConn H s y)ᶜ ((η \ Z) \ labelsMeeting H X)
            ∂(prodBernoulli H.prob) := by
      rw [hn₀, delE]
      exact integral_eq_integral_sdiff_of_zero H Z hZzero
        (fun ω => ind (hyperConn H s y)ᶜ (ω \ labelsMeeting H X))
    rw [h1, h2]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun η => hE η : ∀ η : Set E, _ = _))
  have hzz : ∀ η : Set E, ind (hyperConn H y z) ((η \ Z) \ labelsMeeting H X)
      = ind (hyperConn H y z) (η \ Z) := by
    intro η
    by_cases h : η \ Z ∈ hyperConn H y z
    · have h' : (η \ Z) \ labelsMeeting H X ∈ hyperConn H y z :=
        ((hconn η z).2 h : (openHyperGraph H _).Reachable y z)
      rw [ind_of_mem h, ind_of_mem h']
    · have h' : (η \ Z) \ labelsMeeting H X ∉ hyperConn H y z :=
        fun hh => h ((hconn η z).1 hh)
      rw [ind_of_not_mem h, ind_of_not_mem h']
  have ha : taa H s y z X = nw₀ := by
    have hfun : ∀ η : Set E,
        (avoidEv H y (insert s X)).indicator (fun ν => ind (hyperConn H y z) ν) η
          = ind (avoidEv H y (insert s X)) η * ind (hyperConn H y z) η := by
      intro η
      by_cases h : η ∈ avoidEv H y (insert s X)
      · rw [Set.indicator_of_mem h, ind_of_mem h, one_mul]
      · rw [Set.indicator_of_notMem h, ind_of_not_mem h, zero_mul]
    have h1 : taa H s y z X
        = ∫ η, ind (avoidEv H y (insert s X)) (η \ Z) * ind (hyperConn H y z) (η \ Z)
            ∂(prodBernoulli H.prob) := by
      rw [taa, ← CTBase.setIntegral_ind_eq_real (prodBernoulli H.prob),
        ← integral_indicator (measurableSet_of_fintype (avoidEv H y (insert s X))),
        integral_congr_ae (Filter.Eventually.of_forall hfun)]
      exact integral_eq_integral_sdiff_of_zero H Z hZzero
        (fun ω => ind (avoidEv H y (insert s X)) ω * ind (hyperConn H y z) ω)
    have h2 : nw₀
        = ∫ η, ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) ((η \ Z) \ labelsMeeting H X)
            ∂(prodBernoulli H.prob) := by
      rw [hnw₀, delE]
      exact integral_eq_integral_sdiff_of_zero H Z hZzero
        (fun ω => ind ((hyperConn H s y)ᶜ ∩ hyperConn H y z) (ω \ labelsMeeting H X))
    rw [h1, h2]
    refine integral_congr_ae (Filter.Eventually.of_forall
      (fun η : Set E => ?_ : ∀ η : Set E, _ = _))
    rw [ind_inter, hE η, hzz η]
  have hle : nw₀ ≤ n₀ := by
    simp only [hnw₀, hn₀, delE]
    refine integral_mono (integrable_of_fintype _) (integrable_of_fintype _) fun η => ?_
    rw [ind_inter]
    have h1 := ind_le_one (hyperConn H y z) (η \ labelsMeeting H X)
    have h2 := ind_nonneg (hyperConn H s y)ᶜ (η \ labelsMeeting H X)
    nlinarith [ind_nonneg (hyperConn H y z) (η \ labelsMeeting H X)]
  have hnw0 : 0 ≤ nw₀ := by
    simp only [hnw₀, delE]
    exact integral_nonneg fun η => ind_nonneg _ _
  rw [taQ, hA, hB, ha, hb]
  by_cases hn : n₀ = 0
  · have hz : nw₀ = 0 := le_antisymm (hn ▸ hle) hnw0
    rw [hz, hn]; ring
  · field_simp
    ring

end TABase

/-! ## Section 9.  Lemma (★^H), part one (`CovTau/StarHPrelim.lean`)

The functionals `covH` and `yH` of the one-source bound, the union identity for the marker
indicator, and the Markov bookkeeping along the exploration of the cluster of the source set.  The
bond file also proves van den Berg–Häggström–Kahn's Theorem 1.4 with a vertex SET in the finitary
`ED` form (`bhk14S_ED`); that step does NOT port, and the obstruction is isolated at the end of the
section. -/

section StarH

variable [Fintype E]

/-- The cluster of a source set is the union of the clusters of its members.  The bond has to work
for this (`CovTauStarN.openEdgeCluster_biUnion_eq`) because its `C_S` is a union of EDGE clusters
and the cluster of a member has to be recovered from it; for vertex clusters it is the
definition. -/
theorem hyperClusterSet_biUnion (H : Hypergraph V E) (ω : Set E) (S : Set V) :
    hyperClusterSet H ω S = ⋃ s ∈ S, hyperClusterSet H ω ({s} : Set V) := by
  ext u
  simp only [hyperClusterSet, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_singleton_iff,
    exists_prop]
  exact ⟨fun ⟨s, hs, hr⟩ => ⟨s, hs, s, rfl, hr⟩,
    fun ⟨s, hs, t, ht, hr⟩ => ⟨s, hs, ht ▸ hr⟩⟩

/-- The open labels incident to the cluster of the source set: the hyperedge form of the bond's
union of open edge clusters `C_S = ⋃_{s ∈ S} C_s`. -/
def srcLabels (H : Hypergraph V E) (S : Set V) (ω : Set E) : Set E :=
  ω ∩ labelsMeeting H (hyperClusterSet H ω S)

theorem srcLabels_subset (H : Hypergraph V E) (S : Set V) (ω : Set E) :
    srcLabels H S ω ⊆ ω := Set.inter_subset_left

theorem srcLabels_mono (H : Hypergraph V E) (S : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    srcLabels H S ω ⊆ srcLabels H S ω' := by
  refine Set.inter_subset_inter h fun e he => ?_
  rw [mem_labelsMeeting] at he ⊢
  obtain ⟨u, hue, huC⟩ := Set.not_disjoint_iff.1 he
  exact Set.not_disjoint_iff.2 ⟨u, hue, hyperClusterSet_mono H S h huC⟩

/-- **The cluster of a member, read inside the label cluster of the source set.**  For `x ∈ S` the
cluster of `x` computed from the labels incident to the cluster of `S` is the cluster of `x`: the
hyperedge form of `CovTauStarN.openEdgeCluster_biUnion_eq`.  Every label a walk out of `x` crosses
is incident to a vertex already reached, hence to a vertex of the cluster of `S`. -/
theorem hyperClusterSet_srcLabels (H : Hypergraph V E) {S : Set V} {x : V} (hx : x ∈ S)
    (ω : Set E) :
    hyperClusterSet H (srcLabels H S ω) ({x} : Set V) = hyperClusterSet H ω ({x} : Set V) := by
  refine Set.Subset.antisymm (hyperClusterSet_mono H _ (srcLabels_subset H S ω)) ?_
  intro u hu
  rw [mem_hyperClusterSet_singleton] at hu ⊢
  rw [SimpleGraph.reachable_iff_reflTransGen] at hu ⊢
  induction hu with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    obtain ⟨hne, e, he, hbe, hce⟩ := (openHyperGraph_adj_iff H ω b c).1 hbc
    have hbC : b ∈ hyperClusterSet H ω S :=
      ⟨x, hx, (SimpleGraph.reachable_iff_reflTransGen _ _).2 hab⟩
    have hmeet : e ∈ labelsMeeting H (hyperClusterSet H ω S) :=
      Set.not_disjoint_iff.2 ⟨b, hbe, hbC⟩
    exact ih.tail ((openHyperGraph_adj_iff H _ b c).2 ⟨hne, e, ⟨he, hmeet⟩, hbe, hce⟩)

/-! ### The marker indicator -/

/-- `1{v ↔ S ∪ N} = 1{v ↔ S} + (1 − 1{v ↔ S})·1{v ↔ N}`.  The bond `CovTauStarN.nr_union_eq`. -/
theorem nr_union_eq (H : Hypergraph V E) (S N : Set V) (v : V) (ω : Set E) :
    nr H (S ∪ N) v ω = nr H S v ω + (1 - nr H S v ω) * nr H N v ω := by
  simp only [nr_eq_indMem, AGBase.indMem, hyperClusterSet_union H ω S N, Set.mem_union]
  by_cases h1 : v ∈ hyperClusterSet H ω S
  · rw [if_pos h1, if_pos (Or.inl h1)]; ring
  · rw [if_neg h1]
    by_cases h2 : v ∈ hyperClusterSet H ω N
    · rw [if_pos h2, if_pos (Or.inr h2)]; ring
    · rw [if_neg h2, if_neg (not_or.2 ⟨h1, h2⟩)]; ring

/-! ### Reachability in the world `H − W` -/

/-- A root inside `W` is isolated in the world `H − W`.  The bond
`CovTauStarN.not_reachable_off_of_mem`. -/
theorem not_reachable_off_of_mem (H : Hypergraph V E) {W : Set V} {η : Set E} {s u : V}
    (hs : s ∈ W) (hsu : s ≠ u) : ¬ (openHyperGraph H (off H W η)).Reachable s u := by
  refine fun h => hsu (eq_of_reachable_of_isolated H (fun e he hse => ?_) h).symm
  exact Set.disjoint_left.1 (mem_off.1 he).2 hse hs

/-- In the world `H − W` a vertex outside `W` reaches only vertices outside `W`. -/
theorem notMem_of_reachable_off (H : Hypergraph V E) {W : Set V} {η : Set E} {s u : V}
    (hs : s ∉ W) (h : (openHyperGraph H (off H W η)).Reachable s u) : u ∉ W := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hs
  | @tail b c _ hbc ih =>
    obtain ⟨-, e, he, -, hce⟩ := (openHyperGraph_adj_iff H _ b c).1 hbc
    exact fun hcW => Set.disjoint_left.1 (mem_off.1 he).2 hce hcW

/-! ### The functionals of the one-source bound -/

/-- **`H(W) = Cov_{H − W}(Ψ(C_x), 1{v ↔ S})`**, the covariance in the world with every label
meeting `W` closed.  The bond `CovTauStarN.covH`, in the measure language of the hyperedge
development. -/
def covH (H : Hypergraph V E) (Ψ : Set V → ℝ) (x : V) (S : Set V) (v : V) (W : Set V) : ℝ :=
  (∫ ω, Ψ (hyperClusterSet H (off H W ω) ({x} : Set V)) * nr H S v (off H W ω)
      ∂(prodBernoulli H.prob)) -
    (∫ ω, Ψ (hyperClusterSet H (off H W ω) ({x} : Set V)) ∂(prodBernoulli H.prob)) *
      ∫ ω, nr H S v (off H W ω) ∂(prodBernoulli H.prob)

/-- With nothing deleted, `covH` is the plain covariance. -/
theorem covH_empty (H : Hypergraph V E) (Ψ : Set V → ℝ) (x : V) (S : Set V) (v : V) :
    covH H Ψ x S v (∅ : Set V) =
      (∫ ω, Ψ (hyperClusterSet H ω ({x} : Set V)) * nr H S v ω ∂(prodBernoulli H.prob)) -
        (∫ ω, Ψ (hyperClusterSet H ω ({x} : Set V)) ∂(prodBernoulli H.prob)) *
          ∫ ω, nr H S v ω ∂(prodBernoulli H.prob) := by
  simp only [covH, off_empty]

/-- **`Y^H(N) = E[ H(C_N) ; x ↮ N ]`**.  The bond `CovTauStarN.yH`. -/
def yH (H : Hypergraph V E) (Ψ : Set V → ℝ) (x : V) (S : Set V) (v : V) (N : Set V) : ℝ :=
  ∫ ω, ind (avoidEvent H ({x} : Set V) N) ω *
    covH H Ψ x S v (hyperClusterSet H ω N) ∂(prodBernoulli H.prob)

/-- With nothing avoided, `Y^H(∅)` is `H(∅)`, the plain covariance. -/
theorem yH_empty (H : Hypergraph V E) (Ψ : Set V → ℝ) (x : V) (S : Set V) (v : V) :
    yH H Ψ x S v (∅ : Set V) = covH H Ψ x S v (∅ : Set V) := by
  have h : ∀ ω : Set E, ind (avoidEvent H ({x} : Set V) (∅ : Set V)) ω *
      covH H Ψ x S v (hyperClusterSet H ω (∅ : Set V)) = covH H Ψ x S v (∅ : Set V) := by
    intro ω
    rw [avoidEvent_empty, ind_of_mem (Set.mem_univ ω), one_mul,
      CSHDefs.hyperClusterSet_empty_source]
  rw [yH, integral_congr_ae (Filter.Eventually.of_forall
      (fun ω => h ω : ∀ ω : Set E, _ = covH H Ψ x S v (∅ : Set V))),
    integral_const, probReal_univ, smul_eq_mul, one_mul]

/-! ### The Markov bookkeeping -/

/-- **The Markov bookkeeping of Lemma (★^H)**, along the exploration of the cluster of `N`.  For
every resampling `η`, at the hybrid `spliceRecord (recordAt H N ω) η`:
(i) inside the cluster of `N` the owner's functional is the one of `ω`;
(ii) outside it, the one of the world `H − C_N` on the fresh configuration;
(iii) inside the cluster of `N` the marker indicator is the one of `ω`;
(iv) outside it, the one of the world; and
(v) for a marker inside the cluster of `N` the world indicator vanishes.
The bond `CovTauStarN.starH_markov`.  The five statements are read off
`CTOne.reachable_spliceRecord_of_mem` and `CTOne.reachable_spliceRecord_of_not_mem`; the bond has to
carry `K, K₂ ⊆ D` because its exploration is relative to a coordinate set, and here the exploration
runs over all labels, so those hypotheses disappear. -/
theorem starH_markov (H : Hypergraph V E) (N S : Set V) (x v : V) (hvS : v ∉ S)
    (Ψ : Set V → ℝ) (ω η : Set E) :
    (x ∈ hyperClusterSet H ω N →
        Ψ (hyperClusterSet H (spliceRecord (recordAt H N ω) η) ({x} : Set V))
          = Ψ (hyperClusterSet H ω ({x} : Set V))) ∧
    (x ∉ hyperClusterSet H ω N →
        Ψ (hyperClusterSet H (spliceRecord (recordAt H N ω) η) ({x} : Set V))
          = Ψ (hyperClusterSet H (off H (hyperClusterSet H ω N) η) ({x} : Set V))) ∧
    (v ∈ hyperClusterSet H ω N →
        nr H S v (spliceRecord (recordAt H N ω) η) = nr H S v ω) ∧
    (v ∉ hyperClusterSet H ω N →
        nr H S v (spliceRecord (recordAt H N ω) η)
          = nr H S v (off H (hyperClusterSet H ω N) η)) ∧
    (v ∈ hyperClusterSet H ω N → nr H S v (off H (hyperClusterSet H ω N) η) = 0) := by
  set C := hyperClusterSet H ω N with hC
  refine ⟨fun hx => ?_, fun hx => ?_, fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · rw [hyperClusterSet_spliceRecord_of_mem H N ω η hx]
  · rw [hyperClusterSet_spliceRecord_of_not_mem H N ω η hx]
  · unfold nr
    refine ind_congr_of_iff (exists_congr fun s => and_congr_right fun hs => ?_)
    by_cases hsC : s ∈ C
    · exact (reachable_spliceRecord_of_mem H N ω η hsC v).symm
    · constructor
      · intro h
        exact absurd hv (notMem_of_reachable_off H hsC
          ((reachable_spliceRecord_of_not_mem H N ω η hsC v).2 h))
      · intro h
        obtain ⟨n, hn, hnv⟩ := hv
        exact absurd (⟨n, hn, hnv.trans h.symm⟩ : s ∈ C) hsC
  · unfold nr
    refine ind_congr_of_iff (exists_congr fun s => and_congr_right fun hs => ?_)
    by_cases hsC : s ∈ C
    · have hsv : s ≠ v := fun hh => hv (hh ▸ hsC)
      constructor
      · intro h
        have hsv' : (openHyperGraph H ω).Reachable s v :=
          (reachable_spliceRecord_of_mem H N ω η hsC v).2 h
        obtain ⟨n, hn, hns⟩ := hsC
        exact absurd (⟨n, hn, hns.trans hsv'⟩ : v ∈ C) hv
      · intro h; exact absurd h (not_reachable_off_of_mem H hsC hsv)
    · exact (reachable_spliceRecord_of_not_mem H N ω η hsC v).symm
  · unfold nr
    refine ind_of_not_mem ?_
    rintro ⟨s, hs, hr⟩
    have hsv : s ≠ v := fun hh => hvS (hh ▸ hs)
    by_cases hsC : s ∈ C
    · exact not_reachable_off_of_mem H hsC hsv hr
    · exact notMem_of_reachable_off H hsC hr hv

/-! ### What ports of BHK's Theorem 1.4 with a vertex set, and what does not

The bond `CovTauStarN.bhk14S_ED` reads the owner's functional as `fcl Ψ x`, the value of `Ψ` at the
open EDGE cluster of `x`, and the negative-correlation theorem it quotes is applied with the source
set `S`.  What makes that legitimate is `CovTauStarN.openEdgeCluster_biUnion_eq`: the edge cluster of
`x` is recovered from the edge cluster of `S`, so `fcl Ψ x` IS an increasing functional of the
cluster of the source set.

The hyperedge development states its conditional association theorems for the VERTEX cluster
`hyperClusterSet H ω S` (`KN/HyperOneCluster.lean`, `KN/HyperTwoCluster.lean`,
`CTOne.avoid_cluster_sub_negCorrelation`), and the vertex cluster of a source set does not determine
the cluster of a member: `exists_hyperClusterSet_eq_and_singleton_ne` exhibits one label incident to
two vertices, a source set containing both, and two configurations with the same cluster of the
source set and different clusters of the member.  So `Ψ(C_x)` is not a functional of
`hyperClusterSet H ω S` and the bond statement cannot be transcribed.

`bhk14S_setFunctional` is the part that does port: BHK 1.4 with a vertex set, for a functional of the
cluster of the SET.  Recovering the bond statement needs the two-cluster inequality for functionals
of the LABEL cluster `srcLabels`, which by `hyperClusterSet_srcLabels` does determine the cluster of
each member.  `KN/HyperOneCluster.lean` proves BHK's Theorem 1.1 for functionals of the vertex
cluster only, so that inequality is not available here, and this is where layer three stops. -/

/-- The two-point hypergraph with a single label incident to both vertices. -/
private def twoPoint : Hypergraph Bool Unit where
  incidence := fun _ => Set.univ
  prob := fun _ => ⟨1 / 2, by constructor <;> norm_num⟩

/-- **The vertex cluster of a source set does not determine the cluster of a member.**  Two
configurations of `twoPoint` give the same cluster of the source set `{false, true}` and different
clusters of `false`.  This is why the bond `bhk14S_ED` has no transcription with vertex-cluster
functionals: its owner functional `Ψ(C_x)` is not a functional of the cluster of the source set. -/
theorem exists_hyperClusterSet_eq_and_singleton_ne :
    ∃ (W L : Type) (_ : Fintype W) (_ : Fintype L) (H : Hypergraph W L) (S : Set W) (x : W)
      (ω₁ ω₂ : Set L), x ∈ S ∧
      hyperClusterSet H ω₁ S = hyperClusterSet H ω₂ S ∧
      hyperClusterSet H ω₁ ({x} : Set W) ≠ hyperClusterSet H ω₂ ({x} : Set W) := by
  refine ⟨Bool, Unit, inferInstance, inferInstance, twoPoint, Set.univ, false,
    (∅ : Set Unit), (Set.univ : Set Unit), Set.mem_univ _, ?_, ?_⟩
  · have h1 : hyperClusterSet twoPoint (∅ : Set Unit) (Set.univ : Set Bool) = Set.univ :=
      Set.eq_univ_of_forall fun b => ⟨b, Set.mem_univ b, SimpleGraph.Reachable.refl b⟩
    have h2 : hyperClusterSet twoPoint (Set.univ : Set Unit) (Set.univ : Set Bool) = Set.univ :=
      Set.eq_univ_of_forall fun b => ⟨b, Set.mem_univ b, SimpleGraph.Reachable.refl b⟩
    rw [h1, h2]
  · have h1 : hyperClusterSet twoPoint (∅ : Set Unit) ({false} : Set Bool) = {false} := by
      refine Set.Subset.antisymm (fun b hb => ?_) (subset_hyperClusterSet _ _ _)
      rw [mem_hyperClusterSet_singleton] at hb
      exact (eq_of_reachable_of_isolated twoPoint
        (fun e he => absurd he (Set.notMem_empty e)) hb)
    have h2 : true ∈ hyperClusterSet twoPoint (Set.univ : Set Unit) ({false} : Set Bool) := by
      rw [mem_hyperClusterSet_singleton]
      exact ((openHyperGraph_adj_iff twoPoint (Set.univ : Set Unit) false true).2
        ⟨by decide, (), Set.mem_univ _, Set.mem_univ _, Set.mem_univ _⟩).reachable
    intro hcon
    rw [h1] at hcon
    exact absurd (hcon ▸ h2 : true ∈ ({false} : Set Bool)) (by decide)

/-- **BHK's Theorem 1.4 with a vertex set, for a functional of the cluster of the SET.**  Given
`{S ↮ v}`, an increasing functional of the cluster of `S` and the marker indicator `1{v ↔ N}` are
negatively correlated.  This is `CTOne.avoid_cluster_sub_negCorrelation` with `T = T' = {v}`, the
marker read on the cluster of `v`. -/
theorem bhk14S_setFunctional (H : Hypergraph V E) [Fintype V] (S : Set V) (v : V) (N : Set V)
    {F : Set V → ℝ} (hF : Monotone F) :
    (prodBernoulli H.prob).real (avoidEvent H S ({v} : Set V)) *
        (∫ ω in avoidEvent H S ({v} : Set V),
          F (hyperClusterSet H ω S) * nr H N v ω ∂(prodBernoulli H.prob))
      ≤ (∫ ω in avoidEvent H S ({v} : Set V),
            F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) *
        ∫ ω in avoidEvent H S ({v} : Set V), nr H N v ω ∂(prodBernoulli H.prob) := by
  set G : Set V → ℝ := fun C => if ∃ t ∈ N, t ∈ C then 1 else 0 with hG
  have hGmono : Monotone G := by
    intro C C' hCC'
    simp only [hG]
    by_cases h : ∃ t ∈ N, t ∈ C
    · obtain ⟨t, ht, htC⟩ := h
      rw [if_pos ⟨t, ht, htC⟩, if_pos ⟨t, ht, hCC' htC⟩]
    · rw [if_neg h]; split_ifs <;> norm_num
  have key := avoid_cluster_sub_negCorrelation H S ({v} : Set V) ({v} : Set V) Set.Subset.rfl
    hF hGmono
  have hread : ∀ ω : Set E, G (hyperClusterSet H ω ({v} : Set V)) = nr H N v ω := by
    intro ω
    simp only [hG, nr, mem_hyperClusterSet_singleton]
    by_cases h : ∃ t ∈ N, (openHyperGraph H ω).Reachable v t
    · obtain ⟨t, ht, hvt⟩ := h
      rw [if_pos ⟨t, ht, hvt⟩,
        ind_of_mem (show ω ∈ {ω : Set E | ∃ s ∈ N, (openHyperGraph H ω).Reachable s v} from
          ⟨t, ht, hvt.symm⟩)]
    · rw [if_neg h,
        ind_of_not_mem (show ω ∉ {ω : Set E | ∃ s ∈ N, (openHyperGraph H ω).Reachable s v} from
          fun ⟨t, ht, htv⟩ => h ⟨t, ht, htv.symm⟩)]
  simp only [hread] at key
  exact key

end StarH

/-! ## Section 10.  Co-import check and non-vacuity

Every module of layers zero to two is imported at once and every sub-namespace is open at once, so
a name clash or an incompatible instance would surface here.  `coImportCheck` names one declaration
from each of the seventeen modules; `taQ_empty_of_noBoundary` checks the new base case of Section 8
against the one already proved in `KN/HyperCSHTwoB.lean`; `phiFun_sum_pos` checks that the
finite-sum expression of `Φ` is not identically zero; and
`exists_clusterExchange_ne_of_not_disjoint` shows that the disjointness hypothesis of
`clusterExchange` of `KN/HyperExchange.lean` cannot be dropped. -/

section Checks

/-- **Co-import check.**  One declaration from each of `KN/HyperAGBase.lean`, `HyperCTBase`,
`HyperCSHDefs`, `HyperAGOne`, `HyperCTOne`, `HyperCSHTwoA`, `HyperCSHTwoB`, `HyperTreeHK`,
`HyperPeel`, `HyperProjGen`, `HyperTransfer`, `HyperOneCluster`, `HyperTwoClusterClosed`,
`HyperFibre`, `HyperExpose`, `HyperLabelled` and `HyperDecisionTree`, elaborated with every
sub-namespace open simultaneously. -/
theorem coImportCheck [Fintype V] [Fintype E] (H : Hypergraph V E) (S T : Set V) (o s : V)
    (ω : Set E) (J : Set E) (F : Set V → ℝ) :
    AGBase.indMem o (hyperClusterSet H ω S) = nr H S o ω ∧
    CTBase.cE H S (fun _ => (0 : ℝ)) ω = 0 ∧
    0 ≤ CSHDefs.phiFun H s S (fun _ => (0 : ℝ)) T ∧
    (AGOne.HyperAdditiveGluing → AGOne.HyperNearOneGluing) ∧
    off H (∅ : Set V) ω = ω ∧
    CSHTwoA.worldMean H s (fun _ => (0 : ℝ)) T = 0 ∧
    CSHTwoB.nr H S o ω = nr H S o ω ∧
    TreeHK.reachedBy H S (ω.toFinite.toFinset) = hyperClusterSet H ω S ∧
    surplusY H (∅ : Set V) (∅ : Finset V) (fun _ => 0) F o = surplus H (∅ : Finset V) (fun _ => 0) F o ∧
    hyperConn H o s = hyperConn H s o ∧
    avoidMean H (∅ : Set V) F o = ∫ η, F (hyperClusterSet H η ({o} : Set V)) ∂(prodBernoulli H.prob) ∧
    labelsIn H (Finset.univ : Finset V) = (Set.univ : Set E) ∧
    OneClusterInequality H S T ∧
    S ⊆ supportFromRecord H S J ∧
    Function.Injective (originalLabel H S) ∧
    anchoredSource (fun _ : E => (∅ : Set V)) (Set.univ : Set V) (∅ : Set E) = (∅ : Set V) ∧
    (recordAt H S ω).openLabels ⊆ (recordAt H S ω).queried := by
  refine ⟨(nr_eq_indMem H S o ω).symm, CTBase.cE_const H S 0 ω,
    CSHDefs.phiFun_nonneg H s S monotone_const T, AGOne.hyperAdditiveGluingSuffices,
    off_empty H ω, ?_, rfl, ?_, surplusY_empty H (∅ : Finset V) (fun _ => 0) F o,
    hyperConn_comm H o s, avoidMean_empty H F o, labelsIn_univ H,
    oneClusterInequality_holds H S T, subset_supportFromRecord H S J,
    originalLabel_injective H S, anchoredSource_empty _ _,
    ExplorationRecord.openLabels_subset_queried (recordAt H S ω)⟩
  · rw [CSHTwoA.worldMean]; simp
  · rw [TreeHK.reachedBy_eq]
    congr 1
    exact ω.toFinite.coe_toFinset

/-- **The new base case agrees with the one already proved.**  Section 8 gives `Q = 0` whenever no
label of positive probability joins `X` to its complement; at `X = ∅` that hypothesis is vacuous and
the conclusion is the statement of `CSHTwoB.taQ_empty`, which is proved there without the
hypothesis `s ≠ y`.  The two agree wherever both apply. -/
theorem taQ_empty_of_noBoundary [Fintype E] (H : Hypergraph V E) (s y z : V) (hsy : s ≠ y)
    (g : Set V → ℝ) : taQ H s y z (∅ : Set V) g = 0 :=
  taQ_eq_zero_of_noBoundary H s y z hsy (∅ : Set V) g
    (fun _ a _ _ _ ha _ => absurd ha (Set.notMem_empty a))

/-- **The finite-sum expression of `Φ` is not identically zero.**  In the two-vertex model with one
label incident to both vertices, `Φ` at the owner `false`, no avoided set, the marker functional and
`K = {true}` is positive, so `phiFun_eq_sum` is an expansion of something with content. -/
theorem phiFun_sum_pos :
    0 < ∑ η : Set Unit,
      weight (fun e => (twoPoint.prob e : ℝ)) η *
        (ind (avoidEv twoPoint false (∅ : Set Bool))
            (η \ labelsMeeting twoPoint ({true} : Set Bool)) *
          (CSHTwoA.worldMean twoPoint false (CSHDefs.reachMarker true)
              (hyperClusterSet twoPoint (η \ labelsMeeting twoPoint ({true} : Set Bool))
                (∅ : Set Bool)) -
            CSHDefs.reachMarker true
              (hyperClusterSet twoPoint (η \ labelsMeeting twoPoint ({true} : Set Bool))
                ({false} : Set Bool)))) := by
  have hpos : 0 < CSHDefs.phiFun twoPoint false ∅ (CSHDefs.reachMarker true)
      ({true} : Set Bool) := by
    have hcoe : ∀ e : Unit, ((twoPoint.prob e : unitInterval) : ℝ) = 1 / 2 := fun _ => rfl
    refine CSHDefs.phiFun_pos twoPoint (fun e => ⟨?_, ?_⟩) false true (by decide)
      ⟨Set.univ, ?_⟩
    · exact unitInterval.coe_pos.1 (by rw [hcoe e]; norm_num)
    · exact unitInterval.coe_lt_one.1 (by rw [hcoe e]; norm_num)
    · show (openHyperGraph twoPoint (Set.univ : Set Unit)).Reachable false true
      exact ((openHyperGraph_adj_iff twoPoint _ false true).2
        ⟨by decide, (), Set.mem_univ _, Set.mem_univ _, Set.mem_univ _⟩).reachable
  rwa [phiFun_eq_sum twoPoint false (∅ : Set Bool) ({true} : Set Bool)
    (CSHDefs.reachMarker true)] at hpos

/-- **The cluster exchange identity of `KN/HyperExchange.lean` needs its disjointness hypothesis.**
In the two-vertex model with one label incident to both, take the two sources `{false}` and
`{true}` and the two prescribed clusters `{false}` and `Set.univ`, which meet.  Deleting the labels
meeting `{false}` closes the only label, so the second factor on the left is the probability that
`true` reaches `false` in the empty configuration, namely `0`.  On the right the deletion is
harmless for the event it is applied to, so the product is the probability that the two vertices
are joined, which is positive. -/
theorem exists_clusterExchange_ne_of_not_disjoint :
    ∃ (W L' : Type) (_ : Fintype W) (_ : Fintype L') (H : Hypergraph W L') (S K T L : Set W),
      ¬ Disjoint K L ∧
      (prodBernoulli H.prob).real (clusterEvent H S K) *
          (prodBernoulli (deleteHyper H K).prob).real (clusterEvent H T L)
        ≠ (prodBernoulli H.prob).real (clusterEvent H T L) *
          (prodBernoulli (deleteHyper H L).prob).real (clusterEvent H S K) := by
  refine ⟨Bool, Unit, inferInstance, inferInstance, twoPoint, ({false} : Set Bool),
    ({false} : Set Bool), ({true} : Set Bool), (Set.univ : Set Bool), ?_, ?_⟩
  · exact fun hdisj => Set.disjoint_left.1 hdisj rfl (Set.mem_univ false)
  -- every label meets every nonempty vertex set, so both deletions switch the label off
  have hlab : ∀ Y : Set Bool, Y.Nonempty → labelsMeeting twoPoint Y = (Set.univ : Set Unit) := by
    intro Y hY
    obtain ⟨b, hb⟩ := hY
    exact Set.eq_univ_of_forall fun e => Set.not_disjoint_iff.2 ⟨b, Set.mem_univ b, hb⟩
  have hzero : ∀ Y : Set Bool, Y.Nonempty → ∀ e : Unit, (deleteHyper twoPoint Y).prob e = 0 := by
    intro Y hY e
    simp only [deleteHyper, hlab Y hY, Set.mem_univ, if_pos]
  have hae : ∀ Y : Set Bool, Y.Nonempty →
      ∀ᵐ ω ∂(prodBernoulli (deleteHyper twoPoint Y).prob), ω = (∅ : Set Unit) := by
    intro Y hY
    filter_upwards [prodBernoulli_ae_forall_notMem (deleteHyper twoPoint Y).prob
      (Z := (Set.univ : Set Unit)) (Set.toFinite _).countable
      fun e _ => hzero Y hY e] with ω hω
    exact Set.eq_empty_of_forall_notMem fun e he => hω e (Set.mem_univ e) he
  have hempty : hyperClusterSet twoPoint (∅ : Set Unit) ({true} : Set Bool) = ({true} : Set Bool) := by
    refine Set.Subset.antisymm (fun b hb => ?_) (subset_hyperClusterSet _ _ _)
    rw [mem_hyperClusterSet_singleton] at hb
    exact eq_of_reachable_of_isolated twoPoint (fun e he => absurd he (Set.notMem_empty e)) hb
  have hempty' :
      hyperClusterSet twoPoint (∅ : Set Unit) ({false} : Set Bool) = ({false} : Set Bool) := by
    refine Set.Subset.antisymm (fun b hb => ?_) (subset_hyperClusterSet _ _ _)
    rw [mem_hyperClusterSet_singleton] at hb
    exact eq_of_reachable_of_isolated twoPoint (fun e he => absurd he (Set.notMem_empty e)) hb
  -- the left-hand second factor vanishes
  have hL : (prodBernoulli (deleteHyper twoPoint ({false} : Set Bool)).prob).real
      (clusterEvent twoPoint ({true} : Set Bool) (Set.univ : Set Bool)) = 0 := by
    have hcongr : clusterEvent twoPoint ({true} : Set Bool) (Set.univ : Set Bool)
        =ᵐ[prodBernoulli (deleteHyper twoPoint ({false} : Set Bool)).prob] (∅ : Set (Set Unit)) := by
      filter_upwards [hae ({false} : Set Bool) ⟨false, rfl⟩] with ω hω
      rw [eq_iff_iff]
      constructor
      · intro hmem
        have hcl : hyperClusterSet twoPoint ω ({true} : Set Bool) = Set.univ := hmem
        rw [hω, hempty] at hcl
        have hf : (false : Bool) ∈ ({true} : Set Bool) := by rw [hcl]; trivial
        exact absurd hf (by decide)
      · exact fun h => absurd h (Set.notMem_empty ω)
    rw [measureReal_congr hcongr, measureReal_empty]
  -- the right-hand second factor is one
  have hR : (prodBernoulli (deleteHyper twoPoint (Set.univ : Set Bool)).prob).real
      (clusterEvent twoPoint ({false} : Set Bool) ({false} : Set Bool)) = 1 := by
    have hcongr : clusterEvent twoPoint ({false} : Set Bool) ({false} : Set Bool)
        =ᵐ[prodBernoulli (deleteHyper twoPoint (Set.univ : Set Bool)).prob]
          (Set.univ : Set (Set Unit)) := by
      filter_upwards [hae (Set.univ : Set Bool) ⟨false, Set.mem_univ false⟩] with ω hω
      rw [eq_iff_iff]
      refine ⟨fun _ => Set.mem_univ ω, fun _ => ?_⟩
      show hyperClusterSet twoPoint ω ({false} : Set Bool) = ({false} : Set Bool)
      rw [hω]
      exact hempty'
    rw [measureReal_congr hcongr, probReal_univ]
  -- the right-hand first factor is positive
  have hpos : 0 < (prodBernoulli twoPoint.prob).real
      (clusterEvent twoPoint ({true} : Set Bool) (Set.univ : Set Bool)) := by
    have hcoe : ∀ e : Unit, ((twoPoint.prob e : unitInterval) : ℝ) = 1 / 2 := fun _ => rfl
    refine prodBernoulli_real_pos_of_nonempty (fun e => ⟨?_, ?_⟩) ⟨(Set.univ : Set Unit), ?_⟩
    · exact unitInterval.coe_pos.1 (by rw [hcoe e]; norm_num)
    · exact unitInterval.coe_lt_one.1 (by rw [hcoe e]; norm_num)
    · show hyperClusterSet twoPoint (Set.univ : Set Unit) ({true} : Set Bool) = Set.univ
      refine Set.eq_univ_of_forall fun b => ?_
      rw [mem_hyperClusterSet_singleton]
      by_cases hb : b = true
      · exact hb ▸ SimpleGraph.Reachable.refl _
      · have hb' : b = false := by cases b <;> simp_all
        exact hb' ▸ ((openHyperGraph_adj_iff twoPoint (Set.univ : Set Unit) true false).2
          ⟨by decide, (), Set.mem_univ _, Set.mem_univ _, Set.mem_univ _⟩).reachable
  rw [hL, hR, mul_zero, mul_one]
  exact ne_of_lt hpos

end Checks

end KNAll.Site.CSHThree

end
