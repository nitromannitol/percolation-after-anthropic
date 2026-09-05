import Hypergraph.HyperAGBase
import Hypergraph.HyperProjGen
import Hypergraph.HyperTransfer
import Percolation.Continuity.Statements

/-!
# Additive gluing from the master form (GEN), and the surplus transfer for one relay

The hyperedge form of `Percolation/Continuity/AdditiveGluing/OfAGloc.lean`,
`Percolation/Continuity/AdditiveGluing/SurplusTransfer.lean` and
`Percolation/Continuity/AdditiveGluing/Suffices.lean`.  Everything is stated for a
`Hypergraph V E` with arbitrary incidence sets over two arbitrary types, `Fintype` being asked for
only where the imported inequality asks for it.

## What the three bond files already have here

* The score-compatible injective rank `exists_rank_compat` is the one of `KN/HyperTransfer.lean`,
  proved there for an arbitrary vertex type by well-ordering it; the bond file proves it for
  `Fin n`.  Its auxiliary `scoreFilter_ssubset` is `private` there and is not needed here.
* The two combinatorial facts about the first-in-rank patterns are `firstRank_disjoint'` and
  `firstRank_cover'` of `KN/HyperPeel.lean`, for an arbitrary family of sets, and their reading at
  the connection events is `firstPattern_disjoint`, `firstPattern_cover` and
  `sum_measureReal_avoid_firstPattern` of `KN/HyperProjGen.lean`.  Only the last of these carries
  an avoided set that the bond file does not, so `sum_measureReal_firstPattern` below is that
  statement at `Y = ∅`.
* (GEN) for two relays is `AGBase.gen_pair` of `KN/HyperAGBase.lean`, and (GEN) for all relay sets
  from the surplus transfer is `genY_of_surplusTransferY` of `KN/HyperProjGen.lean`.

## What is added

* `agloc_firstRank_of_gen` — (GEN) at one observer, relay set and rank implies the localised union
  bound (AG-loc) there, by reading (GEN) at the increasing indicator `F = 1{b ∈ ·}`.
* `additiveGluing_of_agloc_firstRank`, `additiveGluing_card_of_agloc_firstRank`,
  `hyperAdditiveGluing_of_agloc_firstRank` — additive gluing from (AG-loc).  Unlike the bond
  template the rank is not an input of the pointwise statement: it is produced from the score
  `a ↦ P(a ↔ b)`.
* `HyperAdditiveGluing`, `HyperNearOneGluing` and `hyperAdditiveGluingSuffices` — the two named
  statements and the implication between them with `δ = ε / 2`.
* `surplusTransfer_single` — the surplus transfer inequality (S5) for a single relay,
  unconditionally, from Harris and the two-cluster inequality of van den Berg–Häggström–Kahn.  The
  bond template's hypotheses `v ≠ a` and `0 ≤ F` are both absent: the hyperedge forms of the two
  inequalities do not ask for them.
* `gen_triple_of_surplusTransfer_pair` — (GEN) for three relays from (S5) for two.  This is not the
  three-relay case of `genY_of_surplusTransferY`, which would need (S5) at every smaller relay set
  as well; the base case here is the unconditional `AGBase.gen_pair`.  The bond template's
  hypotheses `a₃ ≠ a₁`, `a₃ ≠ a₂` are absent for the same reason as above.
* `additiveGluing_of_surplusTransfer` — the layer composed: the surplus transfer with no avoided set
  implies additive gluing.

## Non-vacuity

`additiveGluing_singleton` proves the (AG-loc) hypothesis unconditionally for a single relay, by
Harris for `{o ↔ a}` against `{a ↮ b}`, and reads off the union bound
`P(o ↔ b) ≥ P(o ↔ a) − P(a ↮ b)`.  `surplusTransfer_single_indicator` reads the surplus transfer at
an indicator, where it becomes an inequality between connection probabilities.
`additiveGluing_of_hyperAdditiveGluing` and `nearOneGluing_of_hyperNearOneGluing` recover
`Percolation.Continuity.Statements.AdditiveGluing` and
`Percolation.Continuity.Statements.NearOneGluing` from the two hyperedge statements, through the
bond model `KNAll.Bond.bondHypergraph`.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation
  and related processes*, Random Structures Algorithms 29 (2006), Thms. 1.3–1.5.
* G. Kozma, S. Nitzan, Conj. 1 (p. 3), Conj. 3 (p. 15), Conj. 4 and Thm. 7 (p. 32).
-/

noncomputable section

namespace KNAll.Site.AGOne

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open scoped Classical

variable {V E : Type*}

/-! ## The first-in-rank patterns without an avoided set -/

/-- The first-in-rank patterns have total measure `P(u ↔ T)`. -/
theorem sum_measureReal_firstPattern [Fintype E] (H : Hypergraph V E) (T : Finset V) (r : V → ℕ)
    (u : V) (hr : Set.InjOn r ↑T) :
    ∑ a ∈ T, (prodBernoulli H.prob).real (firstPattern H T r u a) =
      (prodBernoulli H.prob).real (⋃ a ∈ T, hyperConn H u a) := by
  have h := sum_measureReal_avoid_firstPattern H (∅ : Set V) T r u hr
  simpa [avoidEvent_empty] using h

/-- With no avoided set the conditional relay mean is the plain mean. -/
theorem condMeanY_empty [Fintype V] [Fintype E] (H : Hypergraph V E) (F : Set V → ℝ) (a : V) :
    condMeanY H (∅ : Set V) F a
      = ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) := by
  rw [condMeanY, avoidIntegral, avoidEvent_empty, Measure.restrict_univ, probReal_univ, div_one]

/-- The sum form of (GEN) without an avoided set: it is `sum_le_setIntegral_of_genY` at `Y = ∅`. -/
theorem sum_le_setIntegral_of_gen [Fintype V] [Fintype E] (H : Hypergraph V E) (A : Finset V)
    (r : V → ℕ) (F : Set V → ℝ) (o : V) (h : 0 ≤ surplus H A r F o) :
    ∑ a ∈ A, (prodBernoulli H.prob).real (firstPattern H A r o a) *
          ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) ≤
      ∫ ω in ⋃ a ∈ A, hyperConn H o a,
        F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) := by
  rw [← surplusY_empty] at h
  have key := sum_le_setIntegral_of_genY H (∅ : Set V) A r F o h
  simpa [avoidEvent_empty, condMeanY_empty, firstPattern] using key

/-! ## (AG-loc) from the master form (GEN) -/

/-- **(GEN) ⇒ (AG-loc).**  If the master form (GEN) holds at the observer `o`, the relay set `A`
and the rank `r` for every monotone nonnegative set function, then the localised union bound in
first-in-rank form holds at `(o, b)`: take `F = 1{b ∈ ·}`, so that `∫ F(C(a)) = P(a ↔ b)` and
`∫_{o ↔ A} F(C(o)) = P(o ↔ A, o ↔ b)`, and use that the patterns partition `{o ↔ A}`. -/
theorem agloc_firstRank_of_gen [Fintype V] [Fintype E] (H : Hypergraph V E) (A : Finset V)
    (o b : V) (r : V → ℕ) (hr : Set.InjOn r ↑A)
    (hcompat : ∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
      (prodBernoulli H.prob).real (hyperConn H a b) ≤
        (prodBernoulli H.prob).real (hyperConn H a' b))
    (hgen : ∀ F : Set V → ℝ, (∀ S T : Set V, S ⊆ T → F S ≤ F T) → (∀ S : Set V, 0 ≤ F S) →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
          ∫ ω, F (hyperClusterSet H ω ({a'} : Set V)) ∂(prodBernoulli H.prob)) →
      ∑ a ∈ A, (prodBernoulli H.prob).real (firstPattern H A r o a) *
            ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) ≤
        ∫ ω in ⋃ a ∈ A, hyperConn H o a,
          F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob)) :
    (prodBernoulli H.prob).real ((⋃ a ∈ A, hyperConn H o a) ∩ (hyperConn H o b)ᶜ) ≤
      ∑ a ∈ A, (prodBernoulli H.prob).real (firstPattern H A r o a) *
        (1 - (prodBernoulli H.prob).real (hyperConn H a b)) := by
  classical
  set μ := prodBernoulli H.prob with hμ
  have hint : ∀ x : V,
      (∫ ω, AGBase.indMem b (hyperClusterSet H ω ({x} : Set V)) ∂μ) = μ.real (hyperConn H x b) := by
    intro x
    simp only [AGBase.indMem_hyperClusterSet]
    rw [AGBase.integral_ind, hyperConn_comm H b x]
  have hsetint :
      (∫ ω in ⋃ a ∈ A, hyperConn H o a,
          AGBase.indMem b (hyperClusterSet H ω ({o} : Set V)) ∂μ) =
        μ.real ((⋃ a ∈ A, hyperConn H o a) ∩ hyperConn H o b) := by
    simp only [AGBase.indMem_hyperClusterSet]
    rw [AGBase.setIntegral_ind, hyperConn_comm H b o]
  have key := hgen (AGBase.indMem b) (fun S T hST => AGBase.monotone_indMem b hST)
    (fun S => AGBase.indMem_nonneg b S)
    (by intro a ha a' ha' hlt; rw [hint a, hint a']; exact hcompat a ha a' ha' hlt)
  rw [hsetint] at key
  simp only [hint] at key
  have hsp : μ.real (⋃ a ∈ A, hyperConn H o a) =
      μ.real ((⋃ a ∈ A, hyperConn H o a) ∩ hyperConn H o b) +
        μ.real ((⋃ a ∈ A, hyperConn H o a) ∩ (hyperConn H o b)ᶜ) := by
    rw [← measureReal_inter_add_sdiff (s := ⋃ a ∈ A, hyperConn H o a) (h := measure_ne_top _ _)
      (measurableSet_of_fintype (hyperConn H o b)), Set.sdiff_eq]
  have hsum := sum_measureReal_firstPattern H A r o hr
  rw [← hμ] at hsum
  have hexp : ∑ a ∈ A, μ.real (firstPattern H A r o a) * (1 - μ.real (hyperConn H a b)) =
      (∑ a ∈ A, μ.real (firstPattern H A r o a)) -
        ∑ a ∈ A, μ.real (firstPattern H A r o a) * μ.real (hyperConn H a b) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hexp, hsum]
  linarith [key, hsp]

/-! ## Additive gluing from (AG-loc) -/

/-- **Additive gluing from (AG-loc), one model at a time.**  If the localised union bound in
first-in-rank form holds at `(H, A, o, b)` for some rank injective on `A` along which
`a ↦ P(a ↔ b)` does not decrease, then under `P(a ↔ b) ≥ 1 − t` for every relay the right-hand
side of (AG-loc) is at most `t·P(o ↔ A) ≤ t`, and `P(o ↔ A) − P(o ↔ b) ≤ P(o ↔ A, o ↮ b)`.

The rank is not an input: it is produced by `exists_rank_compat` from the score `a ↦ P(a ↔ b)`. -/
theorem additiveGluing_of_agloc_firstRank [Fintype E] (H : Hypergraph V E) (A : Finset V)
    (o b : V) (t : ℝ) (ht : 0 ≤ t)
    (hrel : ∀ a ∈ A, 1 - t ≤ (prodBernoulli H.prob).real (hyperConn H a b))
    (hagloc : ∀ r : V → ℕ, Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (prodBernoulli H.prob).real (hyperConn H a b) ≤
          (prodBernoulli H.prob).real (hyperConn H a' b)) →
      (prodBernoulli H.prob).real ((⋃ a ∈ A, hyperConn H o a) ∩ (hyperConn H o b)ᶜ) ≤
        ∑ a ∈ A, (prodBernoulli H.prob).real (firstPattern H A r o a) *
          (1 - (prodBernoulli H.prob).real (hyperConn H a b))) :
    (prodBernoulli H.prob).real (⋃ a ∈ A, hyperConn H o a) - t ≤
      (prodBernoulli H.prob).real (hyperConn H o b) := by
  classical
  set μ := prodBernoulli H.prob with hμ
  obtain ⟨r, hrinj, hrc⟩ := exists_rank_compat A fun a => μ.real (hyperConn H a b)
  have key := hagloc r hrinj hrc
  have h1 : ∑ a ∈ A, μ.real (firstPattern H A r o a) * (1 - μ.real (hyperConn H a b)) ≤
      ∑ a ∈ A, μ.real (firstPattern H A r o a) * t :=
    Finset.sum_le_sum fun a ha =>
      mul_le_mul_of_nonneg_left (by linarith [hrel a ha]) measureReal_nonneg
  have hsum := sum_measureReal_firstPattern H A r o hrinj
  rw [← hμ] at hsum
  have h2 : ∑ a ∈ A, μ.real (firstPattern H A r o a) * t =
      t * μ.real (⋃ a ∈ A, hyperConn H o a) := by
    rw [← Finset.sum_mul, mul_comm, hsum]
  have h3 : μ.real (⋃ a ∈ A, hyperConn H o a) ≤ 1 := by
    have h := measureReal_mono (μ := μ) (Set.subset_univ (⋃ a ∈ A, hyperConn H o a))
      (measure_ne_top _ _)
    rwa [probReal_univ] at h
  have h4 : μ.real (⋃ a ∈ A, hyperConn H o a) - μ.real (hyperConn H o b) ≤
      μ.real ((⋃ a ∈ A, hyperConn H o a) ∩ (hyperConn H o b)ᶜ) := by
    have hsp : μ.real (⋃ a ∈ A, hyperConn H o a) =
        μ.real ((⋃ a ∈ A, hyperConn H o a) ∩ hyperConn H o b) +
          μ.real ((⋃ a ∈ A, hyperConn H o a) ∩ (hyperConn H o b)ᶜ) := by
      rw [← measureReal_inter_add_sdiff (s := ⋃ a ∈ A, hyperConn H o a) (h := measure_ne_top _ _)
        (measurableSet_of_fintype (hyperConn H o b)), Set.sdiff_eq]
    have hm : μ.real ((⋃ a ∈ A, hyperConn H o a) ∩ hyperConn H o b) ≤ μ.real (hyperConn H o b) :=
      measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
    linarith
  have h5 : t * μ.real (⋃ a ∈ A, hyperConn H o a) ≤ t := by
    simpa using mul_le_mul_of_nonneg_left h3 ht
  linarith [key, h1, h2, h4, h5]

/-! ## The named statements -/

/-- **Additive gluing for hyperedges.**  In every finite model of independent hyperedges, if
`P(a ↔ b) ≥ 1 − t` for every relay `a ∈ A`, then `P(o ↔ b) ≥ P(o ↔ A) − t`.  The hyperedge form of
`Percolation.Continuity.Statements.AdditiveGluing`, whose quantifier prefix over finite models is
that of `KNAll.Site.HyperedgeGluing`. -/
def HyperAdditiveGluing : Prop :=
  ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L) (A : Finset W) (o b : W) (t : ℝ),
    0 ≤ t → (∀ a ∈ A, 1 - t ≤ (prodBernoulli H.prob).real (hyperConn H a b)) →
      (prodBernoulli H.prob).real (⋃ a ∈ A, hyperConn H o a) - t ≤
        (prodBernoulli H.prob).real (hyperConn H o b)

/-- **Near-one gluing for hyperedges**, the hyperedge form of
`Percolation.Continuity.Statements.NearOneGluing`: the slack `δ` may not depend on the number of
relays. -/
def HyperNearOneGluing : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L) (A : Finset W) (o b : W),
      1 - δ < (prodBernoulli H.prob).real (⋃ a ∈ A, hyperConn H o a) →
      (∀ a ∈ A, 1 - δ < (prodBernoulli H.prob).real (hyperConn H a b)) →
        1 - ε < (prodBernoulli H.prob).real (hyperConn H o b)

/-- **`HyperAdditiveGluing` from (AG-loc)**, by name. -/
theorem hyperAdditiveGluing_of_agloc_firstRank
    (h : ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L) (A : Finset W) (o b : W)
        (r : W → ℕ), Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (prodBernoulli H.prob).real (hyperConn H a b) ≤
          (prodBernoulli H.prob).real (hyperConn H a' b)) →
      (prodBernoulli H.prob).real ((⋃ a ∈ A, hyperConn H o a) ∩ (hyperConn H o b)ᶜ) ≤
        ∑ a ∈ A, (prodBernoulli H.prob).real (firstPattern H A r o a) *
          (1 - (prodBernoulli H.prob).real (hyperConn H a b))) :
    HyperAdditiveGluing := by
  intro W L _ _ H A o b t ht hrel
  exact additiveGluing_of_agloc_firstRank H A o b t ht hrel fun r hr hc => h W L H A o b r hr hc

/-- **The graded reduction**, in the shape of the bond template: if (AG-loc) in first-in-rank form
holds for every finite model and every relay set of size at most `K`, then additive gluing holds for
every finite model and every relay set of size at most `K`.  The grading plays no role in the proof:
the rank is produced from the score `a ↦ P(a ↔ b)` inside
`additiveGluing_of_agloc_firstRank`, so the pointwise statement already gives this one and, at
`K = A.card`, `hyperAdditiveGluing_of_agloc_firstRank` as well. -/
theorem additiveGluing_card_of_agloc_firstRank (K : ℕ)
    (h : ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L) (A : Finset W) (o b : W)
        (r : W → ℕ), A.card ≤ K → Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (prodBernoulli H.prob).real (hyperConn H a b) ≤
          (prodBernoulli H.prob).real (hyperConn H a' b)) →
      (prodBernoulli H.prob).real ((⋃ a ∈ A, hyperConn H o a) ∩ (hyperConn H o b)ᶜ) ≤
        ∑ a ∈ A, (prodBernoulli H.prob).real (firstPattern H A r o a) *
          (1 - (prodBernoulli H.prob).real (hyperConn H a b))) :
    ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L) (A : Finset W) (o b : W) (t : ℝ),
      A.card ≤ K → 0 ≤ t →
      (∀ a ∈ A, 1 - t ≤ (prodBernoulli H.prob).real (hyperConn H a b)) →
      (prodBernoulli H.prob).real (⋃ a ∈ A, hyperConn H o a) - t ≤
        (prodBernoulli H.prob).real (hyperConn H o b) := by
  intro W L _ _ H A o b t hK ht hrel
  exact additiveGluing_of_agloc_firstRank H A o b t ht hrel fun r hr hc =>
    h W L H A o b r hK hr hc

/-- **`HyperAdditiveGluing ⇒ HyperNearOneGluing`** with `δ = ε / 2`: apply the additive inequality
with slack `t = ε / 2`.  The hyperedge form of
`Percolation.Continuity.additiveGluingSuffices_proof`. -/
theorem hyperAdditiveGluingSuffices : HyperAdditiveGluing → HyperNearOneGluing := by
  intro hAG ε hε
  refine ⟨ε / 2, by positivity, ?_⟩
  intro W L _ _ H A o b hoA hAb
  have key := hAG W L H A o b (ε / 2) (by positivity) fun a ha => (hAb a ha).le
  linarith

/-! ## The surplus transfer for one relay -/

/-- The real-number content of `surplusTransfer_single`, with every probability and every integral
abstracted: `pD, pDOv, pOa, pU, pQ` are the probabilities of `D`, `D ∩ {o ↔ v}`, `{o ↔ a}`,
`{o ↔ a} ∪ {o ↔ v}` and `{v ↔ a}`, and `IU, IOa, IDOv, ID, IQ` the integrals of `F(C(a))` over
those sets. -/
private theorem transfer_core {pD pDOv pOa pU pQ IU IOa IDOv ID IQ m : ℝ} (hpD : 0 ≤ pD)
    (hHarris : pU * m ≤ IU) (hBHK : pD * IDOv ≤ ID * pDOv)
    (hUint : IU = IOa + IDOv) (hUmu : pU = pOa + pDOv)
    (hDint : ID = m - IQ) (hDmu : pD = 1 - pQ) :
    pDOv * (IQ - pQ * m) ≤ pD * (IOa - pOa * m) := by
  have hA : pDOv * m - IDOv ≤ IOa - pOa * m := by
    rw [hUint, hUmu] at hHarris
    nlinarith [hHarris]
  have hC := mul_le_mul_of_nonneg_left hA hpD
  have heq : pDOv * (IQ - pQ * m) = pD * (pDOv * m) - pDOv * ID := by
    rw [hDint, hDmu]; ring
  rw [heq]
  nlinarith [hBHK, hC]

/-- **Surplus transfer, one relay (S5)₁.**  For `F` monotone on vertex sets, a relay `a`, an
observer `o` and a second observer `v`, with `m = ∫ F(C(a))` and `D = {v ↮ a}`:

  `P(D ∩ {o ↔ v}) · (∫_{v ↔ a} F(C(a)) − P(v ↔ a)·m) ≤ P(D) · (∫_{o ↔ a} F(C(a)) − P(o ↔ a)·m)`,

that is `Cov(F(C_a), 1_{o↔a}) ≥ P(o ↔ v | v ↮ a)·Cov(F(C_a), 1_{v↔a})`.  The two inputs are
Harris for `F(C_a)` on the increasing event `{o ↔ a} ∪ {o ↔ v}` and the two-cluster inequality of
van den Berg–Häggström–Kahn for `F(C_a)` and `1_{o ↔ v}` conditionally on `a ↮ v`.

Two hypotheses of the bond template are absent.  Nonnegativity of `F` is not used: Harris in the
form `AGBase.setIntegral_clusterFun_ge` and the two-cluster inequality in the form
`avoid_cluster_negCorrelation` both hold for a merely monotone functional, and the assembly
`transfer_core` is an identity plus two comparisons.  `v ≠ a` is not used either: when `v = a` the
event `D` is empty and both sides vanish.
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7)] -/
theorem surplusTransfer_single [Fintype V] [Fintype E] (H : Hypergraph V E) (o v a : V)
    (F : Set V → ℝ) (hF : Monotone F) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) ({a} : Set V) ∩ hyperConn H o v) *
        ((∫ ω in hyperConn H v a,
              F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (hyperConn H v a) *
            ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a} : Set V)) *
        ((∫ ω in hyperConn H o a,
              F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (hyperConn H o a) *
            ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) := by
  classical
  -- `({o ↔ a} ∪ {o ↔ v}) \ {o ↔ a} = D ∩ {o ↔ v}`: on `{o ↔ v}`, failing to reach `a` from `o`
  -- and failing to reach it from `v` are the same thing
  have hd : (hyperConn H o a ∪ hyperConn H o v) \ hyperConn H o a =
      avoidEvent H ({v} : Set V) ({a} : Set V) ∩ hyperConn H o v := by
    ext ω
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, mem_hyperConn,
      AGBase.mem_avoidEvent_pair]
    constructor
    · rintro ⟨h1 | h2, hn1⟩
      · exact absurd h1 hn1
      · exact ⟨fun h => hn1 (h2.trans h), h2⟩
    · rintro ⟨hn', h2⟩
      exact ⟨Or.inr h2, fun h1 => hn' (h2.symm.trans h1)⟩
  -- `D` is the complement of `{v ↔ a}`
  have hDQ : avoidEvent H ({v} : Set V) ({a} : Set V) = (hyperConn H v a)ᶜ := by
    ext ω
    rw [AGBase.mem_avoidEvent_pair, Set.mem_compl_iff, mem_hyperConn]
  refine transfer_core (pU := (prodBernoulli H.prob).real
      (hyperConn H o a ∪ hyperConn H o v))
    (IU := ∫ ω in hyperConn H o a ∪ hyperConn H o v,
      F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob))
    (IDOv := ∫ ω in avoidEvent H ({v} : Set V) ({a} : Set V) ∩ hyperConn H o v,
      F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob))
    (ID := ∫ ω in avoidEvent H ({v} : Set V) ({a} : Set V),
      F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob))
    measureReal_nonneg ?_ ?_ ?_ ?_ ?_ ?_
  · -- Harris for `F(C(a))` on the increasing event `{o ↔ a} ∪ {o ↔ v}`
    exact AGBase.setIntegral_clusterFun_ge H ({a} : Set V) F hF _
      ((isUpperSet_hyperConn H o a).union (isUpperSet_hyperConn H o v))
  · -- the two-cluster inequality, conditionally on `a ↮ v`
    have key := avoid_cluster_negCorrelation H ({a} : Set V) ({v} : Set V)
      (oneClusterInequality_holds H _ _) hF (AGBase.monotone_indMem o)
    simp only [AGBase.indMem_hyperClusterSet] at key
    rw [AGBase.setIntegral_mul_ind, AGBase.setIntegral_ind,
      AGBase.avoidEvent_pair_symm H a v] at key
    exact key
  · rw [← integral_inter_add_sdiff (measurableSet_of_fintype (hyperConn H o a))
      (integrable_of_fintype _).integrableOn,
      Set.inter_eq_right.2 Set.subset_union_left, hd]
  · rw [← measureReal_inter_add_sdiff (s := hyperConn H o a ∪ hyperConn H o v)
      (h := measure_ne_top _ _) (measurableSet_of_fintype (hyperConn H o a)),
      Set.inter_eq_right.2 Set.subset_union_left, hd]
  · have h := integral_add_compl (measurableSet_of_fintype (hyperConn H v a))
      (integrable_of_fintype (μ := prodBernoulli H.prob)
        fun ω => F (hyperClusterSet H ω ({a} : Set V)))
    rw [← hDQ] at h
    linarith
  · have h : (prodBernoulli H.prob).real (Set.univ : Set (Set E)) =
        (prodBernoulli H.prob).real (Set.univ ∩ hyperConn H v a) +
          (prodBernoulli H.prob).real (Set.univ \ hyperConn H v a) :=
      (measureReal_inter_add_sdiff (s := Set.univ) (h := measure_ne_top _ _)
        (measurableSet_of_fintype (hyperConn H v a))).symm
    rw [probReal_univ, Set.univ_inter, ← Set.compl_eq_univ_sdiff, ← hDQ] at h
    linarith


/-! ## (GEN) for three relays from the surplus transfer for two -/

/-- The real-number content of `gen_triple_of_surplusTransfer_pair`.  `pO1, pc` are the
probabilities of `{o ↔ a₁}` and `{o ↔ a₂, o ↮ a₁}`, `pD3, pDO3` those of `D₃ = {a₃ ↮ T}` and
`P₃ = D₃ ∩ {o ↔ a₃}`, `pW3, pA1, pA2` those of `{a₃ ↔ T}`, `{a₃ ↔ a₁}` and `{a₃ ↔ a₂, a₃ ↮ a₁}`,
and `IU2, IU23, IP3, ID3, IW3` the integrals over the corresponding events. -/
private theorem triple_core {pO1 pc pD3 pDO3 pW3 pA1 pA2 IU2 IU23 IP3 ID3 IW3 m₁ m₂ m₃ : ℝ}
    (hpD3 : 0 ≤ pD3) (hpDO3 : 0 ≤ pDO3) (hle : pDO3 ≤ pD3) (hpA1 : 0 ≤ pA1) (hpA2 : 0 ≤ pA2)
    (hm13 : m₁ ≤ m₃) (hm23 : m₂ ≤ m₃)
    (hSur0 : pO1 * m₁ + pc * m₂ ≤ IU2) (hsplit : IU23 = IU2 + IP3) (hP3int : 0 ≤ IP3)
    (hBHK : pDO3 * ID3 ≤ pD3 * IP3)
    (hDint : ID3 = m₃ - IW3) (hDmu : pD3 = 1 - pW3) (hWmu : pW3 = pA1 + pA2)
    (hST : pDO3 * (IW3 - (pA1 * m₁ + pA2 * m₂)) ≤ pD3 * (IU2 - (pO1 * m₁ + pc * m₂))) :
    pO1 * m₁ + pc * m₂ + pDO3 * m₃ ≤ IU23 := by
  have hCovSur : IW3 - m₃ * pW3 ≤ IW3 - (pA1 * m₁ + pA2 * m₂) := by
    rw [hWmu]
    nlinarith [mul_nonneg hpA1 (sub_nonneg.2 hm13), mul_nonneg hpA2 (sub_nonneg.2 hm23)]
  have h1 : pD3 * (m₃ * pDO3 - IP3) ≤ pDO3 * (IW3 - m₃ * pW3) := by
    rw [hDint, hDmu] at hBHK
    rw [hDmu]
    nlinarith [hBHK]
  have h2 := mul_le_mul_of_nonneg_left hCovSur hpDO3
  have hkey : pD3 * (m₃ * pDO3 - IP3) ≤ pD3 * (IU2 - (pO1 * m₁ + pc * m₂)) := by linarith
  have hgoal : 0 ≤ IU2 - (pO1 * m₁ + pc * m₂) - (m₃ * pDO3 - IP3) := by
    by_cases hD0 : pD3 = 0
    · have hP0 : pDO3 = 0 := le_antisymm (hD0 ▸ hle) hpDO3
      rw [hP0]
      nlinarith [hSur0, hP3int]
    · have hDpos : 0 < pD3 := lt_of_le_of_ne hpD3 (Ne.symm hD0)
      by_contra hneg
      have hlt := mul_neg_of_pos_of_neg hDpos (lt_of_not_ge hneg)
      nlinarith [hkey]
  rw [hsplit]
  linarith

/-- **(GEN) for three relays from the surplus transfer with two relays.**  For `F` monotone and
nonnegative on vertex sets, an observer `o` and relays `a₁, a₂, a₃` with `m₁ ≤ m₂ ≤ m₃`, ASSUME the
surplus transfer from `a₃` to `o` over `T = {a₁, a₂}`; THEN (GEN) holds for `(o; a₁, a₂, a₃)`.

The defect splits as `Sur_o(T) − deficit₃`; the one-cluster inequality for `C(a₃)` given `a₃ ↮ T`
(`oneCluster_contact_le`) bounds `P(a₃ ↮ T)·deficit₃` by `P(P₃)·Cov(F(C(a₃)), 1_{a₃ ↔ T})`, which is
at most `P(P₃)·Sur_{a₃}(T)` because `m₃` is maximal, and the transfer hypothesis turns that into
`P(a₃ ↮ T)·Sur_o(T)`; `Sur_o(T) ≥ 0` is `AGBase.gen_pair`.

The bond template also assumes `a₃ ≠ a₁` and `a₃ ≠ a₂`, needed there to apply the one-cluster
inequality.  `oneCluster_contact_le` carries no such hypothesis, so neither does this.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] -/
theorem gen_triple_of_surplusTransfer_pair [Fintype V] [Fintype E] (H : Hypergraph V E)
    (o a₁ a₂ a₃ : V) (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hm12 : (∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob))
    (hm23 : (∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, F (hyperClusterSet H ω ({a₃} : Set V)) ∂(prodBernoulli H.prob))
    (hST : (prodBernoulli H.prob).real
          (avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V) ∩ hyperConn H o a₃) *
        ((∫ ω in hyperConn H a₃ a₁ ∪ hyperConn H a₃ a₂,
              F (hyperClusterSet H ω ({a₃} : Set V)) ∂(prodBernoulli H.prob)) -
          ((prodBernoulli H.prob).real (hyperConn H a₃ a₁) *
              ∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob) +
            (prodBernoulli H.prob).real
                (hyperConn H a₃ a₂ ∩ (hyperConn H a₃ a₁)ᶜ) *
              ∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob))) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V)) *
        ((∫ ω in hyperConn H o a₁ ∪ hyperConn H o a₂,
              F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob)) -
          ((prodBernoulli H.prob).real (hyperConn H o a₁) *
              ∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob) +
            (prodBernoulli H.prob).real (hyperConn H o a₂ ∩ (hyperConn H o a₁)ᶜ) *
              ∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)))) :
    (prodBernoulli H.prob).real (hyperConn H o a₁) *
          (∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob)) +
        (prodBernoulli H.prob).real (hyperConn H o a₂ ∩ (hyperConn H o a₁)ᶜ) *
          (∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) +
        (prodBernoulli H.prob).real
            (hyperConn H o a₃ ∩ (hyperConn H o a₁ ∪ hyperConn H o a₂)ᶜ) *
          (∫ ω, F (hyperClusterSet H ω ({a₃} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω in hyperConn H o a₁ ∪ hyperConn H o a₂ ∪ hyperConn H o a₃,
        F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) := by
  classical
  set μ := prodBernoulli H.prob with hμ
  -- the avoidance event `{a₃ ↮ a₁} ∩ {a₃ ↮ a₂}`, unfolded
  have hD3iff : ∀ ω : Set E, ω ∈ avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V) ↔
      (¬ (openHyperGraph H ω).Reachable a₃ a₁ ∧ ¬ (openHyperGraph H ω).Reachable a₃ a₂) := by
    intro ω
    rw [mem_avoidEvent_singleton]
    constructor
    · intro h
      exact ⟨h a₁ (by simp), h a₂ (by simp)⟩
    · rintro ⟨h1, h2⟩ y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact h1
      · exact h2
  -- `P₃ = D₃ ∩ {o ↔ a₃}`
  have hPD : hyperConn H o a₃ ∩ (hyperConn H o a₁ ∪ hyperConn H o a₂)ᶜ =
      avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V) ∩ hyperConn H o a₃ := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_union, mem_hyperConn, hD3iff]
    constructor
    · rintro ⟨h3, hno⟩
      exact ⟨⟨fun h => hno (Or.inl (h3.trans h)), fun h => hno (Or.inr (h3.trans h))⟩, h3⟩
    · rintro ⟨⟨hn1, hn2⟩, h3⟩
      exact ⟨h3, fun h =>
        h.elim (fun h1 => hn1 (h3.symm.trans h1)) fun h2 => hn2 (h3.symm.trans h2)⟩
  -- `D₃ = {a₃ ↔ T}ᶜ`
  have hDW : avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V) =
      (hyperConn H a₃ a₁ ∪ hyperConn H a₃ a₂)ᶜ := by
    ext ω
    simp only [hD3iff, Set.mem_compl_iff, Set.mem_union, mem_hyperConn, not_or]
  rw [hPD]
  refine triple_core (pW3 := μ.real (hyperConn H a₃ a₁ ∪ hyperConn H a₃ a₂))
    (ID3 := ∫ ω in avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V),
      F (hyperClusterSet H ω ({a₃} : Set V)) ∂μ)
    (IW3 := ∫ ω in hyperConn H a₃ a₁ ∪ hyperConn H a₃ a₂,
      F (hyperClusterSet H ω ({a₃} : Set V)) ∂μ)
    (IP3 := ∫ ω in avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V) ∩ hyperConn H o a₃,
      F (hyperClusterSet H ω ({a₃} : Set V)) ∂μ)
    measureReal_nonneg measureReal_nonneg
    (measureReal_mono Set.inter_subset_left (measure_ne_top _ _)) measureReal_nonneg
    measureReal_nonneg (hm12.trans hm23) hm23
    (AGBase.gen_pair H o a₁ a₂ F hF hF0 hm12) ?_
    (setIntegral_nonneg (measurableSet_of_fintype _) fun ω _ => hF0 _) ?_ ?_ ?_ ?_ hST
  · -- the split `∫_{T ∪ {o ↔ a₃}} F(C(o)) = ∫_T F(C(o)) + ∫_{P₃} F(C(a₃))`
    have hd : ((hyperConn H o a₁ ∪ hyperConn H o a₂) ∪ hyperConn H o a₃) \
        (hyperConn H o a₁ ∪ hyperConn H o a₂) =
          hyperConn H o a₃ ∩ (hyperConn H o a₁ ∪ hyperConn H o a₂)ᶜ := by
      ext ω
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    have hlast : (∫ ω in avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V) ∩ hyperConn H o a₃,
          F (hyperClusterSet H ω ({o} : Set V)) ∂μ) =
        ∫ ω in avoidEvent H ({a₃} : Set V) ({a₁, a₂} : Set V) ∩ hyperConn H o a₃,
          F (hyperClusterSet H ω ({a₃} : Set V)) ∂μ :=
      setIntegral_congr_fun (measurableSet_of_fintype _) fun ω hω =>
        congrArg F (hyperClusterSet_singleton_eq_of_reachable H
          (hω.2 : (openHyperGraph H ω).Reachable o a₃))
    rw [← integral_inter_add_sdiff
      (measurableSet_of_fintype (hyperConn H o a₁ ∪ hyperConn H o a₂))
      (integrable_of_fintype (μ := μ)
        fun ω => F (hyperClusterSet H ω ({o} : Set V))).integrableOn,
      Set.inter_eq_right.2 Set.subset_union_left, hd, hPD, hlast]
  · -- the one-cluster inequality in the shape the peeling step consumes
    have hBHK := oneCluster_contact_le H a₃ o ({a₁, a₂} : Set V) hF
    rwa [hyperConn_comm H a₃ o, ← hμ] at hBHK
  · -- `∫_{D₃} F(C(a₃)) = m₃ − ∫_{a₃ ↔ T} F(C(a₃))`
    have h := integral_add_compl
      (measurableSet_of_fintype (hyperConn H a₃ a₁ ∪ hyperConn H a₃ a₂))
      (integrable_of_fintype (μ := μ) fun ω => F (hyperClusterSet H ω ({a₃} : Set V)))
    rw [← hDW] at h
    linarith
  · -- `P(D₃) = 1 − P(a₃ ↔ T)`
    have h : μ.real (Set.univ : Set (Set E)) =
        μ.real (Set.univ ∩ (hyperConn H a₃ a₁ ∪ hyperConn H a₃ a₂)) +
          μ.real (Set.univ \ (hyperConn H a₃ a₁ ∪ hyperConn H a₃ a₂)) :=
      (measureReal_inter_add_sdiff (s := Set.univ) (h := measure_ne_top _ _)
        (measurableSet_of_fintype _)).symm
    rw [probReal_univ, Set.univ_inter, ← Set.compl_eq_univ_sdiff, ← hDW] at h
    linarith
  · -- `P(a₃ ↔ T) = P(a₃ ↔ a₁) + P(a₃ ↔ a₂, a₃ ↮ a₁)`
    rw [← measureReal_inter_add_sdiff (s := hyperConn H a₃ a₁ ∪ hyperConn H a₃ a₂)
      (h := measure_ne_top _ _) (measurableSet_of_fintype (hyperConn H a₃ a₁)),
      Set.inter_eq_right.2 Set.subset_union_left, Set.sdiff_eq]
    congr 2
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    tauto

/-! ## The layer, composed -/

/-- **From the surplus transfer to additive gluing, with nothing else assumed.**  The surplus
transfer inequality with no avoided set gives (GEN) by `genY_of_surplusTransferY`, (GEN) gives
(AG-loc) by `agloc_firstRank_of_gen`, and (AG-loc) gives additive gluing by
`additiveGluing_of_agloc_firstRank`.  Only the monotone functionals are asked for; nonnegativity of
the transfer hypothesis' functional is not used because the only functional it is read at is the
indicator `1{b ∈ ·}`. -/
theorem additiveGluing_of_surplusTransfer [Fintype V] [Fintype E] (H : Hypergraph V E)
    (A : Finset V) (o b : V) (t : ℝ) (ht : 0 ≤ t)
    (hrel : ∀ a ∈ A, 1 - t ≤ (prodBernoulli H.prob).real (hyperConn H a b))
    (hST : ∀ F : Set V → ℝ, (∀ S S' : Set V, S ⊆ S' → F S ≤ F S') →
      ∀ (T : Finset V) (u v : V) (r : V → ℕ), v ∉ T → Set.InjOn r ↑T →
      (∀ c ∈ T, ∀ c' ∈ T, r c < r c' →
        condMeanY H (∅ : Set V) F c ≤ condMeanY H (∅ : Set V) F c') →
      (prodBernoulli H.prob).real
            (avoidEvent H ({v} : Set V) ((∅ : Set V) ∪ (↑T : Set V)) ∩ hyperConn H u v) *
          surplusY H (∅ : Set V) T r F v ≤
        (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ((∅ : Set V) ∪ (↑T : Set V))) *
          surplusY H (∅ : Set V) T r F u) :
    (prodBernoulli H.prob).real (⋃ a ∈ A, hyperConn H o a) - t ≤
      (prodBernoulli H.prob).real (hyperConn H o b) := by
  classical
  have hact : ∀ a : V, 0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) (∅ : Set V)) := by
    intro a
    rw [avoidEvent_empty, probReal_univ]
    norm_num
  refine additiveGluing_of_agloc_firstRank H A o b t ht hrel fun r hr hc => ?_
  refine agloc_firstRank_of_gen H A o b r hr hc fun F hF _ hcF => ?_
  refine sum_le_setIntegral_of_gen H A r F o ?_
  rw [← surplusY_empty]
  refine genY_of_surplusTransferY H (∅ : Set V) F hF
    (fun T u v r' _ _ _ hvT hr' hc' => hST F hF T u v r' hvT hr' hc') A o r
    (fun a _ => Set.notMem_empty a) (fun a _ => hact a) hr ?_
  simpa only [condMeanY_empty] using hcF

/-! ## Non-vacuity -/

/-- **The general inequality contains the union bound.**  For a single relay the localised bound is
Harris' inequality for the increasing event `{o ↔ a}` against the decreasing event `{a ↮ b}`, so
`additiveGluing_of_agloc_firstRank` returns `P(o ↔ b) ≥ P(o ↔ a) − P(a ↮ b)`, which is the union
bound `{o ↮ b} ⊆ {o ↮ a} ∪ {a ↮ b}` read as an inequality between probabilities. -/
theorem additiveGluing_singleton [Fintype V] [Fintype E] (H : Hypergraph V E) (o a b : V) (t : ℝ)
    (ht : 0 ≤ t) (hrel : 1 - t ≤ (prodBernoulli H.prob).real (hyperConn H a b)) :
    (prodBernoulli H.prob).real (hyperConn H o a) - t ≤
      (prodBernoulli H.prob).real (hyperConn H o b) := by
  classical
  set μ := prodBernoulli H.prob with hμ
  have hU : (⋃ x ∈ ({a} : Finset V), hyperConn H o x) = hyperConn H o a := by
    ext ω; simp
  have hkey := additiveGluing_of_agloc_firstRank H ({a} : Finset V) o b t ht
    (by intro x hx; rw [Finset.mem_singleton] at hx; exact hx ▸ hrel) ?_
  · rwa [hU] at hkey
  · intro r _ _
    have hfp : firstPattern H ({a} : Finset V) r o a = hyperConn H o a := by
      have hfil : (({a} : Finset V).filter fun a' => r a' < r a) = (∅ : Finset V) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false,
          not_and]
        rintro rfl
        exact lt_irrefl _
      simp [firstPattern, hfil]
    -- Harris: `P(o ↔ a, a ↮ b) ≤ P(o ↔ a)·P(a ↮ b)`
    have hharris := prodBernoulli_hyperConn_harris H o a a b
    rw [← hμ] at hharris
    have hsp : μ.real (hyperConn H o a) =
        μ.real (hyperConn H o a ∩ hyperConn H a b) +
          μ.real (hyperConn H o a ∩ (hyperConn H a b)ᶜ) := by
      rw [← measureReal_inter_add_sdiff (s := hyperConn H o a) (h := measure_ne_top _ _)
        (measurableSet_of_fintype (hyperConn H a b)), Set.sdiff_eq]
    -- `{o ↔ a} ∩ {o ↮ b} ⊆ {o ↔ a} ∩ {a ↮ b}`
    have hsub : (⋃ x ∈ ({a} : Finset V), hyperConn H o x) ∩ (hyperConn H o b)ᶜ ⊆
        hyperConn H o a ∩ (hyperConn H a b)ᶜ := by
      rw [hU]
      rintro ω ⟨hoa, hob⟩
      exact ⟨hoa, fun hab => hob ((hoa : (openHyperGraph H ω).Reachable o a).trans hab)⟩
    have hmono := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
    rw [Finset.sum_singleton, hfp]
    nlinarith [hmono, hsp, hharris]

/-- **Non-vacuity of `surplusTransfer_single`**, read at the increasing indicator `F = 1{c ∈ ·}`:
for all vertices `o, v, a, c`, with `D = {v ↮ a}`,

  `P(D, o ↔ v) · Cov(1_{c ↔ a}, 1_{v ↔ a}) ≤ P(D) · Cov(1_{c ↔ a}, 1_{o ↔ a})`. -/
theorem surplusTransfer_single_indicator [Fintype V] [Fintype E] (H : Hypergraph V E)
    (o v a c : V) :
    (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a} : Set V) ∩ hyperConn H o v) *
        ((prodBernoulli H.prob).real (hyperConn H v a ∩ hyperConn H c a) -
          (prodBernoulli H.prob).real (hyperConn H v a) *
            (prodBernoulli H.prob).real (hyperConn H c a)) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a} : Set V)) *
        ((prodBernoulli H.prob).real (hyperConn H o a ∩ hyperConn H c a) -
          (prodBernoulli H.prob).real (hyperConn H o a) *
            (prodBernoulli H.prob).real (hyperConn H c a)) := by
  have key := surplusTransfer_single H o v a (AGBase.indMem c) (AGBase.monotone_indMem c)
  simp only [AGBase.indMem_hyperClusterSet] at key
  rw [AGBase.setIntegral_ind, AGBase.setIntegral_ind, AGBase.integral_ind] at key
  exact key

/-- **The hyperedge statement is not weaker than the bond statement it generalizes.**  Bond
percolation is the hyperedge model `KNAll.Bond.bondHypergraph`, so `HyperAdditiveGluing` returns
`Percolation.Continuity.Statements.AdditiveGluing` verbatim. -/
theorem additiveGluing_of_hyperAdditiveGluing (h : HyperAdditiveGluing) :
    Percolation.Continuity.Statements.AdditiveGluing := by
  intro n w A o b t ht hrel
  have key := h (Fin n) (Sym2 (Fin n)) (KNAll.Bond.bondHypergraph w) A o b t ht
    (by simpa only [KNAll.Bond.hyperConn_eq_openConn, KNAll.Bond.bondHypergraph_prob] using hrel)
  simpa only [KNAll.Bond.hyperConn_eq_openConn, KNAll.Bond.bondHypergraph_prob] using key

/-- The same for the near-one form: `HyperNearOneGluing` returns
`Percolation.Continuity.Statements.NearOneGluing`. -/
theorem nearOneGluing_of_hyperNearOneGluing (h : HyperNearOneGluing) :
    Percolation.Continuity.Statements.NearOneGluing := by
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n w A o b hoA hAb
  have key := hmain (Fin n) (Sym2 (Fin n)) (KNAll.Bond.bondHypergraph w) A o b
    (by simpa only [KNAll.Bond.hyperConn_eq_openConn, KNAll.Bond.bondHypergraph_prob] using hoA)
    (by simpa only [KNAll.Bond.hyperConn_eq_openConn, KNAll.Bond.bondHypergraph_prob] using hAb)
  simpa only [KNAll.Bond.hyperConn_eq_openConn, KNAll.Bond.bondHypergraph_prob] using key

end KNAll.Site.AGOne

end

#print axioms KNAll.Site.AGOne.sum_measureReal_firstPattern
#print axioms KNAll.Site.AGOne.condMeanY_empty
#print axioms KNAll.Site.AGOne.sum_le_setIntegral_of_gen
#print axioms KNAll.Site.AGOne.agloc_firstRank_of_gen
#print axioms KNAll.Site.AGOne.additiveGluing_of_agloc_firstRank
#print axioms KNAll.Site.AGOne.additiveGluing_card_of_agloc_firstRank
#print axioms KNAll.Site.AGOne.hyperAdditiveGluing_of_agloc_firstRank
#print axioms KNAll.Site.AGOne.hyperAdditiveGluingSuffices
#print axioms KNAll.Site.AGOne.surplusTransfer_single
#print axioms KNAll.Site.AGOne.gen_triple_of_surplusTransfer_pair
#print axioms KNAll.Site.AGOne.additiveGluing_of_surplusTransfer
#print axioms KNAll.Site.AGOne.additiveGluing_singleton
#print axioms KNAll.Site.AGOne.surplusTransfer_single_indicator
#print axioms KNAll.Site.AGOne.additiveGluing_of_hyperAdditiveGluing
#print axioms KNAll.Site.AGOne.nearOneGluing_of_hyperNearOneGluing
