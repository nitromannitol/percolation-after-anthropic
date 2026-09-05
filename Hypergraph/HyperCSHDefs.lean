import Hypergraph.HyperCTBase

/-!
# The conditioned slack hierarchy for the hyperedge model: the residual functional `Φ`, and the
decoy-free surplus margin

This module is the hyperedge form of `Percolation/Continuity/CSH/Defs.lean` and
`Percolation/Continuity/CSH/Phi.lean`.  Most of the first of those two files is already available
and is not repeated here.

WHAT IS ALREADY AVAILABLE.

* The level forms `CSH.slStep`, `CSH.slForm`, `CSH.cshMarg` and their algebra (`CSH.slForm_add`,
  `CSH.slForm_smul`, `CSH.slForm_sub`, `CSH.slForm_zero`, `CSH.slForm_cons`, `CSH.cshMarg_add`,
  `CSH.cshMarg_smul`, `CSH.cshMarg_cons`, `CSH.cshMarg_nil`, and `CSH.cshMarg_congr` of
  `CSH/PeelTools.lean`) are stated for an arbitrary evaluation type `V` and never mention a
  percolation model, so they are used verbatim.
* The model-specific data of `CSH/Defs.lean` — `avoidConst`, `decoyList`, `obsConst`, `covD`,
  `cshMargin`, `CSHHolds`, `surplus`, and the avoided forms `condMeanY`, `surplusY`,
  `surplusMarginY` with `surplusMarginY_nil` and `surplusTransferY_of_surplusMarginY_nil` — is
  already carried by `KN/HyperPeel.lean`, for a hypergraph `H : Hypergraph V E` with arbitrary
  incidence sets and with the functionals read at the vertex cluster `hyperClusterSet H ω {x}`.
* The labels meeting a vertex set (`labelsMeeting`, the analogue of `CSH.edgesOf`) and its
  monotonicity (`labelsMeeting_mono`) are in `KN/HyperCore.lean` and `KN/HyperTwoCluster.lean`, and
  the labels meeting the open cluster of a vertex set (`CTBase.cut`, the analogue of
  `HullPort.cut`) is in `KN/HyperCTBase.lean`.

WHAT IS ADDED HERE.

* LEMMA `Φ` (all of `CSH/Phi.lean`): the integrand
  `I_K(ω) = 1{s ↮ X off K} · ( g(C_s(ω ∖ cut_X(ω off K))) − g(C_s(ω off K)) )` (`phiIntegrand`,
  where "off `K`" deletes every label meeting `K`) is pointwise nonnegative and pointwise increasing
  in `K` for every monotone `g` (`phiIntegrand_nonneg`, `phiIntegrand_mono`), hence its mean
  `Φ(K)` (`phiFun`) is nonnegative and increasing (`phiFun_nonneg`, `phiFun_mono`).
  The bond proof of nonnegativity goes through the edge-cluster calculus of
  `Percolation/Literature/TwoSetExchange.lean`, which has no hyperedge counterpart; here the
  containment is proved directly, by lifting one adjacency at a time along a walk
  (`adj_lift_of_avoid`, `reachable_lift_of_avoid`, `hyperClusterSet_off_subset`).
* The decoy-free surplus margin `surplusMargin` of `CSH/Defs.lean`, which `KN/HyperPeel.lean` has
  only in its avoided form `surplusMarginY H Y`, together with `surplusMargin_nil` and the product
  form `surplusTransfer_of_surplusMargin_nil` of the surplus transfer inequality (S5).
* Two checks that nothing above is vacuous: `surplusTransfer_of_csh` derives (S5) for the
  hyperedge model from the hierarchy `CSHHolds`, and `integral_off_le_integral` derives from
  `phiFun_nonneg` the statement that closing the labels meeting a vertex set decreases the mean of
  an increasing functional of the cluster, with `phiFun_pos` exhibiting a datum at which `Φ` is
  strictly positive.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006), §1 pp. 3–5 (clusters
  in `G − Z`) and Thm. 1.1.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Site.CSHDefs

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Continuity
open scoped Classical

/-! ## Order behaviour of deletion -/

section Order

variable {V E : Type*}

/-- Deleting the labels meeting a larger vertex set leaves a smaller configuration.  Hyperedge form
of `CSH.sdiff_edgesOf_anti`. -/
theorem sdiff_labelsMeeting_anti (H : Hypergraph V E) (ω : Set E) {K K' : Set V} (h : K ⊆ K') :
    ω \ labelsMeeting H K' ⊆ ω \ labelsMeeting H K :=
  fun _ he => ⟨he.1, fun h' => he.2 (labelsMeeting_mono H h h')⟩

/-- The labels meeting the open cluster of `X` grow with the configuration.  Hyperedge form of
`CSH.cut_mono`. -/
theorem cut_mono (H : Hypergraph V E) (X : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    CTBase.cut H X ω ⊆ CTBase.cut H X ω' :=
  labelsMeeting_mono H (hyperClusterSet_mono H X h)

/-- No vertex lies in the cluster of the empty source. -/
theorem hyperClusterSet_empty_source (H : Hypergraph V E) (ω : Set E) :
    hyperClusterSet H ω (∅ : Set V) = (∅ : Set V) := by
  ext y
  constructor
  · rintro ⟨x, hx, -⟩
    exact hx.elim
  · intro h
    exact h.elim

/-- No label meets the empty vertex set. -/
theorem labelsMeeting_empty (H : Hypergraph V E) : labelsMeeting H (∅ : Set V) = (∅ : Set E) := by
  ext e
  simp only [mem_labelsMeeting, Set.mem_empty_iff_false, iff_false, not_not]
  exact Set.disjoint_empty _

end Order

/-! ## The cluster of the owner, off `K`, sits inside its cluster outside the explored set

The bond argument (`CSH.openEdgeCluster_off_subset`) reads the containment off the description of
the open edge cluster as a set of pairs.  A hyperedge configuration is a set of labels and a label
carries no pair of endpoints, so the containment is proved here for the vertex cluster by lifting
the adjacencies of a walk one at a time.
-/

section Lift

variable {V E : Type*}

/-- **One adjacency lifts.**  If the owner `s` reaches no vertex of `X` in `ν`, then an open label
of `ν` joining `a` to `b` with `a` in the cluster of `s` meets no vertex of the cluster of `X` in
`ν`, so it survives the deletion of `cut_X(ν)` and still joins `a` to `b`. -/
theorem adj_lift_of_avoid (H : Hypergraph V E) {s : V} {X : Set V} {ν ω : Set E} (hνω : ν ⊆ ω)
    (havoid : ∀ x ∈ X, ¬ (openHyperGraph H ν).Reachable s x) {a b : V}
    (hsa : (openHyperGraph H ν).Reachable s a) (hadj : (openHyperGraph H ν).Adj a b) :
    (openHyperGraph H (ω \ CTBase.cut H X ν)).Adj a b := by
  obtain ⟨hne, e, heν, ha, hb⟩ := (openHyperGraph_adj_iff H ν a b).1 hadj
  refine (openHyperGraph_adj_iff H _ a b).2 ⟨hne, e, ⟨hνω heν, ?_⟩, ha, hb⟩
  intro hcut
  rw [CTBase.cut_eq, mem_labelsMeeting] at hcut
  obtain ⟨z, hze, x, hxX, hxz⟩ := Set.not_disjoint_iff.1 hcut
  have haz : (openHyperGraph H ν).Reachable a z := by
    by_cases h : a = z
    · subst h
      exact SimpleGraph.Reachable.refl a
    · exact ((openHyperGraph_adj_iff H ν a z).2 ⟨h, e, heν, ha, hze⟩).reachable
  exact havoid x hxX (hsa.trans (haz.trans hxz.symm))

/-- **Reachability from the owner lifts**, by induction along a walk: every vertex the owner reaches
in `ν` it still reaches after the labels meeting the cluster of `X` in `ν` are deleted. -/
theorem reachable_lift_of_avoid (H : Hypergraph V E) {s : V} {X : Set V} {ν ω : Set E}
    (hνω : ν ⊆ ω) (havoid : ∀ x ∈ X, ¬ (openHyperGraph H ν).Reachable s x) {z : V}
    (h : (openHyperGraph H ν).Reachable s z) :
    (openHyperGraph H (ω \ CTBase.cut H X ν)).Reachable s z := by
  obtain ⟨p⟩ := h
  have key : ∀ (a c : V) (q : (openHyperGraph H ν).Walk a c),
      (openHyperGraph H ν).Reachable s a →
      (openHyperGraph H (ω \ CTBase.cut H X ν)).Reachable s a →
      (openHyperGraph H (ω \ CTBase.cut H X ν)).Reachable s c := by
    intro a c q
    induction q with
    | nil => intro _ h2; exact h2
    | cons hadj q' ih =>
        intro h1 h2
        exact ih (h1.trans hadj.reachable)
          (h2.trans (adj_lift_of_avoid H hνω havoid h1 hadj).reachable)
  exact key s z p (SimpleGraph.Reachable.refl s) (SimpleGraph.Reachable.refl s)

/-- **The containment behind Lemma `Φ`.**  On the event that the owner `s` reaches no vertex of `X`
off `K`, its cluster off `K` lies inside its cluster in the configuration with the labels meeting
the explored cluster of `X` deleted.  Hyperedge form of `CSH.openEdgeCluster_off_subset`. -/
theorem hyperClusterSet_off_subset (H : Hypergraph V E) (s : V) (X : Set V) {ν ω : Set E}
    (hνω : ν ⊆ ω) (havoid : ∀ x ∈ X, ¬ (openHyperGraph H ν).Reachable s x) :
    hyperClusterSet H ν ({s} : Set V) ⊆
      hyperClusterSet H (ω \ CTBase.cut H X ν) ({s} : Set V) := by
  intro z hz
  rw [mem_hyperClusterSet_singleton] at hz ⊢
  exact reachable_lift_of_avoid H hνω havoid hz

end Lift

/-! ## Lemma `Φ` -/

section Phi

variable {V E : Type*}

/-- **The integrand of Lemma `Φ` for the hyperedge model**:
`I_K(ω) = 1{s ↮ X off K} · ( g(C_s(ω ∖ cut_X(ω off K))) − g(C_s(ω off K)) )`, where "off `K`"
deletes every label meeting `K` and `C_s` is the vertex cluster of the owner.  Hyperedge form of
`CSH.phiIntegrand`. -/
def phiIntegrand (H : Hypergraph V E) (s : V) (X K : Set V) (g : Set V → ℝ) (ω : Set E) : ℝ :=
  if (∀ x ∈ X, ¬ (openHyperGraph H (ω \ labelsMeeting H K)).Reachable s x) then
    g (hyperClusterSet H (ω \ CTBase.cut H X (ω \ labelsMeeting H K)) ({s} : Set V)) -
      g (hyperClusterSet H (ω \ labelsMeeting H K) ({s} : Set V))
  else 0

/-- **Lemma `Φ`, pointwise nonnegativity**: `0 ≤ I_K(ω)` for every monotone `g`. -/
theorem phiIntegrand_nonneg (H : Hypergraph V E) (s : V) (X K : Set V) {g : Set V → ℝ}
    (hg : Monotone g) (ω : Set E) : 0 ≤ phiIntegrand H s X K g ω := by
  unfold phiIntegrand
  split_ifs with havoid
  · exact sub_nonneg.2 (hg (hyperClusterSet_off_subset H s X (fun _ he => he.1) havoid))
  · exact le_rfl

/-- **Lemma `Φ`, pointwise monotonicity**: `K ⊆ K' ⟹ I_K(ω) ≤ I_{K'}(ω)` for every monotone `g`.
Deleting more labels shrinks the explored cluster of `X`, so the cluster of `s` outside it grows;
it shrinks the cluster of `s` off `K`; and it enlarges the event `{s ↮ X off K}`, off which
`I_K = 0 ≤ I_{K'}`. -/
theorem phiIntegrand_mono (H : Hypergraph V E) (s : V) (X : Set V) {K K' : Set V} (hKK' : K ⊆ K')
    {g : Set V → ℝ} (hg : Monotone g) (ω : Set E) :
    phiIntegrand H s X K g ω ≤ phiIntegrand H s X K' g ω := by
  have hsub : ω \ labelsMeeting H K' ⊆ ω \ labelsMeeting H K := sdiff_labelsMeeting_anti H ω hKK'
  by_cases havoid : ∀ x ∈ X, ¬ (openHyperGraph H (ω \ labelsMeeting H K)).Reachable s x
  · have havoid' : ∀ x ∈ X, ¬ (openHyperGraph H (ω \ labelsMeeting H K')).Reachable s x :=
      fun x hx h => havoid x hx (h.mono (openHyperGraph_le_of_subset H hsub))
    unfold phiIntegrand
    rw [if_pos havoid, if_pos havoid']
    have h1 : g (hyperClusterSet H (ω \ CTBase.cut H X (ω \ labelsMeeting H K)) ({s} : Set V)) ≤
        g (hyperClusterSet H (ω \ CTBase.cut H X (ω \ labelsMeeting H K')) ({s} : Set V)) :=
      hg (hyperClusterSet_mono H ({s} : Set V)
        (fun _ he => ⟨he.1, fun h' => he.2 (cut_mono H X hsub h')⟩))
    have h2 : g (hyperClusterSet H (ω \ labelsMeeting H K') ({s} : Set V)) ≤
        g (hyperClusterSet H (ω \ labelsMeeting H K) ({s} : Set V)) :=
      hg (hyperClusterSet_mono H ({s} : Set V) hsub)
    linarith
  · have h0 : phiIntegrand H s X K g ω = 0 := by
      unfold phiIntegrand
      rw [if_neg havoid]
    rw [h0]
    exact phiIntegrand_nonneg H s X K' hg ω

/-- **The residual functional `Φ` of the world-wise unfolding**, hyperedge form of `CSH.phiFun`:
`Φ(K) = ∫ I_K dμ_H`. -/
def phiFun (H : Hypergraph V E) (s : V) (X : Set V) (g : Set V → ℝ) (K : Set V) : ℝ :=
  ∫ ω, phiIntegrand H s X K g ω ∂(prodBernoulli H.prob)

/-- **Lemma `Φ`(a)**: `Φ ≥ 0`. -/
theorem phiFun_nonneg (H : Hypergraph V E) (s : V) (X : Set V) {g : Set V → ℝ} (hg : Monotone g)
    (K : Set V) : 0 ≤ phiFun H s X g K :=
  integral_nonneg fun ω => phiIntegrand_nonneg H s X K hg ω

/-- **Lemma `Φ`(b)**: `Φ` is increasing, for every hypergraph and every monotone `g`. -/
theorem phiFun_mono [Fintype E] (H : Hypergraph V E) (s : V) (X : Set V) {g : Set V → ℝ}
    (hg : Monotone g) : Monotone (phiFun H s X g) := by
  intro K K' hKK'
  exact integral_mono (integrable_of_fintype _) (integrable_of_fintype _)
    fun ω => phiIntegrand_mono H s X hKK' hg ω

end Phi

/-! ## The decoy-free surplus margin -/

section Surplus

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **The surplus-transfer margin with decoys and no base avoided set**, (S5D)[T; D; o, v]:
the margin `sl^k[Sur](o) − p · sl^k[Sur](v)` of the surplus `u ↦ surplus H T r F u` for the decoy
list `decoyList H T D` and the observer constant `p = obsConst H o v (T ∪ D)`.  Hyperedge form of
`CSH.surplusMargin`; it is the case `Y = ∅` of `surplusMarginY`. -/
def surplusMargin (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (D : List V) (o v : V)
    (F : Set V → ℝ) : ℝ :=
  CSH.cshMarg (decoyList H (↑T : Set V) D) (obsConst H o v ((↑T : Set V) ∪ {d | d ∈ D})) o v
    (surplus H T r F)

/-- The decoy-free margin is the avoided margin with `Y = ∅`. -/
theorem surplusMarginY_empty (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (D : List V)
    (o v : V) (F : Set V → ℝ) :
    surplusMarginY H ∅ T r D o v F = surplusMargin H T r D o v F := by
  have hfun : surplusY H ∅ T r F = surplus H T r F :=
    funext fun u => surplusY_empty H T r F u
  rw [surplusMarginY, surplusMargin, Set.empty_union, hfun]

/-- **(S5D) with no decoys is (S5) divided by `P(v ↮ T)`.**  Hyperedge form of
`CSH.surplusMargin_nil`. -/
theorem surplusMargin_nil (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (o v : V)
    (F : Set V → ℝ) :
    surplusMargin H T r [] o v F =
      surplus H T r F o -
        (prodBernoulli H.prob).real
            (avoidEvent H ({v} : Set V) (↑T : Set V) ∩ hyperConn H o v) /
            (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V)) *
          surplus H T r F v := by
  simp only [surplusMargin, decoyList, CSH.cshMarg_nil, obsConst, List.not_mem_nil, setOf_false,
    union_empty]

/-- **The surplus transfer inequality (S5) from the decoy-free margin**, product form:
`P(v ↮ T, o ↔ v) · Sur_v(T) ≤ P(v ↮ T) · Sur_o(T)`.  Hyperedge form of
`CSH.surplusTransfer_of_surplusMargin_nil`. -/
theorem surplusTransfer_of_surplusMargin_nil (H : Hypergraph V E) (T : Finset V) (r : V → ℕ)
    (o v : V) (F : Set V → ℝ)
    (hpos : 0 < (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V)))
    (h : 0 ≤ surplusMargin H T r [] o v F) :
    (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V) ∩ hyperConn H o v) *
        surplus H T r F v ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V)) * surplus H T r F o := by
  have hY : ∅ ∪ (↑T : Set V) = (↑T : Set V) := Set.empty_union _
  have h' := surplusTransferY_of_surplusMarginY_nil H ∅ T r o v F (by rwa [hY])
    (by rwa [surplusMarginY_empty])
  rw [hY] at h'
  simpa only [surplusY_empty] using h'

end Surplus

/-! ## Non-vacuity: (S5) for the hyperedge model from the hierarchy -/

section Check

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **The surplus transfer inequality (S5) for the hyperedge model, from `CSHHolds`.**  For
nondegenerate label probabilities, observers `o ≠ v` outside the relay set, a relay set `T` carrying
an injective rank compatible with the unconditioned relay means, and an increasing `F`,
`P(v ↮ T, o ↔ v) · Sur_v(T) ≤ P(v ↮ T) · Sur_o(T)`.  This is the specialization `Y = ∅`, `D = []`
of `surplusMarginY_nonneg_of_csh`, and it is the hypothesis shape that
`AGloc.gen_firstRank_of_surplusTransfer` consumes in the bond development. -/
theorem surplusTransfer_of_csh (H : Hypergraph V E) (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1)
    (o v : V)
    (hCSH : ∀ (x : V) (Y' : Set V) (D : List V),
      x ∉ Y' → o ≠ x → v ≠ x → o ∉ Y' → v ∉ Y' → D.Nodup →
      (∀ d ∈ D, d ≠ x ∧ d ∉ Y' ∧ d ≠ o ∧ d ≠ v) → CSHHolds H x Y' D o v)
    (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (hF : ∀ S S' : Set V, S ⊆ S' → F S ≤ F S')
    (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' → condMeanY H ∅ F a ≤ condMeanY H ∅ F a')
    (hoT : o ∉ T) (hvT : v ∉ T) :
    (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V) ∩ hyperConn H o v) *
        surplus H T r F v ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V)) *
        surplus H T r F o := by
  have hvTset : v ∉ (↑T : Set V) := fun h => hvT (Finset.mem_coe.1 h)
  have hpos : 0 < (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (↑T : Set V)) :=
    prodBernoulli_real_pos_of_nonempty hp ⟨∅, empty_mem_avoidEvent H hvTset⟩
  refine surplusTransfer_of_surplusMargin_nil H T r o v F hpos ?_
  rw [← surplusMarginY_empty]
  exact surplusMarginY_nonneg_of_csh H hp ∅ o v (Set.notMem_empty o) (Set.notMem_empty v) hCSH
    T r [] F hF hr hcompat (fun a _ => Set.notMem_empty a) hoT hvT List.nodup_nil
    (fun d hd => absurd hd (List.not_mem_nil))

end Check

/-! ## Non-vacuity: what `Φ` computes -/

section PhiCheck

variable {V E : Type*}

/-- With no avoided set the indicator in the integrand of Lemma `Φ` is identically one and the
explored cluster is empty, so `I_K(ω) = g(C_s(ω)) − g(C_s(ω off K))`. -/
theorem phiIntegrand_empty_avoided (H : Hypergraph V E) (s : V) (K : Set V) (g : Set V → ℝ)
    (ω : Set E) :
    phiIntegrand H s ∅ K g ω =
      g (hyperClusterSet H ω ({s} : Set V)) -
        g (hyperClusterSet H (ω \ labelsMeeting H K) ({s} : Set V)) := by
  have hcut : CTBase.cut H (∅ : Set V) (ω \ labelsMeeting H K) = (∅ : Set E) := by
    rw [CTBase.cut_eq, hyperClusterSet_empty_source, labelsMeeting_empty]
  unfold phiIntegrand
  rw [if_pos (fun x hx => hx.elim), hcut, Set.sdiff_empty]

/-- With no avoided set, `Φ(K) = E g(C_s) − E g(C_s off K)`. -/
theorem phiFun_empty_avoided [Fintype E] (H : Hypergraph V E) (s : V) (g : Set V → ℝ)
    (K : Set V) :
    phiFun H s ∅ g K =
      (∫ ω, g (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob)) -
        ∫ ω, g (hyperClusterSet H (ω \ labelsMeeting H K) ({s} : Set V))
          ∂(prodBernoulli H.prob) := by
  unfold phiFun
  simp only [phiIntegrand_empty_avoided]
  exact integral_sub (integrable_of_fintype _) (integrable_of_fintype _)

/-- **A known inequality out of Lemma `Φ`(a).**  Closing every label that meets a vertex set can
only decrease the mean of an increasing functional of the cluster of `s`.  This is
`phiFun_nonneg` read at the empty avoided set. -/
theorem integral_off_le_integral [Fintype E] (H : Hypergraph V E) (s : V) {g : Set V → ℝ}
    (hg : Monotone g) (K : Set V) :
    (∫ ω, g (hyperClusterSet H (ω \ labelsMeeting H K) ({s} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω, g (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob) := by
  have h := phiFun_nonneg H s ∅ hg K
  rw [phiFun_empty_avoided] at h
  linarith

/-- The functional `C ↦ 1{t ∈ C}` of the cluster. -/
def reachMarker (t : V) : Set V → ℝ := fun C => if t ∈ C then 1 else 0

/-- `reachMarker t` is monotone. -/
theorem reachMarker_mono (t : V) : Monotone (reachMarker t) := by
  intro C C' h
  unfold reachMarker
  by_cases hC : t ∈ C
  · rw [if_pos hC, if_pos (h hC)]
  · rw [if_neg hC]
    split_ifs <;> norm_num

/-- With no open label incident to `t`, the only vertex `t` reaches is `t`. -/
theorem eq_of_reachable_of_isolated (H : Hypergraph V E) {ν : Set E} {t z : V}
    (hiso : ∀ e ∈ ν, t ∉ H.incidence e) (h : (openHyperGraph H ν).Reachable t z) : z = t := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj q =>
      obtain ⟨-, e, he, ht, -⟩ := (openHyperGraph_adj_iff H ν _ _).1 hadj
      exact absurd ht (hiso e he)

/-- The mean of `reachMarker t` at the cluster of `s` is the probability of `{s ↔ t}`. -/
theorem integral_reachMarker [Fintype E] (H : Hypergraph V E) (s t : V) :
    (∫ ω, reachMarker t (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob)) =
      (prodBernoulli H.prob).real (hyperConn H s t) := by
  have hfun : (fun ω : Set E => reachMarker t (hyperClusterSet H ω ({s} : Set V)))
      = Set.indicator (hyperConn H s t) (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : (openHyperGraph H ω).Reachable s t
    · rw [Set.indicator_of_mem (show ω ∈ hyperConn H s t from h)]
      unfold reachMarker
      rw [if_pos ((mem_hyperClusterSet_singleton H ω s t).2 h)]
    · rw [Set.indicator_of_notMem (show ω ∉ hyperConn H s t from h)]
      unfold reachMarker
      rw [if_neg fun hm => h ((mem_hyperClusterSet_singleton H ω s t).1 hm)]
  rw [hfun, integral_indicator (measurableSet_of_fintype _), setIntegral_const, smul_eq_mul,
    mul_one]

/-- Off `{t}` the vertex `t` is isolated, so a distinct owner never reaches it. -/
theorem reachMarker_off_self (H : Hypergraph V E) (s t : V) (hst : s ≠ t) (ω : Set E) :
    reachMarker t (hyperClusterSet H (ω \ labelsMeeting H ({t} : Set V)) ({s} : Set V)) = 0 := by
  unfold reachMarker
  rw [if_neg]
  intro hmem
  have hreach := (mem_hyperClusterSet_singleton H _ s t).1 hmem
  have hiso : ∀ e ∈ ω \ labelsMeeting H ({t} : Set V), t ∉ H.incidence e := by
    intro e he ht
    exact he.2 ((mem_labelsMeeting H _ e).2 (Set.not_disjoint_iff.2 ⟨t, ht, rfl⟩))
  exact hst (eq_of_reachable_of_isolated H hiso hreach.symm)

/-- **What `Φ` computes at a marker.**  For distinct `s` and `t`, `Φ` at the owner `s`, no avoided
set, the functional `C ↦ 1{t ∈ C}` and `K = {t}` is exactly `P(s ↔ t)`: the second term of the
integrand vanishes because `t` is isolated once every label incident to it is closed. -/
theorem phiFun_reachMarker [Fintype E] (H : Hypergraph V E) (s t : V) (hst : s ≠ t) :
    phiFun H s ∅ (reachMarker t) ({t} : Set V)
      = (prodBernoulli H.prob).real (hyperConn H s t) := by
  have hzero : (∫ ω, reachMarker t
      (hyperClusterSet H (ω \ labelsMeeting H ({t} : Set V)) ({s} : Set V))
      ∂(prodBernoulli H.prob)) = 0 := by
    rw [funext (reachMarker_off_self H s t hst)]
    simp
  rw [phiFun_empty_avoided, integral_reachMarker, hzero, sub_zero]

/-- **`Φ` is not identically zero.**  For nondegenerate label probabilities, distinct `s` and `t`
and a configuration joining them, `Φ` at that datum is `P(s ↔ t) > 0`. -/
theorem phiFun_pos [Fintype E] (H : Hypergraph V E) (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1)
    (s t : V) (hst : s ≠ t) (hne : (hyperConn H s t).Nonempty) :
    0 < phiFun H s ∅ (reachMarker t) ({t} : Set V) := by
  rw [phiFun_reachMarker H s t hst]
  exact prodBernoulli_real_pos_of_nonempty hp hne

/-- Two vertices and one label incident to both, open with probability `1/2`. -/
private def twoPointHyper : Hypergraph Bool Unit where
  incidence := fun _ => Set.univ
  prob := fun _ => Percolation.Literature.half

/-- **A datum at which `Φ` is strictly positive.**  In the two-vertex model with one label incident
to both vertices, `Φ` at the owner `false`, no avoided set, the functional `C ↦ 1{true ∈ C}` and
`K = {true}` is the probability that the two vertices are joined, which is positive.  So neither
`phiFun_nonneg` nor the definitions it rests on are vacuous. -/
theorem phiFun_pos_twoPoint :
    0 < phiFun twoPointHyper false ∅ (reachMarker true) ({true} : Set Bool) := by
  have hcoe : ∀ e : Unit, ((twoPointHyper.prob e : unitInterval) : ℝ) = 1 / 2 := fun _ => rfl
  refine phiFun_pos twoPointHyper (fun e => ⟨?_, ?_⟩) false true (by decide) ⟨Set.univ, ?_⟩
  · exact unitInterval.coe_pos.1 (by rw [hcoe e]; norm_num)
  · exact unitInterval.coe_lt_one.1 (by rw [hcoe e]; norm_num)
  · show (openHyperGraph twoPointHyper (Set.univ : Set Unit)).Reachable false true
    exact ((openHyperGraph_adj_iff twoPointHyper _ false true).2
      ⟨by decide, (), Set.mem_univ _, Set.mem_univ _, Set.mem_univ _⟩).reachable

end PhiCheck

end KNAll.Site.CSHDefs

end

#print axioms KNAll.Site.CSHDefs.phiFun_nonneg
#print axioms KNAll.Site.CSHDefs.phiFun_mono
#print axioms KNAll.Site.CSHDefs.hyperClusterSet_off_subset
#print axioms KNAll.Site.CSHDefs.surplusMargin_nil
#print axioms KNAll.Site.CSHDefs.surplusTransfer_of_surplusMargin_nil
#print axioms KNAll.Site.CSHDefs.surplusTransfer_of_csh
#print axioms KNAll.Site.CSHDefs.integral_off_le_integral
#print axioms KNAll.Site.CSHDefs.phiFun_reachMarker
#print axioms KNAll.Site.CSHDefs.phiFun_pos
#print axioms KNAll.Site.CSHDefs.phiFun_pos_twoPoint
