import Hypergraph.HyperTreeHK
import Hypergraph.HyperAGBase
import Hypergraph.BondRepresentation

/-!
# Layer one of the correlation core, for hyperedges

The hyperedge port of four modules of the bond development:
`Percolation/Continuity/CovTau/StarNPrelim.lean`,
`Percolation/Continuity/HullPort/DeletedEdges.lean`,
`Percolation/Continuity/CovTau/A2Defs.lean` and
`Percolation/Continuity/LowerTail/SurplusTransferPairTools.lean`.

Everything is stated for a `Hypergraph V E` with arbitrary incidence sets over arbitrary types,
finiteness being assumed only where it is used; the two measure-theoretic sections are stated for
an arbitrary finite index type.

## The world `H − W`, and the hybrid along the exploration

`off H W ω` closes every label incident to a vertex of `W`.  The bond `off W K = K.filter (∀ w ∈ e,
w ∉ W)` deletes a pair as soon as ONE of its two endpoints lies in `W`, so its hyperedge form
deletes a label as soon as its incidence set MEETS `W`, that is `ω \ labelsMeeting H W`.  Nothing
weaker will do: a label can join two vertices outside `W` while a third of its vertices lies in
`W`, and such a label must be closed, because on the other side of the congruence it is a label the
exploration has already queried.  This is the same incidence rule as `mem_revealedBy_iff` of
`KN/HyperTreeHK.lean` and `labelsMeeting` of `KN/HyperCore.lean`.

* `reachable_congr_of_agree`, `hyperClusterSet_congr_of_agree`, `recordAt_congr_of_agree` — if `W`
  is closed under the open labels of `ω` and `ω, ω'` agree on every label meeting `W`, then a
  source inside `W` has the same cluster, and the same exploration record, in both;
* `reachable_spliceRecord_of_mem` / `reachable_spliceRecord_of_not_mem` — the two halves of the
  Markov property at the explored cluster: from inside the cluster of `S` the splice
  `spliceRecord (recordAt H S ω)` looks like `ω`, from outside it looks like `off H (C_S ω)`
  [VandenbergHaggstromKahn2005, eq. (6)];
* `cE_clusterFun_of_mem`, `cE_clusterFun_of_not_mem`, `cE_clusterFun_eq_deleteHyper` — what those
  two say about the conditional expectation `cE` of `KN/HyperCTBase.lean`: for a vertex inside the
  explored cluster it collapses, and for a vertex outside it is the mean in the residual model, so
  it is the subtracted term of `projFun` of `KN/HyperProjGen.lean`.

## Deleting labels

`sum_weight_mul_comp_sdiff` and `integral_comp_sdiff_prodBernoulli` say that the law of `ω \ B`
under `prodBernoulli p` is `prodBernoulli` with the parameters of `B` switched off.  The bond file
carries this for `ι = Sym2 V`; it mentions no graph, and the port is the same statement for an
arbitrary finite index type.  `integral_eq_integral_inter_of_zero` is the measure form of the bond
`ED_univ_eq_ED_of_zero`: parameters vanishing off a coordinate set restrict the mean to that set.
What is new is the consequence `delE_eq_integral_deleteHyper`, which identifies the mean `delE` of
`KN/HyperCTBase.lean` in the model with the labels meeting a vertex set deleted with the mean under
the parameters of `deleteHyper` of `KN/HyperCore.lean`.

The remaining bond bridges of `StarNPrelim.lean` are already in the hyperedge development:
`integral_eq_ED` is `TreeHK.integral_eq_sum_wtW`, `measureReal_eq_ED` is `TreeHK.PrW_univ_eq_real`,
and `setIntegral_eq_ED` is `AGBase.integral_mul_ind` read through the first of those.

## The functionals of the two-source inequality

`rest`, and the elementary properties of the cluster `rCluster` of a source set in the model
induced on a vertex set.  Most of the bond `A2Defs.lean` is already in the hyperedge development:
`rCluster`, `rAvoid`, `labelsIn` are those of `KN/HyperOneCluster.lean` and the bond `oInd` is
`indMem` of `KN/HyperAGBase.lean` evaluated at the vertex cluster.

## The three transfer tools of the two-relay surplus step

`ordTransfer`, `blockHarrisTransfer` and `plusPiece_nonneg`.  The bond file reads them off the
two-SET exchange inequality of `Percolation/Literature/TwoSetExchange.lean`; here they are read off
`avoid_twoCluster_le` of `KN/HyperTwoCluster.lean`, whose hypothesis is discharged by
`oneClusterInequality_holds`.  Two things had to be added.

`avoid_sameCluster_negCorrelation`: the bond `ordTransfer` needs an increasing and a DECREASING
functional of the SAME cluster to be negatively correlated on the avoidance event, which is not an
instance of `avoid_twoCluster_le`, whose two functionals must both be increasing in the first
cluster.  It is the instance of `avoid_twoCluster_le` at the pair `(F, −G)`.

`avoid_twoCluster_sub_le`: the bond `blockHarrisTransfer` conditions on `{v ↮ a} ∩ {v ↮ b}` and
integrates a functional of the cluster of `a` alone.  In the bond development that functional is
read off the EDGE cluster of `{a, b}`, from which the cluster of `a` is recovered
(`openCluster_biUnion_eq`); the hyperedge conditional association theorems are stated for the
VERTEX cluster, and the cluster of `a` is not a function of the vertex cluster of `{a, b}`.  What
replaces the recovery is the observation that the recombination of `KN/HyperTwoCluster.lean` never
uses the avoided set beyond two facts: that the cluster of the source avoids it, and that the
cluster read on the other side is unchanged when the labels meeting the source cluster are
discarded.  Both survive when the functional is taken at the cluster of a SUBSET `T' ⊆ T` of the
avoided set, and `avoid_twoCluster_sub_le` is the resulting inequality.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Struct. Alg. 29 (2006), Thms. 1.3–1.5, Thm. 2.1.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
-/

noncomputable section

namespace KNAll.Site.CTOne

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.CTBase KNAll.Site.AGBase
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V E : Type*}

/-! ## The world `H − W`: closing every label incident to a vertex set -/

/-- The configuration `ω` with every label incident to a vertex of `W` closed: the hyperedge form
of the bond `off W K`, in which a pair is deleted as soon as one of its endpoints lies in `W`. -/
def off (H : Hypergraph V E) (W : Set V) (ω : Set E) : Set E := ω \ labelsMeeting H W

/-- Membership in `off`, in incidence form. -/
theorem mem_off {H : Hypergraph V E} {W : Set V} {ω : Set E} {e : E} :
    e ∈ off H W ω ↔ e ∈ ω ∧ Disjoint (H.incidence e) W := by
  simp only [off, Set.mem_sdiff, mem_labelsMeeting, not_not]

/-- Membership in `off`, vertex by vertex: this is the literal transcription of the bond
`e ∈ K ∧ ∀ w ∈ e, w ∉ W`. -/
theorem mem_off_iff_forall {H : Hypergraph V E} {W : Set V} {ω : Set E} {e : E} :
    e ∈ off H W ω ↔ e ∈ ω ∧ ∀ v ∈ H.incidence e, v ∉ W := by
  rw [mem_off]
  exact and_congr_right fun _ =>
    ⟨fun h v hv => Set.disjoint_left.1 h hv, fun h => Set.disjoint_left.2 fun v hv => h v hv⟩

@[simp] theorem off_empty (H : Hypergraph V E) (ω : Set E) : off H (∅ : Set V) ω = ω := by
  ext e
  simp [mem_off]

theorem off_subset (H : Hypergraph V E) (W : Set V) (ω : Set E) : off H W ω ⊆ ω :=
  Set.sdiff_subset

theorem off_mono (H : Hypergraph V E) (W : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    off H W ω ⊆ off H W ω' := Set.sdiff_subset_sdiff_left h

/-! ## Cluster congruence

If `W` is closed under the open labels of `ω`, and `ω` and `ω'` agree on every label whose
incidence set meets `W`, then the two configurations look the same from inside `W`.
-/

section Congr

variable {H : Hypergraph V E} {ω ω' : Set E} {W : Set V}

/-- A walk out of a set closed under the open labels of `ω` stays inside it. -/
theorem mem_of_reachable_closed
    (hcl : ∀ e ∈ ω, ∀ a ∈ H.incidence e, a ∈ W → H.incidence e ⊆ W)
    {x z : V} (hx : x ∈ W) (h : (openHyperGraph H ω).Reachable x z) : z ∈ W := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hx
  | @cons a b c hadj p ih =>
      obtain ⟨-, e, he, hae, hbe⟩ := (openHyperGraph_adj_iff H ω a b).1 hadj
      exact ih (hcl e he a hae hx hbe)

/-- One direction of the congruence: a walk out of `W` is open in any configuration agreeing with
`ω` on the labels meeting `W`. -/
theorem reachable_of_agree
    (hcl : ∀ e ∈ ω, ∀ a ∈ H.incidence e, a ∈ W → H.incidence e ⊆ W)
    (hag : ∀ e : E, ¬ Disjoint (H.incidence e) W → (e ∈ ω ↔ e ∈ ω'))
    {x z : V} (hx : x ∈ W) (h : (openHyperGraph H ω).Reachable x z) :
    (openHyperGraph H ω').Reachable x z := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj p ih =>
      obtain ⟨hne, e, he, hae, hbe⟩ := (openHyperGraph_adj_iff H ω a b).1 hadj
      have hmeet : ¬ Disjoint (H.incidence e) W := Set.not_disjoint_iff.2 ⟨a, hae, hx⟩
      have hsub : H.incidence e ⊆ W := hcl e he a hae hx
      have hadj' : (openHyperGraph H ω').Adj a b :=
        (openHyperGraph_adj_iff H ω' a b).2 ⟨hne, e, (hag e hmeet).1 he, hae, hbe⟩
      exact hadj'.reachable.trans (ih (hsub hbe))

/-- **Cluster congruence.**  From a vertex of `W` the two configurations reach the same
vertices. -/
theorem reachable_congr_of_agree
    (hcl : ∀ e ∈ ω, ∀ a ∈ H.incidence e, a ∈ W → H.incidence e ⊆ W)
    (hag : ∀ e : E, ¬ Disjoint (H.incidence e) W → (e ∈ ω ↔ e ∈ ω'))
    {x : V} (hx : x ∈ W) (z : V) :
    (openHyperGraph H ω).Reachable x z ↔ (openHyperGraph H ω').Reachable x z := by
  have hcl' : ∀ e ∈ ω', ∀ a ∈ H.incidence e, a ∈ W → H.incidence e ⊆ W := fun e he a hae ha =>
    hcl e ((hag e (Set.not_disjoint_iff.2 ⟨a, hae, ha⟩)).2 he) a hae ha
  exact ⟨fun h => reachable_of_agree hcl hag hx h,
    fun h => reachable_of_agree hcl' (fun e hm => (hag e hm).symm) hx h⟩

/-- The cluster of a source set inside `W` is the same in both configurations. -/
theorem hyperClusterSet_congr_of_agree
    (hcl : ∀ e ∈ ω, ∀ a ∈ H.incidence e, a ∈ W → H.incidence e ⊆ W)
    (hag : ∀ e : E, ¬ Disjoint (H.incidence e) W → (e ∈ ω ↔ e ∈ ω'))
    {S : Set V} (hS : S ⊆ W) :
    hyperClusterSet H ω S = hyperClusterSet H ω' S := by
  ext y
  constructor
  · rintro ⟨s, hs, hr⟩
    exact ⟨s, hs, (reachable_congr_of_agree hcl hag (hS hs) y).1 hr⟩
  · rintro ⟨s, hs, hr⟩
    exact ⟨s, hs, (reachable_congr_of_agree hcl hag (hS hs) y).2 hr⟩

/-- **Record congruence.**  The exploration of a source set inside `W` leaves the same record in
both configurations: it reaches the same vertices, and the labels it queries all meet `W`, so the
two configurations agree on every answer it receives. -/
theorem recordAt_congr_of_agree
    (hcl : ∀ e ∈ ω, ∀ a ∈ H.incidence e, a ∈ W → H.incidence e ⊆ W)
    (hag : ∀ e : E, ¬ Disjoint (H.incidence e) W → (e ∈ ω ↔ e ∈ ω'))
    {S : Set V} (hS : S ⊆ W) :
    recordAt H S ω = recordAt H S ω' := by
  have hC : hyperClusterSet H ω S = hyperClusterSet H ω' S :=
    hyperClusterSet_congr_of_agree hcl hag hS
  have hCW : hyperClusterSet H ω S ⊆ W := by
    rintro y ⟨s, hs, hr⟩
    exact mem_of_reachable_closed hcl (hS hs) hr
  have hmeet : ∀ e : E, e ∈ labelsMeeting H (hyperClusterSet H ω S) →
      ¬ Disjoint (H.incidence e) W := by
    intro e he
    obtain ⟨y, hy, hyC⟩ := Set.not_disjoint_iff.1 he
    exact Set.not_disjoint_iff.2 ⟨y, hy, hCW hyC⟩
  refine ExplorationRecord.ext' (by simpa using hC) ?_ ?_
  · show ω ∩ labelsMeeting H (hyperClusterSet H ω S)
      = ω' ∩ labelsMeeting H (hyperClusterSet H ω' S)
    rw [← hC]
    ext e
    exact ⟨fun h => ⟨(hag e (hmeet e h.2)).1 h.1, h.2⟩,
      fun h => ⟨(hag e (hmeet e h.2)).2 h.1, h.2⟩⟩
  · show labelsMeeting H (hyperClusterSet H ω S) \ ω
      = labelsMeeting H (hyperClusterSet H ω' S) \ ω'
    rw [← hC]
    ext e
    exact ⟨fun h => ⟨h.1, fun hc => h.2 ((hag e (hmeet e h.1)).2 hc)⟩,
      fun h => ⟨h.1, fun hc => h.2 ((hag e (hmeet e h.1)).1 hc)⟩⟩

end Congr

/-! ## The hybrid along the exploration of the cluster of `S` -/

/-- An open label incident to the cluster of `S` has all of its vertices in that cluster.  This is
the closure hypothesis of the congruence lemmas at `W = C_S`, and it is the reason `labelsMeeting`
is the right notion of a deleted label. -/
theorem incidence_subset_hyperClusterSet {H : Hypergraph V E} {ω : Set E} {S : Set V} {e : E}
    (he : e ∈ ω) {a : V} (hae : a ∈ H.incidence e) (ha : a ∈ hyperClusterSet H ω S) :
    H.incidence e ⊆ hyperClusterSet H ω S := by
  intro b hbe
  by_cases hab : a = b
  · exact hab ▸ ha
  · exact hyperClusterSet_mem_of_adj H ω S ha
      ((openHyperGraph_adj_iff H ω a b).2 ⟨hab, e, he, hae, hbe⟩)

/-- The splice keeps the recorded answer on a label incident to the explored cluster. -/
theorem mem_spliceRecord_of_meeting (H : Hypergraph V E) (S : Set V) (ω η : Set E) {e : E}
    (he : e ∈ labelsMeeting H (hyperClusterSet H ω S)) :
    e ∈ spliceRecord (recordAt H S ω) η ↔ e ∈ ω := by
  simp only [spliceRecord, Set.mem_union, Set.mem_sdiff, recordAt_openLabels, queried_recordAt,
    Set.mem_inter_iff]
  exact ⟨fun h => h.elim (fun h => h.1) (fun h => absurd he h.2), fun h => Or.inl ⟨h, he⟩⟩

/-- The splice reads a label not incident to the explored cluster off the resampled
configuration. -/
theorem mem_spliceRecord_of_not_meeting (H : Hypergraph V E) (S : Set V) (ω η : Set E) {e : E}
    (he : e ∉ labelsMeeting H (hyperClusterSet H ω S)) :
    e ∈ spliceRecord (recordAt H S ω) η ↔ e ∈ η := by
  simp only [spliceRecord, Set.mem_union, Set.mem_sdiff, recordAt_openLabels, queried_recordAt,
    Set.mem_inter_iff]
  exact ⟨fun h => h.elim (fun h => absurd h.2 he) (fun h => h.1), fun h => Or.inr ⟨h, he⟩⟩

/-- **Inside the explored cluster nothing changes.**  From a vertex of the cluster of `S` the
hybrid `spliceRecord (recordAt H S ω) η` reaches exactly what `ω` reaches.
[cite: VandenbergHaggstromKahn2005, eq. (6) (p. 4)] -/
theorem reachable_spliceRecord_of_mem (H : Hypergraph V E) (S : Set V) (ω η : Set E) {x : V}
    (hx : x ∈ hyperClusterSet H ω S) (z : V) :
    (openHyperGraph H ω).Reachable x z ↔
      (openHyperGraph H (spliceRecord (recordAt H S ω) η)).Reachable x z := by
  refine reachable_congr_of_agree (W := hyperClusterSet H ω S)
    (fun e he a hae ha => incidence_subset_hyperClusterSet he hae ha) (fun e hm => ?_) hx z
  exact (mem_spliceRecord_of_meeting H S ω η hm).symm

/-- The cluster of a vertex inside the explored cluster is unchanged by the splice. -/
theorem hyperClusterSet_spliceRecord_of_mem (H : Hypergraph V E) (S : Set V) (ω η : Set E)
    {x : V} (hx : x ∈ hyperClusterSet H ω S) :
    hyperClusterSet H (spliceRecord (recordAt H S ω) η) ({x} : Set V)
      = hyperClusterSet H ω ({x} : Set V) := by
  refine (hyperClusterSet_congr_of_agree (W := hyperClusterSet H ω S)
    (fun e he a hae ha => incidence_subset_hyperClusterSet he hae ha) (fun e hm => ?_)
    (Set.singleton_subset_iff.2 hx)).symm
  exact (mem_spliceRecord_of_meeting H S ω η hm).symm

/-- **Outside the explored cluster one sees the resampled configuration with the labels incident
to the cluster closed.**  From a vertex outside the cluster of `S` the hybrid reaches exactly what
`off H (C_S ω) η` reaches.  The hyperedge point is in the second case of the agreement: a label
that meets the cluster and is open in `ω` has ALL of its vertices in the cluster, so it cannot be
seen from outside at all.  [cite: VandenbergHaggstromKahn2005, eq. (6) (p. 4)] -/
theorem reachable_spliceRecord_of_not_mem (H : Hypergraph V E) (S : Set V) (ω η : Set E) {x : V}
    (hx : x ∉ hyperClusterSet H ω S) (z : V) :
    (openHyperGraph H (off H (hyperClusterSet H ω S) η)).Reachable x z ↔
      (openHyperGraph H (spliceRecord (recordAt H S ω) η)).Reachable x z := by
  set C := hyperClusterSet H ω S with hC
  have hcl : ∀ e ∈ off H C η, ∀ a ∈ H.incidence e, a ∈ Cᶜ → H.incidence e ⊆ Cᶜ := by
    intro e he _ _ _ b hbe
    exact Set.disjoint_left.1 (mem_off.1 he).2 hbe
  have hag : ∀ e : E, ¬ Disjoint (H.incidence e) Cᶜ →
      (e ∈ off H C η ↔ e ∈ spliceRecord (recordAt H S ω) η) := by
    intro e hm
    obtain ⟨y, hye, hyC⟩ := Set.not_disjoint_iff.1 hm
    by_cases hmeet : e ∈ labelsMeeting H C
    · have hnot : e ∉ off H C η := fun h => (mem_labelsMeeting H C e).1 hmeet (mem_off.1 h).2
      refine ⟨fun h => absurd h hnot, fun h => ?_⟩
      exfalso
      have heω : e ∈ ω := (mem_spliceRecord_of_meeting H S ω η hmeet).1 h
      obtain ⟨c, hce, hcC⟩ := Set.not_disjoint_iff.1 hmeet
      exact hyC (incidence_subset_hyperClusterSet heω hce hcC hye)
    · rw [mem_off, mem_spliceRecord_of_not_meeting H S ω η hmeet]
      have hdisj : Disjoint (H.incidence e) C := not_not.1 hmeet
      exact ⟨fun h => h.1, fun h => ⟨h, hdisj⟩⟩
  exact reachable_congr_of_agree hcl hag (Set.mem_compl hx) z

/-- The cluster of a vertex outside the explored cluster, read at the splice, is its cluster in
the deleted configuration. -/
theorem hyperClusterSet_spliceRecord_of_not_mem (H : Hypergraph V E) (S : Set V) (ω η : Set E)
    {x : V} (hx : x ∉ hyperClusterSet H ω S) :
    hyperClusterSet H (spliceRecord (recordAt H S ω) η) ({x} : Set V)
      = hyperClusterSet H (off H (hyperClusterSet H ω S) η) ({x} : Set V) := by
  ext y
  simp only [hyperClusterSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, hr⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨s, rfl, (reachable_spliceRecord_of_not_mem H S ω η hx y).2 hr⟩
  · rintro ⟨s, hs, hr⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨s, rfl, (reachable_spliceRecord_of_not_mem H S ω η hx y).1 hr⟩


/-! ## What the hybrid says about the conditional expectation `cE` -/

/-- **A cluster functional inside the explored cluster is its own conditional expectation.**  The
bond `cE_clusterFun` of `KN/HyperCTBase.lean` is the case `x ∈ S`; here `x` is any vertex the
exploration reached. -/
theorem cE_clusterFun_of_mem [Fintype E] (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ)
    (ω : Set E) {x : V} (hx : x ∈ hyperClusterSet H ω S) :
    cE H S (fun ν => F (hyperClusterSet H ν ({x} : Set V))) ω
      = F (hyperClusterSet H ω ({x} : Set V)) := by
  have hpt : ∀ η : Set E,
      F (hyperClusterSet H (spliceRecord (recordAt H S ω) η) ({x} : Set V))
        = F (hyperClusterSet H ω ({x} : Set V)) := fun η => by
    rw [hyperClusterSet_spliceRecord_of_mem H S ω η hx]
  show (∫ η, F (hyperClusterSet H (spliceRecord (recordAt H S ω) η) ({x} : Set V))
      ∂(prodBernoulli H.prob)) = _
  simp only [hpt]
  simp

/-- **A cluster functional outside the explored cluster has for conditional expectation its mean
in the model with the queried labels deleted.**  This is the link between the `cE` calculus and the
functionals `delE`, `cut` of `KN/HyperCTBase.lean`. -/
theorem cE_clusterFun_of_not_mem [Fintype E] (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ)
    (ω : Set E) {x : V} (hx : x ∉ hyperClusterSet H ω S) :
    cE H S (fun ν => F (hyperClusterSet H ν ({x} : Set V))) ω
      = delE H (cut H S ω) (fun η => F (hyperClusterSet H η ({x} : Set V))) := by
  show (∫ η, F (hyperClusterSet H (spliceRecord (recordAt H S ω) η) ({x} : Set V))
      ∂(prodBernoulli H.prob))
    = ∫ η, F (hyperClusterSet H (η \ cut H S ω) ({x} : Set V)) ∂(prodBernoulli H.prob)
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  show F (hyperClusterSet H (spliceRecord (recordAt H S ω) η) ({x} : Set V))
      = F (hyperClusterSet H (η \ cut H S ω) ({x} : Set V))
  rw [hyperClusterSet_spliceRecord_of_not_mem H S ω η hx]
  rfl

/-! ## Deleting labels is switching their parameters off

The content of the bond `HullPort/DeletedEdges.lean`.  Nothing in it is about a graph: the index
type is arbitrary and finite.
-/

section Deleted

variable {ι : Type*} [Fintype ι]

/-- One coordinate: the law of `η ∖ {i}` is the product law with the coordinate `i` switched
off. -/
theorem sum_weight_mul_comp_sdiff_singleton (w : ι → ℝ) (i : ι) (φ : Set ι → ℝ) :
    ∑ η, BHK2006.weight w η * φ (η \ {i})
      = ∑ η, BHK2006.weight (fun j => if j = i then 0 else w j) η * φ η := by
  classical
  set w₀ : ι → ℝ := fun j => if j = i then 0 else w j with hw₀
  set R : Set ι → ℝ := fun η => ∏ j ∈ Finset.univ.erase i, (if j ∈ η then w j else 1 - w j) with hR
  have hfac : ∀ η : Set ι, BHK2006.weight w η = (if i ∈ η then w i else 1 - w i) * R η := fun η =>
    (Finset.mul_prod_erase Finset.univ (fun j => if j ∈ η then w j else 1 - w j)
      (Finset.mem_univ i)).symm
  have hfac₀ : ∀ η : Set ι, BHK2006.weight w₀ η = (if i ∈ η then 0 else 1) * R η := by
    intro η
    have h := (Finset.mul_prod_erase Finset.univ (fun j => if j ∈ η then w₀ j else 1 - w₀ j)
      (Finset.mem_univ i)).symm
    have hRe : ∏ j ∈ Finset.univ.erase i, (if j ∈ η then w₀ j else 1 - w₀ j) = R η := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp only [hw₀, if_neg hji]
    rw [hRe] at h
    have hwi : w₀ i = 0 := by simp only [hw₀, if_true]
    rw [hwi] at h
    rw [show BHK2006.weight w₀ η = ∏ j, (if j ∈ η then w₀ j else 1 - w₀ j) from rfl, h]
    split_ifs <;> ring
  have hRins : ∀ η : Set ι, R (insert i η) = R η := fun η =>
    Finset.prod_congr rfl fun j hj => by
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp only [Set.mem_insert_iff, hji, false_or]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun η : Set ι => i ∈ η),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun η : Set ι => i ∈ η)
      (fun η => BHK2006.weight w₀ η * φ η)]
  have hzero : ∑ η ∈ Finset.univ.filter (fun η : Set ι => i ∈ η),
      BHK2006.weight w₀ η * φ η = 0 := by
    refine Finset.sum_eq_zero fun η hη => ?_
    have hi : i ∈ η := (Finset.mem_filter.1 hη).2
    rw [hfac₀ η, if_pos hi]; ring
  have hreidx : ∑ η ∈ Finset.univ.filter (fun η : Set ι => i ∈ η),
        BHK2006.weight w η * φ (η \ {i})
      = ∑ η ∈ Finset.univ.filter (fun η : Set ι => ¬ i ∈ η),
        BHK2006.weight w (insert i η) * φ η := by
    refine Finset.sum_nbij' (fun η => η \ {i}) (fun η => insert i η) ?_ ?_ ?_ ?_ ?_
    · intro η hη
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
        Set.mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true]
    · intro η hη
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_insert_iff, true_or]
    · intro η hη
      have hi : i ∈ η := (Finset.mem_filter.1 hη).2
      simp only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hi]
    · intro η hη
      have hi : i ∉ η := (Finset.mem_filter.1 hη).2
      show insert i η \ {i} = η
      rw [← Set.union_singleton, Set.union_sdiff_right, Set.sdiff_singleton_eq_self hi]
    · intro η hη
      have hi : i ∈ η := (Finset.mem_filter.1 hη).2
      simp only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem hi]
  have hrest : ∑ η ∈ Finset.univ.filter (fun η : Set ι => ¬ i ∈ η),
        BHK2006.weight w η * φ (η \ {i})
      = ∑ η ∈ Finset.univ.filter (fun η : Set ι => ¬ i ∈ η), BHK2006.weight w η * φ η := by
    refine Finset.sum_congr rfl fun η hη => ?_
    have hi : i ∉ η := (Finset.mem_filter.1 hη).2
    rw [Set.sdiff_singleton_eq_self hi]
  rw [hreidx, hrest, hzero, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun η hη => ?_
  have hi : i ∉ η := (Finset.mem_filter.1 hη).2
  rw [hfac (insert i η), hfac η, hfac₀ η, hRins η, if_pos (Set.mem_insert i η), if_neg hi,
    if_neg hi]
  ring

/-- **Deleting coordinates is switching them off.** -/
theorem sum_weight_mul_comp_sdiff (w : ι → ℝ) (B : Set ι) (φ : Set ι → ℝ) :
    ∑ η, BHK2006.weight w η * φ (η \ B)
      = ∑ η, BHK2006.weight (fun j => if j ∈ B then 0 else w j) η * φ η := by
  classical
  suffices h : ∀ (T : Finset ι) (w : ι → ℝ) (φ : Set ι → ℝ),
      ∑ η, BHK2006.weight w η * φ (η \ ↑T)
        = ∑ η, BHK2006.weight (fun j => if j ∈ T then 0 else w j) η * φ η by
    have hB : B = ↑B.toFinset := (Set.coe_toFinset B).symm
    have hh := h B.toFinset w φ
    rw [← hB] at hh
    rw [hh]
    refine Finset.sum_congr rfl fun η _ => ?_
    congr 1
    simp only [Set.mem_toFinset]
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro w φ
    simp only [Finset.coe_empty, Set.sdiff_empty, Finset.notMem_empty, if_false]
  | @insert i T hiT ih =>
    intro w φ
    have h1 : ∀ η : Set ι, η \ ↑(insert i T) = (η \ {i}) \ ↑T := fun η => by
      rw [Finset.coe_insert, ← Set.union_singleton, Set.union_comm, Set.sdiff_sdiff]
    simp only [h1]
    rw [sum_weight_mul_comp_sdiff_singleton w i (fun ζ => φ (ζ \ ↑T)), ih]
    refine Finset.sum_congr rfl fun η _ => ?_
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]

/-- **Restriction**: when the parameters vanish off `D`, the mean of `φ` is the mean of `φ` read
on the coordinates `D` alone.  This is the hyperedge form of the bond `ED_univ_eq_ED_of_zero`,
which says the same about the weighted-cube expectation. -/
theorem integral_eq_integral_inter_of_zero (p : ι → unitInterval) (D : Set ι)
    (hp : ∀ i ∉ D, p i = 0) (φ : Set ι → ℝ) :
    ∫ ω, φ ω ∂(prodBernoulli p) = ∫ ω, φ (ω ∩ D) ∂(prodBernoulli p) := by
  refine integral_congr_ae ?_
  filter_upwards [prodBernoulli_ae_forall_notMem p (Z := Dᶜ) (Set.toFinite _).countable
    fun i hi => hp i hi] with ω hω
  rw [Set.inter_eq_left.2 fun i hi => not_not.1 fun hc => hω i hc hi]

/-- **Deleting coordinates is switching them off, integral form.** -/
theorem integral_comp_sdiff_prodBernoulli (p : ι → unitInterval) (B : Set ι) (φ : Set ι → ℝ) :
    ∫ ω, φ (ω \ B) ∂(prodBernoulli p)
      = ∫ ω, φ ω ∂(prodBernoulli fun j => if j ∈ B then 0 else p j) := by
  classical
  rw [BHK2006.integral_prodBernoulli_eq_sum p (fun ω => φ (ω \ B)),
    BHK2006.integral_prodBernoulli_eq_sum]
  rw [sum_weight_mul_comp_sdiff (fun j => (p j : ℝ)) B φ]
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 2
  funext j
  split_ifs <;> rfl

/-- **Deleting coordinates is switching them off, events.** -/
theorem measureReal_preimage_sdiff_prodBernoulli (p : ι → unitInterval) (B : Set ι)
    (A : Set (Set ι)) :
    (prodBernoulli p).real ((· \ B) ⁻¹' A)
      = (prodBernoulli fun j => if j ∈ B then 0 else p j).real A := by
  classical
  rw [← integral_indicator_one (measurableSet_of_fintype ((· \ B) ⁻¹' A)),
    ← integral_indicator_one (measurableSet_of_fintype A)]
  have h : (((· \ B) ⁻¹' A).indicator (1 : Set ι → ℝ))
      = fun ω => (A.indicator (1 : Set ι → ℝ)) (ω \ B) := by
    funext ω
    simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
  rw [h, integral_comp_sdiff_prodBernoulli p B (A.indicator 1)]

/-- **Deleting coordinates is switching them off, restricted integrals.** -/
theorem setIntegral_preimage_sdiff_prodBernoulli (p : ι → unitInterval) (B : Set ι)
    (A : Set (Set ι)) (φ : Set ι → ℝ) :
    ∫ ω in (· \ B) ⁻¹' A, φ (ω \ B) ∂(prodBernoulli p)
      = ∫ ω in A, φ ω ∂(prodBernoulli fun j => if j ∈ B then 0 else p j) := by
  classical
  rw [← integral_indicator (measurableSet_of_fintype ((· \ B) ⁻¹' A)),
    ← integral_indicator (measurableSet_of_fintype A)]
  have h : (fun ω => ((· \ B) ⁻¹' A).indicator (fun ν => φ (ν \ B)) ω)
      = fun ω => (A.indicator φ) (ω \ B) := by
    funext ω
    simp only [Set.indicator, Set.mem_preimage]
  rw [h, integral_comp_sdiff_prodBernoulli p B (A.indicator φ)]

end Deleted

/-- **The mean with the labels meeting a vertex set deleted is the mean under the deleted
parameters.**  `delE` and `cut` of `KN/HyperCTBase.lean` meet `deleteHyper` of
`KN/HyperCore.lean`. -/
theorem delE_eq_integral_deleteHyper [Fintype E] (H : Hypergraph V E) (K : Set V)
    (φ : Set E → ℝ) :
    delE H (labelsMeeting H K) φ = ∫ ν, φ ν ∂(prodBernoulli (deleteHyper H K).prob) := by
  classical
  have hp : (fun e => if e ∈ labelsMeeting H K then (0 : unitInterval) else H.prob e)
      = (deleteHyper H K).prob := by
    funext e
    show (if e ∈ labelsMeeting H K then (0 : unitInterval) else H.prob e)
        = if e ∈ labelsMeeting H K then (0 : unitInterval) else H.prob e
    congr 1
  rw [delE, integral_comp_sdiff_prodBernoulli H.prob (labelsMeeting H K) φ, hp]

/-- The same, at the cut of an explored cluster. -/
theorem delE_cut_eq_integral_deleteHyper [Fintype E] (H : Hypergraph V E) (X : Set V)
    (ω : Set E) (φ : Set E → ℝ) :
    delE H (cut H X ω) φ
      = ∫ ν, φ ν ∂(prodBernoulli (deleteHyper H (hyperClusterSet H ω X)).prob) :=
  delE_eq_integral_deleteHyper H (hyperClusterSet H ω X) φ

/-- **The conditional expectation of a cluster functional outside the explored cluster is the
subtracted term of `projFun`.**  Combining `cE_clusterFun_of_not_mem` with
`delE_eq_integral_deleteHyper` and `projFun_eq_deleteHyper` of `KN/HyperProjGen.lean`. -/
theorem cE_clusterFun_eq_deleteHyper [Fintype E] (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ)
    (ω : Set E) {x : V} (hx : x ∉ hyperClusterSet H ω S) :
    cE H S (fun ν => F (hyperClusterSet H ν ({x} : Set V))) ω
      = F (hyperClusterSet H ω S) - projFun H x F (hyperClusterSet H ω S) := by
  rw [cE_clusterFun_of_not_mem H S F ω hx, cut,
    delE_eq_integral_deleteHyper H (hyperClusterSet H ω S)
      (fun η => F (hyperClusterSet H η ({x} : Set V))),
    projFun_eq_deleteHyper H x F (hyperClusterSet H ω S)]
  ring


/-! ## The functionals of the two-source inequality

The bond `CovTau/A2Defs.lean` sets up the cluster `sC U N ω` of a source SET in the model induced
on a vertex set `U`, the vertex set `rest U N ω = U ∖ C_N` left after deleting it, and the
observer indicator `oInd`.  The first is `rCluster` of `KN/HyperOneCluster.lean`, the third is
`indMem` of `KN/HyperAGBase.lean` read at the vertex cluster (`indMem_hyperClusterSet`); what is
added here is `rest` and the elementary facts the induction on the vertex set consumes.
-/

section Restricted

/-- The vertices of `U` left after deleting the cluster of the source set `N`. -/
def rest (H : Hypergraph V E) (U : Finset V) (N : Set V) (ω : Set E) : Finset V :=
  U.filter fun u => u ∉ rCluster H U N ω

theorem mem_rest {H : Hypergraph V E} {U : Finset V} {N : Set V} {ω : Set E} {u : V} :
    u ∈ rest H U N ω ↔ u ∈ U ∧ u ∉ rCluster H U N ω := Finset.mem_filter

theorem rest_subset (H : Hypergraph V E) (U : Finset V) (N : Set V) (ω : Set E) :
    rest H U N ω ⊆ U := Finset.filter_subset _ _

/-- The cluster of the empty source set is empty. -/
theorem rCluster_empty (H : Hypergraph V E) (U : Finset V) (ω : Set E) :
    rCluster H U (∅ : Set V) ω = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => h.choose_spec.1

theorem rest_empty (H : Hypergraph V E) (U : Finset V) (ω : Set E) :
    rest H U (∅ : Set V) ω = U := by
  ext u
  simp [mem_rest, rCluster_empty]

/-- The cluster is monotone in the source set. -/
theorem rCluster_mono_source (H : Hypergraph V E) (U : Finset V) {N N' : Set V} (h : N ⊆ N')
    (ω : Set E) : rCluster H U N ω ⊆ rCluster H U N' ω := fun _ hu => by
  obtain ⟨z, hz, hr⟩ := hu
  exact ⟨z, h hz, hr⟩

/-- The cluster of a single vertex is its reachability class in the induced model. -/
theorem mem_rCluster_singleton {H : Hypergraph V E} {U : Finset V} {ω : Set E} {x u : V} :
    u ∈ rCluster H U ({x} : Set V) ω
      ↔ (openHyperGraph H (ω ∩ labelsIn H U)).Reachable x u := by
  constructor
  · rintro ⟨z, hz, hr⟩
    rw [Set.mem_singleton_iff] at hz
    exact hz ▸ hr
  · intro h
    exact ⟨x, rfl, h⟩

/-- `x` misses the cluster of `N` exactly when the cluster of `x` avoids `N`.  The bond
`not_mem_sC_iff`; the two sides exchange the roles of the source and the avoided set. -/
theorem notMem_rCluster_iff_rAvoid (H : Hypergraph V E) (U : Finset V) (N : Set V) (ω : Set E)
    (x : V) : x ∉ rCluster H U N ω ↔ ω ∈ rAvoid H U ({x} : Set V) N := by
  constructor
  · intro h n hn hc
    exact h ⟨n, hn, (mem_rCluster_singleton.1 hc).symm⟩
  · rintro h ⟨z, hz, hr⟩
    exact h z hz (mem_rCluster_singleton.2 hr.symm)

/-- The observer indicator takes the value `1` at most. -/
theorem indMem_le_one (o : V) (K : Set V) : indMem o K ≤ 1 := by
  unfold indMem
  split_ifs
  · exact le_rfl
  · exact zero_le_one

end Restricted


/-! ## Conditional association for two functionals of the same cluster

`avoid_twoCluster_le` of `KN/HyperTwoCluster.lean` asks that both functionals be increasing in the
cluster of the source and decreasing in the cluster of the avoided set.  Two functionals of the
source cluster alone are covered by taking the second argument constant, and the negatively
correlated pair is the instance at `(F, −G)`.
-/

section SameCluster

variable [Fintype V] [Fintype E]

/-- Two increasing functionals of the cluster of `S` are positively associated on the event that
that cluster avoids `T`. -/
theorem avoid_sameCluster_association (H : Hypergraph V E) (S T : Set V) {F G : Set V → ℝ}
    (hF : Monotone F) (hG : Monotone G) :
    (∫ ω in avoidEvent H S T, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) *
        (∫ ω in avoidEvent H S T, G (hyperClusterSet H ω S) ∂(prodBernoulli H.prob))
      ≤ (prodBernoulli H.prob).real (avoidEvent H S T) *
        ∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) * G (hyperClusterSet H ω S) ∂(prodBernoulli H.prob) :=
  avoid_twoCluster_le H S T (oneClusterInequality_holds H S T)
    (F := fun C _ => F C) (G := fun C _ => G C)
    (fun _ => hF) (fun _ => antitone_const) (fun _ => hG) (fun _ => antitone_const)

/-- An increasing and a decreasing functional of the cluster of `S` are negatively correlated on
the event that that cluster avoids `T`.  This is the step of the bond `ordTransfer` that the
two-cluster inequality does not give directly. -/
theorem avoid_sameCluster_negCorrelation (H : Hypergraph V E) (S T : Set V) {F G : Set V → ℝ}
    (hF : Monotone F) (hG : Antitone G) :
    (prodBernoulli H.prob).real (avoidEvent H S T) *
        (∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) * G (hyperClusterSet H ω S) ∂(prodBernoulli H.prob))
      ≤ (∫ ω in avoidEvent H S T, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) *
        ∫ ω in avoidEvent H S T, G (hyperClusterSet H ω S) ∂(prodBernoulli H.prob) := by
  have key := avoid_twoCluster_le H S T (oneClusterInequality_holds H S T)
    (F := fun C _ => F C) (G := fun C _ => -G C)
    (fun _ => hF) (fun _ => antitone_const)
    (fun _ _ _ h => neg_le_neg (hG h)) (fun _ => antitone_const)
  simp only [mul_neg, integral_neg] at key
  linarith

end SameCluster

/-! ## The two-cluster inequality for a functional of a smaller avoided set

The recombination of `KN/HyperTwoCluster.lean` uses the avoided set `T` twice: to know that the
cluster of `S` avoids it, and to know that the cluster read on the other side does not change when
the labels meeting the cluster of `S` are discarded.  Both survive when the functional on the other
side is read at the cluster of a SUBSET `T' ⊆ T`, and that is what the block-Harris transfer needs:
it conditions on `{v ↮ a} ∩ {v ↮ b}` and integrates a functional of the cluster of `a` alone.
-/

section SubCluster

variable [Fintype V] [Fintype E]

omit [Fintype V] in
/-- One term of the recombination, for a functional read at the cluster of `T' ⊆ T`. -/
theorem setIntegral_clusterEvent_avoid_sub_eq (H : Hypergraph V E) (S T T' K : Set V)
    (hT' : T' ⊆ T) (Φ : Set V → Set V → ℝ) :
    (∫ ν in clusterEvent H S K ∩ avoidEvent H S T, Φ K (hyperClusterSet H ν T')
        ∂(prodBernoulli H.prob))
      = condMean H T' Φ K *
        (prodBernoulli H.prob).real (clusterEvent H S K ∩ avoidEvent H S T) := by
  by_cases hKT : Disjoint K T
  · have hKT' : Disjoint K T' := Set.disjoint_of_subset_right hT' hKT
    rw [clusterEvent_inter_avoidEvent_of_disjoint H S T K hKT]
    have hcongr : (∫ ν in clusterEvent H S K, Φ K (hyperClusterSet H ν T')
          ∂(prodBernoulli H.prob))
        = ∫ ν in clusterEvent H S K,
            Φ K (hyperClusterSet H (ν ∩ (labelsMeeting H K)ᶜ) T') ∂(prodBernoulli H.prob) := by
      refine setIntegral_congr_fun (measurableSet_of_fintype _) fun ν hν => ?_
      have hA : ν ∈ avoidEvent H S T' := by
        have hKeq : hyperClusterSet H ν S = K := hν
        show Disjoint (hyperClusterSet H ν S) T'
        rw [hKeq]
        exact hKT'
      rw [hyperClusterSet_trace_eq H S T' K hν hA]
    rw [hcongr, setIntegral_clusterEvent_of_trace H S K
      (h := fun ν => Φ K (hyperClusterSet H (ν ∩ (labelsMeeting H K)ᶜ) T'))
      (fun ν => by rw [Set.inter_assoc, Set.inter_self])]
    exact mul_comm _ _
  · rw [clusterEvent_inter_avoidEvent_of_not_disjoint H S T K hKT]
    simp

/-- The recombination, for a functional read at the cluster of `T' ⊆ T`. -/
theorem setIntegral_avoid_sub_eq_sum (H : Hypergraph V E) (S T T' : Set V) (hT' : T' ⊆ T)
    (Φ : Set V → Set V → ℝ) :
    (∫ ω in avoidEvent H S T,
        Φ (hyperClusterSet H ω S) (hyperClusterSet H ω T') ∂(prodBernoulli H.prob))
      = ∑ K : Finset V, condMean H T' Φ (↑K : Set V) * avoidWeight H S T K := by
  have hexp : ∀ ω : Set E, (avoidEvent H S T).indicator
        (fun ν => Φ (hyperClusterSet H ν S) (hyperClusterSet H ν T')) ω
      = ∑ K : Finset V, (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T')) ω := by
    intro ω
    obtain ⟨K₀, hK₀⟩ : ∃ K : Finset V, (↑K : Set V) = hyperClusterSet H ω S :=
      (Set.toFinite _).exists_finset_coe
    have hmem₀ : ω ∈ clusterEvent H S (↑K₀ : Set V) := hK₀.symm
    have hzero : ∀ K : Finset V, K ≠ K₀ →
        (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T')) ω = 0 := by
      intro K hK
      refine Set.indicator_of_notMem (fun hcon => hK ?_) _
      have h1 : hyperClusterSet H ω S = (↑K : Set V) := hcon.1
      exact Finset.coe_injective (h1.symm.trans hK₀.symm)
    have key : ∑ K : Finset V, (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T')) ω
        = (clusterEvent H S (↑K₀ : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K₀ : Set V) (hyperClusterSet H ν T')) ω :=
      Finset.sum_eq_single K₀ (fun K _ hK => hzero K hK) (fun hc => absurd (Finset.mem_univ _) hc)
    rw [key]
    by_cases hω : ω ∈ avoidEvent H S T
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_inter hmem₀ hω), hK₀]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem fun hc => hω hc.2]
  calc (∫ ω in avoidEvent H S T,
        Φ (hyperClusterSet H ω S) (hyperClusterSet H ω T') ∂(prodBernoulli H.prob))
      = ∫ ω, ∑ K : Finset V, (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T')) ω ∂(prodBernoulli H.prob) := by
        rw [← integral_indicator (measurableSet_avoidEvent H S T)]
        exact integral_congr_ae (Filter.Eventually.of_forall hexp)
    _ = ∑ K : Finset V, ∫ ω, (clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T).indicator
          (fun ν => Φ (↑K : Set V) (hyperClusterSet H ν T')) ω ∂(prodBernoulli H.prob) :=
        integral_finsetSum _ fun K _ =>
          (integrable_of_fintype _).indicator (measurableSet_of_fintype _)
    _ = ∑ K : Finset V, ∫ ω in clusterEvent H S (↑K : Set V) ∩ avoidEvent H S T,
          Φ (↑K : Set V) (hyperClusterSet H ω T') ∂(prodBernoulli H.prob) :=
        Finset.sum_congr rfl fun K _ => integral_indicator (measurableSet_of_fintype _)
    _ = _ :=
        Finset.sum_congr rfl fun K _ =>
          setIntegral_clusterEvent_avoid_sub_eq H S T T' (↑K : Set V) hT' Φ

/-- **The two-cluster inequality with the second cluster read at a subset of the avoided set.** -/
theorem avoid_twoCluster_sub_le (H : Hypergraph V E) (S T T' : Set V) (hT' : T' ⊆ T)
    {F G : Set V → Set V → ℝ}
    (hF1 : ∀ D, Monotone fun C => F C D) (hF2 : ∀ C, Antitone fun D => F C D)
    (hG1 : ∀ D, Monotone fun C => G C D) (hG2 : ∀ C, Antitone fun D => G C D) :
    (∫ ω in avoidEvent H S T,
        F (hyperClusterSet H ω S) (hyperClusterSet H ω T') ∂(prodBernoulli H.prob)) *
      (∫ ω in avoidEvent H S T,
        G (hyperClusterSet H ω S) (hyperClusterSet H ω T') ∂(prodBernoulli H.prob))
      ≤ (prodBernoulli H.prob).real (avoidEvent H S T) *
        ∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) (hyperClusterSet H ω T') *
            G (hyperClusterSet H ω S) (hyperClusterSet H ω T') ∂(prodBernoulli H.prob) := by
  have h1 := setIntegral_avoid_sub_eq_sum H S T T' hT' F
  have h2 := setIntegral_avoid_sub_eq_sum H S T T' hT' G
  have h3 := setIntegral_avoid_sub_eq_sum H S T T' hT' (fun C D => F C D * G C D)
  have hP := real_avoidEvent_eq_sum_avoidWeight H S T
  rw [h1, h2, h3, hP]
  have hone := (oneClusterInequality_holds H S T).of_monotone
    (f := condMean H T' F) (g := condMean H T' G)
    (condMean_mono H T' hF1 hF2) (condMean_mono H T' hG1 hG2)
  rw [avoidIntegral_eq_sum_avoidWeight, avoidIntegral_eq_sum_avoidWeight,
    avoidIntegral_eq_sum_avoidWeight, real_avoidEvent_eq_sum_avoidWeight] at hone
  have hterm : ∑ K : Finset V,
        (condMean H T' F (↑K : Set V) * condMean H T' G (↑K : Set V)) * avoidWeight H S T K
      ≤ ∑ K : Finset V, condMean H T' (fun C D => F C D * G C D) (↑K : Set V) *
          avoidWeight H S T K :=
    Finset.sum_le_sum fun K _ =>
      mul_le_mul_of_nonneg_right (condMean_mul_le H T' hF2 hG2 (↑K : Set V))
        (avoidWeight_nonneg H S T K)
  have hW : 0 ≤ ∑ K : Finset V, avoidWeight H S T K :=
    Finset.sum_nonneg fun K _ => avoidWeight_nonneg H S T K
  calc (∑ K : Finset V, condMean H T' F (↑K : Set V) * avoidWeight H S T K) *
        ∑ K : Finset V, condMean H T' G (↑K : Set V) * avoidWeight H S T K
      ≤ (∑ K : Finset V,
            (condMean H T' F (↑K : Set V) * condMean H T' G (↑K : Set V)) *
              avoidWeight H S T K) * ∑ K : Finset V, avoidWeight H S T K := hone
    _ ≤ (∑ K : Finset V, condMean H T' (fun C D => F C D * G C D) (↑K : Set V) *
            avoidWeight H S T K) * ∑ K : Finset V, avoidWeight H S T K :=
        mul_le_mul_of_nonneg_right hterm hW
    _ = _ := mul_comm _ _

/-- An increasing functional of the cluster of `S` and an increasing functional of the cluster of
`T' ⊆ T` are negatively correlated on the event that the cluster of `S` avoids `T`. -/
theorem avoid_cluster_sub_negCorrelation (H : Hypergraph V E) (S T T' : Set V) (hT' : T' ⊆ T)
    {F G : Set V → ℝ} (hF : Monotone F) (hG : Monotone G) :
    (prodBernoulli H.prob).real (avoidEvent H S T) *
        (∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) * G (hyperClusterSet H ω T') ∂(prodBernoulli H.prob))
      ≤ (∫ ω in avoidEvent H S T, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) *
        ∫ ω in avoidEvent H S T, G (hyperClusterSet H ω T') ∂(prodBernoulli H.prob) := by
  have key := avoid_twoCluster_sub_le H S T T' hT'
    (F := fun C _ => F C) (G := fun _ D => -G D)
    (fun _ => hF) (fun _ => antitone_const)
    (fun _ => monotone_const) (fun _ _ _ h => neg_le_neg (hG h))
  simp only [mul_neg, integral_neg] at key
  linarith

end SubCluster


/-! ## The three transfer tools of the two-relay surplus step -/

section Transfer

variable [Fintype E]

/-- The indicator of a complement. -/
theorem ind_compl {α : Type*} (X : Set α) (a : α) : ind Xᶜ a = 1 - ind X a := by
  by_cases h : a ∈ X
  · rw [ind_of_mem h, ind_of_not_mem (Set.notMem_compl_iff.2 h)]
    ring
  · rw [ind_of_not_mem h, ind_of_mem (Set.mem_compl h)]
    ring

/-- The mean of the observer indicator at the cluster of `s` is the probability of the
connection. -/
theorem setIntegral_indMem (H : Hypergraph V E) (A : Set (Set E)) (o s : V) :
    (∫ ω in A, indMem o (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob))
      = (prodBernoulli H.prob).real (A ∩ hyperConn H o s) := by
  rw [setIntegral_congr_fun (measurableSet_of_fintype A)
    (g := fun ω => ind (hyperConn H o s) ω) fun ω _ => indMem_hyperClusterSet H o s ω]
  exact setIntegral_ind A (hyperConn H o s)

theorem setIntegral_one_sub_indMem (H : Hypergraph V E) (A : Set (Set E)) (b s : V) :
    (∫ ω in A, (1 - indMem b (hyperClusterSet H ω ({s} : Set V))) ∂(prodBernoulli H.prob))
      = (prodBernoulli H.prob).real (A ∩ (hyperConn H b s)ᶜ) := by
  rw [setIntegral_congr_fun (measurableSet_of_fintype A)
    (g := fun ω => ind (hyperConn H b s)ᶜ ω) fun ω _ => by
      show (1 : ℝ) - indMem b (hyperClusterSet H ω ({s} : Set V)) = ind (hyperConn H b s)ᶜ ω
      rw [ind_compl, indMem_hyperClusterSet H b s ω]]
  exact setIntegral_ind A _

theorem setIntegral_indMem_mul (H : Hypergraph V E) (A : Set (Set E)) (o b s : V) :
    (∫ ω in A, indMem o (hyperClusterSet H ω ({s} : Set V)) *
        indMem b (hyperClusterSet H ω ({s} : Set V)) ∂(prodBernoulli H.prob))
      = (prodBernoulli H.prob).real (A ∩ (hyperConn H o s ∩ hyperConn H b s)) := by
  rw [setIntegral_congr_fun (measurableSet_of_fintype A)
    (g := fun ω => ind (hyperConn H o s ∩ hyperConn H b s) ω) fun ω _ => by
      show indMem o (hyperClusterSet H ω ({s} : Set V)) *
          indMem b (hyperClusterSet H ω ({s} : Set V))
        = ind (hyperConn H o s ∩ hyperConn H b s) ω
      rw [indMem_hyperClusterSet H o s ω, indMem_hyperClusterSet H b s ω, BHK2006.ind_inter]]
  exact setIntegral_ind A _

theorem setIntegral_indMem_mul_one_sub (H : Hypergraph V E) (A : Set (Set E)) (o b s : V) :
    (∫ ω in A, indMem o (hyperClusterSet H ω ({s} : Set V)) *
        (1 - indMem b (hyperClusterSet H ω ({s} : Set V))) ∂(prodBernoulli H.prob))
      = (prodBernoulli H.prob).real (A ∩ (hyperConn H o s ∩ (hyperConn H b s)ᶜ)) := by
  rw [setIntegral_congr_fun (measurableSet_of_fintype A)
    (g := fun ω => ind (hyperConn H o s ∩ (hyperConn H b s)ᶜ) ω) fun ω _ => by
      show indMem o (hyperClusterSet H ω ({s} : Set V)) *
          ((1 : ℝ) - indMem b (hyperClusterSet H ω ({s} : Set V)))
        = ind (hyperConn H o s ∩ (hyperConn H b s)ᶜ) ω
      rw [indMem_hyperClusterSet H o s ω, indMem_hyperClusterSet H b s ω, ← ind_compl,
        BHK2006.ind_inter]]
  exact setIntegral_ind A _

/-- Integrating a function against the observer indicator restricts to the connection event. -/
theorem setIntegral_indMem_mul_fun (H : Hypergraph V E) (A : Set (Set E)) (o s : V)
    (g : Set E → ℝ) :
    (∫ ω in A, indMem o (hyperClusterSet H ω ({s} : Set V)) * g ω ∂(prodBernoulli H.prob))
      = ∫ ω in A ∩ hyperConn H o s, g ω ∂(prodBernoulli H.prob) := by
  rw [setIntegral_congr_fun (measurableSet_of_fintype A)
    (g := fun ω => ind (hyperConn H o s) ω * g ω) fun ω _ => by
      show indMem o (hyperClusterSet H ω ({s} : Set V)) * g ω = ind (hyperConn H o s) ω * g ω
      rw [indMem_hyperClusterSet H o s ω]]
  exact setIntegral_ind_mul A (hyperConn H o s) g

variable [Fintype V]

/-- Conditionally on the cluster of `s` avoiding `T`, two connections out of `s` are positively
correlated. -/
theorem real_avoid_two_conn (H : Hypergraph V E) (s : V) (T : Set V) (o b : V) :
    (prodBernoulli H.prob).real (avoidEvent H ({s} : Set V) T ∩ hyperConn H o s) *
        (prodBernoulli H.prob).real (avoidEvent H ({s} : Set V) T ∩ hyperConn H b s)
      ≤ (prodBernoulli H.prob).real (avoidEvent H ({s} : Set V) T) *
        (prodBernoulli H.prob).real
          (avoidEvent H ({s} : Set V) T ∩ (hyperConn H o s ∩ hyperConn H b s)) := by
  have key := avoid_sameCluster_association H ({s} : Set V) T (monotone_indMem o)
    (monotone_indMem b)
  rwa [setIntegral_indMem H _ o s, setIntegral_indMem H _ b s,
    setIntegral_indMem_mul H _ o b s] at key

/-- Conditionally on the cluster of `s` avoiding `T`, a connection and a non-connection out of `s`
are negatively correlated. -/
theorem real_avoid_conn_not_conn (H : Hypergraph V E) (s : V) (T : Set V) (o b : V) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({s} : Set V) T ∩ (hyperConn H o s ∩ (hyperConn H b s)ᶜ)) *
        (prodBernoulli H.prob).real (avoidEvent H ({s} : Set V) T)
      ≤ (prodBernoulli H.prob).real (avoidEvent H ({s} : Set V) T ∩ hyperConn H o s) *
        (prodBernoulli H.prob).real (avoidEvent H ({s} : Set V) T ∩ (hyperConn H b s)ᶜ) := by
  have key := avoid_sameCluster_negCorrelation H ({s} : Set V) T (F := indMem o)
    (G := fun K => 1 - indMem b K) (monotone_indMem o)
    (fun _ _ h => sub_le_sub_left (monotone_indMem b h) 1)
  rw [setIntegral_indMem H _ o s, setIntegral_one_sub_indMem H _ b s,
    setIntegral_indMem_mul_one_sub H _ o b s] at key
  rw [mul_comm]
  exact key

omit [Fintype E] [Fintype V] in
/-- Avoiding a pair of vertices is avoiding each of them. -/
theorem avoidEvent_pair_eq (H : Hypergraph V E) (v a b : V) :
    avoidEvent H ({v} : Set V) ({a, b} : Set V)
      = avoidEvent H ({v} : Set V) ({a} : Set V) ∩ (hyperConn H b v)ᶜ := by
  rw [Set.insert_eq, avoidEvent_union, CTBase.avoidEvent_singleton_eq_compl H v b,
    hyperConn_comm H v b]

/-- The arithmetic of the order transfer. -/
private theorem ordTransfer_core {d x n y u w q : ℝ} (hn0 : 0 ≤ n) (hy0 : 0 ≤ y) (hu0 : 0 ≤ u)
    (hq0 : 0 ≤ q) (hd0 : 0 ≤ d) (hud : u ≤ d) (h1 : x * y ≤ d * w) (h2 : u * d ≤ x * n)
    (h3 : w ≤ q) : u * y ≤ n * q := by
  rcases hd0.eq_or_lt with hdz | hdpos
  · have hu : u = 0 := le_antisymm (hud.trans hdz.ge) hu0
    rw [hu, zero_mul]
    exact mul_nonneg hn0 hq0
  · have e1 : d * (u * y) ≤ x * n * y := by
      calc d * (u * y) = u * d * y := by ring
        _ ≤ x * n * y := mul_le_mul_of_nonneg_right h2 hy0
    have e2 : x * n * y ≤ d * w * n := by
      calc x * n * y = x * y * n := by ring
        _ ≤ d * w * n := mul_le_mul_of_nonneg_right h1 hn0
    have e3 : d * w * n ≤ d * q * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hd0) hn0
    have e4 : d * (u * y) ≤ d * (n * q) := by
      calc d * (u * y) ≤ x * n * y := e1
        _ ≤ d * w * n := e2
        _ ≤ d * q * n := e3
        _ = d * (n * q) := by ring
    exact le_of_mul_le_mul_left e4 hdpos

/-- **T4, the transfer of the order piece.**  With `D = {v ↮ a} ∩ {v ↮ b}` and `Q = {a ↮ b}`,
`μ(D ∩ {o ↔ v}) · μ({v ↔ b} ∩ Q) ≤ μ(D) · μ({o ↔ b} ∩ Q)`: given `v ↮ a`, the connection `{v ↔ o}`
is positively correlated with `{v ↔ b}` and negatively with `{v ↮ b}`, and
`{v ↮ a} ∩ {v ↔ o} ∩ {v ↔ b} ⊆ {o ↔ b} ∩ Q`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] -/
theorem ordTransfer (H : Hypergraph V E) (o v a b : V) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) ({a, b} : Set V) ∩ hyperConn H o v) *
        (prodBernoulli H.prob).real (hyperConn H v b ∩ (hyperConn H a b)ᶜ)
      ≤ (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a, b} : Set V)) *
        (prodBernoulli H.prob).real (hyperConn H o b ∩ (hyperConn H a b)ᶜ) := by
  classical
  have hn : ∀ A : Set (Set E), 0 ≤ (prodBernoulli H.prob).real A := fun _ => measureReal_nonneg
  have h1 := real_avoid_two_conn H v ({a} : Set V) o b
  have h2 := real_avoid_conn_not_conn H v ({a} : Set V) o b
  have hsub : avoidEvent H ({v} : Set V) ({a} : Set V) ∩
      (hyperConn H o v ∩ hyperConn H b v)
      ⊆ (hyperConn H o b ∩ (hyperConn H a b)ᶜ : Set (Set E)) := by
    rintro ω ⟨hD, hov, hbv⟩
    have hva : ¬ (openHyperGraph H ω).Reachable v a := (mem_avoidEvent_pair H v a ω).1 hD
    exact ⟨(hov : (openHyperGraph H ω).Reachable o v).trans
        (hbv : (openHyperGraph H ω).Reachable b v).symm,
      fun hab => hva ((hbv : (openHyperGraph H ω).Reachable b v).symm.trans
        (hab : (openHyperGraph H ω).Reachable a b).symm)⟩
  have h3 : (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a} : Set V) ∩
        (hyperConn H o v ∩ hyperConn H b v))
      ≤ (prodBernoulli H.prob).real (hyperConn H o b ∩ (hyperConn H a b)ᶜ : Set (Set E)) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hud : (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a} : Set V) ∩
        (hyperConn H o v ∩ (hyperConn H b v)ᶜ))
      ≤ (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a} : Set V)) :=
    measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
  have hDOv : avoidEvent H ({v} : Set V) ({a, b} : Set V) ∩ hyperConn H o v
      = avoidEvent H ({v} : Set V) ({a} : Set V) ∩
        (hyperConn H o v ∩ (hyperConn H b v)ᶜ) := by
    rw [avoidEvent_pair_eq H v a b]
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  have hVbQ : (hyperConn H v b ∩ (hyperConn H a b)ᶜ : Set (Set E))
      = avoidEvent H ({v} : Set V) ({a} : Set V) ∩ hyperConn H b v := by
    ext ω
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_compl_iff, mem_avoidEvent_pair H v a ω]
    show ((openHyperGraph H ω).Reachable v b ∧ ¬ (openHyperGraph H ω).Reachable a b)
      ↔ (¬ (openHyperGraph H ω).Reachable v a ∧ (openHyperGraph H ω).Reachable b v)
    constructor
    · rintro ⟨hvb, hab⟩
      exact ⟨fun hva => hab (hva.symm.trans hvb), hvb.symm⟩
    · rintro ⟨hva, hbv⟩
      exact ⟨hbv.symm, fun hab => hva (hbv.symm.trans hab.symm)⟩
  have hDNb : (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a, b} : Set V))
      = (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a} : Set V) ∩
          (hyperConn H b v)ᶜ) := by
    rw [avoidEvent_pair_eq H v a b]
  rw [hDOv, hVbQ, hDNb]
  exact ordTransfer_core (hn _) (hn _) (hn _) (hn _) (hn _) hud h1 h2 h3

/-- The arithmetic of the block-Harris transfer. -/
private theorem blockHarris_core {pD pDOv pUo pUv m IUo IDOv IUv : ℝ} (hpD : 0 ≤ pD)
    (hpUv : pUv = 1 - pD) (hA : (pUo + pDOv) * m ≤ IUo + IDOv)
    (hB : pD * IDOv ≤ pDOv * (m - IUv)) :
    pDOv * (IUv - pUv * m) ≤ pD * (IUo - pUo * m) := by
  subst hpUv
  nlinarith [mul_le_mul_of_nonneg_left hA hpD, hB]

/-- **T1, the transfer of the block-Harris piece.**  With `f = F(C_a)`, `m = E f`,
`D = {v ↮ a} ∩ {v ↮ b}` and `SH_x = ∫_{x↔a ∨ x↔b} f − μ(x↔a ∨ x↔b)·m`:
`μ(D ∩ {o ↔ v}) · SH_v ≤ μ(D) · SH_o`.  Harris on the increasing event
`{o↔a} ∪ {o↔b} ∪ {o↔v}`, which splits as `({o↔a} ∪ {o↔b}) ⊔ (D ∩ {o↔v})`, and the negative
correlation, given `v ↮ {a,b}`, of `1{o ↔ v}` with `F(C_a)`.
[cite: VandenbergHaggstromKahn2005, Thm. 2.1 (p. 9) at q = 1, Remark 1 (p. 5)] -/
theorem blockHarrisTransfer (H : Hypergraph V E) (o v a b : V) (F : Set V → ℝ)
    (hF : Monotone F) :
    (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) ({a, b} : Set V) ∩ hyperConn H o v) *
        ((∫ ω in hyperConn H v a ∪ hyperConn H v b,
              F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (hyperConn H v a ∪ hyperConn H v b) *
            ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob))
      ≤ (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) ({a, b} : Set V)) *
        ((∫ ω in hyperConn H o a ∪ hyperConn H o b,
              F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (hyperConn H o a ∪ hyperConn H o b) *
            ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)) := by
  classical
  set μ := prodBernoulli H.prob with hμ
  set f : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({a} : Set V)) with hf
  set m : ℝ := ∫ ω, f ω ∂μ with hm
  set D : Set (Set E) := avoidEvent H ({v} : Set V) ({a, b} : Set V) with hD
  set Uo : Set (Set E) := hyperConn H o a ∪ hyperConn H o b with hUo
  set Uv : Set (Set E) := hyperConn H v a ∪ hyperConn H v b with hUv
  set Ov : Set (Set E) := hyperConn H o v with hOv
  set U' : Set (Set E) := Uo ∪ Ov with hU'
  have hmeas : ∀ A : Set (Set E), MeasurableSet A := fun _ => measurableSet_of_fintype _
  have hn : ∀ A : Set (Set E), 0 ≤ μ.real A := fun _ => measureReal_nonneg
  have hUup : IsUpperSet U' :=
    ((isUpperSet_hyperConn H o a).union (isUpperSet_hyperConn H o b)).union
      (isUpperSet_hyperConn H o v)
  have hHarris : μ.real U' * m ≤ ∫ ω in U', f ω ∂μ :=
    setIntegral_clusterFun_ge H ({a} : Set V) F hF U' hUup
  have hBHK : μ.real D * ∫ ω in D ∩ Ov, f ω ∂μ ≤ μ.real (D ∩ Ov) * ∫ ω in D, f ω ∂μ := by
    have key := avoid_cluster_sub_negCorrelation H ({v} : Set V) ({a, b} : Set V)
      ({a} : Set V) (by intro z hz; simp_all) (monotone_indMem o) hF
    rwa [setIntegral_indMem_mul_fun H D o v f, setIntegral_indMem H D o v] at key
  have hDU : D = Uvᶜ := by
    rw [hD, hUv, Set.insert_eq, avoidEvent_union, CTBase.avoidEvent_singleton_eq_compl H v a,
      CTBase.avoidEvent_singleton_eq_compl H v b, Set.compl_union]
  have hUdiff : U' \ Uo = D ∩ Ov := by
    rw [hDU]
    ext ω
    simp only [hU', hUo, hUv, hOv, Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff]
    constructor
    · rintro ⟨h1 | h1, hno⟩
      · exact absurd h1 hno
      · refine ⟨fun hc => hno ?_, h1⟩
        rcases hc with hc | hc
        · exact Or.inl ((h1 : (openHyperGraph H ω).Reachable o v).trans hc)
        · exact Or.inr ((h1 : (openHyperGraph H ω).Reachable o v).trans hc)
    · rintro ⟨hnv, hov⟩
      refine ⟨Or.inr hov, fun hc => hnv ?_⟩
      rcases hc with hc | hc
      · exact Or.inl ((hov : (openHyperGraph H ω).Reachable o v).symm.trans hc)
      · exact Or.inr ((hov : (openHyperGraph H ω).Reachable o v).symm.trans hc)
  have hUint : ∫ ω in U', f ω ∂μ = (∫ ω in Uo, f ω ∂μ) + ∫ ω in D ∩ Ov, f ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas Uo) ((integrable_of_fintype f).integrableOn),
      Set.inter_eq_right.2 Set.subset_union_left, hUdiff]
  have hUμ : μ.real U' = μ.real Uo + μ.real (D ∩ Ov) := by
    rw [← measureReal_inter_add_sdiff (s := U') (h := measure_ne_top _ _) (hmeas Uo),
      Set.inter_eq_right.2 Set.subset_union_left, hUdiff]
  have hDint : ∫ ω in D, f ω ∂μ = m - ∫ ω in Uv, f ω ∂μ := by
    have h := integral_add_compl (hmeas Uv) (integrable_of_fintype (μ := μ) f)
    rw [← hDU] at h
    rw [hm]
    linarith
  have hDμ : μ.real Uv = 1 - μ.real D := by
    have h1 : μ.real (Set.univ : Set (Set E))
        = μ.real (Set.univ ∩ Uv) + μ.real (Set.univ \ Uv) :=
      (measureReal_inter_add_sdiff (s := Set.univ) (h := measure_ne_top _ _) (hmeas Uv)).symm
    rw [probReal_univ, Set.univ_inter, ← Set.compl_eq_univ_sdiff, ← hDU] at h1
    linarith
  exact blockHarris_core (hn D) hDμ (by rw [← hUμ, ← hUint]; exact hHarris)
    (by rw [← hDint]; exact hBHK)

/-- **The `(+)`-type piece is nonnegative.**  With `Q = {a ↮ b}` and `h = F(C_b) − F(C_a)`,
increasing in the cluster of `b` and decreasing in the cluster of `a`:
`μ({x ↔ b} ∩ Q) · ∫_Q h ≤ μ(Q) · ∫_{{x ↔ b} ∩ Q} h`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9))] -/
theorem plusPiece_nonneg (H : Hypergraph V E) (x a b : V) (F : Set V → ℝ) (hF : Monotone F) :
    (prodBernoulli H.prob).real (hyperConn H x b ∩ (hyperConn H a b)ᶜ) *
        (∫ ω in ((hyperConn H a b)ᶜ : Set (Set E)),
          (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
            ∂(prodBernoulli H.prob))
      ≤ (prodBernoulli H.prob).real ((hyperConn H a b)ᶜ : Set (Set E)) *
        ∫ ω in (hyperConn H x b ∩ (hyperConn H a b)ᶜ : Set (Set E)),
          (F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
            ∂(prodBernoulli H.prob) := by
  have hQ : avoidEvent H ({b} : Set V) ({a} : Set V) = ((hyperConn H a b)ᶜ : Set (Set E)) := by
    rw [CTBase.avoidEvent_singleton_eq_compl H b a, hyperConn_comm H b a]
  have key := avoid_twoCluster_le H ({b} : Set V) ({a} : Set V)
    (oneClusterInequality_holds H ({b} : Set V) ({a} : Set V))
    (F := fun C _ => indMem x C) (G := fun C D => F C - F D)
    (fun _ => monotone_indMem x) (fun _ => antitone_const)
    (fun _ _ _ h => sub_le_sub_right (hF h) _)
    (fun _ _ _ h => sub_le_sub_left (hF h) _)
  rw [setIntegral_indMem H (avoidEvent H ({b} : Set V) ({a} : Set V)) x b,
    setIntegral_indMem_mul_fun H (avoidEvent H ({b} : Set V) ({a} : Set V)) x b
      (fun ω => F (hyperClusterSet H ω ({b} : Set V)) - F (hyperClusterSet H ω ({a} : Set V))),
    hQ, Set.inter_comm] at key
  exact key

end Transfer

end KNAll.Site.CTOne

end
