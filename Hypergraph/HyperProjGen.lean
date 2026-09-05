import Hypergraph.HyperTwoClusterClosed
import Hypergraph.HyperPeel

/-!
# Projection onto one explored cluster, and the avoided first-relay bound, for hyperedges

The hyperedge form of `KN/Projection.lean` and `KN/AvoidedGen.lean`.  Everything is stated for a
`Hypergraph V E` with arbitrary incidence sets over two arbitrary finite types, in place of the
bond model `w : Sym2 (Fin n) → unitInterval` of those two files.

## The projection (the form of `KN/Projection.lean`)

* `projFun H a F K = F K − E[F(C_a)]` computed after discarding the labels that meet `K`.  The
  bond file writes the discarded set as `bar K`, the pairs meeting `K`, and needs
  `barOf_singleton_eq_bar` to reconcile that with the edge-cluster description used by the
  conditioning lemma it imports.  Here the discarded set is `labelsMeeting H K` of
  `KN/HyperCore.lean`, which is already the vertex-set description, so no reconciliation lemma is
  needed; `projFun_eq_deleteHyper` records instead that the subtracted mean is the mean in the
  residual model `deleteHyper H K`, and `projFun_eq_sub_condMean` that it is the `condMean` of
  `KN/HyperTwoCluster.lean`, which is where its total definedness comes from.
* `monotone_projFun` — a larger explored cluster raises `F K` and closes more labels, so it lowers
  the subtracted mean.
* `setIntegral_clusterFamily_eq`, `setIntegral_sub_eq_projFun`,
  `setIntegral_sub_eq_projFun_conn`, `setIntegral_projFun_avoid` — the projection identities.  The
  bond file gets these from `CovTau.setIntegral_sub_eq_projFun`; here they are proved from
  `setIntegral_avoid_eq_sum` of `KN/HyperTwoCluster.lean`, applied twice, to the two-cluster
  functionals `(C, D) ↦ 1_{C ∈ S} F D` and `(C, D) ↦ 1_{C ∈ S} ψ C`, whose conditional means at a
  cluster `K` agree.

## The avoided first-relay bound (the form of `KN/AvoidedGen.lean`)

* The avoided relay mean `condMeanY`, the avoided surplus `surplusY`, the peeling identity
  `surplusY_erase_add` (Lemma P), the comparison `kappaY_le_surplusY` (Lemma κ) and
  `setIntegral_eq_condMeanY_mul` are the ones of `KN/HyperPeel.lean`, which is imported.  The bond
  development keeps them in `Percolation/Continuity/AdditiveGluing/OfAGloc.lean` and
  `KN/AvoidedPeelTools.lean`.
* `firstPattern` names the first-in-rank pattern that the definition of `surplusY` writes out, and
  `firstPattern_disjoint`, `firstPattern_cover`, `sum_measureReal_avoid_firstPattern` are its
  bookkeeping; the first two are the general `firstRank_disjoint'`, `firstRank_cover'` of
  `KN/HyperPeel.lean` read at the family `a ↦ {u ↔ a}`.
* `oneCluster_contact_le` — the one-cluster inequality in the shape the peeling step consumes.
  The bond file calls `BHK2006_clusterConditionalPositiveAssociation_holds`; here it is
  `oneClusterInequality_holds` of `KN/HyperTwoClusterClosed.lean`, that is
  `avoidIntegral_mul_le_inter` of `KN/HyperOneCluster.lean`, applied to `F` and to the increasing
  indicator `K ↦ 1_{o ∈ K}`.
* `genY_of_surplusTransferY` — (S5) with an avoided set implies (GEN) with an avoided set.  The
  surplus transfer inequality is carried as the explicit hypothesis `hST`, exactly as in the bond
  template; nothing here attempts to prove it.
* `sum_le_setIntegral_of_genY` — the sum form.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open scoped Classical

variable {V E : Type*}

/-! ## Singleton clusters, connection events and avoidance events -/

/-- The cluster of a single vertex is its reachability class. -/
theorem hyperClusterSet_singleton (H : Hypergraph V E) (ω : Set E) (u : V) :
    hyperClusterSet H ω ({u} : Set V) = {y | (openHyperGraph H ω).Reachable u y} := by
  ext y; simp [hyperClusterSet]

/-- `u ↔ a` says that `a` lies in the cluster of `u`. -/
theorem mem_hyperConn_iff (H : Hypergraph V E) (ω : Set E) (u a : V) :
    ω ∈ hyperConn H u a ↔ a ∈ hyperClusterSet H ω ({u} : Set V) := by
  simp [hyperConn, hyperClusterSet]

theorem hyperConn_comm (H : Hypergraph V E) (u a : V) : hyperConn H u a = hyperConn H a u := by
  ext ω; exact ⟨fun h => SimpleGraph.Reachable.symm h, fun h => SimpleGraph.Reachable.symm h⟩

/-! `mem_avoidEvent_singleton` and `hyperClusterSet_singleton_eq_of_reachable` are those of
`KN/HyperPeel.lean`. -/

/-! ## The projected functional -/

/-- The projection of `F(C_o) - F(C_a)` onto an explored vertex cluster `K`: the labels meeting
`K` are discarded and the cluster of `a` is recomputed in a fresh configuration. -/
def projFun (H : Hypergraph V E) (a : V) (F : Set V → ℝ) (K : Set V) : ℝ :=
  F K - ∫ η, F (hyperClusterSet H (η \ labelsMeeting H K) ({a} : Set V)) ∂(prodBernoulli H.prob)

/-- The subtracted term of `projFun` is the conditional mean of `KN/HyperTwoCluster.lean`. -/
theorem projFun_eq_sub_condMean (H : Hypergraph V E) (a : V) (F : Set V → ℝ) (K : Set V) :
    projFun H a F K = F K - condMean H ({a} : Set V) (fun _ D => F D) K := by
  unfold projFun condMean
  simp only [Set.sdiff_eq, supportFromRecord]

/-- The subtracted term of `projFun`, in the residual model of `K`. -/
theorem projFun_eq_deleteHyper [Fintype E] (H : Hypergraph V E) (a : V) (F : Set V → ℝ)
    (K : Set V) :
    projFun H a F K =
      F K - ∫ ν, F (hyperClusterSet H ν ({a} : Set V)) ∂(prodBernoulli (deleteHyper H K).prob) := by
  rw [projFun_eq_sub_condMean, condMean_eq_deleteHyper_integral]

/-- **The projection is increasing.**  A larger explored cluster raises `F K` and closes more
labels, which shrinks the recomputed cluster of `a` and so lowers the subtracted mean. -/
theorem monotone_projFun [Fintype E] (H : Hypergraph V E) (a : V) (F : Set V → ℝ)
    (hF : ∀ K L : Set V, K ⊆ L → F K ≤ F L) :
    Monotone (projFun H a F) := by
  intro K L hKL
  unfold projFun
  refine sub_le_sub (hF K L hKL) ?_
  refine integral_mono (integrable_of_fintype _) (integrable_of_fintype _) fun η => ?_
  refine hF _ _ ?_
  refine fun y hy => ?_
  obtain ⟨x, hx, hr⟩ := hy
  refine ⟨x, hx, hr.mono ?_⟩
  intro p q hpq
  obtain ⟨hne, hor⟩ := hpq
  refine ⟨hne, ?_⟩
  rcases hor with ⟨e, he, hp, hq⟩ | ⟨e, he, hq, hp⟩
  · exact Or.inl ⟨e, ⟨he.1, fun hmem => he.2 (labelsMeeting_mono H hKL hmem)⟩, hp, hq⟩
  · exact Or.inr ⟨e, ⟨he.1, fun hmem => he.2 (labelsMeeting_mono H hKL hmem)⟩, hq, hp⟩

/-! ## The projection identity -/

private theorem setIntegral_ite [Fintype E] (H : Hypergraph V E)
    (A : Set (Set E)) (p : Set E → Prop) (f : Set E → ℝ) :
    ∫ ω in A, (if p ω then f ω else 0) ∂(prodBernoulli H.prob) =
      ∫ ω in A ∩ {ω | p ω}, f ω ∂(prodBernoulli H.prob) := by
  have hfun : (fun ω => if p ω then f ω else 0) = {ω | p ω}.indicator f := by
    funext ω
    by_cases h : p ω
    · rw [if_pos h, Set.indicator_of_mem (show ω ∈ {ω | p ω} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ω ∉ {ω | p ω} from h)]
  rw [hfun, ← integral_indicator (measurableSet_of_fintype A), Set.indicator_indicator,
    integral_indicator (measurableSet_of_fintype (A ∩ {ω | p ω}))]

private theorem condMean_const_fst [Fintype E] (H : Hypergraph V E) (T : Set V)
    (f : Set V → ℝ) (K : Set V) :
    condMean H T (fun C _ => f C) K = f K := by
  rw [condMean_eq]
  simp

private theorem condMean_of_ite [Fintype E] (H : Hypergraph V E) (T : Set V)
    (S : Set (Set V)) (G : Set V → Set V → ℝ) (K : Set V) :
    condMean H T (fun C D => if C ∈ S then G C D else 0) K =
      if K ∈ S then condMean H T G K else 0 := by
  rw [condMean_eq, condMean_eq]
  by_cases h : K ∈ S
  · simp only [if_pos h]
  · simp only [if_neg h, integral_zero]

private theorem condMean_snd [Fintype E] (H : Hypergraph V E) (a : V) (F : Set V → ℝ)
    (K : Set V) :
    condMean H ({a} : Set V) (fun _ D => F D) K =
      ∫ η, F (hyperClusterSet H (η \ labelsMeeting H K) ({a} : Set V)) ∂(prodBernoulli H.prob) := by
  rw [condMean_eq]
  simp only [Set.sdiff_eq]

/-- **The projection identity.**  On the event that the cluster of `o` avoids `a` and lies in an
arbitrary family `S` of vertex sets, the mean of `F(C_a)` is the mean of its projection onto the
cluster of `o`: given the cluster of `o`, the labels meeting it are exhausted and the cluster of
`a` is a fresh cluster in the remaining labels. -/
theorem setIntegral_clusterFamily_eq [Fintype V] [Fintype E] (H : Hypergraph V E) (a o : V)
    (F : Set V → ℝ) (S : Set (Set V)) :
    ∫ ω in avoidEvent H ({o} : Set V) ({a} : Set V) ∩
        {ω | hyperClusterSet H ω ({o} : Set V) ∈ S},
      F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) =
    ∫ ω in avoidEvent H ({o} : Set V) ({a} : Set V) ∩
        {ω | hyperClusterSet H ω ({o} : Set V) ∈ S},
      (∫ η, F (hyperClusterSet H (η \ labelsMeeting H (hyperClusterSet H ω ({o} : Set V)))
          ({a} : Set V)) ∂(prodBernoulli H.prob)) ∂(prodBernoulli H.prob) := by
  set μ := prodBernoulli H.prob with hμ
  set ψ : Set V → ℝ := fun K =>
    ∫ η, F (hyperClusterSet H (η \ labelsMeeting H K) ({a} : Set V)) ∂μ with hψ
  set P : Set (Set E) := {ω | hyperClusterSet H ω ({o} : Set V) ∈ S} with hP
  have h1 := setIntegral_avoid_eq_sum H ({o} : Set V) ({a} : Set V)
    (fun C D => if C ∈ S then F D else 0)
  have h2 := setIntegral_avoid_eq_sum H ({o} : Set V) ({a} : Set V)
    (fun C D => if C ∈ S then ψ C else 0)
  rw [setIntegral_ite H _ (fun ω => hyperClusterSet H ω ({o} : Set V) ∈ S)] at h1
  rw [setIntegral_ite H _ (fun ω => hyperClusterSet H ω ({o} : Set V) ∈ S)] at h2
  have hterm : ∀ K : Finset V,
      condMean H ({a} : Set V) (fun C D => if C ∈ S then F D else 0) (↑K : Set V) =
        condMean H ({a} : Set V) (fun C D => if C ∈ S then ψ C else 0) (↑K : Set V) := by
    intro K
    rw [condMean_of_ite, condMean_of_ite, condMean_const_fst, condMean_snd]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun K _ => by rw [hterm K]

/-- **The projection identity, in the shape used downstream.**  On disconnection of `o` from `a`
and any cluster-determined event, the cluster difference may be replaced by its projection. -/
theorem setIntegral_sub_eq_projFun [Fintype V] [Fintype E] (H : Hypergraph V E) (a o : V)
    (F : Set V → ℝ) (S : Set (Set V)) :
    ∫ ω in avoidEvent H ({o} : Set V) ({a} : Set V) ∩
        {ω | hyperClusterSet H ω ({o} : Set V) ∈ S},
      (F (hyperClusterSet H ω ({o} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
        ∂(prodBernoulli H.prob) =
    ∫ ω in avoidEvent H ({o} : Set V) ({a} : Set V) ∩
        {ω | hyperClusterSet H ω ({o} : Set V) ∈ S},
      projFun H a F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) := by
  have h1 := integral_sub (μ := (prodBernoulli H.prob).restrict
      (avoidEvent H ({o} : Set V) ({a} : Set V) ∩
        {ω | hyperClusterSet H ω ({o} : Set V) ∈ S}))
    (integrable_of_fintype fun ω => F (hyperClusterSet H ω ({o} : Set V)))
    (integrable_of_fintype fun ω => F (hyperClusterSet H ω ({a} : Set V)))
  have h2 := integral_sub (μ := (prodBernoulli H.prob).restrict
      (avoidEvent H ({o} : Set V) ({a} : Set V) ∩
        {ω | hyperClusterSet H ω ({o} : Set V) ∈ S}))
    (integrable_of_fintype fun ω => F (hyperClusterSet H ω ({o} : Set V)))
    (integrable_of_fintype fun ω =>
      ∫ η, F (hyperClusterSet H (η \ labelsMeeting H (hyperClusterSet H ω ({o} : Set V)))
        ({a} : Set V)) ∂(prodBernoulli H.prob))
  rw [h1]
  unfold projFun
  rw [h2, setIntegral_clusterFamily_eq H a o F S]

/-- The projection identity on disconnection from `a` and connection from `o` to a finite relay
set `T`. -/
theorem setIntegral_sub_eq_projFun_conn [Fintype V] [Fintype E] (H : Hypergraph V E) (a o : V)
    (F : Set V → ℝ) (T : Finset V) :
    ∫ ω in avoidEvent H ({o} : Set V) ({a} : Set V) ∩ (⋃ t ∈ T, hyperConn H o t),
      (F (hyperClusterSet H ω ({o} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)))
        ∂(prodBernoulli H.prob) =
    ∫ ω in avoidEvent H ({o} : Set V) ({a} : Set V) ∩ (⋃ t ∈ T, hyperConn H o t),
      projFun H a F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) := by
  have hset : {ω : Set E | hyperClusterSet H ω ({o} : Set V) ∈ {K : Set V | ∃ t ∈ T, t ∈ K}} =
      ⋃ t ∈ T, hyperConn H o t := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    exact exists_congr fun t => and_congr_right fun _ => (mem_hyperConn_iff H ω o t).symm
  rw [← hset]
  exact setIntegral_sub_eq_projFun H a o F {K : Set V | ∃ t ∈ T, t ∈ K}

/-- The mean of the projection on avoidance of `a` is the difference of the two unconditional
cluster means. -/
theorem setIntegral_projFun_avoid [Fintype V] [Fintype E] (H : Hypergraph V E) (a o : V)
    (F : Set V → ℝ) :
    ∫ ω in avoidEvent H ({o} : Set V) ({a} : Set V),
        projFun H a F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) =
      (∫ ω, F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob)) -
        ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob) := by
  set μ := prodBernoulli H.prob with hμ
  set A : Set (Set E) := avoidEvent H ({o} : Set V) ({a} : Set V) with hA
  set g : Set E → ℝ := fun ω =>
    F (hyperClusterSet H ω ({o} : Set V)) - F (hyperClusterSet H ω ({a} : Set V)) with hg
  have huniv : {ω : Set E | hyperClusterSet H ω ({o} : Set V) ∈ (univ : Set (Set V))} =
      (univ : Set (Set E)) := by ext ω; simp
  have hproj : ∫ ω in A, g ω ∂μ =
      ∫ ω in A, projFun H a F (hyperClusterSet H ω ({o} : Set V)) ∂μ := by
    have := setIntegral_sub_eq_projFun H a o F (univ : Set (Set V))
    rwa [huniv, Set.inter_univ] at this
  have hcompl : Aᶜ = hyperConn H o a := by
    ext ω
    simp only [hA, mem_compl_iff, mem_avoidEvent, Set.disjoint_singleton_right, not_not,
      mem_hyperConn_iff]
  have hzero : ∫ ω in Aᶜ, g ω ∂μ = 0 := by
    rw [hcompl]
    refine (setIntegral_congr_fun (measurableSet_of_fintype _)
      (g := fun _ => (0 : ℝ)) fun ω hω => ?_).trans (by simp)
    have : hyperClusterSet H ω ({o} : Set V) = hyperClusterSet H ω ({a} : Set V) :=
      hyperClusterSet_singleton_eq_of_reachable H (hω : (openHyperGraph H ω).Reachable o a)
    simp only [hg, this, sub_self]
  have hsplit := integral_add_compl (measurableSet_of_fintype A) (integrable_of_fintype (μ := μ) g)
  rw [hzero, add_zero] at hsplit
  rw [← hproj, hsplit, hg]
  exact integral_sub (integrable_of_fintype _) (integrable_of_fintype _)

/-! ## The avoided surplus

The relay mean `condMeanY`, the surplus `surplusY`, the identity
`setIntegral_eq_condMeanY_mul`, the peeling identity `surplusY_erase_add` (Lemma P) and the
comparison `kappaY_le_surplusY` (Lemma κ) are those of `KN/HyperPeel.lean`.  What is added here is
the name `firstPattern` for the pattern that the definition of `surplusY` writes out. -/

/-- The first-in-rank pattern of the relay `a`, seen from `u`: `u` reaches `a` and reaches no
relay of smaller rank. -/
def firstPattern (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (u a : V) : Set (Set E) :=
  hyperConn H u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (hyperConn H u a')ᶜ

/-! ## The first-in-rank patterns partition the contact event -/

theorem firstPattern_disjoint (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (u : V)
    (hr : Set.InjOn r ↑T) :
    Set.PairwiseDisjoint (↑T : Set V) (firstPattern H T r u) :=
  firstRank_disjoint' (hyperConn H u) T r hr

theorem firstPattern_cover (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (u : V) :
    (⋃ a ∈ T, firstPattern H T r u a) = ⋃ a ∈ T, hyperConn H u a :=
  firstRank_cover' (hyperConn H u) T r

/-- The avoided first-in-rank patterns have total measure `P(u ↮ Y, u ↔ T)`. -/
theorem sum_measureReal_avoid_firstPattern [Fintype E] (H : Hypergraph V E) (Y : Set V)
    (T : Finset V) (r : V → ℕ) (u : V) (hr : Set.InjOn r ↑T) :
    ∑ a ∈ T, (prodBernoulli H.prob).real
        (avoidEvent H ({u} : Set V) Y ∩ firstPattern H T r u a) =
      (prodBernoulli H.prob).real
        (avoidEvent H ({u} : Set V) Y ∩ ⋃ a ∈ T, hyperConn H u a) := by
  have hdisj : Set.PairwiseDisjoint (↑T : Set V)
      (fun a => avoidEvent H ({u} : Set V) Y ∩ firstPattern H T r u a) := by
    intro a ha b hb hab
    exact (firstPattern_disjoint H T r u hr ha hb hab).mono Set.inter_subset_right
      Set.inter_subset_right
  rw [← firstPattern_cover H T r u, Set.inter_iUnion₂,
    measureReal_biUnion_finset hdisj (fun a _ => measurableSet_of_fintype _)
      (fun _ _ => measure_ne_top _ _)]

/-! ## The avoided first-relay bound -/

private theorem avoidIntegral_ite [Fintype E] (H : Hypergraph V E) (S X : Set V) (o : V)
    (F : Set V → ℝ) :
    avoidIntegral H S X (fun K => if o ∈ K then F K else 0) =
      ∫ ω in avoidEvent H S X ∩ {ω | o ∈ hyperClusterSet H ω S},
        F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob) := by
  rw [avoidIntegral]
  exact setIntegral_ite H _ (fun ω => o ∈ hyperClusterSet H ω S) _

private theorem avoidIntegral_ite_one [Fintype E] (H : Hypergraph V E) (S X : Set V) (o : V) :
    avoidIntegral H S X (fun K => if o ∈ K then (1 : ℝ) else 0) =
      (prodBernoulli H.prob).real
        (avoidEvent H S X ∩ {ω | o ∈ hyperClusterSet H ω S}) := by
  rw [avoidIntegral_ite H S X o (fun _ => (1 : ℝ)), setIntegral_const, smul_eq_mul, mul_one]

/-- **The one-cluster inequality in the shape the peeling step consumes**: for a monotone `F`,
`P(k ↮ B, k ↔ o) · E[F(C_k); k ↮ B] ≤ P(k ↮ B) · E[F(C_k); k ↮ B, k ↔ o]`. -/
theorem oneCluster_contact_le [Fintype V] [Fintype E] (H : Hypergraph V E) (k o : V) (B : Set V)
    {F : Set V → ℝ} (hF : ∀ K L : Set V, K ⊆ L → F K ≤ F L) :
    (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) B ∩ hyperConn H k o) *
        (∫ ω in avoidEvent H ({k} : Set V) B, F (hyperClusterSet H ω ({k} : Set V))
          ∂(prodBernoulli H.prob)) ≤
      (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) B) *
        ∫ ω in avoidEvent H ({k} : Set V) B ∩ hyperConn H k o,
          F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob) := by
  classical
  have hconn : {ω : Set E | o ∈ hyperClusterSet H ω ({k} : Set V)} = hyperConn H k o := by
    ext ω; exact (mem_hyperConn_iff H ω k o).symm
  have hgmono : Monotone (fun K : Set V => if o ∈ K then (1 : ℝ) else 0) := by
    intro K L hKL
    dsimp only
    by_cases h : o ∈ K
    · rw [if_pos h, if_pos (hKL h)]
    · rw [if_neg h]
      split_ifs <;> norm_num
  have key := (oneClusterInequality_holds H ({k} : Set V) B).of_monotone
    (f := F) (g := fun K => if o ∈ K then (1 : ℝ) else 0) (fun K L hKL => hF K L hKL) hgmono
  have hfg : (fun K : Set V => F K * (if o ∈ K then (1 : ℝ) else 0)) =
      fun K => if o ∈ K then F K else 0 := by
    funext K
    by_cases h : o ∈ K
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hfg, avoidIntegral_ite_one, avoidIntegral_ite, hconn] at key
  rw [avoidIntegral] at key
  linarith [key]

/-- **(S5) with avoided set implies (GEN) with avoided set.**  The surplus transfer inequality is
carried as the hypothesis `hST`, exactly as in the bond template. -/
theorem genY_of_surplusTransferY [Fintype V] [Fintype E] (H : Hypergraph V E) (Y : Set V)
    (F : Set V → ℝ) (hF : ∀ S S' : Set V, S ⊆ S' → F S ≤ F S')
    (hST : ∀ (T : Finset V) (o v : V) (r : V → ℕ),
      (∀ a ∈ T, a ∉ Y) →
      (∀ a ∈ T, 0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y)) →
      v ∉ Y → v ∉ T → Set.InjOn r ↑T →
      (∀ b ∈ T, ∀ b' ∈ T, r b < r b' → condMeanY H Y F b ≤ condMeanY H Y F b') →
      (prodBernoulli H.prob).real
            (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) *
          surplusY H Y T r F v ≤
        (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
          surplusY H Y T r F o) :
    ∀ (A : Finset V) (o : V) (r : V → ℕ),
      (∀ a ∈ A, a ∉ Y) →
      (∀ a ∈ A, 0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y)) →
      Set.InjOn r ↑A →
      (∀ b ∈ A, ∀ b' ∈ A, r b < r b' → condMeanY H Y F b ≤ condMeanY H Y F b') →
      0 ≤ surplusY H Y A r F o := by
  classical
  have main : ∀ (N : ℕ) (A : Finset V) (o : V) (r : V → ℕ), A.card = N →
      (∀ a ∈ A, a ∉ Y) →
      (∀ a ∈ A, 0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y)) →
      Set.InjOn r ↑A →
      (∀ b ∈ A, ∀ b' ∈ A, r b < r b' → condMeanY H Y F b ≤ condMeanY H Y F b') →
      0 ≤ surplusY H Y A r F o := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro A o r hN hAY hact hr hcompat
    set μ := prodBernoulli H.prob with hμ
    have hn := fun (S : Set (Set E)) => (measureReal_nonneg : 0 ≤ μ.real S)
    rcases A.eq_empty_or_nonempty with hA0 | hne
    · subst hA0; simp [surplusY]
    obtain ⟨k, hkA, hkmax⟩ := Finset.exists_max_image A r hne
    set T : Finset V := A.erase k with hT
    have hTcard : T.card < N := by
      have hpos : 0 < A.card := Finset.card_pos.2 hne
      rw [hT, Finset.card_erase_of_mem hkA]; omega
    have hTA : ∀ a ∈ T, a ∈ A := fun a ha => Finset.mem_of_mem_erase ha
    have hkT : k ∉ T := Finset.notMem_erase k A
    have hlt : ∀ a ∈ T, r a < r k := by
      intro a ha
      rcases (hkmax a (hTA a ha)).lt_or_eq with h | h
      · exact h
      · exact absurd (hr (hTA a ha) hkA h) (Finset.ne_of_mem_erase ha)
    have hrT : Set.InjOn r ↑T := hr.mono (by intro a ha; exact hTA a ha)
    have hcompatT : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' →
        condMeanY H Y F b ≤ condMeanY H Y F b' :=
      fun b hb b' hb' h => hcompat b (hTA b hb) b' (hTA b' hb') h
    have hmle : ∀ a ∈ T, condMeanY H Y F a ≤ condMeanY H Y F k :=
      fun a ha => hcompat a (hTA a ha) k hkA (hlt a ha)
    have hkY : k ∉ Y := hAY k hkA
    have hTY : ∀ a ∈ T, a ∉ Y := fun a ha => hAY a (hTA a ha)
    have hactT : ∀ a ∈ T, 0 < μ.real (avoidEvent H ({a} : Set V) Y) :=
      fun a ha => hact a (hTA a ha)
    have hIH : 0 ≤ surplusY H Y T r F o := ih T.card hTcard T o r rfl hTY hactT hrT hcompatT
    have hS5 := hST T o k r hTY hactT hkY hkT hrT hcompatT
    rw [hyperConn_comm H o k] at hS5
    set Dk : Set (Set E) := avoidEvent H ({k} : Set V) (Y ∪ (↑T : Set V)) with hDk
    set Ok : Set (Set E) := hyperConn H k o with hOk
    set fk : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({k} : Set V)) with hfk
    set mk : ℝ := condMeanY H Y F k with hmk
    have hpeel : surplusY H Y A r F o = surplusY H Y T r F o +
        ((∫ ω in Dk ∩ Ok, fk ω ∂μ) - μ.real (Dk ∩ Ok) * mk) :=
      surplusY_erase_add H Y A r F hkA hlt o
    have hBHK := oneCluster_contact_le H k o (Y ∪ (↑T : Set V)) hF
    have hκ : mk * μ.real Dk - ∫ ω in Dk, fk ω ∂μ ≤ surplusY H Y T r F k :=
      kappaY_le_surplusY H Y T r F k hrT hmle
    have hkey : μ.real Dk * (mk * μ.real (Dk ∩ Ok) - ∫ ω in Dk ∩ Ok, fk ω ∂μ) ≤
        μ.real Dk * surplusY H Y T r F o := by
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
  intro A o r hAY hact hr hcompat
  exact main A.card A o r rfl hAY hact hr hcompat

/-- The sum form of (GEN) with an avoided set. -/
theorem sum_le_setIntegral_of_genY [Fintype E] (H : Hypergraph V E) (Y : Set V) (A : Finset V)
    (r : V → ℕ) (F : Set V → ℝ) (o : V) (h : 0 ≤ surplusY H Y A r F o) :
    ∑ a ∈ A, (prodBernoulli H.prob).real
          (avoidEvent H ({o} : Set V) Y ∩ firstPattern H A r o a) * condMeanY H Y F a ≤
      ∫ ω in avoidEvent H ({o} : Set V) Y ∩ ⋃ a ∈ A, hyperConn H o a,
        F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) := by
  unfold surplusY at h
  unfold firstPattern
  linarith

end KNAll.Site

end

#print axioms KNAll.Site.monotone_projFun
#print axioms KNAll.Site.setIntegral_clusterFamily_eq
#print axioms KNAll.Site.setIntegral_sub_eq_projFun
#print axioms KNAll.Site.setIntegral_sub_eq_projFun_conn
#print axioms KNAll.Site.setIntegral_projFun_avoid
#print axioms KNAll.Site.projFun_eq_deleteHyper
#print axioms KNAll.Site.sum_measureReal_avoid_firstPattern
#print axioms KNAll.Site.oneCluster_contact_le
#print axioms KNAll.Site.genY_of_surplusTransferY
#print axioms KNAll.Site.sum_le_setIntegral_of_genY
