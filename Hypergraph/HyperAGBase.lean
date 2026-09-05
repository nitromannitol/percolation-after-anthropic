import Hypergraph.HyperDecisionTree
import Hypergraph.HyperTwoClusterClosed
import Hypergraph.ProdBernoulliFKG

/-!
# The base layer of additive gluing, for hyperedges

The hyperedge form of the three base files of the bond development's additive gluing layer:
`Percolation/Continuity/AdditiveGluing/GenPair.lean`,
`Percolation/Continuity/AdditiveGluing/BystanderCluster.lean` and
`Percolation/Continuity/AdditiveGluing/SandwichPrelim.lean`.  Nothing here depends on any other
part of that layer.

The main result is `gen_pair`, the localised union bound for two relays: for a monotone
nonnegative functional `F` of vertex sets, an observer `o` and relays `a₁, a₂` whose unconditional
means are ordered by `m₁ ≤ m₂`,

  `P(o ↔ a₁)·m₁ + P(o ↔ a₂, o ↮ a₁)·m₂ ≤ ∫_{o ↔ a₁ ∨ o ↔ a₂} F(C(o))`.

The value of `F` on the observer's cluster, when the observer holds a relay, is on average at
least the mean value of the least-valued relay it holds.  The bond proof is van den
Berg–Häggström–Kahn's Theorems 1.3 and 1.4 applied four times, together with Harris' inequality;
here the four applications are the hyperedge forms already proved in `KN/HyperOneCluster.lean` and
`KN/HyperTwoCluster.lean`, discharged by `KN/HyperTwoClusterClosed.lean`:

* the two positive-association steps are `oneClusterInequality_holds`, the denominator-free form
  of conditional positive association of two increasing functionals of one cluster, at the pairs of
  vertex sets `({a₂}, {a₁})` and `({a₁}, {a₂})`;
* the two negative-correlation steps are `avoid_cluster_negCorrelation` at the same pairs.

In both, the increasing functional carrying the observer is `indMem o`, whose value at the cluster
of a relay `a` is the indicator of `{o ↔ a}`.

The bond file has to translate between vertex clusters and edge clusters, because the conditional
association theorems there are stated for the edge cluster of a source and a vertex functional has
to be presented as `F {a | a = a₂ ∨ ∃ e ∈ C, a ∈ e}`; the hyperedge development states its
conditional association theorems directly for the vertex cluster `hyperClusterSet`, so that
translation disappears.  The bond file also has to treat `a₁ = a₂` separately, because the
conditional association theorems it quotes carry `a₁ ≠ a₂`; the hyperedge forms carry no such
hypothesis and the degenerate case needs no separate treatment.

Every declaration lives in `KNAll.Site.AGBase`.  The monotonicity of the indicator of an
increasing event is `KNAll.Site.monotone_ind_of_isUpperSet` of `KN/HyperDecisionTree.lean` and is
used, not reproved.  `hyperClusterSet_singleton_eq` repeats
`KNAll.Site.hyperClusterSet_singleton_eq_of_reachable` of `KN/HyperPeel.lean`, which is not
imported here because it would make this base module depend on
`Percolation.Continuity.CSH.PeelTools`.

Two small tools of the bond base layer are restated: the indicator congruence of
`BystanderCluster.lean`, which is not about graphs at all, and the endpoint lemma of
`SandwichPrelim.lean`, whose hyperedge form reads the surviving vertex off the incidence set of
the label crossing the last step.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006), Thms. 1.1, 1.3–1.5.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
* G. Kozma, S. Nitzan, Thm. 7 (p. 32) with Thm. 1 (pp. 7–8).
-/

noncomputable section

namespace KNAll.Site.AGBase

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg
  indicator_eq_mul_ind)

variable {V E : Type*}

/-! ## Two tools of the bond base layer -/

/-- Indicators of equivalent memberships agree.  The content of
`Percolation/Continuity/AdditiveGluing/BystanderCluster.lean`; it mentions no graph. [folklore] -/
theorem ind_congr {α β : Type*} {D : Set α} {D' : Set β} {a : α} {b : β} (h : a ∈ D ↔ b ∈ D') :
    ind D a = ind D' b := by
  by_cases ha : a ∈ D
  · rw [ind_of_mem ha, ind_of_mem (h.1 ha)]
  · rw [ind_of_not_mem ha, ind_of_not_mem fun hb => ha (h.2 hb)]

/-- The endpoint of a nontrivial open path of the model induced on `U` lies in `U`.  The hyperedge
form of the endpoint lemma of `Percolation/Continuity/AdditiveGluing/SandwichPrelim.lean`: there
one reads the surviving vertex off the second endpoint of the crossing edge, here off the
incidence set of the crossing label, which is contained in `U` because `labelsIn` asks that *every*
incident vertex survive. [folklore] -/
theorem mem_of_reachable {H : Hypergraph V E} {U : Finset V} {ω : Set E} {x y : V}
    (h : (openHyperGraph H (ω ∩ labelsIn H U)).Reachable x y) (hne : x ≠ y) : y ∈ U := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, -, hcy⟩
  · exact absurd rfl hne
  · obtain ⟨-, e, he, -, hy⟩ := (openHyperGraph_adj_iff H _ c y).1 hcy
    exact he.2 y hy

/-! ## The cluster of a single vertex -/

/-- Reachable vertices have the same cluster. -/
theorem hyperClusterSet_singleton_eq (H : Hypergraph V E) {ω : Set E} {x y : V}
    (h : (openHyperGraph H ω).Reachable x y) :
    hyperClusterSet H ω ({x} : Set V) = hyperClusterSet H ω ({y} : Set V) := by
  ext z
  constructor
  · rintro ⟨u, hu, hr⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact ⟨y, rfl, h.symm.trans hr⟩
  · rintro ⟨u, hu, hr⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact ⟨x, rfl, h.trans hr⟩

/-- Avoiding one vertex from another is failing to reach it. -/
theorem mem_avoidEvent_pair (H : Hypergraph V E) (x y : V) (ω : Set E) :
    ω ∈ avoidEvent H ({x} : Set V) ({y} : Set V) ↔ ¬ (openHyperGraph H ω).Reachable x y := by
  rw [mem_avoidEvent, Set.disjoint_singleton_right]
  constructor
  · intro h hr
    exact h ⟨x, rfl, hr⟩
  · rintro h ⟨u, hu, hr⟩
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact h hr

/-- The avoidance event of two single vertices is symmetric in them. -/
theorem avoidEvent_pair_symm (H : Hypergraph V E) (x y : V) :
    avoidEvent H ({x} : Set V) ({y} : Set V) = avoidEvent H ({y} : Set V) ({x} : Set V) := by
  ext ω
  rw [mem_avoidEvent_pair, mem_avoidEvent_pair]
  exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

/-! ## The observer as a functional of a vertex set -/

open Classical in
/-- The indicator that a vertex set contains `o`, as a functional of the vertex set.  This is the
increasing functional whose value at the cluster of a relay is the indicator of the connection
event between the relay and `o`. -/
def indMem (o : V) (K : Set V) : ℝ := if o ∈ K then 1 else 0

theorem indMem_nonneg (o : V) (K : Set V) : 0 ≤ indMem o K := by
  unfold indMem
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem monotone_indMem (o : V) : Monotone (indMem o) := by
  intro K K' hKK'
  unfold indMem
  by_cases h : o ∈ K
  · rw [if_pos h, if_pos (hKK' h)]
  · rw [if_neg h]
    split_ifs
    · exact zero_le_one
    · exact le_rfl

/-- Its value at the cluster of `a` is the indicator of `{o ↔ a}`. -/
theorem indMem_hyperClusterSet (H : Hypergraph V E) (o a : V) (ω : Set E) :
    indMem o (hyperClusterSet H ω ({a} : Set V)) = ind (hyperConn H o a) ω := by
  have hiff : o ∈ hyperClusterSet H ω ({a} : Set V) ↔ ω ∈ hyperConn H o a := by
    constructor
    · rintro ⟨u, hu, hr⟩
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact hr.symm
    · intro h
      exact ⟨a, rfl, (h : (openHyperGraph H ω).Reachable o a).symm⟩
  unfold indMem
  by_cases h : o ∈ hyperClusterSet H ω ({a} : Set V)
  · rw [if_pos h, ind_of_mem (hiff.1 h)]
  · rw [if_neg h, ind_of_not_mem fun hc => h (hiff.2 hc)]

/-! ## Integrals against an indicator -/

section Indicator

variable [Fintype E] {μ : Measure (Set E)}

theorem integral_ind (A : Set (Set E)) : ∫ ω, ind A ω ∂μ = μ.real A := by
  rw [← integral_indicator_one (measurableSet_of_fintype A)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  rw [indicator_eq_mul_ind, Pi.one_apply, one_mul]

theorem integral_mul_ind (A : Set (Set E)) (k : Set E → ℝ) :
    ∫ ω, k ω * ind A ω ∂μ = ∫ ω in A, k ω ∂μ := by
  rw [← integral_indicator (measurableSet_of_fintype A)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  rw [indicator_eq_mul_ind]

theorem setIntegral_mul_ind (T A : Set (Set E)) (k : Set E → ℝ) :
    ∫ ω in T, k ω * ind A ω ∂μ = ∫ ω in T ∩ A, k ω ∂μ := by
  rw [← setIntegral_indicator (measurableSet_of_fintype A)]
  refine setIntegral_congr_fun (measurableSet_of_fintype T) fun ω _ => ?_
  rw [indicator_eq_mul_ind]

theorem setIntegral_ind_mul (T A : Set (Set E)) (k : Set E → ℝ) :
    ∫ ω in T, ind A ω * k ω ∂μ = ∫ ω in T ∩ A, k ω ∂μ := by
  rw [← setIntegral_mul_ind T A k]
  refine setIntegral_congr_fun (measurableSet_of_fintype T) fun ω _ => ?_
  rw [mul_comm]

theorem setIntegral_ind (T A : Set (Set E)) : ∫ ω in T, ind A ω ∂μ = μ.real (T ∩ A) := by
  have h := setIntegral_ind_mul (μ := μ) T A fun _ => (1 : ℝ)
  simp only [mul_one, setIntegral_const, smul_eq_mul] at h
  rw [h]

end Indicator

/-! ## Harris' inequality in integral form -/

/-- **Harris, integral form**: for `F` monotone on vertex sets and an increasing event `U`,
`P(U) · ∫ F(C(S)) ≤ ∫_U F(C(S))`.  The cluster grows with the configuration, so `ω ↦ F(C(S))` is
increasing; the indicator of an increasing event is increasing; Harris for two increasing functions
under `prodBernoulli` is `prodBernoulli_integral_mul_le`.  Nonnegativity of `F` is not needed:
`prodBernoulli_integral_mul_le` has already been freed of it.
[cite: HarrisPCPS1960, Lemma 4.1] -/
theorem setIntegral_clusterFun_ge [Fintype E] (H : Hypergraph V E) (S : Set V) (F : Set V → ℝ)
    (hF : Monotone F) (U : Set (Set E)) (hU : IsUpperSet U) :
    (prodBernoulli H.prob).real U * ∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)
      ≤ ∫ ω in U, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob) := by
  have key := prodBernoulli_integral_mul_le H.prob
    (f := fun ω => F (hyperClusterSet H ω S)) (g := fun ω => ind U ω)
    (fun _ _ h => hF (hyperClusterSet_mono H S h)) (monotone_ind_of_isUpperSet hU)
  rw [integral_ind, integral_mul_ind] at key
  calc (prodBernoulli H.prob).real U * ∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)
      = (∫ ω, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) *
          (prodBernoulli H.prob).real U := mul_comm _ _
    _ ≤ _ := key

/-! ## The arithmetic of the four applications -/

/-- The real-number content of `gen_pair`, with every probability and every integral abstracted.
The names are those of the proof below: `pD, p1, p2` are the probabilities of `D`, `D ∩ O₁` and
`D ∩ O₂`, `IU0, IU1, IU2` the integrals of `F(C(o)), F(C(a₁)), F(C(a₂))` over `U`, `ID1, ID2` their
integrals over `D`, `J1, J2` their integrals over `D ∩ O₂` and `K1, K2` over `D ∩ O₁`.
[cite: KozmaNitzan2024, Thm. 7] -/
private theorem gen_pair_core {pD p1 p2 pO1 pc pU IU0 IU1 IU2 ID1 ID2 J1 J2 K1 K2 m₁ m₂ : ℝ}
    (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hpc : 0 ≤ pc)
    (hp1D : p1 ≤ pD) (hp2D : p2 ≤ pD)
    (hdiff1 : IU0 - IU1 = J2 - J1) (hdiff2 : IU0 - IU2 = K1 - K2)
    (h_i : p2 * ID2 ≤ pD * J2) (h_ii : pD * J1 ≤ p2 * ID1)
    (h_iii : p1 * ID1 ≤ pD * K1) (h_iv : pD * K2 ≤ p1 * ID2)
    (hHU1 : pU * m₁ ≤ IU1) (hHU2 : pU * m₂ ≤ IU2)
    (hUmeas : pU = pO1 + pc) (hx2 : pc ≤ p2) (hx1 : p1 ≤ pO1)
    (hm : m₁ ≤ m₂) (hE_O1 : pO1 * m₁ ≤ IU0) :
    pO1 * m₁ + pc * m₂ ≤ IU0 := by
  have key1 : p2 * (ID2 - ID1) ≤ pD * (IU0 - IU1) := by
    rw [hdiff1, mul_sub, mul_sub]
    linarith
  have key2 : p1 * (ID1 - ID2) ≤ pD * (IU0 - IU2) := by
    rw [hdiff2, mul_sub, mul_sub]
    linarith
  have key6 : 0 ≤ pD * (p1 * (IU0 - IU1) + p2 * (IU0 - IU2)) := by
    nlinarith [mul_le_mul_of_nonneg_left key1 hp1, mul_le_mul_of_nonneg_left key2 hp2]
  by_cases hx : p1 + p2 = 0
  · have hx2z : p2 = 0 := by linarith
    have h0 : pc = 0 := le_antisymm (hx2.trans hx2z.le) hpc
    rw [h0, zero_mul, add_zero]
    exact hE_O1
  · have hxpos : 0 < p1 + p2 := lt_of_le_of_ne (by linarith) (Ne.symm hx)
    have hDpos : 0 < pD := by linarith
    have h6 : 0 ≤ p1 * (IU0 - IU1) + p2 * (IU0 - IU2) := by
      by_contra hneg
      have hlt := mul_neg_of_pos_of_neg hDpos (lt_of_not_ge hneg)
      linarith
    have hprod : pc * p1 ≤ p2 * pO1 := mul_le_mul hx2 hx1 hp1 hp2
    have hm' : 0 ≤ m₂ - m₁ := by linarith
    have hgoal : 0 ≤ (p1 + p2) * (IU0 - (pO1 * m₁ + pc * m₂)) := by
      have hA : p1 * (pU * m₁) ≤ p1 * IU1 := mul_le_mul_of_nonneg_left hHU1 hp1
      have hB : p2 * (pU * m₂) ≤ p2 * IU2 := mul_le_mul_of_nonneg_left hHU2 hp2
      rw [hUmeas] at hA hB
      nlinarith [h6, hA, hB, mul_le_mul_of_nonneg_left hprod hm']
    by_contra hlt
    have hneg : (p1 + p2) * (IU0 - (pO1 * m₁ + pc * m₂)) < 0 :=
      mul_neg_of_pos_of_neg hxpos (by linarith [lt_of_not_ge hlt])
    linarith

/-! ## (GEN) for two relays -/

/-- **(GEN) for two relays, for hyperedges.**  For `F` monotone and nonnegative on vertex sets,
relays `a₁, a₂` with `∫ F(C(a₁)) ≤ ∫ F(C(a₂))`, and an observer `o`,

  `P(o ↔ a₁)·∫ F(C(a₁)) + P(o ↔ a₂, o ↮ a₁)·∫ F(C(a₂)) ≤ ∫_{o ↔ a₁ ∨ o ↔ a₂} F(C(o))`.

The four conditional correlation inequalities are `oneClusterInequality_holds` and
`avoid_cluster_negCorrelation` at the two ordered pairs of relays, the increasing functional of a
relay's cluster in each of them being `indMem o`, whose value at `C(a)` is the indicator of
`{o ↔ a}`.
[cite: KozmaNitzan2024, Thm. 7 with Thm. 1]
[cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5] -/
theorem gen_pair [Fintype V] [Fintype E] (H : Hypergraph V E) (o a₁ a₂ : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hm : ∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob)
        ≤ ∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) :
    (prodBernoulli H.prob).real (hyperConn H o a₁) *
          (∫ ω, F (hyperClusterSet H ω ({a₁} : Set V)) ∂(prodBernoulli H.prob)) +
        (prodBernoulli H.prob).real (hyperConn H o a₂ ∩ (hyperConn H o a₁)ᶜ) *
          (∫ ω, F (hyperClusterSet H ω ({a₂} : Set V)) ∂(prodBernoulli H.prob)) ≤
      ∫ ω in hyperConn H o a₁ ∪ hyperConn H o a₂,
        F (hyperClusterSet H ω ({o} : Set V)) ∂(prodBernoulli H.prob) := by
  classical
  have hFmono : Monotone F := fun S T hST => hF S T hST
  set μ := prodBernoulli H.prob with hμ
  set f₀ : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({o} : Set V)) with hf₀
  set f₁ : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({a₁} : Set V)) with hf₁
  set f₂ : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({a₂} : Set V)) with hf₂
  set m₁ : ℝ := ∫ ω, f₁ ω ∂μ with hm₁
  set m₂ : ℝ := ∫ ω, f₂ ω ∂μ with hm₂
  set O₁ : Set (Set E) := hyperConn H o a₁ with hO₁
  set O₂ : Set (Set E) := hyperConn H o a₂ with hO₂
  set D : Set (Set E) := avoidEvent H ({a₁} : Set V) ({a₂} : Set V) with hD
  set U : Set (Set E) := O₁ ∪ O₂ with hU
  have hmeas : ∀ T : Set (Set E), MeasurableSet T := fun _ => measurableSet_of_fintype _
  have hint : ∀ (k : Set E → ℝ) (T : Set (Set E)), IntegrableOn k T μ :=
    fun k T => (integrable_of_fintype (μ := μ) k).integrableOn
  have hn : ∀ T : Set (Set E), 0 ≤ μ.real T := fun _ => measureReal_nonneg
  have hup : ∀ x y : V, IsUpperSet (hyperConn H x y) := fun x y => isUpperSet_hyperConn H x y
  have hUup : IsUpperSet U := (hup o a₁).union (hup o a₂)
  have hDmem : ∀ ω : Set E, ω ∈ D ↔ ¬ (openHyperGraph H ω).Reachable a₁ a₂ :=
    mem_avoidEvent_pair H a₁ a₂
  have hOmem : ∀ (x y : V) (ω : Set E),
      ω ∈ hyperConn H x y ↔ (openHyperGraph H ω).Reachable x y := fun _ _ _ => Iff.rfl
  -- Harris in integral form
  have hHU1 : μ.real U * m₁ ≤ ∫ ω in U, f₁ ω ∂μ :=
    setIntegral_clusterFun_ge H ({a₁} : Set V) F hFmono U hUup
  have hHU2 : μ.real U * m₂ ≤ ∫ ω in U, f₂ ω ∂μ :=
    setIntegral_clusterFun_ge H ({a₂} : Set V) F hFmono U hUup
  have hHO1 : μ.real O₁ * m₁ ≤ ∫ ω in O₁, f₁ ω ∂μ :=
    setIntegral_clusterFun_ge H ({a₁} : Set V) F hFmono O₁ (hup o a₁)
  -- the observer's cluster is the relay's cluster on the connection event
  have h01 : ∀ ω ∈ O₁, f₀ ω = f₁ ω := fun ω hω => by
    show F (hyperClusterSet H ω ({o} : Set V)) = F (hyperClusterSet H ω ({a₁} : Set V))
    rw [hyperClusterSet_singleton_eq H (hω : (openHyperGraph H ω).Reachable o a₁)]
  have h02 : ∀ ω ∈ O₂, f₀ ω = f₂ ω := fun ω hω => by
    show F (hyperClusterSet H ω ({o} : Set V)) = F (hyperClusterSet H ω ({a₂} : Set V))
    rw [hyperClusterSet_singleton_eq H (hω : (openHyperGraph H ω).Reachable o a₂)]
  -- the degenerate bound
  have hE_O1 : μ.real O₁ * m₁ ≤ ∫ ω in U, f₀ ω ∂μ := by
    have h1 : ∫ ω in O₁, f₁ ω ∂μ = ∫ ω in O₁, f₀ ω ∂μ :=
      (setIntegral_congr_fun (hmeas O₁) h01).symm
    have h2 : ∫ ω in O₁, f₀ ω ∂μ ≤ ∫ ω in U, f₀ ω ∂μ :=
      setIntegral_mono_set (hint f₀ U) (Filter.Eventually.of_forall fun ω => hF0 _)
        (Filter.Eventually.of_forall (subset_union_left : O₁ ⊆ U))
    linarith
  -- the measure identities
  have hsplitμ : ∀ A S : Set (Set E), μ.real A = μ.real (A ∩ S) + μ.real (A ∩ Sᶜ) := by
    intro A S
    rw [← measureReal_inter_add_sdiff (s := A) (h := measure_ne_top _ _) (hmeas S), Set.sdiff_eq]
  have hUmeasure : μ.real U = μ.real O₁ + μ.real (O₂ ∩ O₁ᶜ) := by
    rw [hsplitμ U O₁]
    congr 1
    · rw [inter_eq_right.2 subset_union_left]
    · congr 1
      ext ω
      simp only [hU, mem_inter_iff, mem_union, mem_compl_iff]
      tauto
  have hx2 : μ.real (O₂ ∩ O₁ᶜ) ≤ μ.real (D ∩ O₂) := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    rintro ω ⟨h2, hn1⟩
    refine ⟨(hDmem ω).2 fun h12 => ?_, h2⟩
    rw [hO₁, mem_compl_iff, hOmem] at hn1
    rw [hO₂, hOmem] at h2
    exact hn1 (h2.trans h12.symm)
  have hx1 : μ.real (D ∩ O₁) ≤ μ.real O₁ := measureReal_mono inter_subset_right (measure_ne_top _ _)
  have hp1D : μ.real (D ∩ O₁) ≤ μ.real D := measureReal_mono inter_subset_left (measure_ne_top _ _)
  have hp2D : μ.real (D ∩ O₂) ≤ μ.real D := measureReal_mono inter_subset_left (measure_ne_top _ _)
  -- the set identities
  have hU1 : U \ O₁ = D ∩ O₂ := by
    ext ω
    simp only [hU, hO₁, hO₂, mem_sdiff, mem_union, mem_inter_iff, hDmem ω, hOmem]
    constructor
    · rintro ⟨h1 | h2, hn1⟩
      · exact absurd h1 hn1
      · exact ⟨fun h => hn1 (h2.trans h.symm), h2⟩
    · rintro ⟨hnr, h2⟩
      exact ⟨Or.inr h2, fun h1 => hnr (h1.symm.trans h2)⟩
  have hU2 : U \ O₂ = D ∩ O₁ := by
    ext ω
    simp only [hU, hO₁, hO₂, mem_sdiff, mem_union, mem_inter_iff, hDmem ω, hOmem]
    constructor
    · rintro ⟨h1 | h2, hn2⟩
      · exact ⟨fun h => hn2 (h1.trans h), h1⟩
      · exact absurd h2 hn2
    · rintro ⟨hnr, h1⟩
      exact ⟨Or.inl h1, fun h2 => hnr (h1.symm.trans h2)⟩
  have hO1U : U ∩ O₁ = O₁ := inter_eq_right.2 subset_union_left
  have hO2U : U ∩ O₂ = O₂ := inter_eq_right.2 subset_union_right
  have hsplit : ∀ (k : Set E → ℝ) (T : Set (Set E)),
      ∫ ω in U, k ω ∂μ = ∫ ω in U ∩ T, k ω ∂μ + ∫ ω in U \ T, k ω ∂μ :=
    fun k T => (integral_inter_add_sdiff (hmeas T) (hint k U)).symm
  have hdiff1 : ∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₁ ω ∂μ =
      ∫ ω in D ∩ O₂, f₂ ω ∂μ - ∫ ω in D ∩ O₂, f₁ ω ∂μ := by
    rw [hsplit f₀ O₁, hsplit f₁ O₁, hO1U, hU1, setIntegral_congr_fun (hmeas O₁) h01,
      setIntegral_congr_fun ((hmeas D).inter (hmeas O₂)) fun ω hω => h02 ω hω.2]
    ring
  have hdiff2 : ∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₂ ω ∂μ =
      ∫ ω in D ∩ O₁, f₁ ω ∂μ - ∫ ω in D ∩ O₁, f₂ ω ∂μ := by
    rw [hsplit f₀ O₂, hsplit f₂ O₂, hO2U, hU2, setIntegral_congr_fun (hmeas O₂) h02,
      setIntegral_congr_fun ((hmeas D).inter (hmeas O₁)) fun ω hω => h01 ω hω.2]
    ring
  -- the four conditional correlation inequalities
  have h_i : μ.real (D ∩ O₂) * (∫ ω in D, f₂ ω ∂μ) ≤ μ.real D * ∫ ω in D ∩ O₂, f₂ ω ∂μ := by
    have key := oneClusterInequality_holds H ({a₂} : Set V) ({a₁} : Set V) F (indMem o)
      hFmono (monotone_indMem o) hF0 fun K => indMem_nonneg o K
    simp only [avoidIntegral, avoidEvent_pair_symm H a₂ a₁, indMem_hyperClusterSet,
      setIntegral_mul_ind, setIntegral_ind] at key
    rw [← hμ, ← hD, ← hO₂] at key
    linarith
  have h_ii : μ.real D * (∫ ω in D ∩ O₂, f₁ ω ∂μ) ≤ μ.real (D ∩ O₂) * ∫ ω in D, f₁ ω ∂μ := by
    have key := avoid_cluster_negCorrelation H ({a₂} : Set V) ({a₁} : Set V)
      (oneClusterInequality_holds H ({a₂} : Set V) ({a₁} : Set V))
      (F := indMem o) (G := F) (monotone_indMem o) hFmono
    simp only [avoidEvent_pair_symm H a₂ a₁, indMem_hyperClusterSet, setIntegral_ind_mul,
      setIntegral_ind] at key
    rw [← hμ, ← hD, ← hO₂] at key
    linarith
  have h_iii : μ.real (D ∩ O₁) * (∫ ω in D, f₁ ω ∂μ) ≤ μ.real D * ∫ ω in D ∩ O₁, f₁ ω ∂μ := by
    have key := oneClusterInequality_holds H ({a₁} : Set V) ({a₂} : Set V) F (indMem o)
      hFmono (monotone_indMem o) hF0 fun K => indMem_nonneg o K
    simp only [avoidIntegral, indMem_hyperClusterSet, setIntegral_mul_ind, setIntegral_ind] at key
    rw [← hμ, ← hD, ← hO₁] at key
    linarith
  have h_iv : μ.real D * (∫ ω in D ∩ O₁, f₂ ω ∂μ) ≤ μ.real (D ∩ O₁) * ∫ ω in D, f₂ ω ∂μ := by
    have key := avoid_cluster_negCorrelation H ({a₁} : Set V) ({a₂} : Set V)
      (oneClusterInequality_holds H ({a₁} : Set V) ({a₂} : Set V))
      (F := indMem o) (G := F) (monotone_indMem o) hFmono
    simp only [indMem_hyperClusterSet, setIntegral_ind_mul, setIntegral_ind] at key
    rw [← hμ, ← hD, ← hO₁] at key
    linarith
  exact gen_pair_core (hn (D ∩ O₁)) (hn (D ∩ O₂)) (hn (O₂ ∩ O₁ᶜ)) hp1D hp2D hdiff1 hdiff2
    h_i h_ii h_iii h_iv hHU1 hHU2 hUmeasure hx2 hx1 hm hE_O1

end KNAll.Site.AGBase

end
