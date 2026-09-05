import Hypergraph.HyperStarH
import Hypergraph.HyperGluingTail
import Hypergraph.PinnedGluing

/-!
# From the hypergraph CSH to pinned site gluing

This file contains only the downstream, model-independent closure.  Its single substantive input
is the conditioned slack hierarchy at strictly interior label probabilities.  From that input, the
already proved peeling and endpoint-closure modules give avoided GEN at arbitrary probabilities;
the projection argument then gives `HyperFixedClusterComparison`.  The existing short tails give
`HyperedgeGluing` and `PinnedSiteGluing`.

The point of isolating this implication is diagnostic: it does not assert the CSH input and hence
cannot make the final theorem vacuous.  In particular, the owner/observer distinctness conditions
needed by the peeling theorem are displayed in `HyperCSHInterior` below.  Coincident or forbidden
observer positions are handled by `avoidSurplusTransfer_nondegenerate_of_margin`, whose proof splits
those cases before invoking the hierarchy.
-/

noncomputable section

namespace KNAll.Site.HyperFixedFromCSH

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

/-- The precise interior-weight CSH input consumed by the existing avoided peeling theorem. -/
def HyperCSHInterior : Prop :=
  ∀ (W L : Type) [Fintype W] [Fintype L] (H : Hypergraph W L),
    (∀ e, 0 < H.prob e ∧ H.prob e < 1) →
    ∀ (x : W) (Y : Set W) (D : List W) (o v : W),
      x ∉ Y → o ≠ x → v ≠ x → o ∉ Y → v ∉ Y → o ≠ v → D.Nodup →
      (∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      CSHHolds H x Y D o v

@[simp] theorem avoidMean_eq_condMeanY {V E : Type*} [Fintype V] [Fintype E]
    (H : Hypergraph V E) (Y : Set V) (F : Set V → ℝ) (a : V) :
    avoidMean H Y F a = condMeanY H Y F a := rfl

@[simp] theorem firstPat_eq_firstPattern {V E : Type*} [Fintype V] [Fintype E]
    (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (u a : V) :
    firstPat H T r u a = firstPattern H T r u a := rfl

@[simp] theorem avoidSurplus_eq_surplusY {V E : Type*} [Fintype V] [Fintype E]
    (H : Hypergraph V E) (Y : Set V) (T : Finset V) (r : V → ℕ)
    (F : Set V → ℝ) (u : V) :
    avoidSurplus H Y T r F u = surplusY H Y T r F u := rfl

/-- The interior CSH gives the avoided surplus transfer at arbitrary label probabilities. -/
theorem surplusTransferY_of_cshInterior (hCSH : HyperCSHInterior)
    {V E : Type} [Fintype V] [Fintype E] (H : Hypergraph V E) (Y : Set V)
    (T : Finset V) (o v : V) (F : Set V → ℝ)
    (hTY : ∀ a ∈ T, a ∉ Y)
    (hact : ∀ a ∈ T,
      0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y))
    (hvY : v ∉ Y) (hvT : v ∉ T)
    (hF : ∀ K K' : Set V, K ⊆ K' → F K ≤ F K')
    (r : V → ℕ) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMeanY H Y F a ≤ condMeanY H Y F a') :
    (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) *
        surplusY H Y T r F v ≤
      (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
        surplusY H Y T r F o := by
  have key := avoidSurplusTransfer_of_margin H Y T o v F hvY hvT
    (fun p hp r' hr' hc' hoY hoT hov => by
      have hcore : ∀ (x : V) (Y' : Set V) (D : List V),
          x ∉ Y' → o ≠ x → v ≠ x → o ∉ Y' → v ∉ Y' → D.Nodup →
          (∀ d ∈ D, d ≠ x ∧ d ∉ Y' ∧ d ≠ o ∧ d ≠ v) →
          CSHHolds (withProb H p) x Y' D o v := by
        intro x Y' D hxY' hox hvx hoY' hvY' hD hdis
        exact hCSH V E (withProb H p) (by simpa using hp)
          x Y' D o v hxY' hox hvx hoY' hvY' hov hD hdis
      have hm := surplusMarginY_nonneg_of_csh (withProb H p) hp Y o v hoY hvY hcore
        T r' [] F hF hr' (by simpa using hc') hTY hoT hvT List.nodup_nil
        (fun d hd => absurd hd (List.not_mem_nil))
      rw [surplusMarginY_nil] at hm
      simpa using hm)
    hact r hr (by simpa using hcompat)
  simpa using key

/-- Avoided GEN at arbitrary label probabilities, from the interior CSH. -/
theorem genY_of_cshInterior (hCSH : HyperCSHInterior)
    {V E : Type} [Fintype V] [Fintype E] (H : Hypergraph V E) (Y : Set V)
    (F : Set V → ℝ) (hF : ∀ K K' : Set V, K ⊆ K' → F K ≤ F K')
    (A : Finset V) (o : V) (r : V → ℕ)
    (hAY : ∀ a ∈ A, a ∉ Y)
    (hact : ∀ a ∈ A,
      0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y))
    (hr : Set.InjOn r ↑A)
    (hcompat : ∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
      condMeanY H Y F a ≤ condMeanY H Y F a') :
    0 ≤ surplusY H Y A r F o :=
  genY_of_surplusTransferY H Y F hF
    (fun T o' v r' hTY hactT hvY hvT hr' hc' =>
      surplusTransferY_of_cshInterior hCSH H Y T o' v F hTY hactT hvY hvT hF r' hr' hc')
    A o r hAY hact hr hcompat

/-- The fixed-minimizer comparison follows from avoided GEN. -/
theorem hyperFixedClusterComparison_of_cshInterior (hCSH : HyperCSHInterior) :
    HyperFixedClusterComparison := by
  intro W L _ _ H A o a F haA hF hmin
  set μ := prodBernoulli H.prob with hμ
  have hmeas : ∀ S : Set (Set L), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hn := fun (S : Set (Set L)) => (measureReal_nonneg : 0 ≤ μ.real S)
  have hint : ∀ (g : Set L → ℝ) (S : Set (Set L)), IntegrableOn g S μ :=
    fun _ _ => (Integrable.of_finite).integrableOn

  set Phi : Set W → ℝ := projFun H a F with hPhi
  have hPhiMono : ∀ K K' : Set W, K ⊆ K' → Phi K ≤ Phi K' :=
    fun K K' hKK' => monotone_projFun H a F hF hKK'
  set T : Finset W := (A.erase a).filter
    (fun x => 0 < μ.real (avoidEvent H ({x} : Set W) ({a} : Set W))) with hT
  have hTA : ∀ x ∈ T, x ∈ A.erase a := fun x hx => (Finset.mem_filter.1 hx).1
  have hTY : ∀ x ∈ T, x ∉ ({a} : Set W) := fun x hx hxa =>
    Finset.ne_of_mem_erase (hTA x hx) (Set.mem_singleton_iff.1 hxa)
  have hact : ∀ x ∈ T,
      0 < μ.real (avoidEvent H ({x} : Set W) ({a} : Set W)) :=
    fun x hx => (Finset.mem_filter.1 hx).2
  have hmean : ∀ x ∈ T, 0 ≤ condMeanY H ({a} : Set W) Phi x := by
    intro x hx
    unfold condMeanY avoidIntegral
    refine div_nonneg ?_ (hn _)
    rw [hPhi, setIntegral_projFun_avoid H a x F]
    linarith [hmin x (Finset.mem_of_mem_erase (hTA x hx))]
  obtain ⟨r, hr, hcompat⟩ := exists_rank_compat T (condMeanY H ({a} : Set W) Phi)
  have hgen := genY_of_cshInterior hCSH H ({a} : Set W) Phi hPhiMono T o r
    hTY hact hr hcompat
  have hsum := sum_le_setIntegral_of_genY H ({a} : Set W) T r Phi o hgen
  have hsum0 : 0 ≤ ∑ x ∈ T,
      μ.real (avoidEvent H ({o} : Set W) ({a} : Set W) ∩ firstPattern H T r o x) *
        condMeanY H ({a} : Set W) Phi x :=
    Finset.sum_nonneg fun x hx => mul_nonneg (hn _) (hmean x hx)

  set Av : Set (Set L) := avoidEvent H ({o} : Set W) ({a} : Set W) with hAv
  set g : Set L → ℝ := fun omega =>
    F (hyperClusterSet H omega ({o} : Set W)) -
      F (hyperClusterSet H omega ({a} : Set W)) with hg
  have hET : 0 ≤ ∫ omega in Av ∩ ⋃ t ∈ T, hyperConn H o t, g omega ∂μ := by
    have hproj := setIntegral_sub_eq_projFun_conn H a o F T
    rw [hg, hAv, hproj, ← hμ]
    exact hsum0.trans hsum

  set UA : Set (Set L) := ⋃ x ∈ A, hyperConn H o x with hUA
  set EE : Set (Set L) := Av ∩ ⋃ x ∈ A.erase a, hyperConn H o x with hEE
  set ET : Set (Set L) := Av ∩ ⋃ t ∈ T, hyperConn H o t with hETdef
  have hAv' : ∀ omega, omega ∈ Av ↔ ¬ (openHyperGraph H omega).Reachable o a := by
    intro omega
    simp [hAv, mem_avoidEvent, hyperClusterSet]
  have hg0 : ∀ omega ∈ hyperConn H o a, g omega = 0 := by
    intro omega hoa
    simp only [hg]
    rw [hyperClusterSet_singleton_eq_of_reachable H hoa, sub_self]
  have hUA_split : ∫ omega in UA, g omega ∂μ = ∫ omega in EE, g omega ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas (hyperConn H o a)) (hint g UA)]
    have hzero : ∫ omega in UA ∩ hyperConn H o a, g omega ∂μ = 0 := by
      rw [setIntegral_congr_fun (hmeas _) (fun omega homega => hg0 omega homega.2)]
      simp
    have hdiff : UA \ hyperConn H o a = EE := by
      ext omega
      simp only [hUA, hEE, Set.mem_sdiff, Set.mem_iUnion, exists_prop,
        Set.mem_inter_iff, hAv' omega, Finset.mem_erase]
      constructor
      · rintro ⟨⟨x, hx, hox⟩, hna⟩
        exact ⟨hna, x, ⟨fun hxa => hna (hxa ▸ hox), hx⟩, hox⟩
      · rintro ⟨hna, x, ⟨_, hx⟩, hox⟩
        exact ⟨⟨x, hx, hox⟩, hna⟩
    rw [hzero, zero_add, hdiff]

  have hETEE : ET ⊆ EE := fun omega homega => ⟨homega.1, by
    obtain ⟨t, ht, hot⟩ := Set.mem_iUnion₂.1 homega.2
    exact Set.mem_iUnion₂.2 ⟨t, hTA t ht, hot⟩⟩
  have hnull : μ (EE \ ET) = 0 := by
    have hsub : EE \ ET ⊆ ⋃ x ∈ (A.erase a).filter
        (fun x => ¬ 0 < μ.real (avoidEvent H ({x} : Set W) ({a} : Set W))),
        avoidEvent H ({x} : Set W) ({a} : Set W) := by
      intro omega homega
      obtain ⟨⟨hA1, hA2⟩, hnot⟩ := homega
      obtain ⟨x, hx, hox⟩ := Set.mem_iUnion₂.1 hA2
      have hxT : x ∉ T := fun hxT =>
        hnot ⟨hA1, Set.mem_iUnion₂.2 ⟨x, hxT, hox⟩⟩
      have hinact : ¬ 0 < μ.real (avoidEvent H ({x} : Set W) ({a} : Set W)) :=
        fun hpos => hxT (Finset.mem_filter.2 ⟨hx, hpos⟩)
      refine Set.mem_iUnion₂.2 ⟨x, Finset.mem_filter.2 ⟨hx, hinact⟩, ?_⟩
      exact (mem_avoidEvent_singleton_iff H ({a} : Set W) x omega).2
        (fun y hy hxy => by
          rw [Set.mem_singleton_iff] at hy
          subst y
          exact (hAv' omega).1 hA1 (hox.trans hxy))
    refine measure_mono_null hsub
      (measure_biUnion_null_iff (Finset.countable_toSet _) |>.2 fun x hx => ?_)
    have hzero : μ.real (avoidEvent H ({x} : Set W) ({a} : Set W)) = 0 :=
      le_antisymm (not_lt.1 (Finset.mem_filter.1 hx).2) (hn _)
    rwa [Measure.real, ENNReal.toReal_eq_zero_iff,
      or_iff_left (measure_ne_top _ _)] at hzero
  have hEE_split : ∫ omega in EE, g omega ∂μ = ∫ omega in ET, g omega ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas ET) (hint g EE),
      inter_eq_right.2 hETEE, Measure.restrict_eq_zero.2 hnull,
      integral_zero_measure, add_zero]
  have hfinal : 0 ≤ ∫ omega in UA, g omega ∂μ := by
    rw [hUA_split, hEE_split]
    exact hET
  rw [hg, integral_sub (hint _ _) (hint _ _)] at hfinal
  linarith

/-- The existing finite and site tails, with the CSH dependency exposed once. -/
theorem hyperedgeGluing_of_cshInterior (hCSH : HyperCSHInterior) : HyperedgeGluing :=
  hyperedgeGluing_of_fixedClusterComparison
    (hyperFixedClusterComparison_of_cshInterior hCSH)

theorem pinnedSiteGluing_of_cshInterior (hCSH : HyperCSHInterior) : PinnedSiteGluing :=
  pinnedSiteGluing_of_hyperedgeGluing (hyperedgeGluing_of_cshInterior hCSH)

end KNAll.Site.HyperFixedFromCSH

end

#print axioms KNAll.Site.HyperFixedFromCSH.surplusTransferY_of_cshInterior
#print axioms KNAll.Site.HyperFixedFromCSH.genY_of_cshInterior
#print axioms KNAll.Site.HyperFixedFromCSH.hyperFixedClusterComparison_of_cshInterior
#print axioms KNAll.Site.HyperFixedFromCSH.hyperedgeGluing_of_cshInterior
#print axioms KNAll.Site.HyperFixedFromCSH.pinnedSiteGluing_of_cshInterior
