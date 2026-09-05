import Hypergraph.HyperAvoid
import Hypergraph.BondRepresentation

/-!
# The avoided surplus transfer for the hyperedge model, and its closure to arbitrary label
probabilities

The hypergraph form of `KN/AvoidedTransfer.lean` and `KN/AvoidedClosure.lean`, over an arbitrary
vertex type and a finite label type.  The bond development writes the avoidance condition as
`∀ y ∈ Y, ¬ (openGraph ω).Reachable u y`; here it is `avoidEvent H {u} Y` of `KN/HyperAvoid.lean`,
the event that the cluster of `u` is disjoint from `Y`.

* `avoidMean` — the conditional relay mean `m_a^Y = E[F(C_a); C_a ∩ Y = ∅] / P(C_a ∩ Y = ∅)`, with
  the junk value `0` when the denominator vanishes;
* `firstPat` — the first-in-rank pattern `{u ↔ a} ∩ ⋂_{a' ∈ T, r a' < r a} {u ↮ a'}`;
* `avoidSurplus` — `Sur^Y_u(T) = E[F(C_u); C_u ∩ Y = ∅, u ↔ T] − Σ_{a ∈ T} P(C_u ∩ Y = ∅, P^u_a)·m_a^Y`;
* `avoidSurplus_nonneg_of_mem`, `avoidSurplus_eq_zero_of_mem` — the two special observer positions;
* `avoidSurplusTransfer_nondegenerate_of_margin` — the transfer inequality
  `P(v ↮ Y ∪ T, o ↔ v)·Sur^Y_v(T) ≤ P(v ↮ Y ∪ T)·Sur^Y_o(T)` at strictly interior label
  probabilities, from the decoy-free margin, for every observer position;
* `avoidSurplus_eq_minForm` — the ranked surplus equals the rank-free form
  `∫_{C_u ∩ Y = ∅, u ↔ T} (F(C_u) − min_{a ∈ T, u ↔ a} m_a^Y)`, for every injective rank compatible
  with the means.  This is what makes the closure possible: the rank compatible with the means at
  one weight need not be compatible at a neighbouring weight, so the ranked surplus is not a
  function of the weight alone, whereas the minimum form is;
* `continuousAt_avoidMean`, `continuousAt_minForm` — continuity of the minimum form at a weight at
  which every relay's avoidance event has positive probability.  The restriction is real: the
  conditional mean is a quotient, and only the positivity of its denominator makes it continuous;
* `avoidSurplusTransfer_of_nondegenerate` — the transfer at arbitrary label probabilities from the
  transfer at strictly interior ones, by density of the interior weights and continuity at the
  target weight alone;
* `avoidSurplusTransfer_of_margin` — the composite, in the shape the avoided first-relay induction
  consumes.

The last section specializes everything along `KNAll.Bond.bondHypergraph` and re-derives the bond
theorems `KNAll.surplusTransferY_nondegenerate_of_margin` and
`KNAll.surplusTransferY_of_nondegenerate` from the hypergraph ones.

`avoidMean`, `firstPat` and `avoidSurplus` are the conditional relay mean, the first-in-rank
pattern and the avoided surplus of the hypergraph peeling and first-relay modules, with the same
bodies; the identifications are `rfl`.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Literature.BHK2006 (weight integral_prodBernoulli_eq_sum continuous_weight)
open scoped Classical

variable {V E : Type*}

/-! ## Definitions -/

/-- The avoided conditional relay mean. -/
def avoidMean (H : Hypergraph V E) (Y : Set V) (F : Set V → ℝ) (a : V) : ℝ :=
  avoidIntegral H ({a} : Set V) Y F /
    (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y)

/-- The first-in-rank pattern of the relay `a` seen from `u`. -/
def firstPat (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (u a : V) : Set (Set E) :=
  hyperConn H u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (hyperConn H u a')ᶜ

/-- The avoided surplus. -/
def avoidSurplus (H : Hypergraph V E) (Y : Set V) (T : Finset V) (r : V → ℕ)
    (F : Set V → ℝ) (u : V) : ℝ :=
  (∫ ω in avoidEvent H ({u} : Set V) Y ∩ ⋃ a ∈ T, hyperConn H u a,
      F (hyperClusterSet H ω ({u} : Set V)) ∂(prodBernoulli H.prob)) -
    ∑ a ∈ T, (prodBernoulli H.prob).real
        (avoidEvent H ({u} : Set V) Y ∩ firstPat H T r u a) * avoidMean H Y F a

/-! ## Elementary facts about the singleton avoidance event -/

theorem mem_avoidEvent_singleton_iff (H : Hypergraph V E) (X : Set V) (u : V) (ω : Set E) :
    ω ∈ avoidEvent H ({u} : Set V) X ↔
      ∀ y ∈ X, ¬ (openHyperGraph H ω).Reachable u y := by
  simp only [mem_avoidEvent, Set.disjoint_left, hyperClusterSet, mem_setOf_eq,
    mem_singleton_iff, exists_eq_left]
  constructor
  · intro h y hy hr; exact h hr hy
  · intro h y hr hy; exact h y hy hr

theorem avoidEvent_singleton_eq_empty (H : Hypergraph V E) {X : Set V} {u : V} (hu : u ∈ X) :
    avoidEvent H ({u} : Set V) X = ∅ :=
  eq_empty_of_forall_notMem fun ω hω =>
    (mem_avoidEvent_singleton_iff H X u ω).1 hω u hu (SimpleGraph.Reachable.refl u)

theorem openHyperGraph_empty (H : Hypergraph V E) : openHyperGraph H (∅ : Set E) = ⊥ := by
  ext x y
  simp only [openHyperGraph, SimpleGraph.fromRel_adj, SimpleGraph.bot_adj,
    Set.mem_empty_iff_false, false_and, exists_false, or_self, and_false]

theorem empty_mem_avoidEvent_singleton (H : Hypergraph V E) {X : Set V} {u : V} (hu : u ∉ X) :
    (∅ : Set E) ∈ avoidEvent H ({u} : Set V) X := by
  refine (mem_avoidEvent_singleton_iff H X u ∅).2 fun y hy hr => ?_
  rw [openHyperGraph_empty, SimpleGraph.reachable_bot] at hr
  exact hu (hr ▸ hy)

/-! ## The first-in-rank patterns -/

theorem firstPat_disjoint (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (u : V)
    (hr : Set.InjOn r ↑T) :
    Set.PairwiseDisjoint (↑T : Set V) (fun a => firstPat H T r u a) := by
  intro a ha b hb hne
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  rcases lt_or_gt_of_ne (fun h => hne (hr ha hb h)) with hlt | hlt
  · have hna : ω ∈ (hyperConn H u a)ᶜ := by
      have h := h2.2
      rw [Set.mem_iInter₂] at h
      exact h a (Finset.mem_filter.2 ⟨ha, hlt⟩)
    exact hna h1.1
  · have hna : ω ∈ (hyperConn H u b)ᶜ := by
      have h := h1.2
      rw [Set.mem_iInter₂] at h
      exact h b (Finset.mem_filter.2 ⟨hb, hlt⟩)
    exact hna h2.1

theorem firstPat_cover (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (u : V) :
    (⋃ a ∈ T, firstPat H T r u a) = ⋃ a ∈ T, hyperConn H u a := by
  ext ω
  simp only [firstPat, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
  constructor
  · rintro ⟨a, ha, h1, _⟩
    exact ⟨a, ha, h1⟩
  · rintro ⟨a, ha, h1⟩
    have hne : (T.filter fun a' => ω ∈ hyperConn H u a').Nonempty :=
      ⟨a, Finset.mem_filter.2 ⟨ha, h1⟩⟩
    obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image _ r hne
    rw [Finset.mem_filter] at ha₀
    refine ⟨a₀, ha₀.1, ha₀.2, ?_⟩
    rw [Set.mem_iInter₂]
    intro a' ha'
    rw [Finset.mem_filter] at ha'
    intro hω
    have := hmin a' (Finset.mem_filter.2 ⟨ha'.1, hω⟩)
    exact absurd ha'.2 (not_lt.2 this)

theorem sum_measureReal_firstPat [Fintype E] (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (r : V → ℕ) (u : V) (hr : Set.InjOn r ↑T) :
    ∑ a ∈ T, (prodBernoulli H.prob).real
        (avoidEvent H ({u} : Set V) Y ∩ firstPat H T r u a) =
      (prodBernoulli H.prob).real
        (avoidEvent H ({u} : Set V) Y ∩ ⋃ a ∈ T, hyperConn H u a) := by
  have hmeas : ∀ S : Set (Set E), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hdisj : Set.PairwiseDisjoint (↑T : Set V)
      (fun a => avoidEvent H ({u} : Set V) Y ∩ firstPat H T r u a) := fun a ha b hb hab =>
    (firstPat_disjoint H T r u hr ha hb hab).mono inter_subset_right inter_subset_right
  rw [← firstPat_cover H T r u, inter_iUnion₂,
    measureReal_biUnion_finset hdisj (fun a _ => hmeas _) (fun _ _ => measure_ne_top _ _)]

/-- `∫_{a ↮ Y} F(C_a) = m_a^Y · P(a ↮ Y)`, junk value included. -/
theorem avoidIntegral_eq_avoidMean_mul (H : Hypergraph V E) (Y : Set V) (F : Set V → ℝ) (a : V) :
    avoidIntegral H ({a} : Set V) Y F =
      avoidMean H Y F a * (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y) := by
  unfold avoidMean
  by_cases h0 : (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y) = 0
  · rw [h0, mul_zero]
    have hz : (prodBernoulli H.prob) (avoidEvent H ({a} : Set V) Y) = 0 := by
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h0
    rw [avoidIntegral, Measure.restrict_eq_zero.2 hz, integral_zero_measure]
  · rw [div_mul_cancel₀ _ h0]

/-! ## The surplus at special observer positions -/

/-- An observer inside the relay set has nonnegative avoided surplus. -/
theorem avoidSurplus_nonneg_of_mem [Fintype E] (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (r : V → ℕ) (F : Set V → ℝ) (o : V) (hoT : o ∈ T) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' → avoidMean H Y F a ≤ avoidMean H Y F a') :
    0 ≤ avoidSurplus H Y T r F o := by
  unfold avoidSurplus
  set μ := prodBernoulli H.prob with hμ
  set Av : Set (Set E) := avoidEvent H ({o} : Set V) Y with hAv
  have hn := fun (S : Set (Set E)) => (measureReal_nonneg : 0 ≤ μ.real S)
  have hle : ∀ a ∈ T, μ.real (Av ∩ firstPat H T r o a) * avoidMean H Y F a ≤
      μ.real (Av ∩ firstPat H T r o a) * avoidMean H Y F o := by
    intro a ha
    rcases (Av ∩ firstPat H T r o a).eq_empty_or_nonempty with h0 | ⟨ω, hω⟩
    · rw [h0, measureReal_empty, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (hn _)
      have hnot : ¬ r o < r a := by
        intro hlt
        have h2 := hω.2.2
        rw [Set.mem_iInter₂] at h2
        exact h2 o (Finset.mem_filter.2 ⟨hoT, hlt⟩) (SimpleGraph.Reachable.refl _)
      rcases (not_lt.1 hnot).lt_or_eq with hlt | heq
      · exact hcompat a ha o hoT hlt
      · rw [hr ha hoT heq]
  have hsum : ∑ a ∈ T, μ.real (Av ∩ firstPat H T r o a) * avoidMean H Y F a ≤
      avoidMean H Y F o * μ.real (Av ∩ ⋃ a ∈ T, hyperConn H o a) := by
    calc ∑ a ∈ T, μ.real (Av ∩ firstPat H T r o a) * avoidMean H Y F a
        ≤ ∑ a ∈ T, μ.real (Av ∩ firstPat H T r o a) * avoidMean H Y F o := Finset.sum_le_sum hle
      _ = avoidMean H Y F o * μ.real (Av ∩ ⋃ a ∈ T, hyperConn H o a) := by
        rw [← Finset.sum_mul, mul_comm, sum_measureReal_firstPat H Y T r o hr]
  have hU : (Av ∩ ⋃ a ∈ T, hyperConn H o a) = Av := by
    refine inter_eq_left.2 fun ω _ => ?_
    exact mem_iUnion₂.2 ⟨o, hoT, SimpleGraph.Reachable.refl _⟩
  have hI : ∫ ω in Av, F (hyperClusterSet H ω ({o} : Set V)) ∂μ = avoidMean H Y F o * μ.real Av :=
    avoidIntegral_eq_avoidMean_mul H Y F o
  rw [hU] at hsum ⊢
  rw [hI]
  linarith

/-- An observer inside the avoided set has zero avoided surplus. -/
theorem avoidSurplus_eq_zero_of_mem (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (r : V → ℕ) (F : Set V → ℝ) (o : V) (hoY : o ∈ Y) : avoidSurplus H Y T r F o = 0 := by
  unfold avoidSurplus
  simp [avoidEvent_singleton_eq_empty H hoY]

/-! ## The transfer inequality -/

/-- The product form of the decoy-free margin bound. -/
theorem avoidSurplus_transfer_of_margin_nonneg (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (r : V → ℕ) (o v : V) (F : Set V → ℝ)
    (hpos : 0 < (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))))
    (h : 0 ≤ avoidSurplus H Y T r F o -
      (prodBernoulli H.prob).real
          (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) /
        (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
          avoidSurplus H Y T r F v) :
    (prodBernoulli H.prob).real
        (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) *
        avoidSurplus H Y T r F v ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
        avoidSurplus H Y T r F o := by
  set M := (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) with hM
  set N := (prodBernoulli H.prob).real
    (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) with hN
  have h2 : 0 ≤ M * (avoidSurplus H Y T r F o - N / M * avoidSurplus H Y T r F v) :=
    mul_nonneg hpos.le h
  have h3 : M * (avoidSurplus H Y T r F o - N / M * avoidSurplus H Y T r F v) =
      M * avoidSurplus H Y T r F o - N * avoidSurplus H Y T r F v := by
    field_simp
  linarith [h2, h3]

/-- **The avoided surplus transfer at non-degenerate weights, every observer position.** -/
theorem avoidSurplusTransfer_nondegenerate_of_margin [Fintype E] (H : Hypergraph V E)
    (hw : ∀ e, 0 < H.prob e ∧ H.prob e < 1) (Y : Set V) (T : Finset V) (o v : V)
    (F : Set V → ℝ) (r : V → ℕ) (hvY : v ∉ Y) (hvT : v ∉ T) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → avoidMean H Y F b ≤ avoidMean H Y F b')
    (hmarg : o ∉ Y → o ∉ T → o ≠ v →
      0 ≤ avoidSurplus H Y T r F o -
        (prodBernoulli H.prob).real
            (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) /
          (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
            avoidSurplus H Y T r F v) :
    (prodBernoulli H.prob).real
        (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) *
        avoidSurplus H Y T r F v ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
        avoidSurplus H Y T r F o := by
  set μ := prodBernoulli H.prob with hμ
  have hn := fun (S : Set (Set E)) => (measureReal_nonneg : 0 ≤ μ.real S)
  by_cases hov : o = v
  · subst hov
    have hOO : hyperConn H o o = (univ : Set (Set E)) :=
      eq_univ_of_forall fun ω => SimpleGraph.Reachable.refl _
    rw [hOO, inter_univ]
  have hempty : o ∈ Y ∪ (↑T : Set V) →
      (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) = ∅ := by
    intro ho
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    exact (mem_avoidEvent_singleton_iff H (Y ∪ (↑T : Set V)) v ω).1 hω.1 o ho
      (SimpleGraph.Reachable.symm hω.2)
  by_cases hoY : o ∈ Y
  · rw [hempty (Or.inl hoY), measureReal_empty, zero_mul,
      avoidSurplus_eq_zero_of_mem H Y T r F o hoY, mul_zero]
  by_cases hoT : o ∈ T
  · rw [hempty (Or.inr (Finset.mem_coe.2 hoT)), measureReal_empty, zero_mul]
    exact mul_nonneg (hn _) (avoidSurplus_nonneg_of_mem H Y T r F o hoT hr hcompat)
  · have hne : (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))).Nonempty := by
      refine ⟨∅, empty_mem_avoidEvent_singleton H ?_⟩
      rw [mem_union, not_or]
      exact ⟨hvY, fun h => hvT (Finset.mem_coe.1 h)⟩
    have hpos := prodBernoulli_real_pos_of_nonempty hw hne
    exact avoidSurplus_transfer_of_margin_nonneg H Y T r o v F hpos (hmarg hoY hoT hov)

/-! ## Reparametrising the label probabilities -/

/-- The same incidence structure with the label probabilities replaced. -/
def withProb (H : Hypergraph V E) (p : E → unitInterval) : Hypergraph V E where
  incidence := H.incidence
  prob := p

@[simp] theorem withProb_prob (H : Hypergraph V E) (p : E → unitInterval) :
    (withProb H p).prob = p := rfl

@[simp] theorem withProb_incidence (H : Hypergraph V E) (p : E → unitInterval) :
    (withProb H p).incidence = H.incidence := rfl

theorem withProb_self (H : Hypergraph V E) : withProb H H.prob = H := rfl

@[simp] theorem hyperConn_withProb (H : Hypergraph V E) (p : E → unitInterval) (x y : V) :
    hyperConn (withProb H p) x y = hyperConn H x y := rfl

@[simp] theorem hyperClusterSet_withProb (H : Hypergraph V E) (p : E → unitInterval)
    (ω : Set E) (S : Set V) : hyperClusterSet (withProb H p) ω S = hyperClusterSet H ω S := rfl

@[simp] theorem avoidEvent_withProb (H : Hypergraph V E) (p : E → unitInterval) (S X : Set V) :
    avoidEvent (withProb H p) S X = avoidEvent H S X := rfl

@[simp] theorem firstPat_withProb (H : Hypergraph V E) (p : E → unitInterval) (T : Finset V)
    (r : V → ℕ) (u a : V) : firstPat (withProb H p) T r u a = firstPat H T r u a := rfl

/-! ## A score-compatible injective rank -/

private theorem scoreFilter_ssubset [LinearOrder V] (T : Finset V) (s : V → ℝ) {a b : V}
    (ha : a ∈ T) (hlt : s a < s b ∨ (s a = s b ∧ a < b)) :
    (T.filter fun a' => s a' < s a ∨ (s a' = s a ∧ a' < a)) ⊂
      (T.filter fun a' => s a' < s b ∨ (s a' = s b ∧ a' < b)) := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rcases hx.2 with h1 | ⟨h1, h2⟩
    · rcases hlt with h3 | ⟨h3, _⟩
      · exact Or.inl (h1.trans h3)
      · exact Or.inl (h3 ▸ h1)
    · rcases hlt with h3 | ⟨h3, h4⟩
      · exact Or.inl (h1 ▸ h3)
      · exact Or.inr ⟨h1.trans h3, h2.trans h4⟩
  · intro heq
    have hmem : a ∈ T.filter fun a' => s a' < s b ∨ (s a' = s b ∧ a' < b) :=
      Finset.mem_filter.2 ⟨ha, hlt⟩
    rw [← heq, Finset.mem_filter] at hmem
    rcases hmem.2 with h | ⟨_, h⟩
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h

/-- **A score-compatible injective rank exists** on any vertex type. -/
theorem exists_rank_compat (T : Finset V) (s : V → ℝ) :
    ∃ r : V → ℕ, Set.InjOn r ↑T ∧ ∀ a ∈ T, ∀ a' ∈ T, r a < r a' → s a ≤ s a' := by
  letI : LinearOrder V := linearOrderOfSTO WellOrderingRel
  refine ⟨fun a => (T.filter fun a' => s a' < s a ∨ (s a' = s a ∧ a' < a)).card, ?_, ?_⟩
  · intro a ha b hb h
    by_contra hne
    rcases lt_trichotomy (s a) (s b) with hlt | heq | hgt
    · exact absurd h (Finset.card_lt_card (scoreFilter_ssubset T s ha (Or.inl hlt))).ne
    · rcases lt_or_gt_of_ne hne with h1 | h1
      · exact absurd h (Finset.card_lt_card (scoreFilter_ssubset T s ha (Or.inr ⟨heq, h1⟩))).ne
      · exact absurd h.symm
          (Finset.card_lt_card (scoreFilter_ssubset T s hb (Or.inr ⟨heq.symm, h1⟩))).ne
    · exact absurd h.symm (Finset.card_lt_card (scoreFilter_ssubset T s hb (Or.inl hgt))).ne
  · intro a _ a' ha' h
    by_contra hle
    exact lt_asymm h
      (Finset.card_lt_card (scoreFilter_ssubset T s ha' (Or.inl (lt_of_not_ge hle))))

/-! ## The rank-free minimum form -/

/-- On the first-in-rank pattern of `a` the minimum of the means over the attached relays is the
mean at `a`. -/
theorem inf'_eq_of_mem_firstPat (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (m : V → ℝ)
    (x a : V) (ha : a ∈ T) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → m b ≤ m b') (ω : Set E)
    (hω : ω ∈ firstPat H T r x a)
    (hne : (T.filter fun b => ω ∈ hyperConn H x b).Nonempty) :
    (T.filter fun b => ω ∈ hyperConn H x b).inf' hne m = m a := by
  have haF : a ∈ T.filter fun b => ω ∈ hyperConn H x b := Finset.mem_filter.2 ⟨ha, hω.1⟩
  refine le_antisymm (Finset.inf'_le m haF) (Finset.le_inf' hne m fun b hb => ?_)
  rw [Finset.mem_filter] at hb
  have hnot : ¬ r b < r a := by
    intro hlt
    have h2 := hω.2
    rw [Set.mem_iInter₂] at h2
    exact h2 b (Finset.mem_filter.2 ⟨hb.1, hlt⟩) hb.2
  rcases (not_lt.1 hnot).lt_or_eq with hlt | heq
  · exact hcompat a ha b hb.1 hlt
  · rw [hr ha hb.1 heq]

/-- The avoided ranked surplus equals its rank-free minimum form for an injective rank compatible
with the avoided conditional relay means. -/
theorem avoidSurplus_eq_minForm [Fintype E] (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (r : V → ℕ) (F : Set V → ℝ) (x : V) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → avoidMean H Y F b ≤ avoidMean H Y F b') :
    avoidSurplus H Y T r F x =
      ∫ ω in avoidEvent H ({x} : Set V) Y ∩ ⋃ a ∈ T, hyperConn H x a,
        (F (hyperClusterSet H ω ({x} : Set V)) -
          (if h : (T.filter fun b => ω ∈ hyperConn H x b).Nonempty then
            (T.filter fun b => ω ∈ hyperConn H x b).inf' h (fun b => avoidMean H Y F b)
          else 0)) ∂(prodBernoulli H.prob) := by
  set μ := prodBernoulli H.prob with hμ
  set m : V → ℝ := fun b => avoidMean H Y F b with hm
  set g : Set E → ℝ := fun ω =>
    if h : (T.filter fun b => ω ∈ hyperConn H x b).Nonempty then
      (T.filter fun b => ω ∈ hyperConn H x b).inf' h m
    else 0 with hg
  set Av : Set (Set E) := avoidEvent H ({x} : Set V) Y with hAv
  have hmeas : ∀ S : Set (Set E), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (f : Set E → ℝ) (S : Set (Set E)), IntegrableOn f S μ :=
    fun _ _ => (Integrable.of_finite).integrableOn
  have hg_pat : ∀ a ∈ T, ∀ ω ∈ Av ∩ firstPat H T r x a, g ω = m a := by
    intro a ha ω hω
    have hne : (T.filter fun b => ω ∈ hyperConn H x b).Nonempty :=
      ⟨a, Finset.mem_filter.2 ⟨ha, hω.2.1⟩⟩
    simp only [hg, hne, dif_pos]
    exact inf'_eq_of_mem_firstPat H T r m x a ha hr hcompat ω hω.2 hne
  have hdisj : Set.PairwiseDisjoint (↑T : Set V) (fun a => Av ∩ firstPat H T r x a) :=
    fun a ha b hb hab =>
      (firstPat_disjoint H T r x hr ha hb hab).mono inter_subset_right inter_subset_right
  have hsum : ∑ a ∈ T, μ.real (Av ∩ firstPat H T r x a) * m a =
      ∫ ω in Av ∩ ⋃ a ∈ T, hyperConn H x a, g ω ∂μ := by
    rw [← firstPat_cover H T r x, inter_iUnion₂,
      integral_biUnion_finset T (fun a _ => hmeas (Av ∩ firstPat H T r x a)) hdisj
        (fun a _ => hint g (Av ∩ firstPat H T r x a))]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [setIntegral_congr_fun (hmeas (Av ∩ firstPat H T r x a)) (hg_pat a ha),
      setIntegral_const, smul_eq_mul]
  unfold avoidSurplus
  rw [integral_sub (hint _ _) (hint _ _), ← hsum]

/-! ## Continuity in the label probabilities -/

private theorem continuousAt_setIntegral_weights [Fintype E] (U : Set (Set E))
    (q : (E → unitInterval) → Set E → ℝ) (w : E → unitInterval)
    (hq : ∀ ω, ContinuousAt (fun p => q p ω) w) :
    ContinuousAt (fun p : E → unitInterval => ∫ ω in U, q p ω ∂(prodBernoulli p)) w := by
  have hU : MeasurableSet U := MeasurableSet.of_discrete
  have he : (fun p : E → unitInterval => ∫ ω in U, q p ω ∂(prodBernoulli p)) =
      fun p => ∑ ω : Set E, weight (fun e => (p e : ℝ)) ω * U.indicator (q p) ω := by
    funext p
    rw [← integral_indicator hU, integral_prodBernoulli_eq_sum]
  rw [he]
  refine tendsto_finsetSum Finset.univ fun ω _ =>
    (continuous_weight ω).continuousAt.mul ?_
  by_cases hω : ω ∈ U
  · simp only [indicator_of_mem hω]
    exact hq ω
  · simp only [indicator_of_notMem hω]
    exact continuousAt_const

/-- The avoided conditional relay mean is continuous at every weight where its conditioning event
has positive probability. -/
theorem continuousAt_avoidMean [Fintype E] (H : Hypergraph V E) (Y : Set V) (F : Set V → ℝ)
    (a : V) (w : E → unitInterval)
    (hw : 0 < (prodBernoulli w).real (avoidEvent H ({a} : Set V) Y)) :
    ContinuousAt (fun p : E → unitInterval => avoidMean (withProb H p) Y F a) w := by
  simp only [avoidMean, avoidIntegral, avoidEvent_withProb, hyperClusterSet_withProb,
    withProb_prob]
  have hnum : ContinuousAt (fun p : E → unitInterval =>
      ∫ ω in avoidEvent H ({a} : Set V) Y, F (hyperClusterSet H ω ({a} : Set V))
        ∂(prodBernoulli p)) w :=
    continuousAt_setIntegral_weights _ (fun _ ω => F (hyperClusterSet H ω ({a} : Set V))) w
      (fun _ => continuousAt_const)
  have hden : ContinuousAt (fun p : E → unitInterval =>
      (prodBernoulli p).real (avoidEvent H ({a} : Set V) Y)) w :=
    (prodBernoulli_real_continuous _).continuousAt
  exact ContinuousAt.div₀ hnum hden hw.ne'

/-- The avoided minimum form is continuous at weights at which every relay is active. -/
theorem continuousAt_minForm [Fintype E] (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (F : Set V → ℝ) (x : V) (w : E → unitInterval)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli w).real (avoidEvent H ({a} : Set V) Y)) :
    ContinuousAt (fun p : E → unitInterval =>
      ∫ ω in avoidEvent H ({x} : Set V) Y ∩ ⋃ a ∈ T, hyperConn H x a,
        (F (hyperClusterSet H ω ({x} : Set V)) -
          (if h : (T.filter fun b => ω ∈ hyperConn H x b).Nonempty then
            (T.filter fun b => ω ∈ hyperConn H x b).inf' h
              (fun b => avoidMean (withProb H p) Y F b)
          else 0)) ∂(prodBernoulli p)) w := by
  refine continuousAt_setIntegral_weights _ _ w fun ω => continuousAt_const.sub ?_
  by_cases hne : (T.filter fun b => ω ∈ hyperConn H x b).Nonempty
  · simp only [hne, dif_pos]
    exact ContinuousAt.finset_inf'_apply hne fun b hb =>
      continuousAt_avoidMean H Y F b w (hact b (Finset.mem_filter.1 hb).1)
  · simp only [hne, dif_neg, not_false_eq_true]
    exact continuousAt_const

/-- Pointwise closure principle using continuity only at the target weight. -/
theorem weights_le_of_forall_pos_lt_one_at {ι : Type*} {f g : (ι → unitInterval) → ℝ}
    (w : ι → unitInterval) (hf : ContinuousAt f w) (hg : ContinuousAt g w)
    (h : ∀ p, (∀ e, 0 < p e ∧ p e < 1) → f p ≤ g p) : f w ≤ g w := by
  let N : Set (ι → unitInterval) := {p | ∀ e, 0 < p e ∧ p e < 1}
  have hN : Dense N := by
    simpa only [N] using
      (dense_setOf_weights_pos_lt_one : Dense {p : ι → unitInterval | ∀ e, 0 < p e ∧ p e < 1})
  have hwN : w ∈ closure N := by
    rw [hN.closure_eq]; exact mem_univ w
  letI : Filter.NeBot (nhdsWithin w N) := mem_closure_iff_nhdsWithin_neBot.1 hwN
  have hft : Filter.Tendsto f (nhdsWithin w N) (nhds (f w)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hgt : Filter.Tendsto g (nhdsWithin w N) (nhds (g w)) :=
    hg.tendsto.mono_left nhdsWithin_le_nhds
  have hfg : ∀ᶠ p in nhdsWithin w N, f p ≤ g p :=
    eventually_nhdsWithin_of_forall fun p hp => h p hp
  exact le_of_tendsto_of_tendsto hft hgt hfg

/-! ## The passage to arbitrary label probabilities -/

/-- **The avoided surplus transfer at arbitrary label probabilities** follows from the same
assertion at non-degenerate ones, provided every relay is active at the target probabilities. -/
theorem avoidSurplusTransfer_of_nondegenerate [Fintype E] (H : Hypergraph V E) (Y : Set V)
    (T : Finset V) (o v : V) (F : Set V → ℝ)
    (h : ∀ p : E → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ r : V → ℕ, Set.InjOn r ↑T →
        (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
          avoidMean (withProb H p) Y F a ≤ avoidMean (withProb H p) Y F a') →
        (prodBernoulli p).real
            (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) *
              avoidSurplus (withProb H p) Y T r F v ≤
          (prodBernoulli p).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
              avoidSurplus (withProb H p) Y T r F o)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y))
    (r : V → ℕ) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' → avoidMean H Y F a ≤ avoidMean H Y F a') :
    (prodBernoulli H.prob).real
        (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) *
          avoidSurplus H Y T r F v ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
          avoidSurplus H Y T r F o := by
  set S : V → (E → unitInterval) → ℝ := fun x p =>
    ∫ ω in avoidEvent H ({x} : Set V) Y ∩ ⋃ a ∈ T, hyperConn H x a,
      (F (hyperClusterSet H ω ({x} : Set V)) -
        (if hh : (T.filter fun b => ω ∈ hyperConn H x b).Nonempty then
          (T.filter fun b => ω ∈ hyperConn H x b).inf' hh
            (fun b => avoidMean (withProb H p) Y F b)
        else 0)) ∂(prodBernoulli p) with hS
  set f : (E → unitInterval) → ℝ := fun p =>
    (prodBernoulli p).real
        (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) * S v p with hf
  set g : (E → unitInterval) → ℝ := fun p =>
    (prodBernoulli p).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) * S o p with hg
  have hfc : ContinuousAt f H.prob := by
    simp only [hf, hS]
    exact ((prodBernoulli_real_continuous
          (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩
            hyperConn H o v)).continuousAt.mul
        (continuousAt_minForm H Y T F v H.prob hact)).congr
      (Filter.Eventually.of_forall fun _ => rfl)
  have hgc : ContinuousAt g H.prob := by
    simp only [hg, hS]
    exact ((prodBernoulli_real_continuous
          (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)))).continuousAt.mul
        (continuousAt_minForm H Y T F o H.prob hact)).congr
      (Filter.Eventually.of_forall fun _ => rfl)
  have hfg : ∀ p : E → unitInterval, (∀ e, 0 < p e ∧ p e < 1) → f p ≤ g p := by
    intro p hp
    obtain ⟨r', hr', hc'⟩ := exists_rank_compat T (fun a => avoidMean (withProb H p) Y F a)
    have key := h p hp r' hr' hc'
    rw [avoidSurplus_eq_minForm (withProb H p) Y T r' F v hr' hc',
      avoidSurplus_eq_minForm (withProb H p) Y T r' F o hr' hc'] at key
    exact key
  have hwfg := weights_le_of_forall_pos_lt_one_at H.prob hfc hgc hfg
  simp only [hf, hg, hS] at hwfg
  rw [avoidSurplus_eq_minForm H Y T r F v hr hcompat,
    avoidSurplus_eq_minForm H Y T r F o hr hcompat]
  exact hwfg

/-- **From the decoy-free margin at non-degenerate label probabilities to the transfer at arbitrary
ones.**  This is the composite of `avoidSurplusTransfer_nondegenerate_of_margin` with
`avoidSurplusTransfer_of_nondegenerate`, in the shape the avoided first-relay induction consumes. -/
theorem avoidSurplusTransfer_of_margin [Fintype E] (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (o v : V) (F : Set V → ℝ) (hvY : v ∉ Y) (hvT : v ∉ T)
    (hmargin : ∀ p : E → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ r' : V → ℕ, Set.InjOn r' ↑T →
        (∀ a ∈ T, ∀ a' ∈ T, r' a < r' a' →
          avoidMean (withProb H p) Y F a ≤ avoidMean (withProb H p) Y F a') →
        o ∉ Y → o ∉ T → o ≠ v →
        0 ≤ avoidSurplus (withProb H p) Y T r' F o -
          (prodBernoulli p).real
              (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) /
            (prodBernoulli p).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
              avoidSurplus (withProb H p) Y T r' F v)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y))
    (r : V → ℕ) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' → avoidMean H Y F a ≤ avoidMean H Y F a') :
    (prodBernoulli H.prob).real
        (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V)) ∩ hyperConn H o v) *
          avoidSurplus H Y T r F v ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ (↑T : Set V))) *
          avoidSurplus H Y T r F o := by
  refine avoidSurplusTransfer_of_nondegenerate H Y T o v F ?_ hact r hr hcompat
  intro p hp r' hr' hc'
  exact avoidSurplusTransfer_nondegenerate_of_margin (withProb H p) hp Y T o v F r' hvY hvT hr'
    hc' fun hoY hoT hov => hmargin p hp r' hr' hc' hoY hoT hov

/-! ## Fidelity: the bond theorem is the case of two-element incidence sets

Bond percolation is the hyperedge model `KNAll.Bond.bondHypergraph`, so the definitions above
specialize to the ones of `KN/AvoidedDefs.lean` and the transfer theorem specializes to
`KNAll.surplusTransferY_nondegenerate_of_margin`.  Nothing here is used later; it certifies that
the hypergraph statements are not weaker than the bond statements they generalize.
-/

section Bond

open KNAll.Bond

variable {W : Type*}

theorem hyperClusterSet_bondHypergraph_singleton (w : Sym2 W → unitInterval)
    (ω : Set (Sym2 W)) (a : W) :
    hyperClusterSet (bondHypergraph w) ω ({a} : Set W) = openCluster ω a := by
  ext y
  simp only [hyperClusterSet, openCluster, mem_setOf_eq, mem_singleton_iff, exists_eq_left,
    openHyperGraph_eq]

theorem avoidEvent_bondHypergraph_singleton (w : Sym2 W → unitInterval) (Y : Set W) (a : W) :
    avoidEvent (bondHypergraph w) ({a} : Set W) Y =
      {ω : BondConfig W | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y} := by
  ext ω
  rw [mem_avoidEvent_singleton_iff]
  simp only [mem_setOf_eq, openHyperGraph_eq]

theorem firstPat_bondHypergraph (w : Sym2 W → unitInterval) (T : Finset W) (r : W → ℕ) (u a : W) :
    firstPat (bondHypergraph w) T r u a =
      (openConn u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn u a')ᶜ :
        Set (BondConfig W)) := by
  simp only [firstPat, hyperConn_eq_openConn]

theorem avoidMean_bondHypergraph (w : Sym2 W → unitInterval) (Y : Set W) (F : Set W → ℝ) (a : W) :
    avoidMean (bondHypergraph w) Y F a = KNAll.condMean w Y F a := by
  simp only [avoidMean, avoidIntegral, KNAll.condMean, avoidEvent_bondHypergraph_singleton,
    hyperClusterSet_bondHypergraph_singleton, bondHypergraph_prob]

theorem avoidSurplus_bondHypergraph (w : Sym2 W → unitInterval) (Y : Set W) (T : Finset W)
    (r : W → ℕ) (F : Set W → ℝ) (u : W) :
    avoidSurplus (bondHypergraph w) Y T r F u = KNAll.surplusY w Y T r F u := by
  simp only [avoidSurplus, KNAll.surplusY, avoidEvent_bondHypergraph_singleton,
    hyperClusterSet_bondHypergraph_singleton, firstPat_bondHypergraph, hyperConn_eq_openConn,
    avoidMean_bondHypergraph, bondHypergraph_prob]

theorem avoidEvent_bondHypergraph_union (w : Sym2 W → unitInterval) (Y : Set W) (T : Finset W)
    (v : W) :
    avoidEvent (bondHypergraph w) ({v} : Set W) (Y ∪ (↑T : Set W)) =
      {ω : BondConfig W | ∀ a ∈ Y ∪ (↑T : Set W), ¬ (openGraph ω).Reachable v a} :=
  avoidEvent_bondHypergraph_singleton w (Y ∪ (↑T : Set W)) v

/-- The bond theorem `KNAll.surplusTransferY_nondegenerate_of_margin`, re-derived from the
hypergraph theorem. -/
theorem surplusTransferY_nondegenerate_of_margin_of_hyper [Fintype W] [DecidableEq W]
    (w : Sym2 W → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (Y : Set W) (T : Finset W)
    (o v : W) (F : Set W → ℝ) (r : W → ℕ) (hvY : v ∉ Y) (hvT : v ∉ T) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → KNAll.condMean w Y F b ≤ KNAll.condMean w Y F b')
    (hmarg : o ∉ Y → o ∉ T → o ≠ v → 0 ≤ KNAll.surplusMarginY w Y T r [] o v F) :
    (prodBernoulli w).real
        ({ω : BondConfig W | ∀ a ∈ Y ∪ (↑T : Set W), ¬ (openGraph ω).Reachable v a} ∩
          openConn o v) * KNAll.surplusY w Y T r F v ≤
      (prodBernoulli w).real
          {ω : BondConfig W | ∀ a ∈ Y ∪ (↑T : Set W), ¬ (openGraph ω).Reachable v a} *
        KNAll.surplusY w Y T r F o := by
  have key := avoidSurplusTransfer_nondegenerate_of_margin (bondHypergraph w) hw Y T o v F r
    hvY hvT hr (by simpa only [avoidMean_bondHypergraph] using hcompat) ?_
  · simpa only [bondHypergraph_prob, avoidEvent_bondHypergraph_union, hyperConn_eq_openConn,
      avoidSurplus_bondHypergraph] using key
  · intro hoY hoT hov
    have h := hmarg hoY hoT hov
    rw [KNAll.surplusMarginY_nil] at h
    simpa only [bondHypergraph_prob, avoidEvent_bondHypergraph_union, hyperConn_eq_openConn,
      avoidSurplus_bondHypergraph] using h

theorem withProb_bondHypergraph (w p : Sym2 W → unitInterval) :
    withProb (bondHypergraph w) p = bondHypergraph p := rfl

/-- The bond closure theorem `KNAll.surplusTransferY_of_nondegenerate`, re-derived from the
hypergraph closure theorem. -/
theorem surplusTransferY_of_nondegenerate_of_hyper [Fintype W] [DecidableEq W]
    (w : Sym2 W → unitInterval)
    (Y : Set W) (T : Finset W) (o v : W) (F : Set W → ℝ)
    (h : ∀ p : Sym2 W → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ r : W → ℕ, Set.InjOn r ↑T →
        (∀ a ∈ T, ∀ a' ∈ T, r a < r a' → KNAll.condMean p Y F a ≤ KNAll.condMean p Y F a') →
        (prodBernoulli p).real
            ({ω : BondConfig W | ∀ a ∈ Y ∪ (↑T : Set W), ¬ (openGraph ω).Reachable v a} ∩
              openConn o v) * KNAll.surplusY p Y T r F v ≤
          (prodBernoulli p).real
              {ω : BondConfig W | ∀ a ∈ Y ∪ (↑T : Set W), ¬ (openGraph ω).Reachable v a} *
            KNAll.surplusY p Y T r F o)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli w).real
      {ω : BondConfig W | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y})
    (r : W → ℕ) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' → KNAll.condMean w Y F a ≤ KNAll.condMean w Y F a') :
    (prodBernoulli w).real
        ({ω : BondConfig W | ∀ a ∈ Y ∪ (↑T : Set W), ¬ (openGraph ω).Reachable v a} ∩
          openConn o v) * KNAll.surplusY w Y T r F v ≤
      (prodBernoulli w).real
          {ω : BondConfig W | ∀ a ∈ Y ∪ (↑T : Set W), ¬ (openGraph ω).Reachable v a} *
        KNAll.surplusY w Y T r F o := by
  have key := avoidSurplusTransfer_of_nondegenerate (bondHypergraph w) Y T o v F ?_ ?_ r hr
    (by simpa only [avoidMean_bondHypergraph] using hcompat)
  · simpa only [bondHypergraph_prob, avoidEvent_bondHypergraph_union, hyperConn_eq_openConn,
      avoidSurplus_bondHypergraph] using key
  · intro p hp r' hr' hc'
    simp only [withProb_bondHypergraph, avoidMean_bondHypergraph] at hc'
    simpa only [withProb_bondHypergraph, bondHypergraph_prob, avoidEvent_bondHypergraph_union,
      hyperConn_eq_openConn, avoidSurplus_bondHypergraph] using h p hp r' hr' hc'
  · simpa only [bondHypergraph_prob, avoidEvent_bondHypergraph_singleton] using hact

end Bond

end KNAll.Site

end
