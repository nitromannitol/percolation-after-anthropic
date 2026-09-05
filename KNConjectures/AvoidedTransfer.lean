import KNConjectures.AvoidedPeel

/-!
# (S5) with a base avoided set at non-degenerate weights, every observer position

* `surplusY_nonneg_of_mem` — an observer inside the relay set has nonnegative avoided surplus;
* `surplusY_eq_zero_of_mem` — an observer inside the avoided set has zero surplus;
* `surplusTransferY_nondegenerate_of_margin` — (S5) with `Y` at a non-degenerate weight function from the decoy-free margin, all
  observer positions (`o = v`, `o ∈ Y`, `o ∈ T`, else);
* `surplusTransferY_nondegenerate` — the same from the development's hierarchy `CSH.cshHolds`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH Percolation.Literature.KNPreFKG
open scoped Classical

variable {n : ℕ}

/-- An observer inside the relay set has nonnegative avoided surplus: its first relay has rank `≤ r o`, hence mean `≤ m_o^Y`. -/
theorem surplusY_nonneg_of_mem (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (T : Finset (Fin n)) (r : Fin n → ℕ)
    (F : Set (Fin n) → ℝ) (o : Fin n) (hoT : o ∈ T) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' → condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ surplusY w Y T r F o := by
  unfold surplusY
  set μ := prodBernoulli w with hμ
  set Av : Set (BondConfig (Fin n)) := {ω | ∀ y ∈ Y, ¬ (openGraph ω).Reachable o y} with hAv
  set pat : Fin n → Set (BondConfig (Fin n)) := fun a =>
    (openConn o a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) with hpat
  have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
  -- on a nonempty avoided pattern of `a`, `m_a ≤ m_o`
  have hle : ∀ a ∈ T, μ.real (Av ∩ pat a) * condMean w Y F a ≤ μ.real (Av ∩ pat a) * condMean w Y F o := by
    intro a ha
    rcases (Av ∩ pat a).eq_empty_or_nonempty with h0 | ⟨ω, hω⟩
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
  have hsum : ∑ a ∈ T, μ.real (Av ∩ pat a) * condMean w Y F a ≤ condMean w Y F o * μ.real (Av ∩ ⋃ a ∈ T, openConn o a) := by
    calc ∑ a ∈ T, μ.real (Av ∩ pat a) * condMean w Y F a
        ≤ ∑ a ∈ T, μ.real (Av ∩ pat a) * condMean w Y F o := Finset.sum_le_sum hle
      _ = condMean w Y F o * μ.real (Av ∩ ⋃ a ∈ T, openConn o a) := by
        rw [← Finset.sum_mul, mul_comm, sum_measureReal_avoid_firstRank w Y T r o hr]
  -- `Av ∩ ⋃_a {o ↔ a} = Av` since `o ∈ T`
  have hU : (Av ∩ ⋃ a ∈ T, (openConn o a : Set (BondConfig (Fin n)))) = Av := by
    refine inter_eq_left.2 fun ω _ => ?_
    exact mem_iUnion₂.2 ⟨o, hoT, SimpleGraph.Reachable.refl _⟩
  have hI : ∫ ω in Av, F (openCluster ω o) ∂μ = condMean w Y F o * μ.real Av := setIntegral_eq_condMean_mul w Y F o
  rw [hU] at hsum ⊢
  rw [hI]
  linarith

/-- An observer inside the avoided set has zero avoided surplus. -/
theorem surplusY_eq_zero_of_mem (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (T : Finset (Fin n)) (r : Fin n → ℕ)
    (F : Set (Fin n) → ℝ) (o : Fin n) (hoY : o ∈ Y) : surplusY w Y T r F o = 0 := by
  have hAv : {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable o y} = ∅ :=
    eq_empty_of_forall_notMem fun ω hω => hω o hoY (SimpleGraph.Reachable.refl _)
  unfold surplusY
  simp [hAv]

/-- **(S5) with avoided set at a non-degenerate weight function from the decoy-free margin, every observer position.** -/
theorem surplusTransferY_nondegenerate_of_margin (w : Sym2 (Fin n) → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set (Fin n)) (T : Finset (Fin n)) (o v : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ)
    (hvY : v ∉ Y) (hvT : v ∉ T) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → condMean w Y F b ≤ condMean w Y F b')
    (hmarg : o ∉ Y → o ∉ T → o ≠ v → 0 ≤ surplusMarginY w Y T r [] o v F) :
    (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        surplusY w Y T r F v ≤
      (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} *
        surplusY w Y T r F o := by
  set μ := prodBernoulli w with hμ
  have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
  by_cases hov : o = v
  · subst hov
    have hOO : (openConn o o : Set (BondConfig (Fin n))) = univ :=
      eq_univ_of_forall fun ω => SimpleGraph.Reachable.refl _
    rw [hOO, inter_univ]
  -- if `o ∈ Y ∪ T` the event `{v ↮ Y ∪ T} ∩ {o ↔ v}` is empty
  have hempty : o ∈ Y ∪ (↑T : Set (Fin n)) →
      ({ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) = ∅ := by
    intro ho
    refine eq_empty_of_forall_notMem fun ω hω => ?_
    exact hω.1 o ho (SimpleGraph.Reachable.symm hω.2)
  by_cases hoY : o ∈ Y
  · rw [hempty (Or.inl hoY), measureReal_empty, zero_mul, surplusY_eq_zero_of_mem w Y T r F o hoY, mul_zero]
  by_cases hoT : o ∈ T
  · rw [hempty (Or.inr (Finset.mem_coe.2 hoT)), measureReal_empty, zero_mul]
    exact mul_nonneg (hn _) (surplusY_nonneg_of_mem w Y T r F o hoT hr hcompat)
  · have hne : ({ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a}).Nonempty := by
      refine ⟨∅, fun a ha hreach => ?_⟩
      have hbot : openGraph (∅ : BondConfig (Fin n)) = ⊥ := by
        unfold openGraph; exact SimpleGraph.fromEdgeSet_empty
      rw [hbot, SimpleGraph.reachable_bot] at hreach
      subst hreach
      rcases ha with ha | ha
      · exact hvY ha
      · exact hvT (Finset.mem_coe.1 ha)
    have hpos := prodBernoulli_real_pos_of_nonempty hw hne
    exact surplusTransferY_of_surplusMarginY_nil w Y T r o v F hpos (hmarg hoY hoT hov)

/-- **(S5) with avoided set at non-degenerate weights, from the development's hierarchy `CSH.cshHolds`.** No hypothesis on `o`. -/
theorem surplusTransferY_nondegenerate (w : Sym2 (Fin n) → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set (Fin n)) (T : Finset (Fin n)) (o v : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ)
    (hTY : ∀ a ∈ T, a ∉ Y) (hvY : v ∉ Y) (hvT : v ∉ T)
    (hF : ∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → condMean w Y F b ≤ condMean w Y F b') :
    (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        surplusY w Y T r F v ≤
      (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} *
        surplusY w Y T r F o := by
  refine surplusTransferY_nondegenerate_of_margin w hw Y T o v F r hvY hvT hr hcompat fun hoY hoT hov => ?_
  refine surplusMarginY_nonneg_of_csh w hw Y o v hoY hvY ?_ T r [] F hF hr hcompat hTY hoT hvT List.nodup_nil
    (fun _ hd => absurd hd List.not_mem_nil)
  intro x Y' D hxY' hox hvx hoY' hvY' hD hdis
  refine cshHolds w hw x Y' D o v hxY' ?_ ?_ hov hD ?_
  · simp only [mem_insert_iff, not_or]; exact ⟨hox, hoY'⟩
  · simp only [mem_insert_iff, not_or]; exact ⟨hvx, hvY'⟩
  · intro d hd
    obtain ⟨h1, h2, h3, h4⟩ := hdis d hd
    exact ⟨by simp only [mem_insert_iff, not_or]; exact ⟨h1, h2⟩, h3, h4⟩

end KNAll

end
