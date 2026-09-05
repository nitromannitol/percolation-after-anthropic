import KNConjectures.AvoidedPeelTools

/-!
# The avoided first-relay bound (GEN with avoided set) from (S5) with avoided set

`genY_of_surplusTransferY`: if (S5) with base avoided set `Y` holds for every relay set (of relays outside `Y` that can avoid
`Y`), then `Sur^Y_o(A) ≥ 0`, i.e. `Σ_{a ∈ A} P(J^o_a) m_a^Y ≤ E[F(C_o); o ↮ Y, o ↔ A]`, for every such relay set `A`, every
observer `o`, every monotone `F` (no nonnegativity is needed, unlike the development's unconditioned bound) and every `m^Y`-compatible injective rank.  Induction on `|A|`: remove the
rank-maximal relay `k`; the one-cluster BHK inequality for `C_k` given `k ↮ Y ∪ T` bounds the deficit; Lemma κ and (S5) with `v = k`
transfer it (verbatim the bookkeeping of `AGloc.gen_firstRank_of_surplusTransfer`).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH Percolation.Literature.KNPreFKG
open scoped Classical

variable {n : ℕ}

/-- **(S5) with avoided set ⟹ (GEN) with avoided set.** -/
theorem genY_of_surplusTransferY (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (F : Set (Fin n) → ℝ)
    (hF : ∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S')
    (hST : ∀ (T : Finset (Fin n)) (o v : Fin n) (r : Fin n → ℕ),
      (∀ a ∈ T, a ∉ Y) → (∀ a ∈ T, 0 < (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}) →
      v ∉ Y → v ∉ T → Set.InjOn r ↑T →
      (∀ b ∈ T, ∀ b' ∈ T, r b < r b' → condMean w Y F b ≤ condMean w Y F b') →
      (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
          surplusY w Y T r F v ≤
        (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ Y ∪ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a} *
          surplusY w Y T r F o) :
    ∀ (A : Finset (Fin n)) (o : Fin n) (r : Fin n → ℕ),
      (∀ a ∈ A, a ∉ Y) → (∀ a ∈ A, 0 < (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}) →
      Set.InjOn r ↑A → (∀ b ∈ A, ∀ b' ∈ A, r b < r b' → condMean w Y F b ≤ condMean w Y F b') →
      0 ≤ surplusY w Y A r F o := by
  have main : ∀ (N : ℕ) (A : Finset (Fin n)) (o : Fin n) (r : Fin n → ℕ), A.card = N →
      (∀ a ∈ A, a ∉ Y) → (∀ a ∈ A, 0 < (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}) →
      Set.InjOn r ↑A → (∀ b ∈ A, ∀ b' ∈ A, r b < r b' → condMean w Y F b ≤ condMean w Y F b') →
      0 ≤ surplusY w Y A r F o := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro A o r hN hAY hact hr hcompat
    set μ := prodBernoulli w with hμ
    have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
    have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
    rcases A.eq_empty_or_nonempty with hA0 | hne
    · subst hA0; simp [surplusY]
    obtain ⟨k, hkA, hkmax⟩ := Finset.exists_max_image A r hne
    set T : Finset (Fin n) := A.erase k with hT
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
    have hcompatT : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → condMean w Y F b ≤ condMean w Y F b' :=
      fun b hb b' hb' h => hcompat b (hTA b hb) b' (hTA b' hb') h
    have hmle : ∀ a ∈ T, condMean w Y F a ≤ condMean w Y F k := fun a ha => hcompat a (hTA a ha) k hkA (hlt a ha)
    have hkY : k ∉ Y := hAY k hkA
    have hTY : ∀ a ∈ T, a ∉ Y := fun a ha => hAY a (hTA a ha)
    have hactT : ∀ a ∈ T, 0 < μ.real {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y} :=
      fun a ha => hact a (hTA a ha)
    -- induction hypothesis and (S5) with `v = k`
    have hIH : 0 ≤ surplusY w Y T r F o := ih T.card hTcard T o r rfl hTY hactT hrT hcompatT
    have hS5 := hST T o k r hTY hactT hkY hkT hrT hcompatT
    -- objects
    set A' : Set (Fin n) := Y ∪ (↑T : Set (Fin n)) with hA'
    set Dk : Set (BondConfig (Fin n)) := {ω : BondConfig (Fin n) | ∀ a ∈ A', ¬ (openGraph ω).Reachable k a} with hDk
    set Ok : Set (BondConfig (Fin n)) := openConn o k with hOk
    set fk : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω k) with hfk
    set mk : ℝ := condMean w Y F k with hmk
    have hkA' : k ∉ A' := by
      rw [hA', mem_union, not_or]; exact ⟨hkY, fun h => hkT (Finset.mem_coe.1 h)⟩
    -- (1) Lemma P
    have hpeel : surplusY w Y A r F o = surplusY w Y T r F o +
        ((∫ ω in Dk ∩ Ok, fk ω ∂μ) - μ.real (Dk ∩ Ok) * mk) := by
      rw [surplusY_erase_add w Y A r F hkA hlt o, openConn_symm k o]
    -- (2) one-cluster BHK for `C_k` given `k ↮ Y ∪ T`
    have hindk : ∀ ω : BondConfig (Fin n), (connFamily k o).indicator (1 : Set (Sym2 (Fin n)) → ℝ) (openEdgeCluster ω k) =
        Ok.indicator (1 : BondConfig (Fin n) → ℝ) ω := fun ω => by
      rw [congrFun (indicator_comp_openEdgeCluster (connFamily k o) k) ω, ← openConn_eq_setOf_connFamily, openConn_symm k o]
    have hprod : ∀ (S : Set (BondConfig (Fin n))) (g : BondConfig (Fin n) → ℝ),
        ∫ ω in Dk, S.indicator (1 : BondConfig (Fin n) → ℝ) ω * g ω ∂μ = ∫ ω in Dk ∩ S, g ω ∂μ := by
      intro S g
      rw [← setIntegral_mul_indicator_one μ Dk S g]
      refine setIntegral_congr_fun (hmeas Dk) fun ω _ => ?_
      ring
    have hDset : {ω : BondConfig (Fin n) | ∀ x ∈ A', ¬ (openGraph ω).Reachable k x} = Dk := rfl
    have hBHK := BHK2006_clusterConditionalPositiveAssociation_holds (Fin n) w k A'
      ((connFamily k o).indicator 1) (fun C => F {a | a = k ∨ ∃ e ∈ C, a ∈ e})
      (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily k o)) (monotone_clusterFun k F hF) hkA'
    simp only [hDset, clusterFun_openEdgeCluster, hindk] at hBHK
    rw [setIntegral_indicator_one_eq, hprod Ok] at hBHK
    change μ.real (Dk ∩ Ok) * ∫ ω in Dk, fk ω ∂μ ≤ μ.real Dk * ∫ ω in Dk ∩ Ok, fk ω ∂μ at hBHK
    -- (3) Lemma κ
    have hκ : mk * μ.real Dk - ∫ ω in Dk, fk ω ∂μ ≤ surplusY w Y T r F k := kappaY_le_surplusY w Y T r F k hrT hmle
    -- (4) combine
    change μ.real (Dk ∩ Ok) * surplusY w Y T r F k ≤ μ.real Dk * surplusY w Y T r F o at hS5
    have hkey : μ.real Dk * (mk * μ.real (Dk ∩ Ok) - ∫ ω in Dk ∩ Ok, fk ω ∂μ) ≤ μ.real Dk * surplusY w Y T r F o := by
      have h1 : μ.real Dk * (mk * μ.real (Dk ∩ Ok) - ∫ ω in Dk ∩ Ok, fk ω ∂μ) ≤
          μ.real (Dk ∩ Ok) * (mk * μ.real Dk - ∫ ω in Dk, fk ω ∂μ) := by nlinarith [hBHK]
      have h2 := mul_le_mul_of_nonneg_left hκ (hn (Dk ∩ Ok))
      linarith
    rw [hpeel]
    by_cases hD0 : μ.real Dk = 0
    · have hP0 : μ.real (Dk ∩ Ok) = 0 :=
        le_antisymm (hD0 ▸ measureReal_mono inter_subset_left (measure_ne_top _ _)) (hn _)
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

/-- The sum form of (GEN) with avoided set. -/
theorem sum_le_setIntegral_of_genY (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (A : Finset (Fin n)) (r : Fin n → ℕ)
    (F : Set (Fin n) → ℝ) (o : Fin n) (h : 0 ≤ surplusY w Y A r F o) :
    ∑ a ∈ A, (prodBernoulli w).real
        ({ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable o y} ∩
          (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ) : Set (BondConfig (Fin n))) *
      condMean w Y F a ≤
      ∫ ω in {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable o y} ∩ ⋃ a ∈ A, openConn o a,
        F (openCluster ω o) ∂(prodBernoulli w) := by
  unfold surplusY at h; linarith

end KNAll

end
