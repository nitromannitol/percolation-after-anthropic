import KNConjectures.AvoidedTransfer
import KNConjectures.AvoidedClosure
import KNConjectures.AvoidedGen
import KNConjectures.Projection
import KNConjectures.Statements

/-!
# Kozma–Nitzan's Conjectures 4 (fixed-minimizer form), 2 (strong form), 1 and 3 from the avoided first-relay bound

* `genY_all` — (GEN) with avoided set at every weight function, for relay sets whose relays lie outside `Y` and can avoid `Y`;
* `conjecture4Fixed_holds` — with `Y = {a}` (the minimiser) and the projected functional `projFunA`, every avoided relay mean is
  nonnegative, so the avoided first-relay bound gives `E[(F(C_o) − F(C_a)); o ↮ a, o ↔ A ∖ {a}] ≥ 0`; on `{o ↔ a}` the two clusters
  coincide; relays that cannot avoid `a` contribute a null set;
* `conjecture4_holds`, `conjecture2Strong_holds`, `conjecture2_holds`, `question7_holds`; `conjecture1_holds` from the strong
  Conjecture 2 by the Harris inequality; `conjecture3_holds` from Conjecture 1 with `δ = ε/2`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH Percolation.Literature.KNPreFKG
open scoped Classical

variable {n : ℕ}

/-- **(GEN) with avoided set, all weights.** -/
theorem genY_all (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n)) (F : Set (Fin n) → ℝ)
    (hF : ∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') (A : Finset (Fin n)) (o : Fin n) (r : Fin n → ℕ)
    (hAY : ∀ a ∈ A, a ∉ Y)
    (hact : ∀ a ∈ A, 0 < (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y})
    (hr : Set.InjOn r ↑A) (hcompat : ∀ b ∈ A, ∀ b' ∈ A, r b < r b' → condMean w Y F b ≤ condMean w Y F b') :
    0 ≤ surplusY w Y A r F o :=
  genY_of_surplusTransferY w Y F hF
    (fun T o' v r' hTY hactT hvY hvT hr' hc' =>
      surplusTransferY_of_nondegenerate Y T o' v F
        (fun p hp r'' hr'' hc'' => surplusTransferY_nondegenerate p hp Y T o' v F r'' hTY hvY hvT hF hr'' hc'')
        w hactT r' hr' hc')
    A o r hAY hact hr hcompat

/-- **Conjecture 4, fixed-minimizer form.** -/
theorem conjecture4Fixed_holds : Conjecture4Fixed := by
  intro n w A o a F haA hF hmin
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
  have hint : ∀ (g : BondConfig (Fin n) → ℝ) (S : Set (BondConfig (Fin n))), IntegrableOn g S μ :=
    fun g S => (Integrable.of_finite).integrableOn
  -- the projected functional and the active relays of `A ∖ {a}`
  set Φ : Set (Fin n) → ℝ := projFunA w a F with hΦ
  have hΦmono : ∀ S S' : Set (Fin n), S ⊆ S' → Φ S ≤ Φ S' := fun S S' h => monotone_projFunA w a F hF h
  set T : Finset (Fin n) := (A.erase a).filter
    (fun x => 0 < μ.real {ω : BondConfig (Fin n) | ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y}) with hT
  have hTA : ∀ x ∈ T, x ∈ A.erase a := fun x hx => (Finset.mem_filter.1 hx).1
  have hTY : ∀ x ∈ T, x ∉ ({a} : Set (Fin n)) := fun x hx h =>
    Finset.ne_of_mem_erase (hTA x hx) (mem_singleton_iff.1 h)
  have hact : ∀ x ∈ T, 0 < μ.real {ω : BondConfig (Fin n) | ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} :=
    fun x hx => (Finset.mem_filter.1 hx).2
  -- the avoided relay means are nonnegative
  have hmean : ∀ x ∈ T, 0 ≤ condMean w ({a} : Set (Fin n)) Φ x := by
    intro x hx
    unfold condMean
    refine div_nonneg ?_ (hn _)
    rw [hΦ, setIntegral_projFunA_avoid w a x F]
    linarith [hmin x (Finset.mem_of_mem_erase (hTA x hx))]
  obtain ⟨r, hr, hcompat⟩ := AGloc.exists_rank_compat T (condMean w ({a} : Set (Fin n)) Φ)
  have hgen := genY_all w ({a} : Set (Fin n)) Φ hΦmono T o r hTY hact hr hcompat
  have hsum := sum_le_setIntegral_of_genY w ({a} : Set (Fin n)) T r Φ o hgen
  have hsum0 : 0 ≤ ∑ x ∈ T, μ.real
      ({ω : BondConfig (Fin n) | ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable o y} ∩
        (openConn o x ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r x), (openConn o a')ᶜ) : Set (BondConfig (Fin n))) *
      condMean w ({a} : Set (Fin n)) Φ x :=
    Finset.sum_nonneg fun x hx => mul_nonneg (hn _) (hmean x hx)
  -- `∫_{o ↮ a, o ↔ T} (F(C_o) − F(C_a)) ≥ 0`
  set Av : Set (BondConfig (Fin n)) := {ω | ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable o y} with hAv
  set g : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω o) - F (openCluster ω a) with hg
  have hET : 0 ≤ ∫ ω in Av ∩ ⋃ t ∈ T, openConn o t, g ω ∂μ := by
    have := setIntegral_sub_eq_projFunA_conn w a o F T
    rw [hg, hAv, this, ← hμ]
    exact le_trans hsum0 hsum
  -- bookkeeping: the full event `o ↔ A`
  set UA : Set (BondConfig (Fin n)) := ⋃ x ∈ A, openConn o x with hUA
  set E : Set (BondConfig (Fin n)) := Av ∩ ⋃ x ∈ A.erase a, openConn o x with hE
  set ET : Set (BondConfig (Fin n)) := Av ∩ ⋃ t ∈ T, openConn o t with hET'
  have hAv' : ∀ ω, ω ∈ Av ↔ ¬ (openGraph ω).Reachable o a := fun ω => by simp [hAv]
  -- on `{o ↔ a}` the integrand vanishes
  have hg0 : ∀ ω ∈ (openConn o a : Set (BondConfig (Fin n))), g ω = 0 := fun ω hω => by
    simp only [hg]; rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o a), sub_self]
  have hUA_split : ∫ ω in UA, g ω ∂μ = ∫ ω in E, g ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas (openConn o a)) (hint g UA)]
    have h1 : ∫ ω in UA ∩ openConn o a, g ω ∂μ = 0 := by
      rw [setIntegral_congr_fun (hmeas _) (fun ω hω => hg0 ω hω.2)]; simp
    have h2 : UA \ openConn o a = E := by
      ext ω
      simp only [hUA, hE, mem_sdiff, mem_iUnion, exists_prop, mem_inter_iff, hAv' ω, Finset.mem_erase]
      constructor
      · rintro ⟨⟨x, hx, hox⟩, hna⟩
        exact ⟨hna, x, ⟨fun hxa => hna (hxa ▸ hox), hx⟩, hox⟩
      · rintro ⟨hna, x, ⟨_, hx⟩, hox⟩
        exact ⟨⟨x, hx, hox⟩, hna⟩
    rw [h1, zero_add, h2]
  -- inactive relays contribute a null set
  have hETE : ET ⊆ E := fun ω hω => ⟨hω.1, by
    obtain ⟨t, ht, hot⟩ := mem_iUnion₂.1 hω.2
    exact mem_iUnion₂.2 ⟨t, hTA t ht, hot⟩⟩
  have hnull : μ (E \ ET) = 0 := by
    have hsub : E \ ET ⊆ ⋃ x ∈ (A.erase a).filter (fun x => ¬ 0 < μ.real
        {ω : BondConfig (Fin n) | ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y}),
        {ω : BondConfig (Fin n) | ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} := by
      intro ω hω
      obtain ⟨⟨hA1, hA2⟩, hnot⟩ := hω
      obtain ⟨x, hx, hox⟩ := mem_iUnion₂.1 hA2
      have hxT : x ∉ T := fun hxT => hnot ⟨hA1, mem_iUnion₂.2 ⟨x, hxT, hox⟩⟩
      have hinact : ¬ 0 < μ.real {ω : BondConfig (Fin n) | ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} :=
        fun hpos => hxT (Finset.mem_filter.2 ⟨hx, hpos⟩)
      refine mem_iUnion₂.2 ⟨x, Finset.mem_filter.2 ⟨hx, hinact⟩, ?_⟩
      intro y hy hxy
      rw [mem_singleton_iff] at hy
      subst hy
      exact (hAv' ω).1 hA1 (hox.trans hxy)
    refine measure_mono_null hsub (measure_biUnion_null_iff (Finset.countable_toSet _) |>.2 fun x hx => ?_)
    have h0 : μ.real {ω : BondConfig (Fin n) | ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y} = 0 :=
      le_antisymm (not_lt.1 (Finset.mem_filter.1 hx).2) (hn _)
    rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h0
  have hE_split : ∫ ω in E, g ω ∂μ = ∫ ω in ET, g ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas ET) (hint g E), inter_eq_right.2 hETE,
      Measure.restrict_eq_zero.2 hnull, integral_zero_measure, add_zero]
  have hfinal : 0 ≤ ∫ ω in UA, g ω ∂μ := by rw [hUA_split, hE_split]; exact hET
  rw [hg, integral_sub (hint _ _) (hint _ _)] at hfinal
  linarith

/-- **Conjecture 4** (arXiv:2401.12397, p. 32). -/
theorem conjecture4_holds : Conjecture4 := by
  intro n w A hA o F hF
  obtain ⟨a, haA, hmin⟩ := Finset.exists_min_image A (fun x => ∫ ω, F (openCluster ω x) ∂(prodBernoulli w)) hA
  exact le_trans (Finset.inf'_le _ haA) (conjecture4Fixed_holds n w A o a F haA hF hmin)

/-- **Conjecture 2, strong form.** -/
theorem conjecture2Strong_holds : Conjecture2Strong := by
  intro n w A hA o b
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  set F : Set (Fin n) → ℝ := fun M => if b ∈ M then 1 else 0 with hF
  have hFmono : ∀ S T : Set (Fin n), S ⊆ T → F S ≤ F T := by
    intro S T hST
    simp only [hF]
    by_cases hS : b ∈ S
    · rw [if_pos hS, if_pos (hST hS)]
    · rw [if_neg hS]; split_ifs <;> norm_num
  have hFind : ∀ x : Fin n, (fun ω : BondConfig (Fin n) => F (openCluster ω x)) =
      (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
    intro x
    funext ω
    simp only [hF]
    by_cases hω : ω ∈ (openConn x b : Set (BondConfig (Fin n)))
    · rw [Set.indicator_of_mem hω, Pi.one_apply, if_pos (show b ∈ openCluster ω x from hω)]
    · rw [Set.indicator_of_notMem hω, if_neg (show b ∉ openCluster ω x from hω)]
  have hint : ∀ x : Fin n, ∫ ω in ⋃ y ∈ A, openConn o y, F (openCluster ω x) ∂μ =
      μ.real (openConn x b ∩ ⋃ y ∈ A, openConn o y) := by
    intro x
    rw [hFind x, ← integral_indicator (hmeas _), Set.indicator_indicator, integral_indicator_one ((hmeas _).inter (hmeas _)),
      Set.inter_comm]
  have h4 := conjecture4_holds n w A hA o F hFmono
  rw [← hμ] at h4
  simp only [hint] at h4
  exact h4

/-- **Question 7 (affirmative)**: the minimiser of `P(a ↔ b)` is a valid relay in the pre-FKG comparison (41). -/
theorem question7_holds : Question7 := by
  intro n w A o b a haA hmin
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  set F : Set (Fin n) → ℝ := fun M => if b ∈ M then 1 else 0 with hF
  have hFmono : ∀ S T : Set (Fin n), S ⊆ T → F S ≤ F T := by
    intro S T hST
    simp only [hF]
    by_cases hS : b ∈ S
    · rw [if_pos hS, if_pos (hST hS)]
    · rw [if_neg hS]; split_ifs <;> norm_num
  have hFind : ∀ x : Fin n, (fun ω : BondConfig (Fin n) => F (openCluster ω x)) =
      (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
    intro x
    funext ω
    simp only [hF]
    by_cases hω : ω ∈ (openConn x b : Set (BondConfig (Fin n)))
    · rw [Set.indicator_of_mem hω, Pi.one_apply, if_pos (show b ∈ openCluster ω x from hω)]
    · rw [Set.indicator_of_notMem hω, if_neg (show b ∉ openCluster ω x from hω)]
  have hint : ∀ x : Fin n, ∫ ω in ⋃ y ∈ A, openConn o y, F (openCluster ω x) ∂μ =
      μ.real (openConn x b ∩ ⋃ y ∈ A, openConn o y) := by
    intro x
    rw [hFind x, ← integral_indicator (hmeas _), Set.indicator_indicator, integral_indicator_one ((hmeas _).inter (hmeas _)),
      Set.inter_comm]
  have hmean : ∀ x ∈ A, ∫ ω, F (openCluster ω a) ∂μ ≤ ∫ ω, F (openCluster ω x) ∂μ := by
    intro x hx
    have e : ∀ z : Fin n, ∫ ω, F (openCluster ω z) ∂μ = μ.real (openConn z b) := fun z => by
      rw [hFind z, integral_indicator_one (hmeas _)]
    rw [e, e]; exact hmin x hx
  have h4 := conjecture4Fixed_holds n w A o a F haA hFmono hmean
  rw [← hμ, hint, hint] at h4
  exact h4

/-- **Conjecture 2.** -/
theorem conjecture2_holds : Conjecture2 := fun n w A hA o b =>
  le_trans (conjecture2Strong_holds n w A hA o b) (measureReal_mono inter_subset_left (measure_ne_top _ _))

/-- **Conjecture 1 from the strong Conjecture 2 by the Harris inequality**: `P(o ↔ A) · P(x ↔ b) ≤ P(x ↔ b, o ↔ A)` for every `x`
(both events are increasing), so `P(o ↔ A) · min_x P(x ↔ b) ≤ min_x P(x ↔ b, o ↔ A) ≤ P(o ↔ b, o ↔ A) ≤ P(o ↔ b)`. -/
theorem conjecture1_holds : Conjecture1 := by
  intro n w A hA o b
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  set U : Set (BondConfig (Fin n)) := ⋃ y ∈ A, openConn o y with hU
  have hUup : IsUpperSet U := by
    intro ω ω' hle hω
    obtain ⟨y, hy, hoy⟩ := mem_iUnion₂.1 hω
    exact mem_iUnion₂.2 ⟨y, hy, hoy.mono (SimpleGraph.fromEdgeSet_mono hle)⟩
  set F : Set (Fin n) → ℝ := fun M => if b ∈ M then 1 else 0 with hF
  have hFmono : ∀ S T : Set (Fin n), S ⊆ T → F S ≤ F T := by
    intro S T hST
    simp only [hF]
    by_cases hS : b ∈ S
    · rw [if_pos hS, if_pos (hST hS)]
    · rw [if_neg hS]; split_ifs <;> norm_num
  have hF0 : ∀ S, 0 ≤ F S := by intro S; simp only [hF]; split_ifs <;> norm_num
  have hFind : ∀ x : Fin n, (fun ω : BondConfig (Fin n) => F (openCluster ω x)) =
      (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
    intro x
    funext ω
    simp only [hF]
    by_cases hω : ω ∈ (openConn x b : Set (BondConfig (Fin n)))
    · rw [Set.indicator_of_mem hω, Pi.one_apply, if_pos (show b ∈ openCluster ω x from hω)]
    · rw [Set.indicator_of_notMem hω, if_neg (show b ∉ openCluster ω x from hω)]
  -- Harris: `μ(U) · P(x ↔ b) ≤ P(x ↔ b, U)` for every relay `x`
  have hharris : ∀ x ∈ A, μ.real U * μ.real (openConn x b) ≤ μ.real (openConn x b ∩ U) := by
    intro x _
    have h := AGloc.setIntegral_clusterFun_ge w x F hFmono hF0 U hUup
    rw [← hμ, hFind x, integral_indicator_one (hmeas _), ← integral_indicator (hmeas _), Set.indicator_indicator,
      integral_indicator_one ((hmeas _).inter (hmeas _)), Set.inter_comm] at h
    exact h
  -- the minimum of `P(x ↔ b)` is attained at some `a`
  obtain ⟨a, haA, hmin⟩ := Finset.exists_min_image A (fun x => μ.real (openConn x b)) hA
  have hinf : A.inf' hA (fun x => μ.real (openConn x b)) = μ.real (openConn a b) :=
    le_antisymm (Finset.inf'_le _ haA) (Finset.le_inf' hA _ fun x hx => hmin x hx)
  have h2 := conjecture2Strong_holds n w A hA o b
  rw [← hμ, ← hU] at h2
  -- `P(U) · min_x P(x ↔ b) ≤ min_x P(x ↔ b, U)`
  have hlow : μ.real U * μ.real (openConn a b) ≤ A.inf' hA (fun x => μ.real (openConn x b ∩ U)) := by
    refine Finset.le_inf' hA _ fun x hx => ?_
    calc μ.real U * μ.real (openConn a b) ≤ μ.real U * μ.real (openConn x b) :=
          mul_le_mul_of_nonneg_left (hmin x hx) measureReal_nonneg
      _ ≤ μ.real (openConn x b ∩ U) := hharris x hx
  have h3 : μ.real (openConn o b ∩ U) ≤ μ.real (openConn o b) := measureReal_mono inter_subset_left (measure_ne_top _ _)
  rw [hinf]
  linarith [hlow, h2, h3]

/-- **Conjecture 3 from Conjecture 1** (`δ = ε/2`): if `P(o ↔ A) > 1 − δ` and `P(a ↔ b) > 1 − δ` for all `a ∈ A` then
`P(o ↔ b) ≥ P(o ↔ A) · min_a P(a ↔ b) > (1 − δ)² ≥ 1 − ε` (for `δ < 1`; for `δ ≥ 1` the conclusion `1 − ε < P(o ↔ b)` is
trivial since `1 − ε < 0`). -/
theorem conjecture3_holds : Percolation.Literature.KozmaNitzan2024_conjecture3 := by
  intro ε hε
  refine ⟨ε / 2, by positivity, ?_⟩
  intro n w A o b hoA hab
  set μ := prodBernoulli w with hμ
  have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
  by_cases hδ : (1 : ℝ) ≤ ε / 2
  · have : 1 - ε < 0 := by linarith
    exact lt_of_lt_of_le this (hn _)
  · have hδ' : 0 < 1 - ε / 2 := by linarith
    rcases A.eq_empty_or_nonempty with hA0 | hA
    · subst hA0
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, measureReal_empty] at hoA
      exact absurd hoA (not_lt.2 hδ'.le)
    · have h1 := conjecture1_holds n w A hA o b
      rw [← hμ] at h1
      obtain ⟨a, haA, hmin⟩ := Finset.exists_min_image A (fun x => μ.real (openConn x b)) hA
      have hinf : A.inf' hA (fun x => μ.real (openConn x b)) = μ.real (openConn a b) :=
        le_antisymm (Finset.inf'_le _ haA) (Finset.le_inf' hA _ fun x hx => hmin x hx)
      rw [hinf] at h1
      have hab' := hab a haA
      have hprod : (1 - ε / 2) * (1 - ε / 2) < μ.real (⋃ a ∈ A, openConn o a) * μ.real (openConn a b) :=
        mul_lt_mul'' hoA hab' hδ'.le hδ'.le
      nlinarith [h1, hprod]

end KNAll

end

#print axioms KNAll.conjecture4Fixed_holds
#print axioms KNAll.conjecture4_holds
#print axioms KNAll.conjecture2Strong_holds
#print axioms KNAll.conjecture2_holds
#print axioms KNAll.question7_holds
#print axioms KNAll.conjecture1_holds
#print axioms KNAll.conjecture3_holds
