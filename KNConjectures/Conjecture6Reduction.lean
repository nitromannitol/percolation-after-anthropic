import KNConjectures.Conjectures
import KNConjectures.Statements6

/-!
# Conjecture 6: reductions to its strong form (written by a Claude Opus research pass)

Three machine-checked facts (no `sorry`, no new axiom):

* `conjecture6Strong_of_forceOpen_min` — the strong form of Conjecture 6 holds whenever the
  minimality hypothesis is read **in `G/e`** instead of in `G`.  It is literally `question7_holds`
  applied to the weight function `forceOpen w e`.  Hence the *only* gap in Conjecture 6 is that
  the minimiser is prescribed in `G` while the conclusion lives in `G/e`.
* `conjecture6_of_conjecture6Strong` — the strong form implies the paper's (40) (Harris).
* `conjecture6_hypotheses_vacuous` — the paper's hypothesis (39) is a consequence of the proved
  Conjecture 1, so it carries no information.
-/

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity
open scoped Classical

set_option linter.unusedSectionVars false

/-- **Conjecture 6, strong form, with the minimality hypothesis taken in `G/e`.**
This is exactly `question7_holds` for the weight function `forceOpen w s(v, w')`.  In particular the
strong form of Conjecture 6 holds whenever the `G`-minimiser `a` is *also* a minimiser of
`P_{G/e}(x ↔ b)` over `A` (in particular whenever the minimiser does not change when `e` is
shortened). -/
theorem conjecture6Strong_of_forceOpen_min (n : ℕ) (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (v w' b a : Fin n) (haA : a ∈ A)
    (hmin : ∀ x ∈ A, (prodBernoulli (forceOpen w s(v, w'))).real (openConn a b) ≤
        (prodBernoulli (forceOpen w s(v, w'))).real (openConn x b)) :
    (prodBernoulli (forceOpen w s(v, w'))).real (openConn a b ∩ ⋃ y ∈ A, openConn v y) ≤
      (prodBernoulli (forceOpen w s(v, w'))).real (openConn v b ∩ ⋃ y ∈ A, openConn v y) :=
  question7_holds n (forceOpen w s(v, w')) A v b a haA hmin

/-- **Harris step**: for every weight function, `P(U) · P(x ↔ b) ≤ P(x ↔ b, U)` where
`U = {v ↔ A}` is increasing. -/
theorem harris_conn_conn (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (v x b : Fin n) :
    (prodBernoulli w).real (⋃ y ∈ A, openConn v y) * (prodBernoulli w).real (openConn x b) ≤
      (prodBernoulli w).real (openConn x b ∩ ⋃ y ∈ A, openConn v y) := by
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  set U : Set (BondConfig (Fin n)) := ⋃ y ∈ A, openConn v y with hU
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
  have hFind : (fun ω : BondConfig (Fin n) => F (openCluster ω x)) =
      (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
    funext ω
    simp only [hF]
    by_cases hω : ω ∈ (openConn x b : Set (BondConfig (Fin n)))
    · rw [Set.indicator_of_mem hω, Pi.one_apply, if_pos (show b ∈ openCluster ω x from hω)]
    · rw [Set.indicator_of_notMem hω, if_neg (show b ∉ openCluster ω x from hω)]
  have h := AGloc.setIntegral_clusterFun_ge w x F hFmono hF0 U hUup
  rw [← hμ, hFind, integral_indicator_one (hmeas _), ← integral_indicator (hmeas _),
    Set.indicator_indicator, integral_indicator_one ((hmeas _).inter (hmeas _)), Set.inter_comm] at h
  exact h

/-- **The strong form of Conjecture 6 implies Conjecture 6** (Harris). -/
theorem conjecture6_of_conjecture6Strong (h : Conjecture6Strong) : Conjecture6 := by
  intro n w A v w' b a haA hmin
  have hS := h n w A v w' b a haA hmin
  have hH := harris_conn_conn n (forceOpen w s(v, w')) A v a b
  have hle : (prodBernoulli (forceOpen w s(v, w'))).real (openConn v b ∩ ⋃ y ∈ A, openConn v y) ≤
      (prodBernoulli (forceOpen w s(v, w'))).real (openConn v b) :=
    measureReal_mono inter_subset_left (measure_ne_top _ _)
  linarith

/-- **The paper's hypothesis (39) is vacuous**: it is the proved Conjecture 1 in `G`, for the source
`x` and the minimiser `a`. -/
theorem conjecture6_hypotheses_vacuous (n : ℕ) (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (hA : A.Nonempty) (x b a : Fin n) (haA : a ∈ A)
    (hmin : ∀ y ∈ A, (prodBernoulli w).real (openConn a b) ≤ (prodBernoulli w).real (openConn y b)) :
    (prodBernoulli w).real (⋃ y ∈ A, openConn x y) * (prodBernoulli w).real (openConn a b) ≤
      (prodBernoulli w).real (openConn x b) := by
  have h1 := conjecture1_holds n w A hA x b
  have hinf : A.inf' hA (fun y => (prodBernoulli w).real (openConn y b)) =
      (prodBernoulli w).real (openConn a b) :=
    le_antisymm (Finset.inf'_le _ haA) (Finset.le_inf' hA _ fun y hy => hmin y hy)
  rw [hinf] at h1
  exact h1

end KNAll

end

#print axioms KNAll.conjecture6Strong_of_forceOpen_min
#print axioms KNAll.conjecture6_of_conjecture6Strong
#print axioms KNAll.conjecture6_hypotheses_vacuous
