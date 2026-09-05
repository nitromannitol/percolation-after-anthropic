import KNConjectures.Conjectures

/-!
# The dual (linear-functional) form of Kozma–Nitzan's Question 5

Question 5 (arXiv:2401.12397, p. 32) asks for nonnegative `c_a`, `a ∈ A`, with `∑ c_a = 1`,
*independent of `b`*, such that display (38)

    P(o ↔ b) ≥ ∑_{a ∈ A} c_a · P(o ↔ A, a ↔ b)      for all b.

By LP duality (equivalently, by separating the point `(P(o ↔ b))_b` from the polyhedron
`conv {(P(o ↔ A, a ↔ b))_b : a ∈ A} − ℝ^V_{≥0}`), such a vector exists as soon as for every
nonnegative weight vector `y` on the vertices some `a ∈ A` satisfies

    ∑_b y_b · P(o ↔ A, a ↔ b) ≤ ∑_b y_b · P(o ↔ b).

That is the statement proved here, and it is exactly Conjecture 4 applied to the increasing
cluster functional `F_y K = ∑_b y_b · 1{b ∈ K}`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

/-- **Question 5, dual form.** For every nonnegative weight vector `y` on the vertices there is a
relay `a ∈ A` with `∑_b y_b P(o ↔ A, a ↔ b) ≤ ∑_b y_b P(o ↔ b)`. -/
theorem question5_dual (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (hA : A.Nonempty) (o : Fin n) (y : Fin n → ℝ) (hy : ∀ b, 0 ≤ y b) :
    ∃ a ∈ A, ∑ b : Fin n, y b *
        (prodBernoulli w).real (openConn a b ∩ ⋃ x ∈ A, openConn o x) ≤
      ∑ b : Fin n, y b * (prodBernoulli w).real (openConn o b) := by
  set μ := prodBernoulli w with hμ
  set U : Set (BondConfig (Fin n)) := ⋃ x ∈ A, openConn o x with hU
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  -- the increasing functional `F_y K = ∑_b y_b 1{b ∈ K}`
  set F : Set (Fin n) → ℝ := fun K => ∑ b : Fin n, y b * (if b ∈ K then (1 : ℝ) else 0) with hF
  have hFmono : ∀ S T : Set (Fin n), S ⊆ T → F S ≤ F T := by
    intro S T hST
    refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hy b)
    by_cases hb : b ∈ S
    · rw [if_pos hb, if_pos (hST hb)]
    · rw [if_neg hb]; split_ifs <;> norm_num
  -- the two integral computations
  have hone : ∀ (x b : Fin n) (S : Set (BondConfig (Fin n))),
      ∫ ω in S, (if b ∈ openCluster ω x then (1 : ℝ) else 0) ∂μ = μ.real (openConn x b ∩ S) := by
    intro x b S
    have hind : (fun ω : BondConfig (Fin n) => (if b ∈ openCluster ω x then (1 : ℝ) else 0)) =
        (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
      funext ω
      by_cases hω : ω ∈ (openConn x b : Set (BondConfig (Fin n)))
      · rw [Set.indicator_of_mem hω, Pi.one_apply, if_pos (show b ∈ openCluster ω x from hω)]
      · rw [Set.indicator_of_notMem hω, if_neg (show b ∉ openCluster ω x from hω)]
    rw [hind, ← integral_indicator (hmeas _), Set.indicator_indicator,
      integral_indicator_one ((hmeas _).inter (hmeas _)), Set.inter_comm]
  have hint : ∀ x : Fin n, ∫ ω in U, F (openCluster ω x) ∂μ =
      ∑ b : Fin n, y b * μ.real (openConn x b ∩ U) := by
    intro x
    simp only [hF]
    rw [integral_finsetSum _ (fun b _ => (Integrable.of_finite).integrableOn)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, hone x b U]
  -- Conjecture 4 for `F_y`
  have h4 := KNAll.conjecture4_holds n w A hA o F hFmono
  rw [← hμ, ← hU] at h4
  obtain ⟨a, haA, ha⟩ := Finset.exists_mem_eq_inf' hA (fun x => ∫ ω in U, F (openCluster ω x) ∂μ)
  refine ⟨a, haA, ?_⟩
  rw [← hint a, ← ha]
  refine h4.trans ?_
  rw [hint o]
  refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ (hy b)
  exact measureReal_mono Set.inter_subset_left (measure_ne_top _ _)

end KNAll

end

#print axioms KNAll.question5_dual
