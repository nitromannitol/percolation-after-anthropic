import KNConjectures.Question5Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The finite-dimensional separation step for Kozma--Nitzan's Question 5

The dual statement `KNAll.question5_dual` says that every nonnegative linear functional sees
at least one row of the matrix below the target vector.  Strict separation from the Minkowski sum
of the convex hull of the rows and the nonnegative orthant turns that dual statement into a single
convex combination which lies coordinatewise below the target vector.
-/

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical Pointwise

/-- A finite-dimensional theorem of the alternative, in the precise form needed below. -/
private theorem finite_separation
    {I J : Type*} [Finite I] [Fintype J] [DecidableEq J]
    (A : Finset I) (hA : A.Nonempty) (M : I → J → ℝ) (v : J → ℝ)
    (hdual : ∀ y : J → ℝ, (∀ b, 0 ≤ y b) →
      ∃ a ∈ A, ∑ b : J, y b * M a b ≤ ∑ b : J, y b * v b) :
    ∃ c : I → ℝ, (∀ a, 0 ≤ c a) ∧ (∀ a, a ∉ A → c a = 0) ∧
      (∑ a ∈ A, c a = 1) ∧ ∀ b : J, ∑ a ∈ A, c a * M a b ≤ v b := by
  let q : ↑A → (J → ℝ) := fun a ↦ M a
  let P : Set (J → ℝ) := {u | ∀ b, 0 ≤ u b}
  let C : Set (J → ℝ) := convexHull ℝ (Set.range q) + P
  have hPconv : Convex ℝ P := by
    intro x hx y hy a b ha hb hab i
    simp only [P, Set.mem_setOf_eq] at hx hy
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  have hPclosed : IsClosed P := by
    simp only [P, Set.setOf_forall]
    exact isClosed_iInter fun b ↦ isClosed_le continuous_const (continuous_apply b)
  have hRangeFinite : (Set.range q).Finite := Set.finite_range q
  have hCconv : Convex ℝ C := (convex_convexHull ℝ _).add hPconv
  have hCclosed : IsClosed C :=
    hPclosed.add_left_of_isCompact (hRangeFinite.isCompact_convexHull ℝ)
  have hmemConv (a : I) (ha : a ∈ A) : M a ∈ convexHull ℝ (Set.range q) := by
    exact subset_convexHull ℝ _ ⟨⟨a, ha⟩, rfl⟩
  have hzeroP : (0 : J → ℝ) ∈ P := fun _ ↦ le_rfl
  have hmemC (a : I) (ha : a ∈ A) : M a ∈ C := by
    rw [← add_zero (M a)]
    exact Set.add_mem_add (hmemConv a ha) hzeroP
  have hvC : v ∈ C := by
    by_contra hvC
    obtain ⟨f, α, hvα, hsep⟩ :=
      geometric_hahn_banach_point_closed hCconv hCclosed hvC
    let y : J → ℝ := fun b ↦ f (Pi.single b 1)
    have hf_eq (z : J → ℝ) : f z = ∑ b : J, y b * z b := by
      conv_lhs => rw [pi_eq_sum_univ' z, map_sum]
      simp [y, map_smul, smul_eq_mul, mul_comm]
    obtain ⟨a₀, ha₀⟩ := hA
    have hy : ∀ b, 0 ≤ y b := by
      intro b
      by_contra hb
      have hyneg : y b < 0 := lt_of_not_ge hb
      let e : J → ℝ := Pi.single b 1
      have he : e ∈ P := by
        intro i
        by_cases hi : i = b <;> simp [e, hi]
      have hbase : α < f (M a₀) := hsep (M a₀) (hmemC a₀ ha₀)
      let t : ℝ := (f (M a₀) - α + 1) / (-y b)
      have ht : 0 ≤ t := by
        apply div_nonneg
        · linarith
        · linarith
      have hte : t • e ∈ P := by
        intro i
        simp only [P, Set.mem_setOf_eq] at he ⊢
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg ht (he i)
      have hray : α < f (M a₀ + t • e) :=
        hsep _ (Set.add_mem_add (hmemConv a₀ ha₀) hte)
      have hcalc : f (M a₀ + t • e) = α - 1 := by
        rw [map_add, map_smul]
        change f (M a₀) + t * y b = α - 1
        have hne : -y b ≠ 0 := ne_of_gt (by linarith)
        rw [show y b = -(-y b) by ring, mul_neg, ← sub_eq_add_neg]
        dsimp only [t]
        rw [div_mul_cancel₀ _ hne]
        ring
      rw [hcalc] at hray
      linarith
    obtain ⟨a, ha, hle⟩ := hdual y hy
    have hf_le : f (M a) ≤ f v := by
      calc
        f (M a) = ∑ b : J, y b * M a b := hf_eq _
        _ ≤ ∑ b : J, y b * v b := hle
        _ = f v := (hf_eq _).symm
    linarith [hsep (M a) (hmemC a ha)]
  obtain ⟨x, hx, u, hu, hxu⟩ := Set.mem_add.1 hvC
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw₀, hw₁, hwx⟩ := hx
  have hwx' : ∑ i ∈ s, w i • q i = x := by
    rw [← Finset.affineCombination_eq_linear_combination s q w hw₁]
    exact hwx
  let c : I → ℝ := fun a ↦
    if ha : a ∈ A then if (⟨a, ha⟩ : ↑A) ∈ s then w ⟨a, ha⟩ else 0 else 0
  have hAs : A.attach ∩ s = s :=
    Finset.inter_eq_right.2 (fun i _ ↦ A.mem_attach i)
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro a
    simp only [c]
    split_ifs with ha his
    · exact hw₀ _ his
    · exact le_rfl
    · exact le_rfl
  · intro a ha
    simp [c, ha]
  · rw [← A.sum_attach]
    simpa [c, hAs] using hw₁
  · intro b
    have hxb : ∑ a ∈ A, c a * M a b = x b := by
      rw [← A.sum_attach]
      have h := congrFun hwx' b
      simpa [c, q, hAs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    have hub := hu b
    have hxub := congrFun hxu b
    change x b + u b = v b at hxub
    rw [hxb]
    linarith

/-- **Kozma--Nitzan, Question 5 (finite-dimensional separation half).**

There is one probability distribution on the relay set `A`, independent of `b`, whose weighted
row of joint connection probabilities is bounded coordinatewise by the connection probabilities
from `o`. -/
theorem question5_holds (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (hA : A.Nonempty) (o : Fin n) :
    ∃ c : Fin n → ℝ, (∀ a, 0 ≤ c a) ∧ (∀ a, a ∉ A → c a = 0) ∧ (∑ a ∈ A, c a = 1) ∧
      ∀ b : Fin n, ∑ a ∈ A, c a * (prodBernoulli w).real
        (openConn a b ∩ ⋃ x ∈ A, openConn o x) ≤ (prodBernoulli w).real (openConn o b) := by
  let M : Fin n → Fin n → ℝ := fun a b ↦
    (prodBernoulli w).real (openConn a b ∩ ⋃ x ∈ A, openConn o x)
  let v : Fin n → ℝ := fun b ↦ (prodBernoulli w).real (openConn o b)
  apply finite_separation A hA M v
  intro y hy
  simpa [M, v] using question5_dual n w A hA o y hy

end KNAll

end

#print axioms KNAll.question5_holds
