import KNConjectures.Conjectures

/-!
# Kozma--Nitzan Question 8: definitions and closed statements

The selection rule in the printed question minimises
`P(a ↔ b, o ↮ A)`.  This file contains only the common definitions, the four closed
formulations, the elementary total-probability identity, and the statement-only conjectural
bridge from the note.  In particular, `Question8Bridge` is a definition of a proposition, not a
proved theorem.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

/-- The event `U = {o ↔ A}`. -/
def U {n : ℕ} (A : Finset (Fin n)) (o : Fin n) : Set (BondConfig (Fin n)) :=
  ⋃ x ∈ A, openConn o x

/-- `L_a = P(a ↔ b, o ↔ A)`, the left side of display (41). -/
def q8L {n : ℕ} (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) : ℝ :=
  (prodBernoulli w).real (openConn a b ∩ U A o)

/-- `ρ_a = P(a ↔ b, o ↮ A)`, the score actually minimised in Question 8. -/
def q8Score {n : ℕ} (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) : ℝ :=
  (prodBernoulli w).real (openConn a b ∩ (U A o)ᶜ)

/-- `R = P(o ↔ b, o ↔ A)`, the right side of display (41). -/
def q8R {n : ℕ} (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b : Fin n) : ℝ :=
  (prodBernoulli w).real (openConn o b ∩ U A o)

/-- `a` belongs to `A` and minimises the printed Question 8 score on `A`. -/
def IsQ8Min {n : ℕ} (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) : Prop :=
  a ∈ A ∧ ∀ x ∈ A, q8Score w A o b a ≤ q8Score w A o b x

/-- `a` belongs to `A` and is the strict (hence unique) Question 8 minimiser. -/
def IsQ8StrictMin {n : ℕ} (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) : Prop :=
  a ∈ A ∧ ∀ x ∈ A, x ≠ a → q8Score w A o b a < q8Score w A o b x

/-- **Question 8, every-minimiser reading.**  This closed proposition is false. -/
def Question8EveryMin : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n), IsQ8Min w A o b a → q8L w A o b a ≤ q8R w A o b

/-- **Question 8, strict-minimiser reading.**  This is an open closed proposition. -/
def Question8Strict : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n), IsQ8StrictMin w A o b a → q8L w A o b a ≤ q8R w A o b

/-- **Question 8 with positive avoidance.**  Every tied minimiser is quantified over. -/
def Question8Positive : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n),
    0 < (prodBernoulli w).real (U A o)ᶜ →
      IsQ8Min w A o b a → q8L w A o b a ≤ q8R w A o b

/-- **Question 8, existential reading.**  Some minimising relay satisfies display (41). -/
def Question8ExistsGoodMin : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)), A.Nonempty →
    ∀ (o b : Fin n), ∃ a : Fin n, IsQ8Min w A o b a ∧ q8L w A o b a ≤ q8R w A o b

/-- The partition `U ⊎ Uᶜ`: `P(a ↔ b) = L_a + ρ_a`. -/
theorem q8_total_split {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (o b a : Fin n) :
    (prodBernoulli w).real (openConn a b) = q8L w A o b a + q8Score w A o b a := by
  rw [q8L, q8Score, ← measureReal_inter_add_sdiff
    (s := (openConn a b : Set (BondConfig (Fin n))))
    (MeasurableSet.of_discrete : MeasurableSet (U A o)), Set.sdiff_eq]

/--
The conjectural boxed inequality from the note.  The assumptions describe the interior strict
core.  The rank is injective on `A.erase a` and is nondecreasing in
`(ρ_x - ρ_a) / P(x ↮ a)`; its first-relay atoms are written out in the sum.

This is deliberately a statement-only `def`: no result in the proved Q8 chain may use it as a
lemma.
-/
def Question8Bridge : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) (r : Fin n → ℕ),
    (∀ e, 0 < (w e : ℝ) ∧ (w e : ℝ) < 1) →
    2 ≤ A.card →
    0 < (prodBernoulli w).real (U A o)ᶜ →
    0 < q8Score w A o b a →
    IsQ8StrictMin w A o b a →
    Set.InjOn r (↑(A.erase a) : Set (Fin n)) →
    (∀ x ∈ A.erase a, ∀ y ∈ A.erase a, r x < r y →
      (q8Score w A o b x - q8Score w A o b a) /
          (prodBernoulli w).real (openConn x a)ᶜ ≤
        (q8Score w A o b y - q8Score w A o b a) /
          (prodBernoulli w).real (openConn y a)ᶜ) →
    ∑ x ∈ A.erase a,
        (prodBernoulli w).real
            ((openConn o a)ᶜ ∩
              (openConn o x ∩
                ⋂ y ∈ (A.erase a).filter (fun y ↦ r y < r x), (openConn o y)ᶜ) :
              Set (BondConfig (Fin n))) *
          ((q8Score w A o b x - q8Score w A o b a) /
            (prodBernoulli w).real (openConn x a)ᶜ) ≤
      q8R w A o b - q8L w A o b a

end KNAll

end

#print axioms KNAll.q8_total_split
#print KNAll.Question8EveryMin
#print KNAll.Question8Strict
#print KNAll.Question8Positive
#print KNAll.Question8ExistsGoodMin
#print KNAll.Question8Bridge
