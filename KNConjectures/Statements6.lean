import KNConjectures.Statements

/-! Kozma–Nitzan's Conjecture 6 (arXiv:2401.12397, p. 34): statements only; NOT proved here. -/

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature

/-- The weighting with the pair `e` forced open (`G/e` for connectivity events). -/
noncomputable def forceOpen {n : ℕ} (w : Sym2 (Fin n) → unitInterval) (e : Sym2 (Fin n)) : Sym2 (Fin n) → unitInterval :=
  Function.update w e 1

/-- **Conjecture 6, strong form** (no hypothesis on the endpoints): if `a ∈ A` minimises `P_G(x ↔ b)` over `A`, then in `G/e`,
`e = {v, w'}`: `P_{G/e}(a ↔ b, v ↔ A) ≤ P_{G/e}(v ↔ b, v ↔ A)`. -/
def Conjecture6Strong : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (v w' b a : Fin n),
    a ∈ A → (∀ x ∈ A, (prodBernoulli w).real (openConn a b) ≤ (prodBernoulli w).real (openConn x b)) →
    (prodBernoulli (forceOpen w s(v, w'))).real (openConn a b ∩ ⋃ y ∈ A, openConn v y) ≤
      (prodBernoulli (forceOpen w s(v, w'))).real (openConn v b ∩ ⋃ y ∈ A, openConn v y)

/-- **Conjecture 6** (arXiv:2401.12397): with `a` as above (and, in the paper, two endpoint hypotheses that are not needed),
`P_{G/e}(v ↔ b) ≥ P_{G/e}(v ↔ A) · P_{G/e}(a ↔ b)`. -/
def Conjecture6 : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (v w' b a : Fin n),
    a ∈ A → (∀ x ∈ A, (prodBernoulli w).real (openConn a b) ≤ (prodBernoulli w).real (openConn x b)) →
    (prodBernoulli (forceOpen w s(v, w'))).real (⋃ y ∈ A, openConn v y) *
        (prodBernoulli (forceOpen w s(v, w'))).real (openConn a b) ≤
      (prodBernoulli (forceOpen w s(v, w'))).real (openConn v b)

end KNAll
