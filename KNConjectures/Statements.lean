import Percolation.Continuity.MainTheorem

/-!
# The Kozma–Nitzan conjectures as closed propositions, in the development's vocabulary

Finite weighted graph: vertices `Fin n`, weights `w : Sym2 (Fin n) → [0,1]` (absent edge = weight `0`), measure `prodBernoulli w`,
`x ↔ y` = `openConn x y`, `C_x = openCluster ω x`, `o ↔ A` = `⋃ a ∈ A, openConn o a`.  A monotone cluster property is
`ω ↦ F (openCluster ω x)` with `F : Set (Fin n) → ℝ` increasing for `⊆`.
-/

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature

/-- **Conjecture 4, fixed-minimizer form** (stronger than the paper's): if `a ∈ A` minimises `E F(C_x)` over `A` then
`E[F(C_a); o ↔ A] ≤ E[F(C_o); o ↔ A]`. -/
def Conjecture4Fixed : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o a : Fin n) (F : Set (Fin n) → ℝ),
    a ∈ A → (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') →
    (∀ x ∈ A, ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω x) ∂(prodBernoulli w)) →
    ∫ ω in ⋃ x ∈ A, openConn o x, F (openCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in ⋃ x ∈ A, openConn o x, F (openCluster ω o) ∂(prodBernoulli w)

/-- **Conjecture 4** (arXiv:2401.12397, p. 32): `E[F(C_o); o ↔ A] ≥ min_{x ∈ A} E[F(C_x); o ↔ A]` for every increasing `F`. -/
def Conjecture4 : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (hA : A.Nonempty) (o : Fin n) (F : Set (Fin n) → ℝ),
    (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') →
    A.inf' hA (fun x => ∫ ω in ⋃ y ∈ A, openConn o y, F (openCluster ω x) ∂(prodBernoulli w)) ≤
      ∫ ω in ⋃ y ∈ A, openConn o y, F (openCluster ω o) ∂(prodBernoulli w)

/-- **Conjecture 2, strong (pre-FKG) form**: `P(o ↔ b, o ↔ A) ≥ min_{x ∈ A} P(x ↔ b, o ↔ A)`. -/
def Conjecture2Strong : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (hA : A.Nonempty) (o b : Fin n),
    A.inf' hA (fun x => (prodBernoulli w).real (openConn x b ∩ ⋃ y ∈ A, openConn o y)) ≤
      (prodBernoulli w).real (openConn o b ∩ ⋃ y ∈ A, openConn o y)

/-- **Conjecture 2** (arXiv:2401.12397, p. 3): `P(o ↔ b) ≥ min_{x ∈ A} P(o ↔ A, x ↔ b)`. -/
def Conjecture2 : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (hA : A.Nonempty) (o b : Fin n),
    A.inf' hA (fun x => (prodBernoulli w).real (openConn x b ∩ ⋃ y ∈ A, openConn o y)) ≤
      (prodBernoulli w).real (openConn o b)

/-- **Conjecture 1** (arXiv:2401.12397, p. 3): `P(o ↔ b) ≥ P(o ↔ A) · min_{x ∈ A} P(x ↔ b)`. -/
def Conjecture1 : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (hA : A.Nonempty) (o b : Fin n),
    (prodBernoulli w).real (⋃ a ∈ A, openConn o a) * A.inf' hA (fun a => (prodBernoulli w).real (openConn a b)) ≤
      (prodBernoulli w).real (openConn o b)


/-- **Question 7** (arXiv:2401.12397, p. 36, display (41)): if `a ∈ A` minimises `P(a ↔ b)` over `A` then
`P(o ↔ A, a ↔ b) ≤ P(o ↔ b, o ↔ A)`. -/
def Question7 : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b a : Fin n),
    a ∈ A → (∀ x ∈ A, (prodBernoulli w).real (openConn a b) ≤ (prodBernoulli w).real (openConn x b)) →
    (prodBernoulli w).real (openConn a b ∩ ⋃ y ∈ A, openConn o y) ≤
      (prodBernoulli w).real (openConn o b ∩ ⋃ y ∈ A, openConn o y)

end KNAll
