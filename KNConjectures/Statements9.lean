import KNConjectures.Statements
import KNConjectures.GuardedDefs

/-!
# Kozma--Nitzan Question 9 and the set-source fixed-minimizer input

This file contains statements only.  `deleteAt w o` is the weighting obtained by deleting the
whole star of `o`.  The set-source inequality below is the form of Conjecture 4 used after that
star has been exposed.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

/-- The weights of `G` with every edge at `o` deleted. -/
def deleteAt {n : ℕ} (w : Sym2 (Fin n) → unitInterval) (o : Fin n) :
    Sym2 (Fin n) → unitInterval :=
  fun e => if o ∈ e then 0 else w e

/-- **Question 9** (p. 36): if `a` minimises `P_H(x ↔ b)` over `A`, `H = G` minus the edges at
`o`, then display (41) holds. -/
def Question9 : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b a : Fin n),
    a ∈ A →
    (∀ x ∈ A, (prodBernoulli (deleteAt w o)).real (openConn a b) ≤
      (prodBernoulli (deleteAt w o)).real (openConn x b)) →
    (prodBernoulli w).real (openConn a b ∩ ⋃ y ∈ A, openConn o y) ≤
      (prodBernoulli w).real (openConn o b ∩ ⋃ y ∈ A, openConn o y)

/-- **Set-source fixed-minimizer inequality.**  This is the union-of-clusters version of
`conjecture4Fixed_holds`: the source cluster is the union of the clusters rooted in `S`.

No disjointness or nonemptiness assumptions are imposed.  If `S = ∅`, the source-connection
event is empty.  If `a ∈ S`, the source-avoidance event is empty by reflexivity of reachability.
Thus both degenerate cases already reduce to an integral over the empty set. -/
def SetSourceFixedMin : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A S : Finset (Fin n)) (a : Fin n)
      (F : Set (Fin n) → ℝ),
    a ∈ A → Monotone F →
    (∀ x ∈ A,
      (∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
        ∫ ω, F (openCluster ω x) ∂(prodBernoulli w)) →
    0 ≤ ∫ ω in
        {ω | ∀ s ∈ S, ¬ (openGraph ω).Reachable s a} ∩
          {ω | ∃ s ∈ S, ∃ t ∈ A.erase a, (openGraph ω).Reachable s t},
      (F (sourceCluster ω ↑S) - F (openCluster ω a)) ∂(prodBernoulli w)

end KNAll

end
