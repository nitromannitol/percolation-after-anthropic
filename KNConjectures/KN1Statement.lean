-- SPDX-License-Identifier: Apache-2.0
-- Produced by Claude Fable 5.1 (max); released under the Apache License 2.0 (matching the development it is a corollary of).
import Mathlib

/-!
# Kozma–Nitzan's Conjecture 1, stated from Mathlib alone

Bernoulli bond percolation on a finite weighted graph: the vertices are `Fin n`, every unordered pair `e : Sym2 (Fin n)`
carries a weight `w e ∈ [0,1]` and is open independently with probability `w e` (a pair of weight `0` is an absent edge).
`u ↔ v` is the event that `u` and `v` are joined by a path of open edges.  The conjecture (arXiv:2401.12397, p. 3):
`P(o ↔ b) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)` for every nonempty finite set `A` of vertices and all vertices `o, b`.

The three definitions below are definitionally equal copies of the ones used by the Lean development,
`Percolation.Literature.LatticeModels.prodBernoulli`, `Percolation.Literature.openGraph`, `Percolation.Literature.openConn`
(the development's abbreviation `BondConfig V` for `Set (Sym2 V)` is unfolded).
-/

namespace KN1Statement

open MeasureTheory

/-- The product of Bernoulli measures with parameters `p i` on `Set ι`: each `i` belongs to the random set
independently with probability `p i` (the pullback along `s ↦ (i ↦ i ∈ s)` of the infinite product of the two-point
measures `p i • δ_True + (1 - p i) • δ_False`). -/
noncomputable def prodBernoulli {ι : Type*} (p : ι → unitInterval) : Measure (Set ι) :=
  .comap (fun s i => i ∈ s) <| Measure.infinitePi fun i : ι =>
    unitInterval.toNNReal (p i) • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm (p i)) • Measure.dirac False

/-- The graph of open edges of a configuration `ω ⊆ Sym2 V`. -/
def openGraph {V : Type*} (ω : Set (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet ω

/-- The event `{x ↔ y}`: `x` and `y` are joined by an open path. -/
def openConn {V : Type*} (x y : V) : Set (Set (Sym2 V)) := {ω | (openGraph ω).Reachable x y}

/-- **Kozma–Nitzan's Conjecture 1.** For every `n`, every weight function `w` on the pairs of `n` vertices, every
nonempty finite relay set `A` and all vertices `o, b`: `P(o ↔ A) · min_{a ∈ A} P(a ↔ b) ≤ P(o ↔ b)`, where
`o ↔ A` is `⋃ a ∈ A, {o ↔ a}`. -/
def MultiplicativeGluing : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (hA : A.Nonempty) (o b : Fin n),
    (prodBernoulli w).real (⋃ a ∈ A, openConn o a) * A.inf' hA (fun a => (prodBernoulli w).real (openConn a b)) ≤
      (prodBernoulli w).real (openConn o b)

end KN1Statement
