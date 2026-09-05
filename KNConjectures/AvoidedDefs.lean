import Percolation.Continuity.MainTheorem

/-!
# Avoided surplus: definitions

The development's surplus `CSH.surplus w T r F u = E[F(C_u); u ↔ T] − Σ_{a ∈ T} P(P^u_a)·m_a` with a base AVOIDED set `Y`:
* `condMean w Y F a = E[F(C_a); a ↮ Y] / P(a ↮ Y)` (real division, junk `0` when the denominator vanishes);
* `surplusY w Y T r F u = E[F(C_u); u ↮ Y, u ↔ T] − Σ_{a ∈ T} P({u ↮ Y} ∩ P^u_a)·m_a^Y`;
* `surplusMarginY w Y T r D o v F` = the (S5D) margin of `u ↦ surplusY w Y T r F u` with every avoidance set enlarged by `Y`.
-/

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {V : Type*} [Fintype V]

/-- The conditional relay mean `m_a^Y = E[F(C_a); a ↮ Y] / P(a ↮ Y)`. -/
def condMean (w : Sym2 V → unitInterval) (Y : Set V) (F : Set V → ℝ) (a : V) : ℝ :=
  (∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}, F (openCluster ω a) ∂(prodBernoulli w)) /
    (prodBernoulli w).real {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y}

/-- The avoided surplus `Sur^Y_u(T) = E[F(C_u); u ↮ Y, u ↔ T] − Σ_{a ∈ T} P({u ↮ Y} ∩ P^u_a) · m_a^Y`, with
`P^u_a = {u ↔ a} ∩ ⋂_{a' ∈ T, r a' < r a} {u ↮ a'}` the first-in-rank pattern of the development. -/
def surplusY (w : Sym2 V → unitInterval) (Y : Set V) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (u : V) : ℝ :=
  (∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable u y} ∩ ⋃ a ∈ T, openConn u a,
      F (openCluster ω u) ∂(prodBernoulli w)) -
    ∑ a ∈ T, (prodBernoulli w).real
        ({ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable u y} ∩
          (openConn u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn u a')ᶜ) : Set (BondConfig V)) *
      condMean w Y F a

/-- The avoided surplus-transfer margin with decoys: the level form of `u ↦ Sur^Y_u(T)` for the decoy list conditioned to
avoid `Y ∪ T` (and the earlier decoys) and the observer constant `P(o ∈ C_v | v ↮ Y ∪ T ∪ D)`. -/
def surplusMarginY (w : Sym2 V → unitInterval) (Y : Set V) (T : Finset V) (r : V → ℕ) (D : List V) (o v : V)
    (F : Set V → ℝ) : ℝ :=
  cshMarg (decoyList w (Y ∪ ↑T) D) (obsConst w o v (Y ∪ ↑T ∪ {d | d ∈ D})) o v (surplusY w Y T r F)

/-- With no decoys the margin is `Sur^Y_o(T) − p · Sur^Y_v(T)`, `p = P(o ↔ v, v ↮ Y ∪ T) / P(v ↮ Y ∪ T)`. -/
theorem surplusMarginY_nil (w : Sym2 V → unitInterval) (Y : Set V) (T : Finset V) (r : V → ℕ) (o v : V) (F : Set V → ℝ) :
    surplusMarginY w Y T r [] o v F =
      surplusY w Y T r F o -
        (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ Y ∪ (↑T : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) /
            (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ Y ∪ (↑T : Set V), ¬ (openGraph ω).Reachable v a} *
          surplusY w Y T r F v := by
  simp only [surplusMarginY, decoyList, cshMarg_nil, obsConst, List.not_mem_nil, setOf_false, union_empty]

/-- **(S5) with avoided set, product form**: if `P(v ↮ Y ∪ T) > 0` and the decoy-free margin is nonnegative then
`P(v ↮ Y ∪ T, o ↔ v) · Sur^Y_v(T) ≤ P(v ↮ Y ∪ T) · Sur^Y_o(T)`. -/
theorem surplusTransferY_of_surplusMarginY_nil (w : Sym2 V → unitInterval) (Y : Set V) (T : Finset V) (r : V → ℕ) (o v : V)
    (F : Set V → ℝ)
    (hpos : 0 < (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ Y ∪ (↑T : Set V), ¬ (openGraph ω).Reachable v a})
    (h : 0 ≤ surplusMarginY w Y T r [] o v F) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ Y ∪ (↑T : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        surplusY w Y T r F v ≤
      (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ Y ∪ (↑T : Set V), ¬ (openGraph ω).Reachable v a} *
        surplusY w Y T r F o := by
  rw [surplusMarginY_nil] at h
  set M := (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ Y ∪ (↑T : Set V), ¬ (openGraph ω).Reachable v a} with hM
  set E := (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ Y ∪ (↑T : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v)
    with hE
  have h2 : 0 ≤ M * (surplusY w Y T r F o - E / M * surplusY w Y T r F v) := mul_nonneg hpos.le h
  have h3 : M * (surplusY w Y T r F o - E / M * surplusY w Y T r F v) = M * surplusY w Y T r F o - E * surplusY w Y T r F v := by
    field_simp
  linarith [h2, h3]

/-- With `Y = ∅` the avoided surplus is the development's surplus. -/
theorem surplusY_empty (w : Sym2 V → unitInterval) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (u : V) :
    surplusY w ∅ T r F u = surplus w T r F u := by
  simp only [surplusY, surplus, condMean, mem_empty_iff_false, false_implies, implies_true, setOf_true, univ_inter,
    Measure.restrict_univ, probReal_univ, div_one]

end KNAll

end
