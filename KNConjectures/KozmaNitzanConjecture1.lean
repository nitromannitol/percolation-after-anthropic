-- SPDX-License-Identifier: Apache-2.0
-- Produced by Claude Fable 5.1 (max); released under the Apache License 2.0 (matching the development it is a corollary of).
import Percolation.Continuity.MainTheorem

/-!
# Kozma–Nitzan's Conjecture 1 (multiplicative gluing) as a closed corollary of the existing development

`P(o ↔ b) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)` on every finite weighted graph (weights in `[0,1]`, any finite relay set
`A`, any vertices `o, b`, no distinctness assumptions).  Derived from the theorems already in the library along the chain
CSH ⟹ (S5D) ⟹ (S5) at non-degenerate weights ⟹ (S5) at all weights ⟹ (GEN) for every relay set ⟹ (AG-loc), keeping the factor
`P(o ↔ A)` that `AGloc.additiveGluing_card_of_agloc_firstRank` bounds by `1`.
-/

noncomputable section

/- All declarations live in the fresh namespace `KN1Corollary`, so that they cannot be mistaken for theorems of the
development; every name they use from the development is reached through `open`. -/
namespace KN1Corollary

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

/-- **(S5) at every weight function in `[0,1]`**, from the conditioned slack hierarchy. -/
theorem surplusTransfer_all (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (T : Finset (Fin n)) (o v : Fin n)
    (F : Set (Fin n) → ℝ) (r : Fin n → ℕ) (hvT : v ∉ T)
    (hF : ∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') (_hF0 : ∀ S, 0 ≤ F S) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) :
    (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        surplus w T r F v ≤
      (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} * surplus w T r F o :=
  surplusTransfer_of_nondegenerate T o v F
    (fun p hp r' hr' hc' =>
      surplusTransfer_nondegenerate_of_surplusMargin p hp T o v F r' hvT hr' hc'
        (fun hoT hov =>
          surplusMargin_nonneg_of_csh p hp o v (fun x Y D => cshAll n p hp o v x Y D hov) T r' [] F hF hr' hc'
            hoT hvT List.nodup_nil (fun _ hd => absurd hd List.not_mem_nil)))
    w r hr hcompat

/-- **(GEN) for every relay set and every weight function**: `Σ_{a ∈ A} P(P^o_a) · E F(C_a) ≤ E[F(C_o); o ↔ A]`. -/
theorem gen_all (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o : Fin n)
    (F : Set (Fin n) → ℝ) (r : Fin n → ℕ)
    (hF : ∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') (hF0 : ∀ S, 0 ≤ F S) (hr : Set.InjOn r ↑A)
    (hcompat : ∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
      ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) :
    ∑ a ∈ A, (prodBernoulli w).real
          (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in (⋃ a ∈ A, openConn o a), F (openCluster ω o) ∂(prodBernoulli w) := by
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [Finset.card_eq_zero.1 h0]
    simp
  · obtain ⟨K, hK⟩ : ∃ K, A.card = K + 1 := ⟨A.card - 1, by omega⟩
    exact AGloc.gen_firstRank_of_surplusTransfer K
      (fun n w T o v F r _ hvT hF hF0 hr hc => surplusTransfer_all n w T o v F r hvT hF hF0 hr hc)
      n w A o F r (by omega) hF hF0 hr hcompat

/-- **Multiplicative gluing, common-lower-bound form**: if `q ≤ P(a ↔ b)` for every `a ∈ A` then
`q · P(o ↔ A) ≤ P(o ↔ b)`.  No hypothesis on `q`, on `A` (may be empty) or on the vertices. -/
theorem multiplicativeGluing_all (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n)
    (q : ℝ) (hq : ∀ a ∈ A, q ≤ (prodBernoulli w).real (openConn a b)) :
    q * (prodBernoulli w).real (⋃ a ∈ A, openConn o a) ≤ (prodBernoulli w).real (openConn o b) := by
  classical
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun S => (Set.toFinite S).measurableSet
  obtain ⟨r, hrinj, hrc⟩ := AGloc.exists_rank_compat A (fun a => μ.real (openConn a b))
  have key := AGloc.agloc_firstRank_of_gen A.card
    (fun n' w' A' o' F r' _ hF hF0 hr' hc' => gen_all n' w' A' o' F r' hF hF0 hr' hc') n w A o b r le_rfl hrinj hrc
  rw [← hμ] at key
  have h1 : ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ :
        Set (BondConfig (Fin n))) * (1 - μ.real (openConn a b)) ≤
      ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ :
        Set (BondConfig (Fin n))) * (1 - q) := by
    refine Finset.sum_le_sum fun a ha => ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hq a ha]) measureReal_nonneg
  have h2 : ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ :
        Set (BondConfig (Fin n))) * (1 - q) =
      (1 - q) * μ.real (⋃ a ∈ A, openConn o a) := by
    rw [← Finset.sum_mul, mul_comm, AGloc.sum_measureReal_firstRank w A r o hrinj]
  have h4 : μ.real (⋃ a ∈ A, openConn o a) - μ.real (openConn o b) ≤
      μ.real ((⋃ a ∈ A, openConn o a) ∩ (openConn o b)ᶜ : Set (BondConfig (Fin n))) := by
    have hsp : μ.real (⋃ a ∈ A, openConn o a) =
        μ.real ((⋃ a ∈ A, openConn o a) ∩ openConn o b : Set (BondConfig (Fin n))) +
          μ.real ((⋃ a ∈ A, openConn o a) ∩ (openConn o b)ᶜ : Set (BondConfig (Fin n))) := by
      rw [← measureReal_inter_add_sdiff (s := ⋃ a ∈ A, (openConn o a : Set (BondConfig (Fin n)))) (h := measure_ne_top _ _)
        (hmeas (openConn o b)), Set.sdiff_eq]
    have hm : μ.real ((⋃ a ∈ A, openConn o a) ∩ openConn o b : Set (BondConfig (Fin n))) ≤ μ.real (openConn o b) :=
      measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
    linarith
  linarith [key, h1, h2, h4]

/-- **Kozma–Nitzan's Conjecture 1** (arXiv:2401.12397, p. 3): on every finite weighted graph, for every nonempty finite set `A`
of relays and all vertices `o, b`, `P(o ↔ b) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)`. -/
theorem kozmaNitzan_conjecture1 (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (hA : A.Nonempty)
    (o b : Fin n) :
    (prodBernoulli w).real (⋃ a ∈ A, openConn o a) * A.inf' hA (fun a => (prodBernoulli w).real (openConn a b)) ≤
      (prodBernoulli w).real (openConn o b) := by
  rw [mul_comm]
  exact multiplicativeGluing_all n w A o b _ (fun a ha => Finset.inf'_le _ ha)

end KN1Corollary

end

#print axioms KN1Corollary.gen_all
#print axioms KN1Corollary.multiplicativeGluing_all
#print axioms KN1Corollary.kozmaNitzan_conjecture1
