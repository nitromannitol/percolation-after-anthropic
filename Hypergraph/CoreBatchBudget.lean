import Hypergraph.CoreDirection
import Hypergraph.CoreFrontier
import Hypergraph.DamageBlocks

/-!
# The one-owner batch error budget

One macro trial has one incoming failure event and at most four outgoing stopped-direction
failures.  This file records the finite union bound with the exact constants used by the bounded
damage comparison: `rho/32 + 4*(rho/16) = 9*rho/32`.
-/

noncomputable section

namespace KNAll.Site.CoreBatch

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {kappa V : Type*}

/-- A finite union bound under an arbitrary pinned transcript. -/
theorem prob_biUnion_finset_le_sum [DecidableEq V]
    (h : FRDom.Transcript kappa V) (p : kappa → unitInterval)
    (A : Finset V) (F : V → Set (Set kappa)) :
    h.prob p (⋃ x ∈ A, F x) ≤ ∑ x ∈ A, h.prob p (F x) := by
  unfold FRDom.Transcript.prob pinnedProb
  simp only [Set.preimage_iUnion]
  exact measureReal_biUnion_finset_le A _

/-- If every member of a finite family costs at most `c`, its union costs at most
`A.card * c`. -/
theorem prob_biUnion_finset_le_card_mul [DecidableEq V]
    (h : FRDom.Transcript kappa V) (p : kappa → unitInterval)
    (A : Finset V) (F : V → Set (Set kappa)) {c : Real}
    (hF : ∀ x ∈ A, h.prob p (F x) ≤ c) :
    h.prob p (⋃ x ∈ A, F x) ≤ A.card * c := by
  refine (prob_biUnion_finset_le_sum h p A F).trans ?_
  calc
    ∑ x ∈ A, h.prob p (F x) ≤ ∑ _x ∈ A, c :=
      Finset.sum_le_sum fun x hx => hF x hx
    _ = A.card * c := by simp

/-- The exact batch budget.  No independence between the direction events is used. -/
theorem prob_incoming_or_directions_le {d : Nat} [NeZero d]
    (h : MacroExp.Tr d) (p : Site d → unitInterval)
    (heads : Finset (Site 2)) (incomingFail : Set (SiteConfig (Site d)))
    (directionFail : Site 2 → Set (SiteConfig (Site d))) {rho : Real}
    (hrho : 0 ≤ rho) (hcard : heads.card ≤ 4)
    (hin : h.prob p incomingFail ≤ rho / 32)
    (hout : ∀ y ∈ heads, h.prob p (directionFail y) ≤ rho / 16) :
    h.prob p (incomingFail ∪ ⋃ y ∈ heads, directionFail y) ≤ 9 * rho / 32 := by
  have hdirs : h.prob p (⋃ y ∈ heads, directionFail y) ≤ heads.card * (rho / 16) :=
    prob_biUnion_finset_le_card_mul h p heads directionFail hout
  have hcard' : (heads.card : Real) ≤ 4 := by exact_mod_cast hcard
  have hmul : (heads.card : Real) * (rho / 16) ≤ 4 * (rho / 16) :=
    mul_le_mul_of_nonneg_right hcard' (by positivity)
  calc
    h.prob p (incomingFail ∪ ⋃ y ∈ heads, directionFail y)
        ≤ h.prob p incomingFail + h.prob p (⋃ y ∈ heads, directionFail y) :=
      AtomTower.prob_union_le h p _ _
    _ ≤ rho / 32 + heads.card * (rho / 16) := add_le_add hin hdirs
    _ ≤ rho / 32 + 4 * (rho / 16) := add_le_add le_rfl hmul
    _ = 9 * rho / 32 := by ring

/-- Specialization to the one-owner frontier's newly created heads. -/
theorem prob_newHead_batchFailure_le {d : Nat} [NeZero d]
    (h : MacroExp.Tr d) (p : Site d → unitInterval) (z : Site 2)
    (incomingFail : Set (SiteConfig (Site d)))
    (directionFail : Site 2 → Set (SiteConfig (Site d))) {rho : Real}
    (hrho : 0 ≤ rho) (hin : h.prob p incomingFail ≤ rho / 32)
    (hout : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      h.prob p (directionFail y) ≤ rho / 16) :
    h.prob p
        (incomingFail ∪ ⋃ y ∈ CoreFrontier.newHeads (d := d) h z, directionFail y) ≤
      9 * rho / 32 :=
  prob_incoming_or_directions_le h p _ incomingFail directionFail hrho
    (CoreFrontier.card_newHeads_le_four h z) hin hout

/-- Complement form consumed by adaptive domination. -/
theorem one_sub_le_prob_compl {d : Nat} [NeZero d]
    (h : MacroExp.Tr d) (p : Site d → unitInterval)
    (failure : Set (SiteConfig (Site d))) {eta : Real}
    (hm : MeasurableSet failure) (hfail : h.prob p failure ≤ eta) :
    1 - eta ≤ h.prob p failureᶜ := by
  change pinnedProb p (↑h.inspected : Set (Site d)) h.state failure ≤ eta at hfail
  rw [FRDom.Transcript.prob_eq, pinnedProb_compl _ _ _ hm]
  linarith

/-- At the fixed planar comparison density, the batch error is exactly `DamageBlocks.etaMax`. -/
theorem nine_rho_over_thirtytwo_eq_etaMax
    {rho : Real} (hrho : rho = 1 / 2 ^ 32) :
    9 * rho / 32 = (KNAll.Site.DamageBlocks.etaMax : unitInterval) := by
  rw [hrho, KNAll.Site.DamageBlocks.coe_etaMax]
  norm_num

#print axioms KNAll.Site.CoreBatch.prob_biUnion_finset_le_sum
#print axioms KNAll.Site.CoreBatch.prob_incoming_or_directions_le
#print axioms KNAll.Site.CoreBatch.prob_newHead_batchFailure_le
#print axioms KNAll.Site.CoreBatch.one_sub_le_prob_compl
#print axioms KNAll.Site.CoreBatch.nine_rho_over_thirtytwo_eq_etaMax

end KNAll.Site.CoreBatch

end
