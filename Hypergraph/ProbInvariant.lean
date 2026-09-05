import Hypergraph.FiniteRadiusDomination

/-!
# Persistence of pinned-probability invariants

This file contains the measure-theoretic fact needed by the corrected macro examination.  A
conditional lower bound is represented by `FRDom.Transcript.prob`, hence by a product measure with
the finite transcript overwritten.  If a later examination reads coordinates disjoint from those
which determine the stored event, its pinned probability is unchanged.

No conditional-probability denominator is used, and the result applies to every transcript,
including transcripts having zero probability under the original product law.
-/

noncomputable section

namespace KNAll.Site.ProbInv

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {κ V : Type*}

/-- Pinned probability is monotone in the event. -/
theorem prob_mono (h : FRDom.Transcript κ V) (p : κ → unitInterval)
    {A B : Set (Set κ)} (hAB : A ⊆ B) : h.prob p A ≤ h.prob p B := by
  rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq]
  unfold pinnedProb
  exact measureReal_mono (Set.preimage_mono hAB) (measure_ne_top _ _)

/-- **Irrelevant-step persistence.**  Suppose `F` is fresh for a transcript and is disjoint from
the coordinate set `S` which determines `A`.  Reading `F`, with either macro verdict and with any
realized states, leaves the pinned probability of `A` unchanged.

Freshness is stated separately from `Disjoint F S`: in applications `S` contains the old inspected
set as well as a protected unread region. -/
theorem prob_step_eq_of_disjoint [DecidableEq κ] [DecidableEq V]
    (h : FRDom.Transcript κ V) (p : κ → unitInterval) (z : V) (F : Finset κ)
    (b : Bool) (ω : Set κ) {A : Set (Set κ)} {S : Set κ}
    (hfresh : Disjoint F h.inspected) (hA : DeterminedBy A S)
    (hdisj : Disjoint (↑F : Set κ) S) :
    (h.step z F b ω).prob p A = h.prob p A := by
  have hTS : Disjoint (↑F : Set κ) (S \ (↑h.inspected : Set κ)) :=
    hdisj.mono_right Set.sdiff_subset
  have hpin :
      pinnedProb p (↑(h.inspected ∪ F) : Set κ) (h.step z F b ω).state A =
        pinnedProb p (↑h.inspected : Set κ) (h.step z F b ω).state A := by
    rw [Finset.coe_union]
    exact pinnedProb_union_eq p (h.step z F b ω).state hA hTS
  have hstate : ∀ x ∈ (↑h.inspected : Set κ),
      ((h.step z F b ω).state x ↔ h.state x) := by
    intro x hx
    rw [FRDom.Transcript.step_state]
    have hxF : x ∉ F := fun hxF => Finset.disjoint_left.1 hfresh hxF (Finset.mem_coe.1 hx)
    simp [hxF]
  have hval :
      pinnedProb p (↑h.inspected : Set κ) (h.step z F b ω).state A =
        pinnedProb p (↑h.inspected : Set κ) h.state A :=
    pinnedProb_congr_val p _ hstate A
  rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq,
    FRDom.Transcript.step_inspected, hpin, hval]

#print axioms KNAll.Site.ProbInv.prob_mono
#print axioms KNAll.Site.ProbInv.prob_step_eq_of_disjoint

end KNAll.Site.ProbInv

end
