import Hypergraph.ExactTargetPlan

/-!
# Left stability of exact target plans

An exact target plan contains only finitely many cylinder estimates.  If all of them hold
strictly at `p`, their Lipschitz dependence on the homogeneous parameter gives a common positive
radius on which they continue to hold.  Restricting to positive parameters on the left of `p`
also preserves the two non-leaf clauses of `ExactTargetPlan.Plan.ValidAt`.
-/

noncomputable section

namespace KNAll.Site.ExactTargetPlan

open KNAll.Site Percolation.Literature Percolation.Literature.LatticeModels

variable {d : Nat}

namespace Plan

/-- An exact target plan valid at `p` stays valid at every sufficiently close positive parameter
on the left of `p`.  The radius is the minimum of the individual leaf margins divided by one more
than their support cardinalities. -/
theorem exists_valid_left_nhds (C : ExactTargetPlan.Plan d) {p : unitInterval}
    (hvalid : C.ValidAt p) :
    ∃ ε > 0, ∀ q : unitInterval, 0 < (q : Real) →
      (q : Real) ≤ (p : Real) → |(q : Real) - (p : Real)| < ε → C.ValidAt q := by
  classical
  have hleaf : ∀ i, (C.leaf i).lower < (C.leaf i).experiment.prob p := hvalid.2.2
  rcases eq_or_ne C.numLeaves 0 with hzero | hpos
  · refine ⟨1, one_pos, fun q hq hqp _ => ⟨hq, hqp.trans hvalid.2.1, ?_⟩⟩
    intro i
    exact absurd i.isLt (by omega)
  · have hne : (Finset.univ : Finset (Fin C.numLeaves)).Nonempty :=
      ⟨⟨0, Nat.pos_of_ne_zero hpos⟩, Finset.mem_univ _⟩
    let radius : Fin C.numLeaves → Real := fun i =>
      ((C.leaf i).experiment.prob p - (C.leaf i).lower) /
        (((C.leaf i).experiment.support.card : Real) + 1)
    have hradius_pos : ∀ i, 0 < radius i := by
      intro i
      exact div_pos (sub_pos.2 (hleaf i)) (by positivity)
    refine ⟨Finset.univ.inf' hne radius,
      (Finset.lt_inf'_iff hne).2 (fun i _ => hradius_pos i), ?_⟩
    intro q hq hqp hdist
    refine ⟨hq, hqp.trans hvalid.2.1, ?_⟩
    intro i
    have hinf : Finset.univ.inf' hne radius ≤ radius i :=
      Finset.inf'_le radius (Finset.mem_univ i)
    have hcard : (0 : Real) < ((C.leaf i).experiment.support.card : Real) + 1 := by
      positivity
    have hlip := (C.leaf i).experiment.abs_prob_sub_le p q
    have hloss :
        (C.leaf i).experiment.prob p - (C.leaf i).experiment.prob q <
          radius i * (((C.leaf i).experiment.support.card : Real) + 1) := by
      calc
        (C.leaf i).experiment.prob p - (C.leaf i).experiment.prob q ≤
            |(C.leaf i).experiment.prob p - (C.leaf i).experiment.prob q| :=
          le_abs_self _
        _ ≤ ((C.leaf i).experiment.support.card : Real) *
            |(p : Real) - (q : Real)| := hlip
        _ ≤ (((C.leaf i).experiment.support.card : Real) + 1) *
            |(q : Real) - (p : Real)| := by
          rw [abs_sub_comm]
          exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (((C.leaf i).experiment.support.card : Real) + 1) *
            Finset.univ.inf' hne radius := mul_lt_mul_of_pos_left hdist hcard
        _ ≤ (((C.leaf i).experiment.support.card : Real) + 1) * radius i :=
          mul_le_mul_of_nonneg_left hinf hcard.le
        _ = radius i * (((C.leaf i).experiment.support.card : Real) + 1) :=
          mul_comm _ _
    have hradius :
        radius i * (((C.leaf i).experiment.support.card : Real) + 1) =
          (C.leaf i).experiment.prob p - (C.leaf i).lower := by
      dsimp [radius]
      field_simp
    rw [hradius] at hloss
    unfold ProbabilityBound.HoldsAt
    linarith

/-- A valid exact target plan at a positive parameter is valid at some strictly smaller positive
parameter. -/
theorem exists_smaller_valid (C : ExactTargetPlan.Plan d) {p : unitInterval}
    (hp : 0 < (p : Real)) (hvalid : C.ValidAt p) :
    ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p : Real) ∧ C.ValidAt q := by
  obtain ⟨ε, hε, hleft⟩ := C.exists_valid_left_nhds hvalid
  let t : Real := min (ε / 2) ((p : Real) / 2)
  have ht : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htp : t ≤ (p : Real) / 2 := min_le_right _ _
  let q : unitInterval :=
    ⟨(p : Real) - t, Set.mem_Icc.2 ⟨by linarith, by linarith [p.2.2]⟩⟩
  refine ⟨q, ?_, ?_, ?_⟩
  · change 0 < (p : Real) - t
    linarith
  · change (p : Real) - t < (p : Real)
    linarith
  · apply hleft q
    · change 0 < (p : Real) - t
      linarith
    · change (p : Real) - t ≤ (p : Real)
      linarith
    · change |(p : Real) - t - (p : Real)| < ε
      rw [show (p : Real) - t - (p : Real) = -t by ring, abs_neg, abs_of_pos ht]
      exact htε

end Plan

end KNAll.Site.ExactTargetPlan

end

#print axioms KNAll.Site.ExactTargetPlan.Plan.exists_valid_left_nhds
#print axioms KNAll.Site.ExactTargetPlan.Plan.exists_smaller_valid
