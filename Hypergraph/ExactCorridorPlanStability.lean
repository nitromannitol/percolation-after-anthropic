import Hypergraph.ExactCorridorPlan
import Hypergraph.ExactTargetPlanStability

/-!
# Left stability of exact corridor plans

An exact corridor contains the finite family of `d + 1` exact target plans.  Taking the
minimum of their individual left-neighbourhood radii gives one parameter at which every stage
remains valid simultaneously.
-/

noncomputable section

namespace KNAll.Site.ExactCorridorPlan

open KNAll.Site Percolation.Literature Percolation.Literature.LatticeModels

variable {d : Nat}

namespace Plan

/-- Simultaneous left-neighbourhood stability of all `d + 1` exact target nodes in a corridor. -/
theorem exists_valid_left_nhds (K : ExactCorridorPlan.Plan d) {p : unitInterval}
    (hvalid : K.ValidAt p) :
    ∃ ε > 0, ∀ q : unitInterval, 0 < (q : Real) →
      (q : Real) ≤ (p : Real) → |(q : Real) - (p : Real)| < ε → K.ValidAt q := by
  classical
  choose radius hradius_pos hstay using
    fun i : Fin (d + 1) => (K.stage i).exists_valid_left_nhds (hvalid i)
  have hne : (Finset.univ : Finset (Fin (d + 1))).Nonempty :=
    ⟨0, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne radius,
    (Finset.lt_inf'_iff hne).2 (fun i _ => hradius_pos i), ?_⟩
  intro q hq hqp hdist i
  apply hstay i q hq hqp
  exact hdist.trans_le (Finset.inf'_le radius (Finset.mem_univ i))

/-- A corridor plan valid at a positive parameter is simultaneously valid at some strictly
smaller positive parameter. -/
theorem exists_smaller_valid (K : ExactCorridorPlan.Plan d) {p : unitInterval}
    (hp : 0 < (p : Real)) (hvalid : K.ValidAt p) :
    ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p : Real) ∧ K.ValidAt q := by
  obtain ⟨ε, hε, hleft⟩ := K.exists_valid_left_nhds hvalid
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

/-- Assemble the raw corridor record from a single indexed family of its `d + 1` exact nodes.
The first `d` family members become quarter-face nodes and the last member becomes the aspect-88
node.  No validity or geometry is hidden in this constructor. -/
def ofStageFamily
    (scale : Nat) (startCentre endCentre : Site d)
    (boxes : Fin (d + 1) → Finset (Site d))
    (stages : Fin (d + 1) → ExactTargetPlan.Plan d)
    (longAxis : Fin d) (longSign : Int)
    (past : Fin (d + 1) → Finset (Site d))
    (eta : Fin (d + 1) → Real) (alpha : Real) : ExactCorridorPlan.Plan d where
  scale := scale
  startCentre := startCentre
  endCentre := endCentre
  boxes := boxes
  quarter := fun i => stages i.castSucc
  aspect88 := stages (Fin.last d)
  longAxis := longAxis
  longSign := longSign
  past := past
  eta := eta
  alpha := alpha

@[simp] theorem stage_ofStageFamily
    (scale : Nat) (startCentre endCentre : Site d)
    (boxes : Fin (d + 1) → Finset (Site d))
    (stages : Fin (d + 1) → ExactTargetPlan.Plan d)
    (longAxis : Fin d) (longSign : Int)
    (past : Fin (d + 1) → Finset (Site d))
    (eta : Fin (d + 1) → Real) (alpha : Real) (i : Fin (d + 1)) :
    (ofStageFamily scale startCentre endCentre boxes stages longAxis longSign past eta alpha).stage i =
      stages i := by
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [ofStageFamily]

/-- Package supplied node-wise consistency and concrete face/long-box geometry into corridor
well-formedness.  This is deliberately only a record constructor: finite extraction and
probability estimates remain separate. -/
theorem wellFormed_ofStageFamily
    (scale : Nat) (startCentre endCentre : Site d)
    (boxes : Fin (d + 1) → Finset (Site d))
    (stages : Fin (d + 1) → ExactTargetPlan.Plan d)
    (longAxis : Fin d) (longSign : Int)
    (past : Fin (d + 1) → Finset (Site d))
    (eta : Fin (d + 1) → Real) (alpha : Real)
    (hscale : 0 < scale)
    (hstage : ∀ i, (stages i).WellFormed)
    (hsource : ∀ i, (stages i).source = boxes i)
    (hinitial : boxes 0 = CorrMove.cube startCentre (3 * (scale : Int)))
    (hquarterTarget : ∀ i : Fin d, (stages i.castSucc).target = boxes i.succ)
    (hquarterGeometry : ∀ i : Fin d,
      CorrMove.FaceTarget ((stages i.castSucc).radius : Int) (stages i.castSucc).active
        (stages i.castSucc).source (stages i.castSucc).target)
    (haspectTarget :
      (stages (Fin.last d)).target = CorrMove.cube endCentre (2 * (scale : Int)))
    (hlongSign : longSign = 1 ∨ longSign = -1)
    (haspectGeometry :
      CorrMove.LongTarget (((stages (Fin.last d)).radius : Nat) : Int) longAxis longSign
        (stages (Fin.last d)).active (stages (Fin.last d)).source
        (stages (Fin.last d)).target)
    (hdelta : ∀ i, (stages i).delta = eta i)
    (hquarterEpsilon : ∀ i : Fin d, (stages i.castSucc).epsilon = eta i.succ)
    (haspectEpsilon : (stages (Fin.last d)).epsilon = alpha)
    (hdomain : ∀ i : Fin d,
      past i.castSucc ∪ (stages i.castSucc).active ⊆
        past i.succ ∪ (stages i.succ).active) :
    WellFormed
      (ofStageFamily scale startCentre endCentre boxes stages longAxis longSign past eta alpha) := by
  let K := ofStageFamily scale startCentre endCentre boxes stages longAxis longSign past eta alpha
  have hKstage : ∀ i, K.stage i = stages i := by
    intro i
    exact stage_ofStageFamily scale startCentre endCentre boxes stages longAxis longSign past eta
      alpha i
  refine ⟨hscale, ?_, ?_, ?_, ?_, ?_, ?_, hlongSign, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hKstage i]
    exact hstage i
  · intro i
    rw [hKstage i]
    exact hsource i
  · simpa [K, ofStageFamily, initialCore] using hinitial
  · intro i
    rw [hKstage i.castSucc]
    exact hquarterTarget i
  · intro i
    simpa [K, ofStageFamily] using hquarterGeometry i
  · simpa [K, ofStageFamily, innerTarget] using haspectTarget
  · simpa [K, ofStageFamily] using haspectGeometry
  · intro i
    rw [hKstage i]
    exact hdelta i
  · intro i
    rw [hKstage i.castSucc]
    exact hquarterEpsilon i
  · simpa [K, ofStageFamily] using haspectEpsilon
  · intro i
    change K.domain i.castSucc ⊆ K.domain i.succ
    rw [domain, domain, hKstage i.castSucc, hKstage i.succ]
    exact hdomain i

end Plan

end KNAll.Site.ExactCorridorPlan

end

#print axioms KNAll.Site.ExactCorridorPlan.Plan.exists_valid_left_nhds
#print axioms KNAll.Site.ExactCorridorPlan.Plan.exists_smaller_valid
#print axioms KNAll.Site.ExactCorridorPlan.Plan.wellFormed_ofStageFamily
