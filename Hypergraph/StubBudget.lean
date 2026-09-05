import Hypergraph.ProbInvariant

/-!
# Probability budgets for the corrected directional-stub examination

The corrected macro examination stores probability clauses, rather than deterministic paths to
designated sites.  This file contains the bookkeeping needed to combine those clauses.  All events
are abstract events of a site configuration and all probabilities are `pinnedProb`, so the results
apply at any transcript, including a transcript of zero probability under the unpinned law.

For successive levels, the hypothesis

`P(previous levels bad ∩ this level bad) ≤ (1 - δ₂) P(previous levels bad)`

is the denominator-free form of the corresponding conditional-probability bound.  It also has the
right meaning when the event describing the previous levels has probability zero.
-/

noncomputable section

namespace KNAll.Site.Budget

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {κ V ι : Type*}

/-- The usable event: the incoming experiment succeeds and every required direction succeeds. -/
def usable (incoming : Set (Set κ)) (direction : ι → Set (Set κ)) : Set (Set κ) :=
  incoming ∩ ⋂ i, direction i

/-- The event that the first `K` level tests are all bad. -/
def allBad (bad : ℕ → Set (Set κ)) : ℕ → Set (Set κ)
  | 0 => Set.univ
  | K + 1 => allBad bad K ∩ bad K

/-- The exact arithmetic behind the incoming-plus-four-directions budget. -/
theorem quarter_add_four_sixteenth (ρ : ℝ) :
    ρ / 4 + 4 * (ρ / 16) = ρ / 2 := by
  ring

/-- A stored probability bound survives an examination of fresh coordinates disjoint from those
which determine its event.  This is the reserved-frontier use of
`ProbInv.prob_step_eq_of_disjoint`. -/
theorem failure_bound_step_of_disjoint [DecidableEq κ] [DecidableEq V]
    (h : FRDom.Transcript κ V) (p : κ → unitInterval) (z : V) (F : Finset κ)
    (b : Bool) (ω : Set κ) {A : Set (Set κ)} {S : Set κ} {ε : ℝ}
    (hfresh : Disjoint F h.inspected) (hA : DeterminedBy A S)
    (hdisj : Disjoint (↑F : Set κ) S) (hfail : h.prob p Aᶜ ≤ ε) :
    (h.step z F b ω).prob p Aᶜ ≤ ε := by
  rw [ProbInv.prob_step_eq_of_disjoint h p z F b ω hfresh hA.compl hdisj]
  exact hfail

/-- **Incoming plus at most four directions.**  If the incoming failure costs at most `ρ/4` and
each directional failure costs at most `ρ/16`, then the usable event has pinned probability at
least `1 - ρ/2`.  For positive `ρ`, this threshold is strictly larger than `1 - ρ`.

The finite type `ι` is only an index for whichever directional events an application uses; no
geometry or designated target occurs in the statement. -/
theorem pinnedProb_usable_budget [Fintype ι]
    (p : κ → unitInterval) (R : Set κ) (val : κ → Prop)
    (incoming : Set (Set κ)) (direction : ι → Set (Set κ)) (ρ : ℝ)
    (hρ : 0 < ρ) (hcard : Fintype.card ι ≤ 4)
    (hIncomingMeas : MeasurableSet incoming)
    (hDirectionMeas : ∀ i, MeasurableSet (direction i))
    (hIncoming : pinnedProb p R val incomingᶜ ≤ ρ / 4)
    (hDirection : ∀ i, pinnedProb p R val (direction i)ᶜ ≤ ρ / 16) :
    1 - ρ < 1 - ρ / 2 ∧
      1 - ρ / 2 ≤ pinnedProb p R val (usable incoming direction) := by
  have hUnionDirection :
      pinnedProb p R val (⋃ i, (direction i)ᶜ) ≤
        ∑ i, pinnedProb p R val (direction i)ᶜ := by
    simp only [pinnedProb, Set.preimage_iUnion]
    exact measureReal_iUnion_fintype_le _
  have hDirectionSum :
      (∑ i, pinnedProb p R val (direction i)ᶜ) ≤ 4 * (ρ / 16) := by
    calc
      (∑ i, pinnedProb p R val (direction i)ᶜ)
          ≤ ∑ _i : ι, ρ / 16 := Finset.sum_le_sum fun i _ => hDirection i
      _ = (Fintype.card ι : ℝ) * (ρ / 16) := by simp
      _ ≤ 4 * (ρ / 16) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hUnion :
      pinnedProb p R val (incomingᶜ ∪ ⋃ i, (direction i)ᶜ) ≤
        pinnedProb p R val incomingᶜ + pinnedProb p R val (⋃ i, (direction i)ᶜ) := by
    simp only [pinnedProb, Set.preimage_union]
    exact measureReal_union_le _ _
  have hFailure :
      pinnedProb p R val (usable incoming direction)ᶜ ≤ ρ / 2 := by
    have hcompl :
        (usable incoming direction)ᶜ = incomingᶜ ∪ ⋃ i, (direction i)ᶜ := by
      rw [usable, Set.compl_inter, Set.compl_iInter]
    rw [hcompl]
    calc
      pinnedProb p R val (incomingᶜ ∪ ⋃ i, (direction i)ᶜ)
          ≤ pinnedProb p R val incomingᶜ +
              pinnedProb p R val (⋃ i, (direction i)ᶜ) := hUnion
      _ ≤ ρ / 4 + 4 * (ρ / 16) := add_le_add hIncoming (hUnionDirection.trans hDirectionSum)
      _ = ρ / 2 := quarter_add_four_sixteenth ρ
  have hUsableMeas : MeasurableSet (usable incoming direction) :=
    hIncomingMeas.inter (MeasurableSet.iInter hDirectionMeas)
  have hComplement :
      pinnedProb p R val (usable incoming direction)ᶜ =
        1 - pinnedProb p R val (usable incoming direction) :=
    pinnedProb_compl p R val hUsableMeas
  constructor
  · linarith
  · linarith

/-- **Level exhaustion.**  If, after any bad prefix among the first `K` levels, the next bad event
has conditional probability at most `1 - δ₂` in denominator-free form, then all `K` levels are bad
with pinned probability at most `(1 - δ₂)^K`. -/
theorem pinnedProb_allBad_le_pow
    (p : κ → unitInterval) (R : Set κ) (val : κ → Prop)
    (bad : ℕ → Set (Set κ)) (K : ℕ) (δ₂ : ℝ)
    (hδ₂1 : δ₂ ≤ 1)
    (hcond : ∀ k < K,
      pinnedProb p R val (allBad bad k ∩ bad k) ≤
        (1 - δ₂) * pinnedProb p R val (allBad bad k)) :
    pinnedProb p R val (allBad bad K) ≤ (1 - δ₂) ^ K := by
  induction K with
  | zero =>
      simp [allBad]
  | succ K ih =>
      have hprev : pinnedProb p R val (allBad bad K) ≤ (1 - δ₂) ^ K :=
        ih (fun k hk => hcond k (Nat.lt_succ_of_lt hk))
      calc
        pinnedProb p R val (allBad bad (K + 1))
            = pinnedProb p R val (allBad bad K ∩ bad K) := by rfl
        _ ≤ (1 - δ₂) * pinnedProb p R val (allBad bad K) :=
          hcond K (Nat.lt_succ_self K)
        _ ≤ (1 - δ₂) * (1 - δ₂) ^ K :=
          mul_le_mul_of_nonneg_left hprev (sub_nonneg.2 hδ₂1)
        _ = (1 - δ₂) ^ (K + 1) := by ring

/-- **Choice of the number of levels.**  For `ρ > 0` and `0 < δ₂ ≤ 1`, there is a finite `K` for
which the geometric exhaustion cost is strictly below `ρ/32`. -/
theorem exists_levelCount (ρ δ₂ : ℝ) (hρ : 0 < ρ) (hδ₂0 : 0 < δ₂) (_hδ₂1 : δ₂ ≤ 1) :
    ∃ K : ℕ, (1 - δ₂) ^ K < ρ / 32 := by
  exact exists_pow_lt_of_lt_one (by positivity) (by linarith)

/-- **Level exhaustion plus corridor failure.**  Once `K` is chosen with
`(1 - δ₂)^K ≤ ρ/32`, a corridor failure of probability at most `ρ/32` together with the
conditional bad-level bounds for precisely the first `K` levels costs at most `ρ/16`. -/
theorem pinnedProb_corridor_or_allBad_le
    (p : κ → unitInterval) (R : Set κ) (val : κ → Prop)
    (corridorFailure : Set (Set κ)) (bad : ℕ → Set (Set κ))
    (K : ℕ) (ρ δ₂ : ℝ) (hδ₂1 : δ₂ ≤ 1)
    (hK : (1 - δ₂) ^ K ≤ ρ / 32)
    (hCorridor : pinnedProb p R val corridorFailure ≤ ρ / 32)
    (hcond : ∀ k < K,
      pinnedProb p R val (allBad bad k ∩ bad k) ≤
        (1 - δ₂) * pinnedProb p R val (allBad bad k)) :
    pinnedProb p R val (corridorFailure ∪ allBad bad K) ≤ ρ / 16 := by
  have hAllBad : pinnedProb p R val (allBad bad K) ≤ (1 - δ₂) ^ K :=
    pinnedProb_allBad_le_pow p R val bad K δ₂ hδ₂1
      hcond
  have hUnion :
      pinnedProb p R val (corridorFailure ∪ allBad bad K) ≤
        pinnedProb p R val corridorFailure + pinnedProb p R val (allBad bad K) := by
    simp only [pinnedProb, Set.preimage_union]
    exact measureReal_union_le _ _
  refine hUnion.trans ?_
  calc
    pinnedProb p R val corridorFailure + pinnedProb p R val (allBad bad K)
        ≤ ρ / 32 + (1 - δ₂) ^ K := add_le_add hCorridor hAllBad
    _ ≤ ρ / 32 + ρ / 32 := add_le_add_right hK _
    _ = ρ / 16 := by ring

#print axioms KNAll.Site.Budget.quarter_add_four_sixteenth
#print axioms KNAll.Site.Budget.failure_bound_step_of_disjoint
#print axioms KNAll.Site.Budget.pinnedProb_usable_budget
#print axioms KNAll.Site.Budget.pinnedProb_allBad_le_pow
#print axioms KNAll.Site.Budget.exists_levelCount
#print axioms KNAll.Site.Budget.pinnedProb_corridor_or_allBad_le

end KNAll.Site.Budget

end
