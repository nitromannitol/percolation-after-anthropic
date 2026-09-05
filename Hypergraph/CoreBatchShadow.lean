import Hypergraph.BoundedDamageAdaptiveRegion
import Hypergraph.CoreDamage

/-!
# Shadow facts for the bounded-damage core batch

The stopped physical phase lives in a bounded-damage transcript, while the core geometry is
stated for its ordinary `base` transcript.  This file records the exact bridge.  Reveal-only
rounds preserve the macro verdicts, so the frontier and the finite set of newly created heads are
the same before and after the phase.  In particular a batch may pessimistically close *all* new
heads on failure; this removes any need to encode a touched-head cursor in the transcript and
still costs at most four collateral vertices.
-/

noncomputable section

namespace KNAll.Site.CoreBatchShadow

open Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

abbrev Tr (d : Nat) := BDDom.Transcript (Site d) (Site 2)

/-- Frontier membership depends only on the macro open/closed verdicts, hence is unchanged during
a reveal-only phase. -/
theorem frontier_phase_iff (R : BDAdaptReg.RevealPhase (Site d) (Site 2))
    {base k : Tr d} (hk : R.Phase base k) (y : Site 2) :
    CoreFrontier.Frontier k.base y ↔ CoreFrontier.Frontier base.base y := by
  have hopen := R.openV_eq base k hk
  have hclosed := R.closedV_eq base k hk
  change k.base.openV = base.base.openV at hopen
  change k.base.closedV = base.base.closedV at hclosed
  unfold CoreFrontier.Frontier
  rw [hopen, hclosed]

/-- The undetermined neighbours of any centre are unchanged during a reveal-only phase. -/
theorem pending_phase_eq (R : BDAdaptReg.RevealPhase (Site d) (Site 2))
    {base k : Tr d} (hk : R.Phase base k) (z : Site 2) :
    MacroExp.pending d k.base z = MacroExp.pending d base.base z := by
  classical
  have hopen := R.openV_eq base k hk
  have hclosed := R.closedV_eq base k hk
  change k.base.openV = base.base.openV at hopen
  change k.base.closedV = base.base.closedV at hclosed
  ext y
  rw [MacroExp.mem_pending, MacroExp.mem_pending,
    hopen, hclosed]

/-- The complete set of heads allocated by the batch can be computed before any physical read. -/
theorem newHeads_phase_eq (R : BDAdaptReg.RevealPhase (Site d) (Site 2))
    {base k : Tr d} (hk : R.Phase base k) (z : Site 2) :
    CoreFrontier.newHeads (d := d) k.base z =
      CoreFrontier.newHeads (d := d) base.base z := by
  classical
  ext y
  rw [CoreFrontier.mem_newHeads, CoreFrontier.mem_newHeads,
    pending_phase_eq R hk z, frontier_phase_iff R hk y]

/-- The maximal collateral rule: on a failed trial close every head which opening `z` could have
created.  It is fixed by the pre-reveal transcript. -/
def maximalDamage (base : Tr d) (z : Site 2) : Finset (Site 2) :=
  CoreDamage.damage base.base z

theorem maximalDamage_local (base : Tr d) (z : Site 2) :
    ∀ y ∈ maximalDamage base z, z = y ∨ (zdGraph 2).Adj z y :=
  CoreDamage.touched_local Finset.Subset.rfl

theorem maximalDamage_disjoint_open (base : Tr d) (z : Site 2) :
    Disjoint (maximalDamage base z) base.openV :=
  CoreDamage.damage_disjoint_open base.base z

theorem card_maximalDamage_le_four (base : Tr d) (z : Site 2) :
    (maximalDamage base z).card ≤ 4 :=
  CoreDamage.card_damage_le_four base.base z

theorem card_closed_batch_le_five (base : Tr d) (z : Site 2) :
    (insert z (maximalDamage base z)).card ≤ 5 :=
  CoreDamage.card_insert_touched_le_five Finset.Subset.rfl

/-- The maximal collateral rule preserves bounded-damage soundness after the one final commit.
No hypothesis about the collateral vertices lying in the arena is needed. -/
theorem sound_commit_maximalDamage
    {A : Finset (Site 2)} {o : Site 2}
    (R : BDAdaptReg.RevealPhase (Site d) (Site 2))
    {base k : Tr d} (hk : R.Phase base k)
    (hs : base.Sound (zdGraph 2) A o) {z : Site 2}
    (hzA : z ∈ A) (hzo : z ∉ base.openV) (hzc : z ∉ base.closedV)
    (b : Bool) (omega : SiteConfig (Site d)) :
    (k.step z ∅ (maximalDamage base z) b omega).Sound (zdGraph 2) A o := by
  have hsK : k.Sound (zdGraph 2) A o := by
    unfold BDDom.Transcript.Sound at hs ⊢
    rw [R.openV_eq base k hk, R.closedV_eq base k hk, R.failed_eq base k hk]
    exact hs
  apply BDAdaptReg.sound_step_of_local k hsK hzA
  · rwa [R.openV_eq base k hk]
  · rwa [R.closedV_eq base k hk]
  · exact maximalDamage_local base z
  · rw [R.openV_eq base k hk]
    exact maximalDamage_disjoint_open base z

#print axioms KNAll.Site.CoreBatchShadow.frontier_phase_iff
#print axioms KNAll.Site.CoreBatchShadow.pending_phase_eq
#print axioms KNAll.Site.CoreBatchShadow.newHeads_phase_eq
#print axioms KNAll.Site.CoreBatchShadow.sound_commit_maximalDamage

end KNAll.Site.CoreBatchShadow

end
