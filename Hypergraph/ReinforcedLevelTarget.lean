import Hypergraph.ReinforcedOneLevel
import Hypergraph.ReinforcedLevelGeometry

/-!
# A concrete centered reinforced level

This file instantiates the abstract one-level target theorem with the deterministic centered-box
geometry and exact greedy selector.  In particular, the selected list is read entirely outside the
shell; it is not allowed to depend on any collar bit.
-/

noncomputable section

namespace KNAll.Site.ReinforcedLevel

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

/-- A deterministic centered shell with sufficiently many contacts reaches the target.  The only
probability inputs left are the rich-shell estimate, the canonical seed inequality, and the
finite hit-event defects. -/
theorem target_gt_at_level
    (w : Site d → unitInterval) (m k N : Nat) (hm : 1 ≤ m)
    (z : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, ReinforcedShell.thickness m ≤ rho a)
    {Dom D : Finset (Site d)} (hOD : Corridor.rbox z rho ⊆ D) (hDDom : D ⊆ Dom)
    (o : Site d) (hoDom : o ∈ Dom) (hoD : o ∉ D) (hwo : w o = 1)
    (T : Set (Site d)) (qI : unitInterval)
    (hwO : ∀ y ∈ Corridor.rbox z rho, w y = qI)
    (hpack : k * (CorrMove.cube (0 : Site d) (8 * (m : Int))).card ≤ N)
    (H : Site d → Set (SiteConfig (Site d)))
    {ε δ δc η : Real}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ = ε ^ 2 / 64) (hδc : δc = ε / 4)
    (hη0 : 0 ≤ η)
    (hbudget : (k : Real) *
      ((qI : Real) ^ ReinforcedShell.seedSize d m * η / δc) ≤ δ)
    (hseed : (1 - (qI : Real) ^ ReinforcedShell.seedSize d m) ^ k ≤ δ)
    (hHup : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox z rho),
      IsUpperSet (H x))
    (hHm : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox z rho),
      MeasurableSet (H x))
    (hforce : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox z rho),
      ReinforcedTarget.openWindow (J m z rho x) ∩ H x ⊆
        TargetExt.toTarget (zdGraph d) D T (relay m z rho x))
    (hhit : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox z rho),
      (prodBernoulli w).real (H x)ᶜ ≤ η)
    (hrich : 1 - 2 * δ <
      (prodBernoulli w).real
        (TargetExt.poor (zdGraph d) Dom (Corridor.rbox z rho) o N)ᶜ) :
    1 - ε < (prodBernoulli w).real
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o T) := by
  let O : Finset (Site d) := Corridor.rbox z rho
  let Int : Finset (Site d) := ReinforcedShell.innerBox m z rho
  let sel : Finset (Site d) → Finset (Site d) := selected m k z rho
  let win : Site d → Finset (Site d) := J m z rho
  let v : Site d → Site d := relay m z rho
  have hF := facts m k hm z rho hrho Dom
  have hselLower : ∀ K ⊆ TargetExt.outerBoundary (zdGraph d) Dom O,
      N ≤ K.card → k ≤ (sel K).card := by
    intro K hK hNK
    have heq := card_selected_eq_of_boundary m k N z rho Dom K hK hpack hNK
    simpa only [sel] using heq.ge
  have hseed0 := TargetExt.real_poorCompl_diff_seeds_le
    (zdGraph d) w Dom O o N k (ReinforcedShell.seedSize d m)
      qI.2.1 qI.2.2 sel win
      (by simpa only [sel] using hF.sel_subset) hselLower
      (by simpa only [sel, win] using hF.sel_disjoint)
      (by
        intro x hx
        exact (hF.window_subset x hx).trans hF.collar_subset)
      (by
        intro x hx
        rw [show (win x).card = ReinforcedShell.seedSize d m by
          simpa only [win] using hF.window_card x hx])
      (by
        intro x hx y hy
        have hyO : y ∈ O := hF.collar_subset (hF.window_subset x hx hy)
        rw [hwO y hyO])
  have hnoopen : (prodBernoulli w).real
      ((TargetExt.poor (zdGraph d) Dom O o N)ᶜ \
        ReinforcedTarget.selectedOpen (zdGraph d) Dom O o sel win) ≤ δ := by
    have hseed0' : (prodBernoulli w).real
        ((TargetExt.poor (zdGraph d) Dom O o N)ᶜ \
          ReinforcedTarget.selectedOpen (zdGraph d) Dom O o sel win) ≤
        (1 - (qI : Real) ^ ReinforcedShell.seedSize d m) ^ k := by
      simpa only [ReinforcedTarget.selectedOpen, TargetExt.selectedAt,
        ReinforcedTarget.openWindow, TargetExt.seedOpen] using hseed0
    exact hseed0'.trans hseed
  have hopen : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom O,
      (prodBernoulli w).real (ReinforcedTarget.openWindow (win x)) ≤
        (qI : Real) ^ ReinforcedShell.seedSize d m := by
    intro x hx
    have hcard : (win x).card = ReinforcedShell.seedSize d m := by
      simpa only [win] using hF.window_card x hx
    have hwinO : win x ⊆ O := (hF.window_subset x hx).trans hF.collar_subset
    change (prodBernoulli w).real
      {omega | (↑(win x) : Set (Site d)) ⊆ omega} ≤ _
    rw [prodBernoulli_real_subset]
    calc
      ∏ y ∈ win x, (w y : Real) = ∏ _y ∈ win x, (qI : Real) := by
        apply Finset.prod_congr rfl
        intro y hy
        rw [hwO y (hwinO hy)]
      _ ≤ (qI : Real) ^ ReinforcedShell.seedSize d m := by
        rw [Finset.prod_const, hcard]
  apply ReinforcedTarget.oneLevel_target_gt_of_hits
    (zdGraph d) w (innerBox_subset_shell m z rho) hOD hDDom
    o hoDom hoD hwo T N k sel win v H hε0 hε1 hδ hδc
      (pow_nonneg (unitInterval.nonneg qI) _)
      hη0 hbudget
      (by simpa only [sel] using hF.sel_subset)
      (by simpa only [sel] using hF.sel_card_le)
      (by simpa only [O, Int, win, ReinforcedShell.collar] using hF.window_subset)
      (by simpa only [O, Int, v, ReinforcedShell.collar] using hF.relay_mem)
      (by simpa only [O, win, v] using hF.bridge)
      (by simpa only [O] using hHup)
      (by simpa only [O] using hHm)
      (by simpa only [O, win, v] using hforce)
      hopen
      (by simpa only [O] using hhit)
      (by simpa only [O] using hrich)
      hnoopen

#print axioms KNAll.Site.ReinforcedLevel.target_gt_at_level

end KNAll.Site.ReinforcedLevel

end
