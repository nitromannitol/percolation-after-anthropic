import Hypergraph.FreshLeafTransport
import Hypergraph.IntBoxCenteredEnvelope
import Hypergraph.ReinforcedHitBridge
import Hypergraph.ReinforcedTargetScan

/-!
# Product-law soundness of an exact target plan

This module interprets the finite T1--T6 data of an `ExactTargetPlan.Plan` in an arbitrary
product environment whose weights agree with the plan parameter on the active box.  All shell,
window, and leaf choices are the concrete deterministic choices stored by the plan.
-/

noncomputable section

namespace KNAll.Site.ExactTargetPlan.Plan

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

private abbrev envCentre (C : ExactTargetPlan.Plan d) : Site d :=
  IntBoxCenteredEnvelope.centre C.sourceBox

private abbrev envRho (C : ExactTargetPlan.Plan d) : Fin d → Int :=
  IntBoxCenteredEnvelope.rho C.sourceBox

private abbrev levelRho (C : ExactTargetPlan.Plan d) (i : Nat) : Fin d → Int :=
  ReinforcedLevel.radius C.envRho C.m C.L i

private abbrev levelRelay (C : ExactTargetPlan.Plan d) (i : Nat)
    (x : Site d) : Site d :=
  ReinforcedLevel.relay C.m C.envCentre (C.levelRho i) x

/-- The exact T4 hit chosen for the reinforced relay at level `i`.  Outside the genuine scan
domain the definition is harmlessly empty; `relay_mem_sourcePlus` selects the first branch at
every contact actually consumed by the scan. -/
def scanHit (C : ExactTargetPlan.Plan d) (i : Nat) (x : Site d) :
    Set (SiteConfig (Site d)) :=
  if hv : C.levelRelay i x ∈ C.sourcePlus then
    ExactTargetPlan.hitEvent (C.selectedRegion ⟨C.levelRelay i x, hv⟩)
      (ReinforcedShell.sourceCube C.m C.envCentre (C.levelRho i) x)
      (C.selectedFace ⟨C.levelRelay i x, hv⟩)
  else ∅

/-- The radius-`n` integer cube at the origin is literally the corridor cube of radius `n`. -/
private theorem cube_zero_eq_siteBox (n : Nat) :
    CorrMove.cube (0 : Site d) (n : Int) = siteBox d n := by
  ext x
  rw [CorrMove.mem_cube, mem_siteBox]
  constructor
  · intro h a
    have ha := h a
    rw [abs_le] at ha
    simpa using ha
  · intro h a
    have ha := h a
    rw [abs_le]
    simpa using ha

/-- The numerical cancellation used in the target scan's selected-defect budget. -/
private theorem budget_of_le_inv {a δ δc η : Real}
    (hδ : 0 < δ) (hδc : 0 < δc) (ha : a ≤ δ⁻¹)
    (hη : η = δ ^ 2 * δc) : a * (η / δc) ≤ δ := by
  have hratio : η / δc = δ ^ 2 := by
    rw [hη]
    field_simp
  rw [hratio]
  calc
    a * δ ^ 2 ≤ δ⁻¹ * δ ^ 2 :=
      mul_le_mul_of_nonneg_right ha (sq_nonneg δ)
    _ = δ := by
      field_simp

/-- Every relay used by a genuine shell contact lies in the plan's finite T4 indexing domain. -/
private theorem relay_mem_sourcePlus (C : ExactTargetPlan.Plan d) (hC : C.WellFormed)
    {Dom : Finset (Site d)} {i : Nat} (hi : i < C.L) {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (ReinforcedLevel.shell C.envCentre C.envRho C.m C.L i)) :
    C.levelRelay i x ∈ C.sourcePlus := by
  have hsourceOrd : C.sourceBox.Ordered := hC.1.2.2.1
  have hR : 2 * C.m + C.L + 2 ≤ C.radius := hC.2.2.1.1
  have hrho : ∀ a, ReinforcedShell.thickness C.m ≤ C.levelRho i a := by
    intro a
    have hbase := IntBoxCenteredEnvelope.rho_nonneg C.sourceBox a
    have hoff := ReinforcedLevel.thickness_le_offset C.m C.L i hi
    change ReinforcedShell.thickness C.m ≤ C.envRho a + ReinforcedLevel.offset C.m C.L i
    exact hoff.trans (by linarith)
  have hcollar : C.levelRelay i x ∈
      ReinforcedShell.collar C.m C.envCentre (C.levelRho i) :=
    ReinforcedLevel.relay_mem_collar_of_boundary C.m C.envCentre
      (C.levelRho i) hrho Dom hx
  have hshell : C.levelRelay i x ∈
      ReinforcedLevel.shell C.envCentre C.envRho C.m C.L i :=
    ReinforcedLevel.collar_subset_shell C.m C.envCentre (C.levelRho i) hcollar
  have hinflate := IntBoxCenteredEnvelope.shell_subset_inflate hsourceOrd
    C.m C.L C.radius i hi hR hshell
  exact hinflate

/-- **Exact target-plan product soundness.**  Only the active box is required to retain the
homogeneous plan parameter; the exterior product weights are arbitrary, apart from the named
forced-open source. -/
theorem soundProduct (C : ExactTargetPlan.Plan d) (hC : C.WellFormed)
    {q : unitInterval} (hvalid : C.ValidAt q)
    (w : Site d → unitInterval) {Dom : Finset (Site d)}
    (hactiveDom : C.active ⊆ Dom)
    (hwactive : ∀ x ∈ C.active, w x = q)
    (o : Site d) (ho : o ∈ Dom \ C.active) (hwo : w o = 1)
    (hsrc : 1 - C.delta <
      (prodBernoulli w).real (connWithinSet (zdGraph d)
        (↑Dom : Set (Site d)) o (↑C.source : Set (Site d)))) :
    1 - C.epsilon <
      (prodBernoulli w).real (connWithinSet (zdGraph d)
        (↑Dom : Set (Site d)) o (↑C.target : Set (Site d))) := by
  have h1 := hC.1
  have h2 := hC.2.1
  have h3 := hC.2.2.1
  have h4 := hC.2.2.2.1
  have h5 := hC.2.2.2.2.1
  have h6 := hC.2.2.2.2.2
  have hm : 1 ≤ C.m := h2.2.2.1
  have hL : 0 < C.L := h2.2.2.2.2.2
  have hq1 : (q : Real) < 1 := lt_of_le_of_lt hvalid.2.1 h1.2.1
  have hδpos : 0 < C.delta := by
    unfold ExactTargetPlan.Plan.delta
    exact div_pos (sq_pos_of_pos h2.1) (by norm_num)
  have hδcpos : 0 < C.deltaC := by
    unfold ExactTargetPlan.Plan.deltaC
    exact div_pos h2.1 (by norm_num)
  have hη0 : 0 ≤ C.eta := by
    unfold ExactTargetPlan.Plan.eta
    positivity
  have houter : ReinforcedLevel.shell C.envCentre C.envRho C.m C.L 0 ⊆ C.active := by
    have hs := IntBoxCenteredEnvelope.shell_subset_inflate h1.2.2.1
      C.m C.L C.radius 0 hL h3.1
    exact hs.trans h1.2.2.2.2.2.1
  have hB : ∀ i < C.L, (↑C.source : Set (Site d)) ⊆
      ↑(ReinforcedLevel.shell C.envCentre C.envRho C.m C.L i) := by
    intro i hi x hx
    exact Finset.mem_coe.2
      (IntBoxCenteredEnvelope.sites_subset_shell h1.2.2.1 C.m C.L i hi
        (Finset.mem_coe.1 hx))
  have hwShell : ∀ i < C.L, ∀ y ∈
      ReinforcedLevel.shell C.envCentre C.envRho C.m C.L i, w y = q := by
    intro i hi y hy
    exact hwactive y (ReinforcedLevel.shell_subset_active C.envCentre C.envRho
      C.m C.L i houter hy)
  have hpack : C.k *
      (CorrMove.cube (0 : Site d) (8 * (C.m : Int))).card ≤ C.N := by
    rw [show 8 * (C.m : Int) = ((8 * C.m : Nat) : Int) by norm_num,
      cube_zero_eq_siteBox]
    exact h3.2.1
  have hbarrierProb : C.barrierLower <
      (1 - (q : Real)) ^ ((2 * d) * C.N) := by
    have hv := hvalid.barrierLeaf_holds
    unfold ProbabilityBound.HoldsAt at hv
    rw [h6.2.2.2.1, FreshLeafTransport.plan_barrierLeaf_prob_eq q hC] at hv
    simpa only [Nat.mul_assoc] using hv
  have hcoefpos : 0 < (C.L : Real) * C.delta :=
    mul_pos (by positivity) hδpos
  have hbarrier : 1 ≤ (C.L : Real) * C.delta *
      (1 - (q : Real)) ^ ((2 * d) * C.N) := by
    have hmul := mul_lt_mul_of_pos_left hbarrierProb hcoefpos
    exact le_of_lt (lt_trans h6.2.2.2.2.2.2 hmul)
  have hseedSize : ReinforcedShell.seedSize d C.m = C.seedCard := rfl
  have hseed : (1 - (q : Real) ^ ReinforcedShell.seedSize d C.m) ^ C.k ≤ C.delta := by
    have hv := hvalid.seedLeaf_holds
    unfold ProbabilityBound.HoldsAt at hv
    rw [h5.2.2.2.2, FreshLeafTransport.plan_seedLeaf_prob_eq q hC] at hv
    rw [hseedSize]
    linarith
  have hpow : (q : Real) ^ ReinforcedShell.seedSize d C.m ≤
      (C.p0 : Real) ^ C.seedCard := by
    rw [hseedSize]
    exact pow_le_pow_left₀ q.2.1 hvalid.2.1 C.seedCard
  have hkpow : (C.k : Real) *
      (q : Real) ^ ReinforcedShell.seedSize d C.m ≤ C.delta⁻¹ := by
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans h3.2.2
  have hbudget : (C.k : Real) *
      ((q : Real) ^ ReinforcedShell.seedSize d C.m * C.eta / C.deltaC) ≤ C.delta := by
    calc
      (C.k : Real) *
          ((q : Real) ^ ReinforcedShell.seedSize d C.m * C.eta / C.deltaC) =
          ((C.k : Real) * (q : Real) ^ ReinforcedShell.seedSize d C.m) *
            (C.eta / C.deltaC) := by ring
      _ ≤ C.delta := budget_of_le_inv hδpos hδcpos hkpow rfl
  apply ReinforcedLevel.target_gt_from_scan w C.m C.k C.N C.L hm hL
    C.envCentre C.envRho (IntBoxCenteredEnvelope.rho_nonneg C.sourceBox)
    houter hactiveDom o (Finset.mem_sdiff.1 ho).1 (Finset.mem_sdiff.1 ho).2 hwo
    (↑C.source : Set (Site d))
    (↑C.target : Set (Site d)) hB q hq1 hwShell C.scanHit
    h2.1 h2.2.1 rfl rfl hη0 hbarrier hpack hbudget hseed
  · intro i hi x hx
    have hrelay := relay_mem_sourcePlus C hC hi hx
    simp only [scanHit, dif_pos hrelay]
    exact ReinforcedHit.isUpperSet_hitEvent _ _ _
  · intro i hi x hx
    have hrelay := relay_mem_sourcePlus C hC hi hx
    simp only [scanHit, dif_pos hrelay]
    exact ReinforcedHit.measurableSet_hitEvent _ _ _
  · intro i hi x hx
    have hrelay := relay_mem_sourcePlus C hC hi hx
    let v : C.sourcePlus := ⟨C.levelRelay i x, hrelay⟩
    rcases h4 v with ⟨_, _, hregion, hface, _, _, _, _⟩
    have hrho : ∀ a, ReinforcedShell.thickness C.m ≤ C.levelRho i a := by
      intro a
      have hbase := IntBoxCenteredEnvelope.rho_nonneg C.sourceBox a
      have hoff := ReinforcedLevel.thickness_le_offset C.m C.L i hi
      change ReinforcedShell.thickness C.m ≤ C.envRho a + ReinforcedLevel.offset C.m C.L i
      exact hoff.trans (by linarith)
    have hwin : ReinforcedShell.window C.m C.envCentre (C.levelRho i) x ⊆ C.active :=
      (ReinforcedLevel.window_subset_collar_of_boundary C.m C.envCentre
          (C.levelRho i) hrho Dom hx).trans
        (ReinforcedLevel.collar_subset_active C.envCentre C.envRho C.m C.L i houter)
    simp only [scanHit, dif_pos hrelay]
    apply ReinforcedHit.openWindow_inter_hitEvent_subset_toTarget C.m C.envCentre
      (C.levelRho i) (ReinforcedLevel.isContact_of_mem_outerBoundary_rbox Dom
        C.envCentre (C.levelRho i) hx)
      (C.selectedRegion v) (C.selectedFace v) C.active (↑C.target : Set (Site d))
      hwin hregion
    exact fun y hy => Finset.mem_coe.2 (hface (Finset.mem_coe.1 hy))
  · intro i hi x hx
    have hrelay := relay_mem_sourcePlus C hC hi hx
    let v : C.sourcePlus := ⟨C.levelRelay i x, hrelay⟩
    rcases h4 v with ⟨_, _, hregion, _, _, hsupp, hevent, hlower⟩
    have hv := hvalid.hitLeaf_holds v
    unfold ProbabilityBound.HoldsAt at hv
    have hsource : ReinforcedShell.sourceCube C.m C.envCentre (C.levelRho i) x =
        siteBoxAt v.1 C.m := by
      exact ReinforcedHit.sourceCube_eq_siteBoxAt C.m C.envCentre (C.levelRho i) x
    have hhitq : 1 - C.eta <
        (prodBernoulli (fun _ : Site d => q)).real
          (ExactTargetPlan.hitEvent (C.selectedRegion v)
            (ReinforcedShell.sourceCube C.m C.envCentre (C.levelRho i) x)
            (C.selectedFace v)) := by
      rw [hlower, CylinderExperiment.prob, hevent] at hv
      change 1 - C.eta <
        (prodBernoulli (fun _ : Site d => q)).real
          (ExactTargetPlan.hitEvent (C.selectedRegion v) (siteBoxAt v.1 C.m)
            (C.selectedFace v)) at hv
      simpa only [hsource] using hv
    have hmeas := ReinforcedHit.measurableSet_hitEvent (C.selectedRegion v)
      (ReinforcedShell.sourceCube C.m C.envCentre (C.levelRho i) x)
      (C.selectedFace v)
    have hdet : DeterminedBy
        (ExactTargetPlan.hitEvent (C.selectedRegion v)
          (ReinforcedShell.sourceCube C.m C.envCentre (C.levelRho i) x)
          (C.selectedFace v)) (↑(C.selectedRegion v) : Set (Site d)) := by
      have hd := (C.leaf (C.hitLeaf v)).experiment.determined
      rw [hsupp, hevent] at hd
      simpa only [hsource] using hd
    have hcompq :
        (prodBernoulli (fun _ : Site d => q)).real
          (ExactTargetPlan.hitEvent (C.selectedRegion v)
            (ReinforcedShell.sourceCube C.m C.envCentre (C.levelRho i) x)
            (C.selectedFace v))ᶜ ≤ C.eta := by
      have hc :
          (prodBernoulli (fun _ : Site d => q)).real
            (ExactTargetPlan.hitEvent (C.selectedRegion v)
              (ReinforcedShell.sourceCube C.m C.envCentre (C.levelRho i) x)
              (C.selectedFace v))ᶜ =
            1 - (prodBernoulli (fun _ : Site d => q)).real
              (ExactTargetPlan.hitEvent (C.selectedRegion v)
                (ReinforcedShell.sourceCube C.m C.envCentre (C.levelRho i) x)
                (C.selectedFace v)) := by
        rw [measureReal_compl hmeas, probReal_univ]
      linarith
    have htransfer := prodBernoulli_real_eq_of_determinedBy
      (fun _ : Site d => q) w
      (fun y hy => (hwactive y (hregion (Finset.mem_coe.1 hy))).symm)
      hdet.compl hmeas.compl
    simp only [scanHit, dif_pos hrelay]
    rw [← htransfer]
    exact hcompq
  · exact hsrc

#print axioms KNAll.Site.ExactTargetPlan.Plan.soundProduct

end KNAll.Site.ExactTargetPlan.Plan

end
