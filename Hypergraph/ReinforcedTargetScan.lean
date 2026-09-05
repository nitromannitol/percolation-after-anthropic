import Hypergraph.ReinforcedLevelTarget

/-!
# From the finite shell scan to a target

The outer-to-inner scan is used only to choose one deterministic rich level.  The proof then
restarts in the original product space and invokes the concrete one-level theorem at that index.
-/

noncomputable section

namespace KNAll.Site.ReinforcedLevel

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

theorem card_filter_adj_le (S : Finset (Site d)) (x : Site d) :
    (S.filter ((zdGraph d).Adj x)).card ≤ 2 * d := by
  classical
  have hsub : S.filter ((zdGraph d).Adj x) ⊆
      (Finset.univ : Finset (Fin d × Bool)).image
        fun p => if p.2 then x + Pi.single p.1 1 else x - Pi.single p.1 1 := by
    intro y hy
    have hadj : (zdGraph d).Adj x y := (Finset.mem_filter.1 hy).2
    obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff x y).1 hadj
    · exact Finset.mem_image.2 ⟨(i, true), Finset.mem_univ _, by simp [hi]⟩
    · refine Finset.mem_image.2 ⟨(i, false), Finset.mem_univ _, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      rw [hi]
      exact add_sub_cancel_right y (Pi.single i 1)
  calc
    (S.filter ((zdGraph d).Adj x)).card ≤
        ((Finset.univ : Finset (Fin d × Bool)).image
          fun p => if p.2 then x + Pi.single p.1 1 else x - Pi.single p.1 1).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ, mul_comm]

/-- Exact finite shell-scan assembly.  Every probability hypothesis refers to the single current
parameter; no estimate is transported from the extraction parameter. -/
theorem target_gt_from_scan
    (w : Site d → unitInterval) (m k N L : Nat) (hm : 1 ≤ m) (hL : 0 < L)
    (z : Site d) (rho0 : Fin d → Int) (hrho0 : ∀ a, 0 ≤ rho0 a)
    {Dom D : Finset (Site d)} (houter : shell z rho0 m L 0 ⊆ D) (hDDom : D ⊆ Dom)
    (o : Site d) (hoDom : o ∈ Dom) (hoD : o ∉ D) (hwo : w o = 1)
    (B T : Set (Site d))
    (hB : ∀ i < L, B ⊆ ↑(shell z rho0 m L i))
    (qI : unitInterval) (hq1 : (qI : Real) < 1)
    (hw : ∀ i < L, ∀ y ∈ shell z rho0 m L i, w y = qI)
    (H : Nat → Site d → Set (SiteConfig (Site d)))
    {ε δ δc η : Real}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ = ε ^ 2 / 64) (hδc : δc = ε / 4)
    (hη0 : 0 ≤ η)
    (hbarrier : 1 ≤ (L : Real) * δ *
      (1 - (qI : Real)) ^ ((2 * d) * N))
    (hpack : k * (CorrMove.cube (0 : Site d) (8 * (m : Int))).card ≤ N)
    (hbudget : (k : Real) *
      ((qI : Real) ^ ReinforcedShell.seedSize d m * η / δc) ≤ δ)
    (hseed : (1 - (qI : Real) ^ ReinforcedShell.seedSize d m) ^ k ≤ δ)
    (hHup : ∀ i < L, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (shell z rho0 m L i), IsUpperSet (H i x))
    (hHm : ∀ i < L, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (shell z rho0 m L i), MeasurableSet (H i x))
    (hforce : ∀ i < L, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (shell z rho0 m L i),
      ReinforcedTarget.openWindow (J m z (radius rho0 m L i) x) ∩ H i x ⊆
        TargetExt.toTarget (zdGraph d) D T (relay m z (radius rho0 m L i) x))
    (hhit : ∀ i < L, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (shell z rho0 m L i),
      (prodBernoulli w).real (H i x)ᶜ ≤ η)
    (hsrc : 1 - δ <
      (prodBernoulli w).real (connWithinSet (zdGraph d)
        (↑Dom : Set (Site d)) o B)) :
    1 - ε < (prodBernoulli w).real
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o T) := by
  classical
  have hdeg : ∀ x,
      (@Finset.filter (Site d) ((zdGraph d).Adj x)
        (fun y => Classical.propDecidable ((zdGraph d).Adj x y)) Dom).card ≤ 2 * d := by
    intro x
    rw [Finset.filter_congr_decidable]
    exact card_filter_adj_le Dom x
  have hsub : ∀ i < L, shell z rho0 m L i ⊆ Dom := by
    intro i hi
    exact (shell_subset_active z rho0 m L i houter).trans hDDom
  have hnest : ∀ i, i + 1 < L → shell z rho0 m L (i + 1) ⊆ shell z rho0 m L i := by
    intro i hi
    exact shell_succ_subset z rho0 m L i
  have hgate : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ shell z rho0 m L i →
      ∀ y ∈ shell z rho0 m L i, (zdGraph d).Adj x y →
        y ∉ shell z rho0 m L (i + 1) := by
    intro i hi x hxDom hx y hy hadj
    exact scan_gate z rho0 m L i hi hxDom hx hy hadj
  have hwle : ∀ i < L, ∀ y ∈ shell z rho0 m L i, (w y : Real) ≤ qI := by
    intro i hi y hy
    rw [hw i hi y hy]
  have ho : ∀ i < L, o ∉ shell z rho0 m L i := by
    intro i hi hoi
    exact hoD (shell_subset_active z rho0 m L i houter hoi)
  obtain ⟨i, hi, hrich⟩ := TargetExt.exists_level_real_poor_compl_gt_rel
    (zdGraph d) Dom o N (2 * d) qI.2.1 hq1 hdeg hL
      (fun j => shell z rho0 m L j) w hsub hnest hgate hwle ho hB hbarrier hsrc
  have hrhoi : ∀ a, ReinforcedShell.thickness m ≤ radius rho0 m L i a := by
    intro a
    have hbase := hrho0 a
    have hoff := thickness_le_offset m L i hi
    simp only [radius]
    omega
  exact target_gt_at_level w m k N hm z (radius rho0 m L i) hrhoi
    (shell_subset_active z rho0 m L i houter) hDDom o hoDom hoD hwo T qI
    (hw i hi) hpack (H i) hε0 hε1 hδ hδc hη0 hbudget hseed
    (hHup i hi) (hHm i hi) (hforce i hi) (hhit i hi) hrich

#print axioms KNAll.Site.ReinforcedLevel.target_gt_from_scan

end KNAll.Site.ReinforcedLevel

end
