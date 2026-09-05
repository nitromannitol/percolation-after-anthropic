import Hypergraph.ReinforcedTargetBridge

/-!
# One reinforced shell level reaches its target

This file is the probability assembly for one deterministic shell selected by the outer-to-inner
scan.  It deliberately does not choose that shell and does not package any probability theorem as
data.  Its inputs are the rich-shell estimate, the selected-window failure estimate, and the
per-window unreliability estimates.  The conclusion uses the already closed pinned-site gluing
theorem.
-/

noncomputable section

namespace KNAll.Site.ReinforcedTarget

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- A rich deterministic shell reaches the target with the v15 error budget.  This is the exact
probability-theoretic interface between the shell scan and the reinforced-window geometry. -/
theorem oneLevel_target_gt
    (G : SimpleGraph V) (w : V → unitInterval)
    {Dom D O Int : Finset V} (hIntO : Int ⊆ O) (hOD : O ⊆ D)
    (hDDom : D ⊆ Dom) (o : V) (hoDom : o ∈ Dom) (hoD : o ∉ D)
    (hwo : w o = 1) (T : Set V) (N k : Nat)
    (sel : Finset V → Finset V) (J : V → Finset V) (v : V → V)
    {ε δ δc c : Real}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ = ε ^ 2 / 64) (hδc : δc = ε / 4)
    (hc0 : 0 ≤ c) (hkc : (k : Real) * c ≤ δ)
    (hselSub : ∀ K, sel K ⊆ K) (hselCard : ∀ K, (sel K).card ≤ k)
    (hJ : ∀ x ∈ TargetExt.outerBoundary G Dom O, J x ⊆ O \ Int)
    (hv : ∀ x ∈ TargetExt.outerBoundary G Dom O, v x ∈ O \ Int)
    (hbridge : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      ∀ omega : SiteConfig V, x ∈ omega → omega ∈ openWindow (J x) →
        omega ∈ connWithin G (insert x (↑(J x) : Set V)) x (v x))
    (hrich : 1 - 2 * δ <
      (prodBernoulli w).real (TargetExt.poor G Dom O o N)ᶜ)
    (hnoopen : (prodBernoulli w).real
      ((TargetExt.poor G Dom O o N)ᶜ \ selectedOpen G Dom O o sel J) ≤ δ)
    (honebad : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      (prodBernoulli w).real
        (openWindow (J x) ∩ lowRelay G w (O \ Int) D T δc (v x)) ≤ c) :
    1 - ε < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set V) o T) := by
  let Bad : V → Set (SiteConfig V) := fun x =>
    openWindow (J x) ∩ lowRelay G w (O \ Int) D T δc (v x)
  have hBadDet : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      DeterminedBy (Bad x) (↑(O \ Int) : Set V) := by
    intro x hx
    exact ((determinedBy_openWindow (J x)).mono fun y hy =>
      Finset.mem_coe.2 (hJ x hx (Finset.mem_coe.1 hy))).inter
        (determinedBy_lowRelay G w (O \ Int) D T δc (v x))
  have hbad0 := TargetExt.real_rich_inter_selectedBad_le
    G w Dom O o N k sel (O \ Int) Bad Finset.sdiff_subset hselSub hselCard
    hBadDet hc0 (fun x hx => honebad x hx)
  have hbad : (prodBernoulli w).real
      ((TargetExt.poor G Dom O o N)ᶜ ∩
        selectedUnreliable G w Dom D O Int o T δc sel J v) ≤ δ := by
    have heq : (⋃ x ∈ TargetExt.outerBoundary G Dom O,
          TargetExt.selectedAt G Dom O o sel x ∩ Bad x) =
        selectedUnreliable G w Dom D O Int o T δc sel J v := by
      rfl
    rw [heq] at hbad0
    exact hbad0.trans hkc
  have hsub : (TargetExt.poor G Dom O o N)ᶜ ∩
      (selectedOpen G Dom O o sel J \
        selectedUnreliable G w Dom D O Int o T δc sel J v) ⊆
      TargetExt.reachRelayD G w Dom D O Int o T δc := by
    intro omega homega
    apply selectedReliable_subset_reachRelayD G w hIntO hOD hDDom o T δc
      sel J v hselSub hJ hv hbridge
    exact selectedOpen_diff_unreliable_subset_reliable
      G w Dom D O Int o T δc sel J v homega.2
  have hrelay : 1 - 4 * δ <
      (prodBernoulli w).real (TargetExt.reachRelayD G w Dom D O Int o T δc) :=
    real_selectedReliable_gt (prodBernoulli w) hrich hnoopen hbad hsub
  have hδc1 : δc ≤ 1 := by
    rw [hδc]
    linarith
  have htarget := TargetExt.real_reachRelayD_target_ge G
    FiniteHyperGluingClosed.pinnedSiteGluing w hIntO hOD hDDom
    o hoDom hoD hwo T hδc1
  exact target_error_arithmetic hε0 hε1 hδ hδc hrelay htarget

/-- Convenience wrapper: finite hit events discharge each per-window unreliability estimate by
the restricted collar Markov inequality and Harris association. -/
theorem oneLevel_target_gt_of_hits
    (G : SimpleGraph V) (w : V → unitInterval)
    {Dom D O Int : Finset V} (hIntO : Int ⊆ O) (hOD : O ⊆ D)
    (hDDom : D ⊆ Dom) (o : V) (hoDom : o ∈ Dom) (hoD : o ∉ D)
    (hwo : w o = 1) (T : Set V) (N k : Nat)
    (sel : Finset V → Finset V) (J : V → Finset V) (v : V → V)
    (H : V → Set (SiteConfig V)) {ε δ δc a η : Real}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ = ε ^ 2 / 64) (hδc : δc = ε / 4)
    (ha0 : 0 ≤ a) (hη0 : 0 ≤ η)
    (hbudget : (k : Real) * (a * η / δc) ≤ δ)
    (hselSub : ∀ K, sel K ⊆ K) (hselCard : ∀ K, (sel K).card ≤ k)
    (hJ : ∀ x ∈ TargetExt.outerBoundary G Dom O, J x ⊆ O \ Int)
    (hv : ∀ x ∈ TargetExt.outerBoundary G Dom O, v x ∈ O \ Int)
    (hbridge : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      ∀ omega : SiteConfig V, x ∈ omega → omega ∈ openWindow (J x) →
        omega ∈ connWithin G (insert x (↑(J x) : Set V)) x (v x))
    (hHup : ∀ x ∈ TargetExt.outerBoundary G Dom O, IsUpperSet (H x))
    (hHm : ∀ x ∈ TargetExt.outerBoundary G Dom O, MeasurableSet (H x))
    (hforce : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      openWindow (J x) ∩ H x ⊆ TargetExt.toTarget G D T (v x))
    (hopen : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      (prodBernoulli w).real (openWindow (J x)) ≤ a)
    (hhit : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      (prodBernoulli w).real (H x)ᶜ ≤ η)
    (hrich : 1 - 2 * δ <
      (prodBernoulli w).real (TargetExt.poor G Dom O o N)ᶜ)
    (hnoopen : (prodBernoulli w).real
      ((TargetExt.poor G Dom O o N)ᶜ \ selectedOpen G Dom O o sel J) ≤ δ) :
    1 - ε < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set V) o T) := by
  have hδc0 : 0 < δc := by
    rw [hδc]
    linarith
  apply oneLevel_target_gt G w hIntO hOD hDDom o hoDom hoD hwo T N k sel J v
    hε0 hε1 hδ hδc (div_nonneg (mul_nonneg ha0 hη0) hδc0.le) hbudget
    hselSub hselCard hJ hv hbridge hrich hnoopen
  intro x hx
  exact real_openWindow_inter_lowRelay_le G w (O \ Int) D (J x) T (v x)
    (hJ x hx) (hHup x hx) (hHm x hx) (hforce x hx)
    hδc0 ha0 hη0 (hopen x hx) (hhit x hx)

#print axioms KNAll.Site.ReinforcedTarget.oneLevel_target_gt
#print axioms KNAll.Site.ReinforcedTarget.oneLevel_target_gt_of_hits

end KNAll.Site.ReinforcedTarget

end
