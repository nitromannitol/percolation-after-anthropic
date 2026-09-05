import Hypergraph.CoreBatchTransition
import Hypergraph.CoreDirectionNoGluing

/-!
# A core batch without pinned gluing

`CoreBatchTransition.prob_batchFailure_le_of_postWindow` was written before the
middle-box support in `PostFam.tailWindow` was used directly.  It therefore routes
through the obsolete support-in-`D` proof and assumes `PinnedSiteGluing`.

The theorem below keeps the same honest batch interface but uses
`CoreDirectionNoGluing.prob_directionFailure_le_of_postWindow`.  In particular,
the finite target-aware window family and the face/long-box inputs remain visible;
no correlation conjecture is hidden in the wrapper.
-/

noncomputable section

namespace KNAll.Site.CoreBatchNoGluing

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- The complete one-owner batch estimate using the gluing-free stopped-level proof. -/
theorem prob_batchFailure_le_of_postWindow
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hd : 3 ≤ d) {r t R s K : Nat} {h : MacroExp.Tr d}
    {w z : Site 2} (axis : Site 2 → Fin d) (sign : Site 2 → Int)
    {rho : Real}
    (hr : 0 < r) (ht : 5 * r ≤ t) (h44 : 44 ≤ r) (hR1 : 1 ≤ R)
    (hscale : 100 * (d + 1) * (R + 1) < r)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hwz : w ≠ z) (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
      MacroExp.thin d t)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (heps_rho : C.eps ≤ rho / 32)
    (he_beta : C.eps ≤ AtomTower.beta rho d)
    (hpow : (1 - AtomTower.f C.eps) ^ K ≤ rho / 32)
    (hincoming : CoreRes.Bound (d := d) r t q C.eps h w z)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (htail : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      (MacroExp.emb (y - z) : Site d) = Pi.single (axis y) (sign y))
    (hy0 : ∀ y ∈ CoreFrontier.newHeads (d := d) h z, y ≠ 0)
    (hfresh : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y))
    (hzero : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      (MacroExp.emb 0 : Site d) ∉ MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (hfresh_out : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      Disjoint (h.inspected ∪ MacroExp.E d r t w z) (MacroExp.E d r t z y))
    (hface : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      CoreRes.FaceInputs (d := d) R h q
        (h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) (axis y) (sign y) r t (17 * r)))
    (hlong : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      CoreRes.LongInputs (d := d) R h q
        (h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) (axis y) (sign y) r t (17 * r))
        (axis y) (sign y))
    (hwindow : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
        CorePost.CorePostWindowBound C q (MacroExp.ctr d r z) (axis y) (sign y)
          r t s j
          (CorePost.levelDom r t s (AtomTower.incomingTr d r t h w z outer)
            z y (axis y) (sign y) j xi) y) :
    h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h w z axis sign q C.eps) ≤
        9 * rho / 32 := by
  have hout : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      h.prob (fun _ : Site d => q)
        (CoreBatchTransition.directionFailure r t s K h w z y
          (axis y) (sign y) q C.eps) ≤ rho / 16 := by
    intro y hy
    exact CoreDirectionNoGluing.prob_directionFailure_le_of_postWindow
      hwf hv hd hr ht h44 hR1 hscale hs hbudget
      (hsigma y hy) (hemb y hy) (hy0 y hy) hwz horigin
      (hfresh y hy) (hzero y hy) hthin (hfresh_out y hy)
      (hface y hy) (hlong y hy) hrho0 hrho1 he_beta hpow hincoming
      hclear hwidth htail hplanar htrans (hwindow y hy)
  exact CoreBatchTransition.prob_batchFailure_le_of_directionBounds
    hrho0 heps_rho hincoming hout

/-- Complement form at the same explicit batch event. -/
theorem one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {r t R s K : Nat} {h : MacroExp.Tr d} {w z : Site 2}
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {rho : Real}
    (hfail : h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h w z axis sign q C.eps) ≤
        9 * rho / 32) :
    1 - 9 * rho / 32 ≤ h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchSuccess r t s K h w z axis sign q C.eps) :=
  CoreBatchTransition.one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess hfail

#print axioms KNAll.Site.CoreBatchNoGluing.prob_batchFailure_le_of_postWindow
#print axioms KNAll.Site.CoreBatchNoGluing.one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess

end KNAll.Site.CoreBatchNoGluing

end
