import Hypergraph.CoreAcceptedTransition
import Hypergraph.CorePostSupported

/-!
# Accepted core transition with support-owned post windows

This is the additive support-owned analogue of
`CoreAcceptedTransition.prob_batchFailure_le_of_preReveal`.  It retains the accepted-only owner
selection and all of its deterministic freshness consequences, but its post-entry input is the
flexible `CorePostSupport.CorePostWindowBound`.  Thus the complete target-aware support
`Q x ∪ P x` may be owned by the fresh tail without being forced into `PostFam.tailO`.
-/

noncomputable section

namespace KNAll.Site.CoreAcceptedSupport

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- The gluing-free accepted batch estimate using support-owned target-aware windows.  The only
probabilistic inputs not contained in the certificate are the displayed face, long-box, and
post-window families. -/
theorem prob_batchFailure_le_of_preReveal
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hd : 3 ≤ d) {r t R s K : Nat} {h : MacroExp.Tr d}
    {z : Site 2} (hz : CoreFrontier.Frontier h z)
    (hpre : CoreAcceptedTransition.PreReveal r t q C.eps h)
    (axis : Site 2 → Fin d) (sign : Site 2 → Int) {rho : Real}
    (hr : 0 < r) (ht : 5 * r ≤ t) (h44 : 44 ≤ r) (hR1 : 1 ≤ R)
    (hscale : 100 * (d + 1) * (R + 1) < r)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (heps_rho : C.eps ≤ rho / 32)
    (he_beta : C.eps ≤ AtomTower.beta rho d)
    (hpow : (1 - AtomTower.f C.eps) ^ K ≤ rho / 32)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (htail : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hsigma : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      sign y = 1 ∨ sign y = -1)
    (hemb : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      (MacroExp.emb (y - z) : Site d) = Pi.single (axis y) (sign y))
    (hface : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      CoreRes.FaceInputs (d := d) R h q
        (h.inspected ∪
          MacroExp.E d r t (CoreAcceptedTransition.owner hpre.frontier z hz) z ∪
          Stopped.stub (MacroExp.ctr d r z) (axis y) (sign y) r t (17 * r)))
    (hlong : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      CoreRes.LongInputs (d := d) R h q
        (h.inspected ∪
          MacroExp.E d r t (CoreAcceptedTransition.owner hpre.frontier z hz) z ∪
          Stopped.stub (MacroExp.ctr d r z) (axis y) (sign y) r t (17 * r))
        (axis y) (sign y))
    (hwindow : ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
        CorePostSupport.CorePostWindowBound C q (MacroExp.ctr d r z)
          (axis y) (sign y) r t s j
          (CorePost.levelDom r t s
            (AtomTower.incomingTr d r t h
              (CoreAcceptedTransition.owner hpre.frontier z hz) z outer)
            z y (axis y) (sign y) j xi)
          (↑(CoreRes.target (d := d) r y) : Set (Site d))) :
    h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h
        (CoreAcceptedTransition.owner hpre.frontier z hz) z axis sign q C.eps) ≤
      9 * rho / 32 := by
  let w := CoreAcceptedTransition.owner hpre.frontier z hz
  have hw := CoreAcceptedTransition.owner_spec hpre.frontier z hz
  have hgeom := CoreAcceptedTransition.outgoing_geometry_of_preReveal
    (d := d) (by omega) hr hpre hz
  change w ≠ z ∧
      (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
        MacroExp.thin d t ∧
      ∀ y ∈ CoreFrontier.newHeads (d := d) h z,
        y ≠ 0 ∧
        Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y) ∧
        (MacroExp.emb 0 : Site d) ∉
          MacroExp.Q d r t z ∪ MacroExp.E d r t z y ∧
        Disjoint (h.inspected ∪ MacroExp.E d r t w z)
          (MacroExp.E d r t z y) at hgeom
  change h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h w z axis sign q C.eps) ≤
        9 * rho / 32
  apply CoreBatchTransition.prob_batchFailure_le_of_directionBounds
    hrho0 heps_rho hw.2.2
  intro y hy
  exact CorePostSupport.prob_directionFailure_le_of_corePostWindow
    hwf hv hd hr ht h44 hR1 hscale hs hbudget
    (hsigma y hy) (hemb y hy) (hgeom.2.2 y hy).1 hgeom.1 hpre.origin_open
    (hgeom.2.2 y hy).2.1 (hgeom.2.2 y hy).2.2.1 hgeom.2.1
    (hgeom.2.2 y hy).2.2.2 (hface y hy) (hlong y hy)
    hrho0 hrho1 he_beta hpow hw.2.2 hclear hwidth htail hplanar htrans
    (hwindow y hy)

/-- Complement form of the support-owned accepted batch estimate. -/
theorem one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess_of_preReveal
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {r t s K : Nat} {h : MacroExp.Tr d} {z : Site 2}
    (hz : CoreFrontier.Frontier h z)
    (hpre : CoreAcceptedTransition.PreReveal r t q C.eps h)
    {axis : Site 2 → Fin d} {sign : Site 2 → Int} {rho : Real}
    (hfail : h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchFailure r t s K h
        (CoreAcceptedTransition.owner hpre.frontier z hz) z axis sign q C.eps) ≤
      9 * rho / 32) :
    1 - 9 * rho / 32 ≤ h.prob (fun _ : Site d => q)
      (CoreBatchTransition.batchSuccess r t s K h
        (CoreAcceptedTransition.owner hpre.frontier z hz) z axis sign q C.eps) :=
  CoreBatchTransition.one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess hfail

#print axioms KNAll.Site.CoreAcceptedSupport.prob_batchFailure_le_of_preReveal
#print axioms KNAll.Site.CoreAcceptedSupport.one_sub_nine_rho_over_thirtytwo_le_prob_batchSuccess_of_preReveal

end KNAll.Site.CoreAcceptedSupport

end
