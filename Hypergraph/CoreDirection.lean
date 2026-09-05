import Hypergraph.CoreAtomTower

/-!
# One stopped outgoing direction from a core reservation

This file composes the three already isolated pieces of the repaired move:

1. an incoming core reservation supplies the narrow corridor source;
2. the corridor cascade reaches the next radius-`2r` core at the pre-examination law;
3. the incoming-atom tower converts this into failure probability at most `rho / 16`.

The conclusion is still a single-direction estimate.  Batch bookkeeping and bounded-damage
domination are deliberately left to the macro layer.
-/

noncomputable section

namespace KNAll.Site.CoreDirection

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

theorem atom_beta_eq_corr_beta (rho : Real) (d : Nat) :
    AtomTower.beta rho d = CorrMove.beta rho d := by
  rw [AtomTower.beta, CorrMove.beta_closed_form]

theorem atom_f_eq_corr_f (e : Real) : AtomTower.f e = CorrMove.f e := rfl

/-- A complete one-direction estimate from an owned incoming core reservation.  All probability
inputs below are analytic finite-window inputs; no post-step source estimate occurs. -/
theorem prob_directionFailure_le
    (hd : 3 ≤ d) {r t R s K : Nat} {h : MacroExp.Tr d}
    {w z y : Site 2} {i : Fin d} {sigma : Int} {q : unitInterval}
    {deltaC e rho : Real}
    (hr : 0 < r) (ht : 5 * r ≤ t) (h44 : 44 ≤ r) (hR1 : 1 ≤ R)
    (hscale : 100 * (d + 1) * (R + 1) < r)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hy : y ≠ 0) (hwz : w ≠ z)
    (hfresh : Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y))
    (hzero : (MacroExp.emb 0 : Site d) ∉
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh_out : Disjoint (h.inspected ∪ MacroExp.E d r t w z) (MacroExp.E d r t z y))
    (hface : CoreRes.FaceInputs (d := d) R h q
      (h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)))
    (hlong : CoreRes.LongInputs (d := d) R h q
      (h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) i sigma)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (he0 : 0 < e) (he_beta : e ≤ AtomTower.beta rho d)
    (hpow : (1 - AtomTower.f e) ^ K ≤ rho / 32)
    (hincoming : CoreRes.Bound (d := d) r t q e h w z)
    (hone : ∀ omega : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
      substitute
          (↑(AtomTower.incomingTr d r t h w z omega).inspected : Set (Site d))
          (AtomTower.incomingTr d r t h w z omega).state xi ∈
        CoreStopped.levelBad r t s (AtomTower.incomingTr d r t h w z omega)
          z y i sigma q deltaC j →
      (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z omega)
          z i sigma j xi).prob (fun _ : Site d => q)
        (Stopped.crossEvent d r t s (AtomTower.incomingTr d r t h w z omega)
          z i sigma j) ≤ 1 - AtomTower.f e) :
    h.prob (fun _ : Site d => q)
      {omega | omega ∉ CoreStopped.directionEvent r t s
        (AtomTower.incomingTr d r t h w z omega) z y i sigma q deltaC K} ≤
      rho / 16 := by
  have heCorr : e ≤ CorrMove.beta rho d := by
    rwa [← atom_beta_eq_corr_beta]
  have hsrc := CoreRes.bound_implies_narrowSource (d := d) (i := i) (sigma := sigma)
    heCorr hincoming
  have hcorr := CoreRes.corridorMoveNarrowCore (d := d) (by omega : 2 ≤ d)
    hsigma hemb h44 hR1 hscale ht hrho0 hrho1 hwz hfresh hzero hface hlong hsrc
  have houter := CoreAtom.prob_outerNoGoodLevel_le hd hr ht hs hbudget hsigma hemb hy
    hthin hfresh_out hrho0 hrho1 he0 he_beta hpow hcorr hone
  exact CoreAtom.prob_outerDirectionFailure_le houter

#print axioms KNAll.Site.CoreDirection.prob_directionFailure_le

end KNAll.Site.CoreDirection

end
