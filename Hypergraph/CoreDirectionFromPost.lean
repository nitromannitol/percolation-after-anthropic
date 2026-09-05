import Hypergraph.CoreDirection
import Hypergraph.CorePostFamily

/-!
# A stopped direction from the recorded post-entry windows

This module removes the raw one-level hypothesis from `CoreDirection.prob_directionFailure_le`.
For each atom of the incoming read, `CorePost.hpost_of_corePostWindowBound` constructs the exact
support-in-`D` family and `CorePerLevel.hone_of_postEntry_D` supplies the one-level estimate.  The
only remaining analytic post-entry input is the named finite-cylinder inequality
`CorePost.CorePostWindowBound`.

The construction is deliberately performed separately on every incoming atom.  No conditional
probability bound is transported through the overlapping incoming read.
-/

noncomputable section

namespace KNAll.Site.CoreDirectionFromPost

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat}

/-! ## Certificate specialization

The direction estimate below is stated for an abstract failure budget `rho`.  At assembly time
that budget is always the complement of the certificate's planar comparison density.  The next
three lemmas discharge the corresponding positivity, upper-bound, and nested tolerance
obligations directly from `Certificate2.WellFormed`; callers therefore do not need to repeat this
arithmetic or introduce a free analytic parameter.
-/

/-- The certificate leaves a strictly positive margin below its planar comparison density. -/
theorem densityGap_pos {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    0 < 1 - (C.density : Real) := by
  have he := hwf.eps_pos
  have hbudget := hwf.eps_le
  linarith

/-- A unit-interval density has complementary margin at most one. -/
theorem densityGap_le_one (C : LeftImp2.Certificate2 d) :
    1 - (C.density : Real) ≤ 1 := by
  have hdensity_nonneg : 0 ≤ (C.density : Real) := C.density.2.1
  linarith

variable [NeZero d]

/-- The certificate tolerance fits the atom-tower budget at its actual density margin. -/
theorem eps_le_atomBeta_density {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    C.eps ≤ AtomTower.beta (1 - (C.density : Real)) d := by
  rw [CoreDirection.atom_beta_eq_corr_beta]
  rw [← MacroExp.beta_eq_corridorMove_beta hwf]
  exact hwf.eps_le_beta

/-- The complete one-direction bound after replacing the abstract stopped-level estimate by the
actual post-entry window family. -/
theorem prob_directionFailure_le_of_postWindow
    (hgl : PinnedSiteGluing)
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hdelta : C.delta = C.eps ^ 2 / 96)
    (hd : 3 ≤ d) {r t R s K : Nat} {h : MacroExp.Tr d}
    {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    (hr : 0 < r) (ht : 5 * r ≤ t) (h44 : 44 ≤ r) (hR1 : 1 ≤ R)
    (hscale : 100 * (d + 1) * (R + 1) < r)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hy : y ≠ 0) (hwz : w ≠ z)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfresh : Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y))
    (hzero : (MacroExp.emb 0 : Site d) ∉
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
      MacroExp.thin d t)
    (hfresh_out : Disjoint (h.inspected ∪ MacroExp.E d r t w z)
      (MacroExp.E d r t z y))
    (hface : CoreRes.FaceInputs (d := d) R h q
      (h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)))
    (hlong : CoreRes.LongInputs (d := d) R h q
      (h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) i sigma)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (he_beta : C.eps ≤ AtomTower.beta rho d)
    (hpow : (1 - AtomTower.f C.eps) ^ K ≤ rho / 32)
    (hincoming : CoreRes.Bound (d := d) r t q C.eps h w z)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (htail : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
        CorePost.CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
          (CorePost.levelDom r t s (AtomTower.incomingTr d r t h w z outer)
            z y i sigma j xi) y) :
    h.prob (fun _ : Site d => q)
      {outer | outer ∉ CoreStopped.directionEvent r t s
        (AtomTower.incomingTr d r t h w z outer) z y i sigma q C.eps K} ≤
      rho / 16 := by
  have hd2 : 2 ≤ d := by omega
  have hfar : 10 * s * K ≤ 13 * r := by omega
  have hone : ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
      substitute
          (↑(AtomTower.incomingTr d r t h w z outer).inspected : Set (Site d))
          (AtomTower.incomingTr d r t h w z outer).state xi ∈
        CoreStopped.levelBad r t s (AtomTower.incomingTr d r t h w z outer)
          z y i sigma q C.eps j →
      (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma j xi).prob (fun _ : Site d => q)
        (Stopped.crossEvent d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma j) ≤ 1 - AtomTower.f C.eps := by
    intro outer
    let h' := AtomTower.incomingTr d r t h w z outer
    have hQ : MacroExp.Q d r t z ⊆ h'.inspected := by
      intro x hx
      change x ∈ (AtomTower.incomingTr d r t h w z outer).inspected
      rw [AtomTower.incomingTr_inspected]
      exact Finset.mem_union_right _ (CorrMove.Q_subset_E hd2 r t hr hwz hx)
    have horigin' : (MacroExp.emb 0 : Site d) ∈ h'.openSites := by
      dsimp only [h', AtomTower.incomingTr, FRDom.Transcript.step]
      exact Finset.mem_union_left _ horigin
    have hthin' : (↑h'.inspected : Set (Site d)) ⊆ MacroExp.thin d t := by
      simpa only [h', AtomTower.incomingTr_inspected] using hthin
    have hfresh' : Disjoint h'.inspected (MacroExp.E d r t z y) := by
      simpa only [h', AtomTower.incomingTr_inspected] using hfresh_out
    have hpost := CorePost.hpost_of_corePostWindowBound hwf hd2 hr (by omega) hsigma hemb
      hthin' hfresh' horigin' hfar hclear hwidth htail hplanar htrans
      (fun j hj xi => hwindow outer j hj xi)
    have hlevel := CorePerLevel.hone_of_postEntry_D hgl hwf hv hdelta hr (by omega) hfar hsigma hemb
      hQ horigin' hpost
    simpa only [h', hdelta, AtomTower.f] using hlevel
  exact CoreDirection.prob_directionFailure_le hd hr ht h44 hR1 hscale hs hbudget hsigma
    hemb hy hwz hfresh hzero hthin hfresh_out hface hlong hrho0 hrho1 hwf.eps_pos he_beta
    hpow hincoming hone

#print axioms KNAll.Site.CoreDirectionFromPost.prob_directionFailure_le_of_postWindow

end KNAll.Site.CoreDirectionFromPost

end
