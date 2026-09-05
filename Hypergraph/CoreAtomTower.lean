import Hypergraph.AtomTower
import Hypergraph.CoreStopped

/-!
# Incoming-atom tower for core reservations

This is the pre-examination stopped-corridor argument with the recursive target kept at the
radius-`3r` core of the head block.  The incoming region is first decomposed into its finitely many
atoms.  On each atom only the crossed-bad exhaustion estimate is used.  The full corridor event is
independent of the atom, so its probability is paid once under the original transcript.

In particular, no probability estimate is transported from the incoming-only transcript to a
later transcript which has read overlapping outgoing coordinates.
-/

noncomputable section

namespace KNAll.Site.CoreAtom

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- The retained pre-examination corridor event, ending at the recursive core of `y`. -/
def narrowCoreCorridor (r t : Nat) (h : MacroExp.Tr d) (w z y : Site 2)
    (i : Fin d) (sigma : Int) : Set (SiteConfig (Site d)) :=
  connWithinSet (zdGraph d)
    (↑(h.inspected ∪ MacroExp.E d r t w z ∪
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
    (MacroExp.emb 0) (↑(CoreRes.target (d := d) r y) : Set (Site d))

theorem measurableSet_narrowCoreCorridor (r t : Nat) (h : MacroExp.Tr d)
    (w z y : Site 2) (i : Fin d) (sigma : Int) :
    MeasurableSet (narrowCoreCorridor r t h w z y i sigma) :=
  measurableSet_connWithinSet _ _ _ _

/-- The core corridor is literally unchanged on every atom of the incoming read. -/
theorem corridorEvent_incomingTr_eq (r t : Nat) (h : MacroExp.Tr d)
    (w z y : Site 2) (i : Fin d) (sigma : Int) (omega : SiteConfig (Site d)) :
    CoreStopped.corridorEvent r t (AtomTower.incomingTr d r t h w z omega) z y i sigma =
      narrowCoreCorridor r t h w z y i sigma := by
  rw [CoreStopped.corridorEvent, narrowCoreCorridor, AtomTower.incomingTr_inspected]

/-- Dynamic failure of all core-reservation levels after the incoming read. -/
def outerNoGoodLevel (r t s K : Nat) (h : MacroExp.Tr d) (w z y : Site 2)
    (i : Fin d) (sigma : Int) (q : unitInterval) (deltaC : Real) :
    Set (SiteConfig (Site d)) :=
  {omega | omega ∈ CoreStopped.noGoodLevel r t s
    (AtomTower.incomingTr d r t h w z omega) z y i sigma q deltaC K}

/-- Dynamic crossed-bad exhaustion event after the incoming read. -/
def outerCrossedBad (r t s K : Nat) (h : MacroExp.Tr d) (w z y : Site 2)
    (i : Fin d) (sigma : Int) (q : unitInterval) (deltaC : Real) :
    Set (SiteConfig (Site d)) :=
  {omega | omega ∈ CoreStopped.crossedBad r t s
    (AtomTower.incomingTr d r t h w z omega) z y i sigma q deltaC K}

/-- The denominator-free incoming-atom tower, now delivering a recursive core reservation. -/
theorem prob_outerNoGoodLevel_le
    {r t s K : Nat} {h : MacroExp.Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int}
    {q : unitInterval} {deltaC e rho : Real}
    (hd : 3 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) (hy : y ≠ 0)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh_out : Disjoint (h.inspected ∪ MacroExp.E d r t w z) (MacroExp.E d r t z y))
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) (he0 : 0 < e)
    (he_beta : e ≤ AtomTower.beta rho d)
    (hpow : (1 - AtomTower.f e) ^ K ≤ rho / 32)
    (hcorr_core : 1 - rho / 32 < h.prob (fun _ : Site d => q)
      (narrowCoreCorridor r t h w z y i sigma))
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
      (outerNoGoodLevel r t s K h w z y i sigma q deltaC) ≤ rho / 16 := by
  classical
  let F := AtomTower.incomingRegion d r t h w z
  let p : Site d → unitInterval := fun _ => q
  let G : MacroExp.Tr d → Set (SiteConfig (Site d)) := fun k =>
    CoreStopped.crossedBad r t s k z y i sigma q deltaC K
  have hd2 : 2 ≤ d := by omega
  have hzy : z ≠ y := by
    intro h
    subst y
    have hi := congrFun hemb i
    rcases hsigma with rfl | rfl <;> simp at hi
  have htargetE : CoreRes.target (d := d) r y ⊆ MacroExp.E d r t z y :=
    (CoreRes.target_subset_M ht y).trans (MacroExp.M_subset_E hd2 r t hr hzy)
  have htargetFresh : ∀ omega : SiteConfig (Site d),
      Disjoint (AtomTower.incomingTr d r t h w z omega).inspected
        (CoreRes.target (d := d) r y) := by
    intro omega
    rw [AtomTower.incomingTr_inspected]
    exact hfresh_out.mono_right htargetE
  have hdelta2 : AtomTower.f e ≤ 1 :=
    AtomTower.f_le_one_of_le_beta hrho0 hrho1 he0 he_beta
  have hsep : ∀ omega : SiteConfig (Site d),
      ∀ u ∈ (AtomTower.incomingTr d r t h w z omega).inspected,
      ∀ v ∈ Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r),
        (zdGraph d).Adj u v →
        (5 * r : Int) < Stopped.lam (MacroExp.ctr d r z) i sigma v →
        Stopped.lam (MacroExp.ctr d r z) i sigma u ≤ 5 * r := by
    intro omega
    apply Stopped.sep_of_fresh hd2 hr (show 17 * r ≤ 17 * r by omega)
      hsigma hemb
    · simpa only [AtomTower.incomingTr_inspected] using hthin
    · simpa only [AtomTower.incomingTr_inspected] using hfresh_out
  have ho : (MacroExp.emb 0 : Site d) ∉
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r) :=
    Stopped.origin_notMem_stub hd2 hr (show 17 * r ≤ 17 * r by omega) hsigma hemb hy
  have hGatom : ∀ omega : SiteConfig (Site d),
      (AtomTower.incomingTr d r t h w z omega).prob p
          (G (AtomTower.incomingTr d r t h w z omega)) ≤
        (1 - AtomTower.f e) ^ K := by
    intro omega
    exact CoreStopped.prob_crossedBad_le_pow hsigma hdelta2
      (fun j hj xi hxi => hone omega j hj xi hxi)
  have hG : h.prob p (outerCrossedBad r t s K h w z y i sigma q deltaC) ≤
      (1 - AtomTower.f e) ^ K := by
    have htower := AtomTower.prob_dynamic_step_le p h z F
      (by simpa only [F] using AtomTower.incomingRegion_fresh d r t h w z) G
      (fun k => CoreStopped.measurableSet_crossedBad r t s k z y i sigma q deltaC K)
      (c := (1 - AtomTower.f e) ^ K) hGatom
    simpa only [outerCrossedBad, G, F, p, AtomTower.incomingTr] using htower
  have hsubset : outerNoGoodLevel r t s K h w z y i sigma q deltaC ⊆
      (narrowCoreCorridor r t h w z y i sigma)ᶜ ∪
        outerCrossedBad r t s K h w z y i sigma q deltaC := by
    intro omega homega
    have hlocal := CoreStopped.noGoodLevel_subset_corridor_compl_union_crossedBad
      ht hsigma hemb hs hbudget (hsep omega) ho (htargetFresh omega) homega
    rcases hlocal with hcorr | hbad
    · exact Or.inl (by rwa [corridorEvent_incomingTr_eq] at hcorr)
    · exact Or.inr hbad
  have hcorr_compl : h.prob p (narrowCoreCorridor r t h w z y i sigma)ᶜ ≤
      rho / 32 := by
    have hm := measurableSet_narrowCoreCorridor r t h w z y i sigma
    rw [FRDom.Transcript.prob_eq, pinnedProb_compl _ _ _ hm,
      ← FRDom.Transcript.prob_eq]
    simpa only [p] using (show
      1 - h.prob (fun _ : Site d => q) (narrowCoreCorridor r t h w z y i sigma) ≤
        rho / 32 by linarith)
  calc
    h.prob p (outerNoGoodLevel r t s K h w z y i sigma q deltaC)
        ≤ h.prob p ((narrowCoreCorridor r t h w z y i sigma)ᶜ ∪
          outerCrossedBad r t s K h w z y i sigma q deltaC) :=
      ProbInv.prob_mono h p hsubset
    _ ≤ h.prob p (narrowCoreCorridor r t h w z y i sigma)ᶜ +
          h.prob p (outerCrossedBad r t s K h w z y i sigma q deltaC) :=
      AtomTower.prob_union_le h p _ _
    _ ≤ rho / 32 + rho / 32 := add_le_add hcorr_compl (hG.trans hpow)
    _ = rho / 16 := by ring

/-- Failure of the corrected dynamic direction event is contained in core exhaustion. -/
theorem prob_outerDirectionFailure_le
    {r t s K : Nat} {h : MacroExp.Tr d} {w z y : Site 2} {i : Fin d} {sigma : Int}
    {q : unitInterval} {deltaC rho : Real}
    (hbound : h.prob (fun _ : Site d => q)
      (outerNoGoodLevel r t s K h w z y i sigma q deltaC) ≤ rho / 16) :
    h.prob (fun _ : Site d => q)
      {omega | omega ∉ CoreStopped.directionEvent r t s
        (AtomTower.incomingTr d r t h w z omega) z y i sigma q deltaC K} ≤
      rho / 16 := by
  refine (ProbInv.prob_mono h _ ?_).trans hbound
  intro omega homega
  change omega ∈ CoreStopped.noGoodLevel r t s
    (AtomTower.incomingTr d r t h w z omega) z y i sigma q deltaC K
  by_contra hnot
  exact homega (Or.inr hnot)

#print axioms KNAll.Site.CoreAtom.prob_outerNoGoodLevel_le
#print axioms KNAll.Site.CoreAtom.prob_outerDirectionFailure_le

end KNAll.Site.CoreAtom

end
