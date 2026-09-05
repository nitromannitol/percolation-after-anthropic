import Hypergraph.CoreReservation

/-!
# Stopped levels for core reservations

This is the target-parametric repair of the stopped directional argument.  The existing
`Stopped.levelBad` tests a reservation to the broad anisotropic box `MacroExp.M`.  That output
cannot be recycled as the radius-`3r` source required by the next corridor cascade.  Here a bad
level instead tests the radius-`2r` core at the head.

The probabilistic tower is unchanged.  The only geometric change is that the full corridor event
ends in the core.  `CorrMove.cube_subset_stubTarget` shows that every such path still crosses all
nested faces used by the ordered-face argument.
-/

noncomputable section

namespace KNAll.Site.CoreStopped

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- Level `j` is bad when the transcript revealed through that level does not yet carry a core
reservation at error `deltaC`. -/
def levelBad (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (sigma : Int)
    (q : unitInterval) (deltaC : Real) (j : Nat) : Set (SiteConfig (Site d)) :=
  {omega | (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
    (CoreRes.event r t (Stopped.levelTr d r t s h z i sigma j omega) z y) ≤ 1 - deltaC}

/-- No core-reservation level below `K` is good. -/
def noGoodLevel (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (sigma : Int)
    (q : unitInterval) (deltaC : Real) (K : Nat) : Set (SiteConfig (Site d)) :=
  Budget.allBad (levelBad r t s h z y i sigma q deltaC) K

/-- The full narrow corridor event with its target kept at the radius-`2r` core. -/
def corridorEvent (r t : Nat) (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (sigma : Int) :
    Set (SiteConfig (Site d)) :=
  connWithinSet (zdGraph d)
    (↑(h.inspected ∪ Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) :
      Set (Site d))
    (MacroExp.emb 0) (↑(CoreRes.target (d := d) r y) : Set (Site d))

/-- Either the head is no longer pending, or some core-reservation level is good. -/
def directionEvent (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d)
    (sigma : Int) (q : unitInterval) (deltaC : Real) (K : Nat) :
    Set (SiteConfig (Site d)) :=
  {_omega | y ∉ MacroExp.pending d h z} ∪ (noGoodLevel r t s h z y i sigma q deltaC K)ᶜ

/-- A core bad-level event depends only on the coordinates exposed at that level. -/
theorem determinedBy_levelBad (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2)
    (i : Fin d) (sigma : Int) (q : unitInterval) (deltaC : Real) (j : Nat) :
    DeterminedBy (levelBad r t s h z y i sigma q deltaC j)
      (↑(Stopped.revealSet d r t s h z i sigma j) : Set (Site d)) := by
  rw [determinedBy_iff]
  intro omega omega' hagree
  simp only [levelBad, Set.mem_setOf_eq,
    Stopped.levelTr_congr d r t s h z i sigma j hagree]

/-- Pinning the old inspected states does not change core bad-level membership. -/
theorem substitute_mem_levelBad_iff (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2)
    (i : Fin d) (sigma : Int) (q : unitInterval) (deltaC : Real) (j : Nat)
    (omega : SiteConfig (Site d)) :
    substitute (↑h.inspected : Set (Site d)) h.state omega ∈
        levelBad r t s h z y i sigma q deltaC j ↔
      omega ∈ levelBad r t s h z y i sigma q deltaC j := by
  refine (determinedBy_iff _ _).1
    (determinedBy_levelBad r t s h z y i sigma q deltaC j) _ _ ?_
  ext x
  simp only [Set.mem_inter_iff, and_congr_left_iff]
  intro hx
  have hxI : x ∉ (↑h.inspected : Set (Site d)) := fun hc =>
    Finset.disjoint_left.1 (Stopped.revealSet_fresh d r t s h z i sigma j)
      (Finset.mem_coe.1 hx) (Finset.mem_coe.1 hc)
  exact mem_substitute_of_notMem _ hxI

/-- Every tested level is both crossed and core-bad. -/
def crossedBad (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d)
    (sigma : Int) (q : unitInterval) (deltaC : Real) (K : Nat) :
    Set (SiteConfig (Site d)) :=
  Budget.allBad (fun j => Stopped.crossEvent d r t s h z i sigma j ∩
    levelBad r t s h z y i sigma q deltaC j) K

private theorem measurableSet_allBad {kappa : Type*} (bad : Nat → Set (Set kappa))
    (hbad : ∀ j, MeasurableSet (bad j)) : ∀ K, MeasurableSet (Budget.allBad bad K) := by
  intro K
  induction K with
  | zero => exact MeasurableSet.univ
  | succ K ih => exact ih.inter (hbad K)

theorem measurableSet_levelBad (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2)
    (i : Fin d) (sigma : Int) (q : unitInterval) (deltaC : Real) (j : Nat) :
    MeasurableSet (levelBad r t s h z y i sigma q deltaC j) :=
  (determinedBy_levelBad r t s h z y i sigma q deltaC j).measurableSet_of_finset

theorem measurableSet_crossedBad (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2)
    (i : Fin d) (sigma : Int) (q : unitInterval) (deltaC : Real) (K : Nat) :
    MeasurableSet (crossedBad r t s h z y i sigma q deltaC K) := by
  apply measurableSet_allBad
  intro j
  exact (Stopped.measurableSet_crossEvent d r t s h z i sigma j).inter
    (measurableSet_levelBad r t s h z y i sigma q deltaC j)

/-- The exhaustion part of the core tower, with no corridor estimate. -/
theorem prob_crossedBad_le_pow {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : Int} {q : unitInterval} {deltaC delta2 : Real}
    (hsigma : sigma = 1 ∨ sigma = -1) (hdelta2 : delta2 ≤ 1)
    (hone : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state omega ∈
          levelBad r t s h z y i sigma q deltaC j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
        (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - delta2) :
    h.prob (fun _ : Site d => q) (crossedBad r t s h z y i sigma q deltaC K) ≤
      (1 - delta2) ^ K := by
  classical
  let p : Site d → unitInterval := fun _ => q
  let bad : Nat → Set (SiteConfig (Site d)) := fun j =>
    Stopped.crossEvent d r t s h z i sigma j ∩
      levelBad r t s h z y i sigma q deltaC j
  have hstep : ∀ k, k < K →
      pinnedProb p (↑h.inspected : Set (Site d)) h.state
          (Budget.allBad bad k ∩ bad k) ≤
        (1 - delta2) *
          pinnedProb p (↑h.inspected : Set (Site d)) h.state (Budget.allBad bad k) := by
    intro k hk
    have hEq : Budget.allBad bad k ∩ bad k =
        (Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k) ∩
          Stopped.crossEvent d r t s h z i sigma k := by
      ext omega
      simp only [bad, Set.mem_inter_iff]
      tauto
    have hCdet : DeterminedBy
        (Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k)
        ((↑h.inspected : Set (Site d)) ∪
          ↑(Stopped.revealSet d r t s h z i sigma k)) := by
      refine DeterminedBy.inter (Stopped.determinedBy_allBad bad _ k fun j hj => ?_) ?_
      · refine DeterminedBy.inter ?_ ?_
        · refine (Stopped.determinedBy_crossEvent d r t s h z i sigma j).mono ?_
          intro x hx
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hxOld | hxStub
          · exact Or.inl (Finset.mem_coe.2 hxOld)
          · by_cases hxI : x ∈ h.inspected
            · exact Or.inl (Finset.mem_coe.2 hxI)
            · refine Or.inr (Finset.mem_coe.2 ?_)
              rw [Stopped.revealSet, Finset.mem_sdiff]
              exact ⟨Stopped.stub_mono hsigma (Nat.mul_le_mul_left _ (by omega)) hxStub, hxI⟩
        · refine (determinedBy_levelBad r t s h z y i sigma q deltaC j).mono ?_
          intro x hx
          exact Or.inr (Finset.mem_coe.2
            (Stopped.revealSet_mono hsigma (by omega) (Finset.mem_coe.1 hx)))
      · exact (determinedBy_levelBad r t s h z y i sigma q deltaC k).mono
          fun _ hx => Or.inr hx
    have htower := Stopped.prob_inter_le_of_step_prob_le h p z
      (Stopped.revealSet d r t s h z i sigma k) true
      (Stopped.revealSet_fresh d r t s h z i sigma k)
      (Stopped.measurableSet_crossEvent d r t s h z i sigma k) hCdet
      (c := 1 - delta2) (fun omega hmem => hone k hk omega hmem.2)
    have hmono : h.prob p
        (Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k) ≤
        h.prob p (Budget.allBad bad k) :=
      ProbInv.prob_mono h p Set.inter_subset_left
    have hnonneg : 0 ≤ 1 - delta2 := by linarith
    calc
      pinnedProb p (↑h.inspected : Set (Site d)) h.state (Budget.allBad bad k ∩ bad k)
          = h.prob p
              ((Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k) ∩
                Stopped.crossEvent d r t s h z i sigma k) := by rw [hEq]; rfl
      _ ≤ (1 - delta2) * h.prob p
          (Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k) := htower
      _ ≤ (1 - delta2) * h.prob p (Budget.allBad bad k) :=
        mul_le_mul_of_nonneg_left hmono hnonneg
  simpa only [crossedBad, bad, p, FRDom.Transcript.prob_eq] using
    Budget.pinnedProb_allBad_le_pow p (↑h.inspected : Set (Site d)) h.state
      bad K delta2 hdelta2 hstep

/-- A point of the radius-`3r` recursive core which lies in the stopped stub is beyond every
face used by a stopped tower of total depth at most `10r`.  Stub membership is essential: the
radius-`3r` core is wider than the isotropic radius-`2r` stub. -/
theorem target_mem_deep {r t s K j : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    (ht : 5 * r ≤ t) (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hbudget : 10 * s * K ≤ 10 * r) (hj : j < K) {x : Site d}
    (hx : x ∈ CoreRes.target (d := d) r y)
    (hxstub : x ∈ Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) :
    x ∈ Stopped.deep (MacroExp.ctr d r z) i sigma r t (17 * r) (10 * s * (j + 1)) := by
  have hcube : x ∈ CorrMove.cube (MacroExp.ctr d r y) (3 * (r : Int)) := by
    simpa only [CoreRes.target] using hx
  have hi := (CorrMove.mem_cube.1 hcube) i
  have hcy : (MacroExp.ctr d r y : Site d) =
      MacroExp.ctr d r z + Pi.single i (sigma * (20 * (r : Int))) :=
    CorrMove.ctr_add_dir r hemb
  rw [hcy] at hi
  simp only [Pi.add_apply, Pi.single_eq_same] at hi
  have hsigma2 : sigma * sigma = 1 := by
    rcases hsigma with rfl | rfl <;> ring
  have heq : sigma * (x i - MacroExp.ctr d r z i) - 20 * (r : Int) =
      sigma * (x i - (MacroExp.ctr d r z i + sigma * (20 * (r : Int)))) := by
    linear_combination (20 * (r : Int)) * hsigma2
  have habs :
      |sigma * (x i - MacroExp.ctr d r z i) - 20 * (r : Int)| ≤ 3 * (r : Int) := by
    rw [heq, CorrMove.abs_signed hsigma]
    exact hi
  rw [abs_le] at habs
  have hjK : j + 1 ≤ K := Nat.succ_le_iff.2 hj
  have hmul : 10 * s * (j + 1) ≤ 10 * s * K := Nat.mul_le_mul_left (10 * s) hjK
  have hdepth : 5 * r + 10 * s * (j + 1) ≤ 15 * r := by omega
  have hdepthZ : (((5 * r + 10 * s * (j + 1) : Nat) : Int)) ≤ 15 * (r : Int) := by
    exact_mod_cast hdepth
  have hlower : 17 * (r : Int) ≤ sigma * (x i - MacroExp.ctr d r z i) := by
    omega
  refine ⟨hxstub, ?_⟩
  simp only [Stopped.lam]
  exact hdepthZ.trans (by omega)

/-- The deterministic half of the core stopped tower.  If every tested level is bad, then either
the full core corridor fails or every level is both crossed and bad.  Keeping this statement
separate from the probability estimate is what permits the incoming-region atom argument to
average only the exhaustion term. -/
theorem noGoodLevel_subset_corridor_compl_union_crossedBad
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    {q : unitInterval} {deltaC : Real}
    (ht : 5 * r ≤ t) (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsep : ∀ u ∈ h.inspected,
      ∀ v ∈ Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r),
      (zdGraph d).Adj u v →
      (5 * r : Int) < Stopped.lam (MacroExp.ctr d r z) i sigma v →
      Stopped.lam (MacroExp.ctr d r z) i sigma u ≤ 5 * r)
    (ho : (MacroExp.emb 0 : Site d) ∉
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r))
    (htargetFresh : Disjoint h.inspected (CoreRes.target (d := d) r y)) :
    noGoodLevel r t s h z y i sigma q deltaC K ⊆
      (corridorEvent r t h z y i sigma)ᶜ ∪
        crossedBad r t s h z y i sigma q deltaC K := by
  classical
  have hcross : ∀ j, j < K →
      corridorEvent r t h z y i sigma ⊆ Stopped.crossEvent d r t s h z i sigma j := by
    intro j hj omega homega
    rw [corridorEvent] at homega
    obtain ⟨b, hbTarget, hconn⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 homega
    have hconn' : omega ∈ connWithin (zdGraph d)
        ((↑h.inspected : Set (Site d)) ∪
          ↑(Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)))
        (MacroExp.emb 0) b := by
      rwa [Finset.coe_union] at hconn
    have hbStub : b ∈ Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r) := by
      rcases (TargetExt.mem_of_connWithin (zdGraph d) hconn').2 with hbOld | hbStub
      · exact False.elim (Finset.disjoint_left.1 htargetFresh
          (Finset.mem_coe.1 hbOld) (Finset.mem_coe.1 hbTarget))
      · exact Finset.mem_coe.1 hbStub
    have hbdeep := target_mem_deep (d := d) ht hsigma hemb hbudget hj
      (Finset.mem_coe.1 hbTarget) hbStub
    have hfaceDepth : 1 < 10 * s * (j + 1) := by
      have : 10 * 1 * 1 ≤ 10 * s * (j + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 10 hs) (by omega)
      omega
    have hcr := Stopped.connWithinSet_stubFace_of_conn hsigma hfaceDepth hsep ho hbdeep hconn'
    rw [Stopped.crossEvent, Finset.coe_union]
    exact hcr
  intro omega homega
  by_cases hc : omega ∈ corridorEvent r t h z y i sigma
  · refine Or.inr ?_
    rw [crossedBad, Stopped.mem_allBad_iff]
    intro j hj
    exact ⟨hcross j hj hc, (Stopped.mem_allBad_iff _ K omega).1 homega j hj⟩
  · exact Or.inl hc

/-- **Core stopped-tower bound.**  The proof is the same finite-atom tower as
`Stopped.prob_noGoodLevel_le`; only the tested target has changed. -/
theorem prob_noGoodLevel_le {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : Int} {q : unitInterval} {deltaC delta2 rho : Real}
    (ht : 5 * r ≤ t) (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsep : ∀ u ∈ h.inspected,
      ∀ v ∈ Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r),
      (zdGraph d).Adj u v →
      (5 * r : Int) < Stopped.lam (MacroExp.ctr d r z) i sigma v →
      Stopped.lam (MacroExp.ctr d r z) i sigma u ≤ 5 * r)
    (ho : (MacroExp.emb 0 : Site d) ∉
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r))
    (htargetFresh : Disjoint h.inspected (CoreRes.target (d := d) r y))
    (hdelta2 : delta2 ≤ 1) (hpow : (1 - delta2) ^ K ≤ rho / 32)
    (hcorr : h.prob (fun _ : Site d => q) (corridorEvent r t h z y i sigma)ᶜ ≤ rho / 32)
    (hone : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state omega ∈
          levelBad r t s h z y i sigma q deltaC j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
        (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - delta2) :
    h.prob (fun _ : Site d => q) (noGoodLevel r t s h z y i sigma q deltaC K) ≤
      rho / 16 := by
  classical
  let p : Site d → unitInterval := fun _ => q
  let bad : Nat → Set (SiteConfig (Site d)) := fun j =>
    Stopped.crossEvent d r t s h z i sigma j ∩
      levelBad r t s h z y i sigma q deltaC j
  have hcross : ∀ j, j < K →
      corridorEvent r t h z y i sigma ⊆ Stopped.crossEvent d r t s h z i sigma j := by
    intro j hj omega homega
    rw [corridorEvent] at homega
    obtain ⟨b, hbTarget, hconn⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 homega
    have hconn' : omega ∈ connWithin (zdGraph d)
        ((↑h.inspected : Set (Site d)) ∪
          ↑(Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)))
        (MacroExp.emb 0) b := by
      rwa [Finset.coe_union] at hconn
    have hbStub : b ∈ Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r) := by
      rcases (TargetExt.mem_of_connWithin (zdGraph d) hconn').2 with hbOld | hbStub
      · exact False.elim (Finset.disjoint_left.1 htargetFresh
          (Finset.mem_coe.1 hbOld) (Finset.mem_coe.1 hbTarget))
      · exact Finset.mem_coe.1 hbStub
    have hbdeep := target_mem_deep (d := d) ht hsigma hemb hbudget hj
      (Finset.mem_coe.1 hbTarget) hbStub
    have hfaceDepth : 1 < 10 * s * (j + 1) := by
      have : 10 * 1 * 1 ≤ 10 * s * (j + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 10 hs) (by omega)
      omega
    have hcr := Stopped.connWithinSet_stubFace_of_conn hsigma hfaceDepth hsep ho hbdeep hconn'
    rw [Stopped.crossEvent, Finset.coe_union]
    exact hcr
  have hsubset : noGoodLevel r t s h z y i sigma q deltaC K ⊆
      (corridorEvent r t h z y i sigma)ᶜ ∪ Budget.allBad bad K := by
    intro omega homega
    by_cases hc : omega ∈ corridorEvent r t h z y i sigma
    · refine Or.inr ((Stopped.mem_allBad_iff bad K omega).2 fun j hj => ⟨hcross j hj hc, ?_⟩)
      exact (Stopped.mem_allBad_iff _ K omega).1 homega j hj
    · exact Or.inl hc
  have hstep : ∀ k, k < K →
      pinnedProb p (↑h.inspected : Set (Site d)) h.state
          (Budget.allBad bad k ∩ bad k) ≤
        (1 - delta2) *
          pinnedProb p (↑h.inspected : Set (Site d)) h.state (Budget.allBad bad k) := by
    intro k hk
    have hEq : Budget.allBad bad k ∩ bad k =
        (Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k) ∩
          Stopped.crossEvent d r t s h z i sigma k := by
      ext omega
      simp only [bad, Set.mem_inter_iff]
      tauto
    have hCdet : DeterminedBy
        (Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k)
        ((↑h.inspected : Set (Site d)) ∪
          ↑(Stopped.revealSet d r t s h z i sigma k)) := by
      refine DeterminedBy.inter (Stopped.determinedBy_allBad bad _ k fun j hj => ?_) ?_
      · refine DeterminedBy.inter ?_ ?_
        · refine (Stopped.determinedBy_crossEvent d r t s h z i sigma j).mono ?_
          intro x hx
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hxOld | hxStub
          · exact Or.inl (Finset.mem_coe.2 hxOld)
          · by_cases hxI : x ∈ h.inspected
            · exact Or.inl (Finset.mem_coe.2 hxI)
            · refine Or.inr (Finset.mem_coe.2 ?_)
              rw [Stopped.revealSet, Finset.mem_sdiff]
              exact ⟨Stopped.stub_mono hsigma (Nat.mul_le_mul_left _ (by omega)) hxStub, hxI⟩
        · refine (determinedBy_levelBad r t s h z y i sigma q deltaC j).mono ?_
          intro x hx
          exact Or.inr (Finset.mem_coe.2
            (Stopped.revealSet_mono hsigma (by omega) (Finset.mem_coe.1 hx)))
      · exact (determinedBy_levelBad r t s h z y i sigma q deltaC k).mono
          fun _ hx => Or.inr hx
    have htower := Stopped.prob_inter_le_of_step_prob_le h p z
      (Stopped.revealSet d r t s h z i sigma k) true
      (Stopped.revealSet_fresh d r t s h z i sigma k)
      (Stopped.measurableSet_crossEvent d r t s h z i sigma k) hCdet
      (c := 1 - delta2) (fun omega hmem => hone k hk omega hmem.2)
    have hmono : h.prob p
        (Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k) ≤
        h.prob p (Budget.allBad bad k) :=
      ProbInv.prob_mono h p Set.inter_subset_left
    have hnonneg : 0 ≤ 1 - delta2 := by linarith
    calc
      pinnedProb p (↑h.inspected : Set (Site d)) h.state (Budget.allBad bad k ∩ bad k)
          = h.prob p
              ((Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k) ∩
                Stopped.crossEvent d r t s h z i sigma k) := by rw [hEq]; rfl
      _ ≤ (1 - delta2) * h.prob p
          (Budget.allBad bad k ∩ levelBad r t s h z y i sigma q deltaC k) := htower
      _ ≤ (1 - delta2) * h.prob p (Budget.allBad bad k) :=
        mul_le_mul_of_nonneg_left hmono hnonneg
  have hfinal := Budget.pinnedProb_corridor_or_allBad_le p
    (↑h.inspected : Set (Site d)) h.state (corridorEvent r t h z y i sigma)ᶜ
    bad K rho delta2 hdelta2 hpow hcorr hstep
  exact (ProbInv.prob_mono h p hsubset).trans hfinal

/-! ## Stopping and the delivered reservation -/

open Classical in
def stopLevel (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d)
    (sigma : Int) (q : unitInterval) (deltaC : Real) (K : Nat)
    (omega : SiteConfig (Site d)) : Nat :=
  if hex : ∃ j, j < K ∧ omega ∉ levelBad r t s h z y i sigma q deltaC j
  then Nat.find hex else K

theorem exists_good_of_notMem_noGoodLevel {r t s K : Nat} {h : MacroExp.Tr d}
    {z y : Site 2} {i : Fin d} {sigma : Int} {q : unitInterval} {deltaC : Real}
    {omega : SiteConfig (Site d)}
    (homega : omega ∉ noGoodLevel r t s h z y i sigma q deltaC K) :
    ∃ j, j < K ∧ omega ∉ levelBad r t s h z y i sigma q deltaC j := by
  by_contra hc
  refine homega ((Stopped.mem_allBad_iff _ K omega).2 fun j hj => ?_)
  by_contra hcj
  exact hc ⟨j, hj, hcj⟩

theorem stopLevel_lt {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : Int} {q : unitInterval} {deltaC : Real}
    {omega : SiteConfig (Site d)}
    (homega : omega ∉ noGoodLevel r t s h z y i sigma q deltaC K) :
    stopLevel r t s h z y i sigma q deltaC K omega < K := by
  classical
  have hex := exists_good_of_notMem_noGoodLevel homega
  rw [stopLevel, dif_pos hex]
  exact (Nat.find_spec hex).1

/-- At the stopping transcript, the requested core reservation holds in the actual pinned law. -/
theorem bound_stopLevel {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : Int} {q : unitInterval} {deltaC : Real}
    {omega : SiteConfig (Site d)}
    (homega : omega ∉ noGoodLevel r t s h z y i sigma q deltaC K) :
    CoreRes.Bound r t q deltaC
      (Stopped.levelTr d r t s h z i sigma
        (stopLevel r t s h z y i sigma q deltaC K omega) omega) z y := by
  classical
  have hex := exists_good_of_notMem_noGoodLevel homega
  have hgood : omega ∉ levelBad r t s h z y i sigma q deltaC
      (stopLevel r t s h z y i sigma q deltaC K omega) := by
    rw [stopLevel, dif_pos hex]
    exact (Nat.find_spec hex).2
  rw [levelBad, Set.mem_setOf_eq, not_le] at hgood
  exact hgood

#print axioms KNAll.Site.CoreStopped.determinedBy_levelBad
#print axioms KNAll.Site.CoreStopped.target_mem_deep
#print axioms KNAll.Site.CoreStopped.prob_noGoodLevel_le
#print axioms KNAll.Site.CoreStopped.bound_stopLevel

end KNAll.Site.CoreStopped

end
