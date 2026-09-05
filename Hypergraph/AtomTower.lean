import Hypergraph.AdaptiveRegion

/-!
# The incoming-atom tower for a stopped corridor

This file formalizes the denominator-free calculation of
`math/CORRIDOR_TRANSFER.md`, Section 5.  The incoming edge region is read once.  On each of its
finitely many atoms the stopped proof is factored into

* a deterministic inclusion in "narrow corridor failure or crossed bad levels", and
* an exhaustion estimate for the crossed bad levels which does not use the corridor estimate.

Only the exhaustion estimate is averaged over the incoming atoms.  The narrow corridor event is
literally the same event on every atom, so its failure remains at the pre-examination law.  In
particular, no conditional estimate is transported across the overlapping incoming read.

`CorrMove.corridorMove` is intentionally neither imported nor used: its broad success event cannot
supply the narrow hypothesis below.
-/

noncomputable section

namespace KNAll.Site.AtomTower

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## Constants -/

/-- The final per-direction corridor budget. -/
def alpha (rho : ℝ) : ℝ := rho / 32

/-- The number of steps in the corridor tolerance cascade. -/
def J (d : ℕ) : ℕ := d + 1

/-- The loss at one step of the `d+1` step corridor cascade. -/
def f (a : ℝ) : ℝ := a ^ 2 / 96

/-- The closed form of the initial tolerance in the `d+1` step cascade. -/
def beta (rho : ℝ) (d : ℕ) : ℝ :=
  (rho / 32) ^ (2 ^ (d + 1)) / 96 ^ (2 ^ (d + 1) - 1)

theorem beta_pos {rho : ℝ} (hrho : 0 < rho) (d : ℕ) : 0 < beta rho d := by
  unfold beta
  positivity

theorem beta_le_one {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) (d : ℕ) :
    beta rho d ≤ 1 := by
  have ha0 : 0 ≤ rho / 32 := by positivity
  have ha1 : rho / 32 ≤ 1 := by linarith
  have hn0 : 0 ≤ (rho / 32) ^ (2 ^ (d + 1)) := by positivity
  have hn1 : (rho / 32) ^ (2 ^ (d + 1)) ≤ 1 := pow_le_one₀ ha0 ha1
  have hd1 : (1 : ℝ) ≤ 96 ^ (2 ^ (d + 1) - 1) := by
    exact one_le_pow₀ (by norm_num)
  rw [beta]
  exact (div_le_self hn0 hd1).trans hn1

theorem f_pos {e : ℝ} (he : 0 < e) : 0 < f e := by
  unfold f
  positivity

theorem f_le_one_of_le_beta {rho e : ℝ} {d : ℕ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) (he0 : 0 < e) (hebeta : e ≤ beta rho d) :
    f e ≤ 1 := by
  have he1 : e ≤ 1 := hebeta.trans (beta_le_one hrho0 hrho1 d)
  unfold f
  nlinarith [sq_nonneg (e - 1)]

/-! ## The exact finite-atom formula -/

variable {kappa V : Type*}

/-- The probability of the atom which records precisely `S` open in the finite read `F`.
For `S ⊆ F`, `atomWeight_eq` below expands this as the two products in (5.1). -/
def atomWeight (p : kappa → unitInterval) (F S : Finset kappa) : ℝ :=
  (prodBernoulli p).real (localCylinder (↑F : Set kappa) (↑S : Set kappa))

theorem atomWeight_eq [DecidableEq kappa] (p : kappa → unitInterval) {F S : Finset kappa}
    (hSF : S ⊆ F) :
    atomWeight p F S =
      (∏ x ∈ S, (p x : ℝ)) * ∏ x ∈ F \ S, (1 - (p x : ℝ)) := by
  classical
  rw [atomWeight, prodBernoulli_real_localCylinder]
  congr 1
  · apply Finset.prod_congr
    · ext x
      simp only [Finset.mem_filter, Finset.mem_coe]
      exact and_iff_right_iff_imp.2 fun hx => hSF hx
    · intro x hx
      rfl
  · apply Finset.prod_congr
    · ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_coe]
    · intro x hx
      rfl

theorem atomWeight_nonneg (p : kappa → unitInterval) (F S : Finset kappa) :
    0 ≤ atomWeight p F S := measureReal_nonneg

theorem sum_atomWeight [DecidableEq kappa] (p : kappa → unitInterval) (F : Finset kappa) :
    ∑ S ∈ F.powerset, atomWeight p F S = 1 :=
  TargetExt.sum_real_localCylinder p F

/-- **The atom formula (5.3).**  This is the exact pre-examination integral.  It uses no quotient
and hence remains valid on atoms of probability zero. -/
theorem prob_dynamic_step_eq_sum [DecidableEq kappa] [DecidableEq V]
    (p : kappa → unitInterval) (h : FRDom.Transcript kappa V) (z : V) (F : Finset kappa)
    (hfresh : Disjoint F h.inspected) (B : FRDom.Transcript kappa V → Set (Set kappa))
    (hBm : ∀ k, MeasurableSet (B k)) :
    h.prob p {omega | omega ∈ B (h.step z F true omega)} =
      ∑ S ∈ F.powerset,
        atomWeight p F S *
          (h.step z F true (↑S : Set kappa)).prob p (B (h.step z F true (↑S : Set kappa))) := by
  classical
  let X : Set (Set kappa) := {omega | omega ∈ B (h.step z F true omega)}
  have hXm : MeasurableSet X := by
    unfold X
    rw [h.setOf_step_eq_biUnion (fun k omega => omega ∈ B k)]
    exact Finset.measurableSet_biUnion _ fun S _ =>
      (measurableSet_localCylinder F.finite_toSet.countable _).inter (hBm _)
  rw [show h.prob p {omega | omega ∈ B (h.step z F true omega)} = h.prob p X by rfl,
    FRDom.Transcript.prob_eq, pinnedProb,
    TargetExt.real_eq_sum_inter_localCylinder p F ((measurable_substitute _ _) hXm)]
  apply Finset.sum_congr rfl
  intro S hSF
  have hSF' : S ⊆ F := Finset.mem_powerset.1 hSF
  let omegaS : Set kappa := (↑S : Set kappa)
  let k := h.step z F true omegaS
  have hfreeze : ∀ xi ∈ localCylinder (↑F : Set kappa) omegaS,
      h.step z F true (substitute (↑h.inspected : Set kappa) h.state xi) = k := by
    intro xi hxi
    apply h.step_congr
    intro x hx
    have hxI : x ∉ (↑h.inspected : Set kappa) := fun hxI =>
      Finset.disjoint_left.1 hfresh hx (Finset.mem_coe.1 hxI)
    rw [mem_substitute_of_notMem _ hxI]
    exact hxi x (Finset.mem_coe.2 hx)
  have hXeq :
      (substitute (↑h.inspected : Set kappa) h.state ⁻¹' X) ∩
          localCylinder (↑F : Set kappa) omegaS =
        (substitute (↑h.inspected : Set kappa) h.state ⁻¹' B k) ∩
          localCylinder (↑F : Set kappa) omegaS := by
    ext xi
    simp only [Set.mem_inter_iff, Set.mem_preimage, X, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxi, hcyl⟩
      exact ⟨hfreeze xi hcyl ▸ hxi, hcyl⟩
    · rintro ⟨hxi, hcyl⟩
      exact ⟨hfreeze xi hcyl ▸ hxi, hcyl⟩
  rw [hXeq,
    TargetExt.real_inter_localCylinder_eq_mul_pinnedProb p F omegaS
      ((measurable_substitute _ _) (hBm k)),
    ← Stopped.step_prob_eq_pinnedProb h p z F true omegaS (B k) hfresh]
  rfl

/-- Averaging a uniform upper bound over the incoming atoms introduces no loss. -/
theorem prob_dynamic_step_le [DecidableEq kappa] [DecidableEq V]
    (p : kappa → unitInterval) (h : FRDom.Transcript kappa V) (z : V) (F : Finset kappa)
    (hfresh : Disjoint F h.inspected) (B : FRDom.Transcript kappa V → Set (Set kappa))
    (hBm : ∀ k, MeasurableSet (B k)) {c : ℝ}
    (hbound : ∀ omega : Set kappa,
      (h.step z F true omega).prob p (B (h.step z F true omega)) ≤ c) :
    h.prob p {omega | omega ∈ B (h.step z F true omega)} ≤ c := by
  classical
  rw [prob_dynamic_step_eq_sum p h z F hfresh B hBm]
  calc
    ∑ S ∈ F.powerset,
          atomWeight p F S *
            (h.step z F true (↑S : Set kappa)).prob p (B (h.step z F true (↑S : Set kappa)))
        ≤ ∑ S ∈ F.powerset, atomWeight p F S * c := by
          exact Finset.sum_le_sum fun S _ =>
            mul_le_mul_of_nonneg_left (hbound (↑S : Set kappa)) (atomWeight_nonneg p F S)
    _ = c := by rw [← Finset.sum_mul, sum_atomWeight p F, one_mul]

/-! ## The stopped proof, factored before the corridor estimate -/

section StoppedFactor

variable {d : ℕ} [NeZero d]

/-- The event `G` in (5.5): every tested level is both crossed and bad. -/
def crossedBad (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z y : Site 2)
    (i : Fin d) (sigma : ℤ) (q : unitInterval) (deltaC : ℝ) (K : ℕ) :
    Set (SiteConfig (Site d)) :=
  Budget.allBad (fun j =>
    Stopped.crossEvent d r t s h z i sigma j ∩
      Stopped.levelBad d r t s h z y i sigma q deltaC j) K

theorem measurableSet_allBad {iota : Type*} (bad : ℕ → Set (Set iota))
    (hbad : ∀ j, MeasurableSet (bad j)) : ∀ K, MeasurableSet (Budget.allBad bad K) := by
  intro K
  induction K with
  | zero => exact MeasurableSet.univ
  | succ K ih => exact ih.inter (hbad K)

theorem measurableSet_levelBad (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d)
    (z y : Site 2) (i : Fin d) (sigma : ℤ) (q : unitInterval) (deltaC : ℝ) (j : ℕ) :
    MeasurableSet (Stopped.levelBad d r t s h z y i sigma q deltaC j) :=
  (Stopped.determinedBy_levelBad d r t s h z y i sigma q deltaC j).measurableSet_of_finset

theorem measurableSet_crossedBad (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d)
    (z y : Site 2) (i : Fin d) (sigma : ℤ) (q : unitInterval) (deltaC : ℝ) (K : ℕ) :
    MeasurableSet (crossedBad d r t s h z y i sigma q deltaC K) := by
  apply measurableSet_allBad
  intro j
  exact (Stopped.measurableSet_crossEvent d r t s h z i sigma j).inter
    (measurableSet_levelBad d r t s h z y i sigma q deltaC j)

/-- Equation (5.7), with the corridor hypothesis absent.  The proof is the exhaustion part of
`Stopped.prob_noGoodLevel_le`, ending at `Budget.pinnedProb_allBad_le_pow`. -/
theorem prob_crossedBad_le_pow {r t s K : ℕ} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : ℤ} {q : unitInterval} {deltaC delta2 : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hdelta2 : delta2 ≤ 1)
    (hone : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state omega ∈
          Stopped.levelBad d r t s h z y i sigma q deltaC j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
          (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - delta2) :
    h.prob (fun _ : Site d => q) (crossedBad d r t s h z y i sigma q deltaC K) ≤
      (1 - delta2) ^ K := by
  classical
  let p : Site d → unitInterval := fun _ => q
  let bad : ℕ → Set (SiteConfig (Site d)) := fun j =>
    Stopped.crossEvent d r t s h z i sigma j ∩
      Stopped.levelBad d r t s h z y i sigma q deltaC j
  have hstep : ∀ k, k < K →
      pinnedProb p (↑h.inspected : Set (Site d)) h.state
          (Budget.allBad bad k ∩ bad k) ≤
        (1 - delta2) *
          pinnedProb p (↑h.inspected : Set (Site d)) h.state (Budget.allBad bad k) := by
    intro k hk
    have hEq : Budget.allBad bad k ∩ bad k =
        (Budget.allBad bad k ∩
            Stopped.levelBad d r t s h z y i sigma q deltaC k) ∩
          Stopped.crossEvent d r t s h z i sigma k := by
      ext omega
      simp only [bad, Set.mem_inter_iff]
      tauto
    have hCdet : DeterminedBy
        (Budget.allBad bad k ∩ Stopped.levelBad d r t s h z y i sigma q deltaC k)
        ((↑h.inspected : Set (Site d)) ∪
          ↑(Stopped.revealSet d r t s h z i sigma k)) := by
      refine DeterminedBy.inter (Stopped.determinedBy_allBad bad _ k fun j hj => ?_) ?_
      · refine DeterminedBy.inter ?_ ?_
        · refine (Stopped.determinedBy_crossEvent d r t s h z i sigma j).mono ?_
          intro x hx
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
          · exact Or.inl (Finset.mem_coe.2 hx)
          · by_cases hxI : x ∈ h.inspected
            · exact Or.inl (Finset.mem_coe.2 hxI)
            · refine Or.inr (Finset.mem_coe.2 ?_)
              rw [Stopped.revealSet, Finset.mem_sdiff]
              exact ⟨Stopped.stub_mono hsigma
                (Nat.mul_le_mul_left _ (by omega)) hx, hxI⟩
        · refine (Stopped.determinedBy_levelBad d r t s h z y i sigma q deltaC j).mono ?_
          intro x hx
          exact Or.inr (Finset.mem_coe.2
            (Stopped.revealSet_mono hsigma (by omega) (Finset.mem_coe.1 hx)))
      · exact (Stopped.determinedBy_levelBad d r t s h z y i sigma q deltaC k).mono
          fun x hx => Or.inr hx
    have htower := Stopped.prob_inter_le_of_step_prob_le h p z
      (Stopped.revealSet d r t s h z i sigma k) true
      (Stopped.revealSet_fresh d r t s h z i sigma k)
      (Stopped.measurableSet_crossEvent d r t s h z i sigma k) hCdet
      (c := 1 - delta2) (fun omega homegaC => hone k hk omega homegaC.2)
    have hmono :
        h.prob p (Budget.allBad bad k ∩
            Stopped.levelBad d r t s h z y i sigma q deltaC k) ≤
          h.prob p (Budget.allBad bad k) :=
      ProbInv.prob_mono h p Set.inter_subset_left
    have h0 : (0 : ℝ) ≤ 1 - delta2 := by linarith
    calc
      pinnedProb p (↑h.inspected : Set (Site d)) h.state
          (Budget.allBad bad k ∩ bad k) =
          h.prob p ((Budget.allBad bad k ∩
              Stopped.levelBad d r t s h z y i sigma q deltaC k) ∩
            Stopped.crossEvent d r t s h z i sigma k) := by rw [hEq]; rfl
      _ ≤ (1 - delta2) * h.prob p (Budget.allBad bad k ∩
          Stopped.levelBad d r t s h z y i sigma q deltaC k) := htower
      _ ≤ (1 - delta2) * h.prob p (Budget.allBad bad k) :=
        mul_le_mul_of_nonneg_left hmono h0
  simpa only [crossedBad, bad, p, FRDom.Transcript.prob_eq] using
    Budget.pinnedProb_allBad_le_pow p (↑h.inspected : Set (Site d)) h.state bad K delta2
      hdelta2 hstep

/-- Equation (5.6), separated from every probabilistic corridor estimate. -/
theorem noGoodLevel_subset_corridor_compl_union_crossedBad
    {r t s A K : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : ℤ}
    {q : unitInterval} {deltaC : ℝ}
    (hsigma : sigma = 1 ∨ sigma = -1) (hs : 0 < s) (hfar : 10 * s * K ≤ 13 * r)
    (hsep : ∀ u ∈ h.inspected,
      ∀ v ∈ Stopped.stub (MacroExp.ctr d r z) i sigma r t A,
        (zdGraph d).Adj u v →
        (5 * r : ℤ) < Stopped.lam (MacroExp.ctr d r z) i sigma v →
        Stopped.lam (MacroExp.ctr d r z) i sigma u ≤ 5 * r)
    (ho : (MacroExp.emb 0 : Site d) ∉
      Stopped.stub (MacroExp.ctr d r z) i sigma r t A) :
    Stopped.noGoodLevel d r t s h z y i sigma q deltaC K ⊆
      (Stopped.corridorEvent d r t A h z i sigma)ᶜ ∪
        crossedBad d r t s h z y i sigma q deltaC K := by
  classical
  let bad : ℕ → Set (SiteConfig (Site d)) := fun j =>
    Stopped.crossEvent d r t s h z i sigma j ∩
      Stopped.levelBad d r t s h z y i sigma q deltaC j
  have hcross : ∀ j, j < K →
      Stopped.corridorEvent d r t A h z i sigma ⊆
        Stopped.crossEvent d r t s h z i sigma j := by
    intro j hj omega homega
    obtain ⟨b, hbT, hconn⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 homega
    have hconn' : omega ∈ connWithin (zdGraph d)
        ((↑h.inspected : Set (Site d)) ∪
          ↑(Stopped.stub (MacroExp.ctr d r z) i sigma r t A))
        (MacroExp.emb 0) b := by
      rwa [Finset.coe_union] at hconn
    have hmul : 10 * s * (j + 1) ≤ 10 * s * K := Nat.mul_le_mul_left _ (by omega)
    have hm : 5 * r + 10 * s * (j + 1) ≤ 18 * r := by omega
    have hbdeep := Stopped.mem_deep_of_mem_stubTarget
      (m := 10 * s * (j + 1)) hm (Finset.mem_coe.1 hbT)
    have h1 : 1 < 10 * s * (j + 1) := by
      have : 10 * 1 * 1 ≤ 10 * s * (j + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 10 hs) (by omega)
      omega
    have hcr := Stopped.connWithinSet_stubFace_of_conn hsigma h1 hsep ho hbdeep hconn'
    rw [Stopped.crossEvent, Finset.coe_union]
    exact hcr
  intro omega homega
  by_cases hc : omega ∈ Stopped.corridorEvent d r t A h z i sigma
  · refine Or.inr ?_
    rw [crossedBad, Stopped.mem_allBad_iff]
    intro j hj
    exact ⟨hcross j hj hc, (Stopped.mem_allBad_iff _ K omega).1 homega j hj⟩
  · exact Or.inl hc

end StoppedFactor

/-! ## The pre-examination incoming read -/

section Incoming

variable {d : ℕ} [NeZero d]

/-- Only the unread part of the incoming edge region is examined. -/
def incomingRegion (d r t : ℕ) (h : MacroExp.Tr d) (w z : Site 2) : Finset (Site d) :=
  MacroExp.E d r t w z \ h.inspected

/-- The incoming examination, before any stopped stub level is read. -/
def incomingTr (d r t : ℕ) (h : MacroExp.Tr d) (w z : Site 2)
    (omega : SiteConfig (Site d)) : MacroExp.Tr d :=
  h.step z (incomingRegion d r t h w z) true omega

/-- Freshness is satisfiable by construction; it is not a hypothesis of the main theorem. -/
theorem incomingRegion_fresh (d r t : ℕ) (h : MacroExp.Tr d) (w z : Site 2) :
    Disjoint (incomingRegion d r t h w z) h.inspected :=
  Finset.sdiff_disjoint

/-- Every incoming atom has the same inspected set. -/
theorem incomingTr_inspected (d r t : ℕ) (h : MacroExp.Tr d) (w z : Site 2)
    (omega : SiteConfig (Site d)) :
    (incomingTr d r t h w z omega).inspected =
      h.inspected ∪ MacroExp.E d r t w z := by
  simp only [incomingTr, FRDom.Transcript.step_inspected, incomingRegion,
    Finset.union_sdiff_self_eq_union]

/-- The incoming read does not make pendingness depend on the atom when its anchor is already
occupied. -/
theorem incomingTr_openV (d r t : ℕ) (h : MacroExp.Tr d) (w z : Site 2)
    (hz : z ∈ h.openV) (omega : SiteConfig (Site d)) :
    (incomingTr d r t h w z omega).openV = h.openV := by
  simp [incomingTr, hz]

theorem incomingTr_closedV (d r t : ℕ) (h : MacroExp.Tr d) (w z : Site 2)
    (omega : SiteConfig (Site d)) :
    (incomingTr d r t h w z omega).closedV = h.closedV := by
  simp [incomingTr]

/-- The retained narrow event at the pre-examination transcript, with `A = 17 r`. -/
def narrowCorridor (d r t : ℕ) [NeZero d] (h : MacroExp.Tr d) (w z : Site 2)
    (i : Fin d) (sigma : ℤ) : Set (SiteConfig (Site d)) :=
  connWithinSet (zdGraph d)
    (↑(h.inspected ∪ MacroExp.E d r t w z ∪
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
    (MacroExp.emb 0)
    (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))

theorem measurableSet_narrowCorridor (d r t : ℕ) [NeZero d] (h : MacroExp.Tr d)
    (w z : Site 2) (i : Fin d) (sigma : ℤ) :
    MeasurableSet (narrowCorridor d r t h w z i sigma) :=
  measurableSet_connWithinSet _ _ _ _

/-- A retained bound of the requested size cannot be vacuous through an empty success event. -/
theorem narrowCorridor_nonempty_of_bound (d r t : ℕ) [NeZero d]
    (h : MacroExp.Tr d) (w z : Site 2) (i : Fin d) (sigma : ℤ) (q : unitInterval)
    {rho : ℝ} (hrho1 : rho ≤ 1)
    (hcorr_narrow : 1 - rho / 32 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) :
          Set (Site d)))) :
    (narrowCorridor d r t h w z i sigma).Nonempty := by
  by_contra hnone
  have hempty : narrowCorridor d r t h w z i sigma = ∅ := by
    ext omega
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun homega => hnone ⟨omega, homega⟩
  have hzero : h.prob (fun _ : Site d => q) (narrowCorridor d r t h w z i sigma) = 0 := by
    rw [hempty, FRDom.Transcript.prob_eq, pinnedProb_emptyEvent]
  rw [show connWithinSet (zdGraph d)
      (↑(h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
      (MacroExp.emb 0)
      (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d)) =
        narrowCorridor d r t h w z i sigma by rfl, hzero] at hcorr_narrow
  linarith

/-- Equation (5.8): the stopped corridor event is independent of the incoming atom. -/
theorem corridorEvent_incomingTr_eq (d r t : ℕ) [NeZero d] (h : MacroExp.Tr d)
    (w z : Site 2) (i : Fin d) (sigma : ℤ) (omega : SiteConfig (Site d)) :
    Stopped.corridorEvent d r t (17 * r) (incomingTr d r t h w z omega) z i sigma =
      narrowCorridor d r t h w z i sigma := by
  rw [Stopped.corridorEvent, narrowCorridor, incomingTr_inspected]

/-- The dynamic event `N-hat` of (5.9). -/
def outerNoGoodLevel (d r t s K : ℕ) [NeZero d] (h : MacroExp.Tr d)
    (w z y : Site 2) (i : Fin d) (sigma : ℤ) (q : unitInterval) (deltaC : ℝ) :
    Set (SiteConfig (Site d)) :=
  {omega | omega ∈ Stopped.noGoodLevel d r t s (incomingTr d r t h w z omega)
    z y i sigma q deltaC K}

/-- The dynamic exhaustion event `G-hat` of (5.9). -/
def outerCrossedBad (d r t s K : ℕ) [NeZero d] (h : MacroExp.Tr d)
    (w z y : Site 2) (i : Fin d) (sigma : ℤ) (q : unitInterval) (deltaC : ℝ) :
    Set (SiteConfig (Site d)) :=
  {omega | omega ∈ crossedBad d r t s (incomingTr d r t h w z omega)
    z y i sigma q deltaC K}

/-- The target is nonempty; no target-nonemptiness assumption is hidden in the tower. -/
theorem narrowTarget_nonempty (r t : ℕ) (z : Site 2) (i : Fin d) {sigma : ℤ}
    (hsigma : sigma = 1 ∨ sigma = -1) :
    (Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)).Nonempty :=
  Stopped.stubTarget_nonempty _ i hsigma (by omega)

/-- The target lies in the allowed set, ruling out the empty/unreachable-by-containment failure. -/
theorem narrowTarget_subset_allowed (r t : ℕ) (h : MacroExp.Tr d) (w z : Site 2)
    (i : Fin d) (sigma : ℤ) :
    Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r) ⊆
      h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r) :=
  le_trans (Finset.filter_subset _ _) Finset.subset_union_right

/-- The target contains at least two sites when `r > 0`; it is not a designated-site event. -/
theorem one_lt_card_narrowTarget {r t : ℕ} (hr : 0 < r) (z : Site 2) (i : Fin d)
    {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1) :
    1 < (Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)).card := by
  classical
  let c := MacroExp.ctr d r z
  let x18 : Site d := c + Pi.single i (sigma * ((5 * r + 13 * r : ℕ) : ℤ))
  let x19 : Site d := c + Pi.single i (sigma * ((5 * r + 14 * r : ℕ) : ℤ))
  have hmem (m : ℕ) (hm1 : 18 * r ≤ 5 * r + m) (hm2 : m ≤ 17 * r) :
      c + Pi.single i (sigma * ((5 * r + m : ℕ) : ℤ)) ∈
        Stopped.stubTarget c i sigma r t (17 * r) := by
    rw [Stopped.stubTarget, Finset.mem_filter]
    refine ⟨Stopped.stub_mono hsigma hm2
      (Finset.mem_filter.1 (Stopped.axial_mem_stubFace c i hsigma r t m)).1, ?_⟩
    have hlam := (Stopped.mem_stubFace hsigma).1
      (Stopped.axial_mem_stubFace c i hsigma r t m)
    rw [hlam.1]
    exact_mod_cast hm1
  have hx18 : x18 ∈ Stopped.stubTarget c i sigma r t (17 * r) := by
    exact hmem (13 * r) (by omega) (by omega)
  have hx19 : x19 ∈ Stopped.stubTarget c i sigma r t (17 * r) := by
    exact hmem (14 * r) (by omega) (by omega)
  have hne : x18 ≠ x19 := by
    intro heq
    have hi := congrFun heq i
    simp only [x18, x19, Pi.add_apply, Pi.single_eq_same] at hi
    rcases hsigma with rfl | rfl <;> simp only [one_mul, neg_mul] at hi <;>
      push_cast at hi <;> omega
  exact Finset.one_lt_card.2 ⟨x18, hx18, x19, hx19, hne⟩

/-- A union bound under a transcript's pinned law. -/
theorem prob_union_le (h : FRDom.Transcript kappa V) (p : kappa → unitInterval)
    (A B : Set (Set kappa)) :
    h.prob p (A ∪ B) ≤ h.prob p A + h.prob p B := by
  simp only [FRDom.Transcript.prob_eq, pinnedProb, Set.preimage_union]
  exact measureReal_union_le _ _

/-!
**The denominator-free pre-examination tower.**

`hcorr_narrow` is deliberately an explicit named hypothesis, with exactly the narrow event and
strict success-probability shape supplied by the corridor refactor.  `hone` is the atom-indexed
non-corridor input from the stopped proof.  The two frozen-set hypotheses are geometric, not
conditional probability estimates.  The incoming read itself is fresh by `incomingRegion_fresh`.

Satisfiability of every binder is visible rather than hidden in an interface: `hd` supplies the
`NeZero d` instance; `hr`, `hs`, and `hfar` are compatible after choosing `r` above `s*K`; the
signed-coordinate binders are realized by an ordinary oriented lattice edge; `hthin` and
`hfresh_out` are the frozen-base geometry before the outgoing read; and the error/level-count
binders are jointly witnessed by `numerical_hypotheses_satisfiable`.  The two genuinely
probabilistic binders are exactly the named inputs advertised above, not consequences silently
claimed by this tower.  The cheap non-vacuity checks are `narrowCorridor_nonempty_of_bound`,
`narrowTarget_nonempty`, `narrowTarget_subset_allowed`, and `one_lt_card_narrowTarget`.
-/
theorem prob_outerNoGoodLevel_le
    {r t s K : ℕ} {h : MacroExp.Tr d} {w z y : Site 2} {i : Fin d} {sigma : ℤ}
    {q : unitInterval} {deltaC e rho : ℝ}
    (hd : 3 ≤ d) (hr : 0 < r) (hs : 0 < s) (hfar : 10 * s * K ≤ 13 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) (hy : y ≠ 0)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh_out : Disjoint (h.inspected ∪ MacroExp.E d r t w z) (MacroExp.E d r t z y))
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) (he0 : 0 < e) (he_beta : e ≤ beta rho d)
    (hpow : (1 - f e) ^ K ≤ rho / 32)
    (hcorr_narrow : 1 - rho / 32 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) :
          Set (Site d))))
    (hone : ∀ omega : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
      substitute
          (↑(incomingTr d r t h w z omega).inspected : Set (Site d))
          (incomingTr d r t h w z omega).state xi ∈
        Stopped.levelBad d r t s (incomingTr d r t h w z omega)
          z y i sigma q deltaC j →
      (Stopped.levelTr d r t s (incomingTr d r t h w z omega)
          z i sigma j xi).prob (fun _ : Site d => q)
        (Stopped.crossEvent d r t s (incomingTr d r t h w z omega)
          z i sigma j) ≤ 1 - f e) :
    h.prob (fun _ : Site d => q)
      (outerNoGoodLevel d r t s K h w z y i sigma q deltaC) ≤ rho / 16 := by
  classical
  let F := incomingRegion d r t h w z
  let p : Site d → unitInterval := fun _ => q
  let G : MacroExp.Tr d → Set (SiteConfig (Site d)) := fun k =>
    crossedBad d r t s k z y i sigma q deltaC K
  have hd2 : 2 ≤ d := by omega
  have hdelta2 : f e ≤ 1 := f_le_one_of_le_beta hrho0 hrho1 he0 he_beta
  have hsep : ∀ omega : SiteConfig (Site d),
      ∀ u ∈ (incomingTr d r t h w z omega).inspected,
      ∀ v ∈ Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r),
        (zdGraph d).Adj u v →
        (5 * r : ℤ) < Stopped.lam (MacroExp.ctr d r z) i sigma v →
        Stopped.lam (MacroExp.ctr d r z) i sigma u ≤ 5 * r := by
    intro omega
    apply Stopped.sep_of_fresh hd2 hr (show 17 * r ≤ 17 * r by omega)
      hsigma hemb
    · simpa only [incomingTr_inspected] using hthin
    · simpa only [incomingTr_inspected] using hfresh_out
  have ho : (MacroExp.emb 0 : Site d) ∉
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r) :=
    Stopped.origin_notMem_stub hd2 hr (show 17 * r ≤ 17 * r by omega) hsigma hemb hy
  have hGatom : ∀ omega : SiteConfig (Site d),
      (incomingTr d r t h w z omega).prob p
          (G (incomingTr d r t h w z omega)) ≤ (1 - f e) ^ K := by
    intro omega
    exact prob_crossedBad_le_pow hsigma hdelta2
      (fun j hj xi hxi => hone omega j hj xi hxi)
  have hG : h.prob p (outerCrossedBad d r t s K h w z y i sigma q deltaC) ≤
      (1 - f e) ^ K := by
    have htower := prob_dynamic_step_le p h z F
      (by simpa only [F] using incomingRegion_fresh d r t h w z) G
      (fun k => measurableSet_crossedBad d r t s k z y i sigma q deltaC K)
      (c := (1 - f e) ^ K) hGatom
    simpa only [outerCrossedBad, G, F, p, incomingTr] using htower
  have hsubset : outerNoGoodLevel d r t s K h w z y i sigma q deltaC ⊆
      (narrowCorridor d r t h w z i sigma)ᶜ ∪
        outerCrossedBad d r t s K h w z y i sigma q deltaC := by
    intro omega homega
    have hlocal := noGoodLevel_subset_corridor_compl_union_crossedBad
      hsigma hs hfar (hsep omega) ho homega
    rcases hlocal with hcorr | hbad
    · exact Or.inl (by rwa [corridorEvent_incomingTr_eq] at hcorr)
    · exact Or.inr hbad
  have hcorr_compl : h.prob p (narrowCorridor d r t h w z i sigma)ᶜ ≤ rho / 32 := by
    have hm := measurableSet_narrowCorridor d r t h w z i sigma
    rw [FRDom.Transcript.prob_eq, pinnedProb_compl _ _ _ hm,
      ← FRDom.Transcript.prob_eq]
    simpa only [narrowCorridor, p] using (show
      1 - h.prob (fun _ : Site d => q) (narrowCorridor d r t h w z i sigma) ≤ rho / 32 by
        change 1 - h.prob (fun _ : Site d => q)
          (connWithinSet (zdGraph d)
            (↑(h.inspected ∪ MacroExp.E d r t w z ∪
              Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
            (MacroExp.emb 0)
            (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) :
              Set (Site d))) ≤ rho / 32
        linarith)
  calc
    h.prob p (outerNoGoodLevel d r t s K h w z y i sigma q deltaC)
        ≤ h.prob p ((narrowCorridor d r t h w z i sigma)ᶜ ∪
          outerCrossedBad d r t s K h w z y i sigma q deltaC) :=
      ProbInv.prob_mono h p hsubset
    _ ≤ h.prob p (narrowCorridor d r t h w z i sigma)ᶜ +
          h.prob p (outerCrossedBad d r t s K h w z y i sigma q deltaC) :=
      prob_union_le h p _ _
    _ ≤ rho / 32 + rho / 32 := add_le_add hcorr_compl (hG.trans hpow)
    _ = rho / 16 := by ring

/-- The same estimate for the complement of the dynamic corrected direction event. -/
theorem prob_outerDirectionFailure_le
    {r t s K : ℕ} {h : MacroExp.Tr d} {w z y : Site 2} {i : Fin d} {sigma : ℤ}
    {q : unitInterval} {deltaC rho : ℝ}
    (hbound : h.prob (fun _ : Site d => q)
      (outerNoGoodLevel d r t s K h w z y i sigma q deltaC) ≤ rho / 16) :
    h.prob (fun _ : Site d => q)
      {omega | omega ∉ Stopped.directionEvent d r t s (incomingTr d r t h w z omega)
        z y i sigma q deltaC K} ≤ rho / 16 := by
  refine (ProbInv.prob_mono h _ ?_).trans hbound
  intro omega homega
  change omega ∈ Stopped.noGoodLevel d r t s (incomingTr d r t h w z omega)
    z y i sigma q deltaC K
  by_contra hnot
  exact homega (Or.inr hnot)

/-! ## Cheap non-vacuity checks for the numerical and freshness hypotheses -/

/-- The numerical scheme is jointly satisfiable: `e = beta`, `delta2 = f e`, and a finite level
count exists. -/
theorem numerical_hypotheses_satisfiable (d : ℕ) {rho : ℝ}
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ e : ℝ, 0 < e ∧ e ≤ beta rho d ∧ f e ≤ 1 ∧
      ∃ K : ℕ, (1 - f e) ^ K ≤ rho / 32 := by
  refine ⟨beta rho d, beta_pos hrho0 d, le_rfl,
    f_le_one_of_le_beta hrho0 hrho1 (beta_pos hrho0 d) le_rfl, ?_⟩
  obtain ⟨K, hK⟩ := Budget.exists_levelCount rho (f (beta rho d)) hrho0
    (f_pos (beta_pos hrho0 d))
    (f_le_one_of_le_beta hrho0 hrho1 (beta_pos hrho0 d) le_rfl)
  exact ⟨K, hK.le⟩

#print axioms KNAll.Site.AtomTower.prob_dynamic_step_eq_sum
#print axioms KNAll.Site.AtomTower.prob_outerNoGoodLevel_le
#print axioms KNAll.Site.AtomTower.prob_outerDirectionFailure_le
#print axioms KNAll.Site.AtomTower.numerical_hypotheses_satisfiable

end Incoming

end KNAll.Site.AtomTower

end
