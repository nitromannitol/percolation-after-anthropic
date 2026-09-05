import Hypergraph.CoreTaggedCover
import Hypergraph.CorePostGeometry

/-!
# Initial core reservations

The empty live list in `CoreTaggedCover.holds_start` is a valid cover of the sites inspected at
the start, but it does not establish the probabilistic frontier invariant.  This file identifies
the missing initial statement exactly and proves it from the recorded initial long-box estimate
followed by the same longitudinal target-extension family used after an accepted step.

In particular, no generic fresh-corridor theorem is applied at the root: `Q 0` has already been
read there.  The special initial argument works under the pinned start law, uses the fresh part
`E 0 y`, and regards `Q 0` only as a recorded-open source region.
-/

noncomputable section

namespace KNAll.Site.CoreInitial

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- The exact probabilistic input needed to initialize the one-owner frontier invariant. -/
def InitialCoreBounds (r t : Nat) (q : unitInterval) (eps : Real) : Prop :=
  ∀ y ∈ MacroExp.pending d (MacroExp.start d r t) 0,
    CoreRes.Bound r t q eps (MacroExp.start d r t) 0 y

/-- At the start transcript, being a frontier vertex is exactly being a pending neighbour of the
unique open macro vertex `0`. -/
theorem frontier_start_iff_pending (r t : Nat) (y : Site 2) :
    CoreFrontier.Frontier (MacroExp.start d r t) y ↔
      y ∈ MacroExp.pending d (MacroExp.start d r t) 0 := by
  constructor
  · rintro ⟨hyu, u, hu, huy⟩
    have hu0 : u = 0 := by simpa [MacroExp.start] using hu
    subst u
    exact (MacroExp.mem_pending (d := d)).2 ⟨huy, hyu⟩
  · intro hy
    have hp := (MacroExp.mem_pending (d := d)).1 hy
    exact ⟨hp.2, 0, by simp [MacroExp.start], hp.1⟩

/-- Initial core bounds are neither more nor less than the missing start instance of the frontier
invariant. -/
theorem invariant_start_iff_initialCoreBounds (r t : Nat) (q : unitInterval) (eps : Real) :
    CoreFrontier.Invariant r t q eps (MacroExp.start d r t) ↔
      InitialCoreBounds (d := d) r t q eps := by
  constructor
  · intro hI y hy
    obtain ⟨u, hu, hyu, hb⟩ := hI y ((frontier_start_iff_pending r t y).2 hy)
    have hu0 : u = 0 := by simpa [MacroExp.start] using hu
    subst u
    exact hb
  · intro hb y hy
    have hyp := (frontier_start_iff_pending r t y).1 hy
    exact ⟨0, by simp [MacroExp.start], hyp, hb y hyp⟩

/-- The deterministic tagged cover and the probabilistic frontier invariant can both be started
once—and only once—the genuine initial core bounds have been supplied. -/
theorem initialized_of_initialCoreBounds (r t : Nat) (q : unitInterval) (eps : Real)
    (hb : InitialCoreBounds (d := d) r t q eps) :
    CoreTaggedCover.Holds r t q eps (MacroExp.start d r t) ∧
      CoreFrontier.Invariant r t q eps (MacroExp.start d r t) := by
  exact ⟨CoreTaggedCover.holds_start d r t q eps,
    (invariant_start_iff_initialCoreBounds r t q eps).2 hb⟩

/-- The target of the recorded initial long-box estimate does not contain the radius-`2r` core.
Consequently the desired reservation cannot be obtained from H1 by target monotonicity alone. -/
theorem coreTarget_not_subset_initialInnerBox
    (hd : 3 ≤ d) (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) (y : Site 2) :
    ¬ CoreRes.target (d := d) C.corridor y ⊆
      LongBox.innerBox C (MacroExp.ctr d C.corridor y) := by
  let i : Fin d := ⟨0, by omega⟩
  let c := MacroExp.ctr d C.corridor y
  let x : Site d := c + Pi.single i (2 * (C.corridor : Int))
  have hxT : x ∈ CoreRes.target (d := d) C.corridor y := by
    rw [CoreRes.target, CorrMove.mem_cube]
    intro j
    by_cases hji : j = i
    · subst j
      simp only [x, c, Pi.add_apply, Pi.single_eq_same]
      have hr : (0 : Int) ≤ C.corridor := by positivity
      rw [add_sub_cancel_left, abs_of_nonneg (by omega)]
      omega
    · simp only [x, c, Pi.add_apply, Pi.single_eq_of_ne hji, add_zero, sub_self, abs_zero]
      positivity
  intro hsub
  have hxB := hsub hxT
  rw [LongBox.innerBox, Corridor.Ibox, Corridor.mem_rbox] at hxB
  have hi := (hxB i).2
  have hi0 : i.val < 2 := by simp only [i]; omega
  simp only [x, c, Pi.add_apply, Pi.single_eq_same, Corridor.ρI, Corridor.ρO,
    Corridor.ρD, Corridor.scalesOf, MacroExp.rad, if_pos hi0] at hi
  have hr := hwf.corridor_ge_44
  push_cast at hi
  omega

/-! ## The special root target-extension argument -/

/-- The precise finite-window premise needed to turn the already recorded initial long-box
estimate in direction `y` into a radius-`2r` core reservation.  It is the genuine target-aware
post-window family, not the old intermediate sphere window. -/
def InitialWindowBounds (C : LeftImp2.Certificate2 d) (q : unitInterval) (s : Nat) : Prop :=
  ∀ y ∈ MacroExp.pending d (MacroExp.start d C.corridor C.halfWidth) 0,
    ∀ (i : Fin d) (sigma : Int), sigma = 1 ∨ sigma = -1 →
      (MacroExp.emb y : Site d) = Pi.single i sigma →
      CorePost.CorePostWindowBound C q (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0
        ((MacroExp.start d C.corridor C.halfWidth).inspected ∪
          MacroExp.E d C.corridor C.halfWidth 0 y) y

/-- The geometric premises used below are simultaneously realizable with the certificate's own
root geometry.  Taking one longitudinal stage and `s = levels + 1` suffices. -/
theorem exists_initial_scale_clearance (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) :
    ∃ s K : Nat, 0 < K ∧
      10 * s * K ≤ 13 * C.corridor ∧
      C.levels + 1 ≤ 10 * s ∧
      C.levels + 1 ≤ 3 * C.corridor ∧
      5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * C.corridor ∧
      C.faceTarget + 1 ≤ 2 * C.corridor ∧
      C.faceTarget + 1 ≤ C.halfWidth := by
  let L := C.levels
  let F := C.faceTarget
  let r := C.corridor
  have hL0 : 0 < L := by simpa only [L] using hwf.levels_pos
  have hL : 1 ≤ L := by omega
  have hrLF : L * (2 * F + 2) ≤ r := by
    simpa only [L, F, r] using hwf.corridor_ge
  have hrL : 2 * L ≤ r := by
    calc
      2 * L = L * 2 := by omega
      _ ≤ L * (2 * F + 2) := Nat.mul_le_mul_left L (by omega)
      _ ≤ r := hrLF
  have hrF : 2 * F + 2 ≤ r := by
    calc
      2 * F + 2 = 1 * (2 * F + 2) := by omega
      _ ≤ L * (2 * F + 2) := Nat.mul_le_mul_right (2 * F + 2) hL
      _ ≤ r := hrLF
  have hr44 : 44 ≤ r := by simpa only [r] using hwf.corridor_ge_44
  have htF : F + 1 ≤ C.halfWidth := by
    have hinner := hwf.innerRadius_ge.trans (min_le_right C.corridor C.halfWidth)
    change L + 2 * F + 1 ≤ C.halfWidth at hinner
    omega
  refine ⟨L + 1, 1, by omega, ?_, by omega, ?_, ?_, by omega, htF⟩
  · omega
  · omega
  · omega

/-- The concrete scale choice used by the root bridge.  This spelling is convenient for consumers:
it leaves no auxiliary numerical witness to choose. -/
theorem canonical_initial_scale_clearance (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) :
    0 < (1 : Nat) ∧
      10 * (C.levels + 1) * 1 ≤ 13 * C.corridor ∧
      C.levels + 1 ≤ 10 * (C.levels + 1) ∧
      C.levels + 1 ≤ 3 * C.corridor ∧
      5 * (C.levels + 1) * 1 + C.levels + C.faceTarget + 2 ≤ 8 * C.corridor ∧
      C.faceTarget + 1 ≤ 2 * C.corridor ∧
      C.faceTarget + 1 ≤ C.halfWidth := by
  have hL0 := hwf.levels_pos
  have hL : 1 ≤ C.levels := by omega
  have hrLF := hwf.corridor_ge
  have hrL : 2 * C.levels ≤ C.corridor := by
    calc
      2 * C.levels = C.levels * 2 := by omega
      _ ≤ C.levels * (2 * C.faceTarget + 2) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ C.corridor := hrLF
  have hrF : 2 * C.faceTarget + 2 ≤ C.corridor := by
    calc
      2 * C.faceTarget + 2 = 1 * (2 * C.faceTarget + 2) := by omega
      _ ≤ C.levels * (2 * C.faceTarget + 2) :=
        Nat.mul_le_mul_right _ hL
      _ ≤ C.corridor := hrLF
  have hr44 := hwf.corridor_ge_44
  have hinner := hwf.innerRadius_ge.trans (min_le_right C.corridor C.halfWidth)
  omega

/-- Every cylinder whose probability is requested by `InitialWindowBounds` has an explicit
all-open witness.  This rules out both an empty target and a vacuously impossible window; only the
quantitative probability estimate remains an analytic certificate-extraction obligation. -/
theorem initialWindow_event_nonempty
    (hd : 3 ≤ d) {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {s K : Nat} (hK : 0 < K)
    (hfar : 10 * s * K ≤ 13 * C.corridor)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * C.corridor)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * C.corridor)
    (hplanar : C.faceTarget + 1 ≤ 2 * C.corridor)
    (htrans : C.faceTarget + 1 ≤ C.halfWidth)
    {y : Site 2}
    (hy : y ∈ MacroExp.pending d (MacroExp.start d C.corridor C.halfWidth) 0)
    {i : Fin d} {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb y : Site d) = Pi.single i sigma)
    {m : Nat} (hm : m < C.levels) {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d)
      ((MacroExp.start d C.corridor C.halfWidth).inspected ∪
        MacroExp.E d C.corridor C.halfWidth 0 y)
      (PostFam.tailD C (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0 m)) :
    (PostFam.tailWindow C (MacroExp.ctr d C.corridor 0) i sigma
      C.corridor C.halfWidth s 0 m
      (↑(CoreRes.target (d := d) C.corridor y) : Set (Site d)) x).Nonempty := by
  exact CorePost.coreTailWindow_nonempty C hwf hsigma (by simpa only [sub_zero] using hemb)
    (by omega : 0 < C.corridor) hK hm hfar hclear hwidth hlong hplanar htrans hx

/-- The initial long-box estimate followed by the target-aware longitudinal family gives all four
core reservations at the start.  Every probability is evaluated at the start transcript itself;
no estimate is transported across a read of `Q 0`.

The scale assumptions are the ordinary fit assumptions for the tail family.  `K` is present only
because the same arithmetic package is used later; the initial call is its level `j = 0`. -/
theorem initialCoreBounds_of_longBox_and_windows
    (hd : 3 ≤ d) {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {q : unitInterval} (hv : C.ValidAt2 q) {s K : Nat} (hK : 0 < K)
    (hwidth : C.levels ≤ 3 * C.corridor)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * C.corridor)
    (hplanar : C.faceTarget + 1 ≤ 2 * C.corridor)
    (htrans : C.faceTarget + 1 ≤ C.halfWidth)
    (hwindow : InitialWindowBounds C q s) :
    InitialCoreBounds (d := d) C.corridor C.halfWidth q C.eps := by
  classical
  intro y hy
  have hyNbr : y ∈ MacroExp.nbrs (0 : Site 2) :=
    ((MacroExp.mem_pending (d := d)).1 hy).1
  obtain ⟨i, sigma, hsigma, hemb⟩ :=
    MacroExp.exists_single_emb_sub (d := d) (by omega : 2 ≤ d) hyNbr
  have hemb0 : (MacroExp.emb y : Site d) = Pi.single i sigma := by
    simpa only [sub_zero] using hemb
  let h := MacroExp.start d C.corridor C.halfWidth
  let Dom : Finset (Site d) :=
    h.inspected ∪ MacroExp.E d C.corridor C.halfWidth 0 y
  let B : Set (Site d) := ↑(LongBox.innerBox C (MacroExp.ctr d C.corridor y))
  let T : Set (Site d) := ↑(CoreRes.target (d := d) C.corridor y)
  have hj : 0 < K := hK
  have hfitAll : ∀ m,
      Corridor.Fits (PostFam.tailScales C i C.corridor C.halfWidth s 0
        (PostFam.clipLevel C m)) 0 := by
    intro m
    exact PostFam.tail_fits C hj (PostFam.clipLevel_lt C hwf m)
      hlong hplanar htrans i
  have hsubAll : ∀ m,
      PostFam.tailD C (MacroExp.ctr d C.corridor 0) i sigma
          C.corridor C.halfWidth s 0 (PostFam.clipLevel C m) ⊆ Dom := by
    intro m x hx
    apply Finset.mem_union_right
    exact PostFam.tailD_subset_E (t := C.halfWidth) (by omega : 2 ≤ d) C
      hsigma hemb (j := 0) hj (PostFam.clipLevel_lt C hwf m) hwidth hlong hx
  have hfreshAll : ∀ m, Disjoint
      (PostFam.tailD C (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0 (PostFam.clipLevel C m)) h.inspected := by
    intro m
    have hDE := PostFam.tailD_subset_E (t := C.halfWidth) (by omega : 2 ≤ d) C
      hsigma hemb (j := 0) hj (PostFam.clipLevel_lt C hwf m) hwidth hlong
    simpa only [h, MacroExp.start] using
      (Corridor.E_disjoint_Q_tail d C.corridor C.halfWidth 0 y).mono_left hDE
  have hoAll : ∀ m, MacroExp.emb 0 ∉
      PostFam.tailD C (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0 (PostFam.clipLevel C m) := by
    intro m hom
    exact Finset.disjoint_left.1 (hfreshAll m) hom (by
      change (MacroExp.emb 0 : Site d) ∈ MacroExp.Q d C.corridor C.halfWidth 0
      exact MacroExp.M_subset_Q C.corridor C.halfWidth 0
        (MacroExp.emb_zero_mem_M C.corridor C.halfWidth))
  let lv : Nat → TargetExt.LevelGeometry (zdGraph d) Dom (MacroExp.emb 0) T := fun m =>
    PostFam.tailLevel C (MacroExp.ctr d C.corridor 0) i sigma
      C.corridor C.halfWidth s 0 (PostFam.clipLevel C m) Dom (MacroExp.emb 0) T
      (hfitAll m) (hsubAll m) (hoAll m)
  have hDomThin : (↑Dom : Set (Site d)) ⊆ MacroExp.thin d C.halfWidth := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact MacroExp.Q_subset_thin (by omega : 2 ≤ d) C.corridor C.halfWidth 0
        (Finset.mem_coe.2 (by simpa only [h, MacroExp.start] using hx))
    · exact MacroExp.E_subset_thin (by omega : 2 ≤ d) C.corridor C.halfWidth 0 y
        (Finset.mem_coe.2 hx)
  have hnest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D := by
    intro m hm
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm,
      PostFam.clipLevel_eq C hm0] using
      (PostFam.tailD_succ_subset C (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0 m)
  have hgate : ∀ m, m + 1 < C.levels → ∀ x ∈ Dom, x ∉ (lv m).D →
      ∀ v ∈ (lv m).D, (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D := by
    intro m hm x hxDom hxout v hv hadj
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    have hxout' : x ∉ PostFam.tailD C (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0 m := by
      simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm0] using hxout
    have hv' : v ∈ PostFam.tailD C (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0 m := by
      simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm0] using hv
    have hout := PostFam.tail_gate_rel (z := (0 : Site 2)) C
      (Stopped.dir_planar hsigma hemb) (sigma := sigma)
      (r := C.corridor) (t := C.halfWidth) (s := s) (j := 0) (m := m)
      (Dom := Dom) hDomThin x hxDom hxout' v hv' hadj
    simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] using hout
  have hB : ∀ m < C.levels, B ⊆ ↑(lv m).D := by
    intro m hm x hx
    rw [Finset.mem_coe] at hx ⊢
    simpa only [B, lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] using
      (CorePost.initialInnerBox_subset_tailD hwf hsigma hemb0 (s := s) hm
        (Finset.mem_coe.1 hx))
  have hsel : ∀ m < C.levels, ∀ L ⊆ TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card := by
    intro m hm L hL hcard
    simp only [lv, PostFam.tailLevel_sel, PostFam.clipLevel_eq C hm]
    simp only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] at hL
    apply Corridor.le_card_selC_of_subset_outerBoundary
      (PostFam.tailScales C i C.corridor C.halfWidth s 0 m)
      (PostFam.tailCentre (MacroExp.ctr d C.corridor 0) i sigma C.corridor s 0)
      0 Dom L (k := C.seedCount) (N := C.contacts)
    · simpa only [PostFam.tailD] using hL
    · have heq : 4 * (1 + 2 * C.faceTarget) + 1 = 8 * C.faceTarget + 5 := by omega
      simpa only [PostFam.tailScales, heq] using hwf.contacts_ge
    · exact hcard
  have hseed : ∀ m < C.levels, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      ((lv m).J x).card ≤ C.seedSize := by
    intro m hm x hx
    simp only [lv, PostFam.tailLevel_J, PostFam.clipLevel_eq C hm]
    simp only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] at hx
    refine (MacroExp.card_seed_le
      (Sc := PostFam.tailScales C i C.corridor C.halfWidth s 0 m) rfl
      (PostFam.tail_fits C hj hm hlong hplanar htrans i) ?_).trans ?_
    · exact Corridor.isContact_of_mem_outerBoundary _ _ _ Dom
        (by simpa only [PostFam.tailD] using hx)
    · simpa only [PostFam.tailScales] using hwf.seedSize_ge
  have hG : ∀ m < C.levels, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      1 - 3 * (C.eps / 8) ^ 2 ≤
        (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x) := by
    intro m hm x hx
    have hwnd := hwindow y hy i sigma hsigma hemb0 m hm x (by
      simpa only [Dom, lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] using hx)
    simp only [lv, PostFam.tailLevel_Gx, PostFam.clipLevel_eq C hm]
    have hdelta := MacroExp.delta_le_eps_div_eight hwf
    have hdelta0 := hwf.delta_pos.le
    have heps8 : 0 ≤ C.eps / 8 :=
      div_nonneg hwf.eps_pos.le (by norm_num)
    have hsquare : C.delta ^ 2 ≤ (C.eps / 8) ^ 2 := by nlinarith
    linarith
  have hq0 : 0 < (q : Real) := MacroExp.coe_pos_of_validAt2 hwf hv
  have hq1 : (q : Real) < 1 := MacroExp.coe_lt_one_of_validAt2 hwf hv
  let w : Site d → unitInterval :=
    pinW (fun _ : Site d => q) (↑h.inspected : Set (Site d))
      (↑h.openSites : Set (Site d))
  have hw : ∀ m < C.levels, ∀ x ∈ (lv m).D, w x = q := by
    intro m hm x hx
    dsimp only [w]
    rw [pinW_apply_of_not_mem]
    intro hxI
    exact Finset.disjoint_left.1 (by
      simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] using hfreshAll m)
      hx (Finset.mem_coe.1 hxI)
  have hsrc0 := InitBridge.hinitialLongBox_holds d hd C q hwf hv y hy
  have hsrc : 1 - C.eps / 8 <
      (prodBernoulli w).real (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) B) := by
    rw [MacroExp.prob_eq_real_pinW h q hq0 hq1
      (measurableSet_connWithinSet (zdGraph d) Dom (MacroExp.emb 0) B)] at hsrc0
    simpa only [h, Dom, B, w] using hsrc0
  have hout := TargetExt.targetExtension_eps_rel (zdGraph d) Dom (MacroExp.emb 0) T
    (Δ := 2 * d) (by
      intro x
      rw [Finset.filter_congr_decidable]
      exact MacroExp.card_le_of_forall_adj fun z hz => (Finset.mem_filter.1 hz).2)
    hwf.levels_pos lv hnest hgate hB q hq1 w hw
    C.contacts C.seedCount C.seedSize hsel hseed hwf.eps_pos hwf.eps_le_one
    (by
      have hlev := hwf.level_of_le hv.2.2
      have hdelta := MacroExp.delta_le_eps_div_eight hwf
      have hpow : (0 : Real) ≤ (1 - (q : Real)) ^ (2 * d * C.contacts) := by positivity
      have hL0 : (0 : Real) ≤ C.levels := Nat.cast_nonneg _
      have hmul : (C.levels : Real) * C.delta *
          (1 - (q : Real)) ^ (2 * d * C.contacts) ≤
          (C.levels : Real) * (C.eps / 8) *
            (1 - (q : Real)) ^ (2 * d * C.contacts) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdelta hL0) hpow
      linarith)
    (le_trans hv.2.1.le (MacroExp.delta_le_eps_div_eight hwf)) hG hsrc
  unfold CoreRes.Bound CoreRes.event
  rw [MacroExp.prob_eq_real_pinW h q hq0 hq1
    (measurableSet_connWithinSet (zdGraph d) Dom (MacroExp.emb 0) T)]
  simpa only [h, Dom, T, w] using hout

/-- The actual initialization package consumed by the core scheduler. -/
theorem initialized_of_longBox_and_windows
    (hd : 3 ≤ d) {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {q : unitInterval} (hv : C.ValidAt2 q) {s K : Nat} (hK : 0 < K)
    (hwidth : C.levels ≤ 3 * C.corridor)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * C.corridor)
    (hplanar : C.faceTarget + 1 ≤ 2 * C.corridor)
    (htrans : C.faceTarget + 1 ≤ C.halfWidth)
    (hwindow : InitialWindowBounds C q s) :
    CoreTaggedCover.Holds C.corridor C.halfWidth q C.eps
        (MacroExp.start d C.corridor C.halfWidth) ∧
      CoreFrontier.Invariant C.corridor C.halfWidth q C.eps
        (MacroExp.start d C.corridor C.halfWidth) := by
  exact initialized_of_initialCoreBounds C.corridor C.halfWidth q C.eps
    (initialCoreBounds_of_longBox_and_windows hd hwf hv hK hwidth hlong hplanar htrans hwindow)

/-- With the canonical root scales, the only additional proposition beyond certificate validity is
the target-aware finite-window family itself. -/
theorem initialized_of_canonical_initial_windows
    (hd : 3 ≤ d) {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {q : unitInterval} (hv : C.ValidAt2 q)
    (hwindow : InitialWindowBounds C q (C.levels + 1)) :
    CoreTaggedCover.Holds C.corridor C.halfWidth q C.eps
        (MacroExp.start d C.corridor C.halfWidth) ∧
      CoreFrontier.Invariant C.corridor C.halfWidth q C.eps
        (MacroExp.start d C.corridor C.halfWidth) := by
  obtain ⟨hK, hfar, hclear, hwidth, hlong, hplanar, htrans⟩ :=
    canonical_initial_scale_clearance C hwf
  exact initialized_of_longBox_and_windows hd hwf hv hK (by omega) hlong hplanar htrans hwindow

#print axioms KNAll.Site.CoreInitial.frontier_start_iff_pending
#print axioms KNAll.Site.CoreInitial.invariant_start_iff_initialCoreBounds
#print axioms KNAll.Site.CoreInitial.coreTarget_not_subset_initialInnerBox
#print axioms KNAll.Site.CoreInitial.exists_initial_scale_clearance
#print axioms KNAll.Site.CoreInitial.canonical_initial_scale_clearance
#print axioms KNAll.Site.CoreInitial.initialWindow_event_nonempty
#print axioms KNAll.Site.CoreInitial.initialCoreBounds_of_longBox_and_windows
#print axioms KNAll.Site.CoreInitial.initialized_of_longBox_and_windows
#print axioms KNAll.Site.CoreInitial.initialized_of_canonical_initial_windows
#print axioms KNAll.Site.CoreInitial.initialized_of_initialCoreBounds
#print axioms KNAll.Site.CoreInitial.initialCoreBounds_of_longBox_and_windows
#print axioms KNAll.Site.CoreInitial.initialized_of_longBox_and_windows

end KNAll.Site.CoreInitial

end
