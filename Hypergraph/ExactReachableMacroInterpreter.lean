import Hypergraph.StrictParameterDescent
import Hypergraph.ExactMacroGeometry
import Hypergraph.ExactMacroNumerics
import Hypergraph.ExactDirectionMaps
import Hypergraph.CoreInitialReservation

set_option maxHeartbeats 1000000

/-!
# The exact reachable macro interpreter

`StrictParameterDescent.ReachableAdaptiveMacroPlanSoundness` is the last interface standing between
the finite certificate machinery and `thetaSite d (criticalProbSiteI d) = 0`.  This module builds
the interpreter it asks for out of objects that already exist:

* the exploration is the concrete `CoreAcceptedAssembly.exploration`, instantiated at the
  centre-aware total direction maps `ExactDirectionMaps.axis`/`ExactDirectionMaps.sign`, whose two
  scheduler clauses are the already proved `scheduler_sign`/`scheduler_emb`;
* the initial state is the genuine `CoreAcceptedTransition.start`, so `h0.base` is literally
  `MacroExp.start` and `h0.failed` is literally `∅`;
* the planar scales are read off the certificate itself: `r = C.corridor` and `t = C.halfWidth`.
  Then `0 < r`, `5 * r ≤ t` and `2 * t ≤ C.width` are the certificate's own well-formedness fields
  `corridor_ge_44`, `halfWidth_ge_five_corridor` and `width_eq`; no width interface is assumed;
* the reachable physical invariant is `CoreReachSafe.physical_of_reachable_acceptedExploration`
  started at `CoreReachSafe.physical_of_base_eq_start`.

Two inputs are left, and both are stated in the open as explicit hypotheses of the assembly
theorem.  Neither is hidden in a structure and the final theorem is not claimed unconditional.

1. `CoreInitial.InitialCoreBounds` — the start reservation estimate.  By
   `CoreInitial.invariant_start_iff_initialCoreBounds` this is *exactly* the start instance of the
   one-owner frontier invariant, i.e. the minimal statement that makes
   `CoreAcceptedTransition.start_admissible_of_initialCoreBounds` applicable.  It is discharged
   from the certificate by `CoreInitial.initialCoreBounds_of_longBox_and_windows`; the corollary
   `reachable_tuple_of_initialWindows` below performs that reduction with the canonical root
   scales, leaving `CoreInitial.InitialWindowBounds`.

2. `LocalAcceptedSuccess` — the local accepted-state probability statement.  This is the one
   remaining premise of the module.  It is stated verbatim in the shape produced by
   `ExactMacroGeometry.Family.acceptedExploration_success_v15`, and
   `localAcceptedSuccess_of_families` below performs that discharge from a per-state exact family
   plus its finite `ValidAt` leaf checks.

Everything else -- `h0.failed = ∅`, the density equality, admissibility of the start, the reachable
`Physical` invariant and both direction/sign clauses -- is proved here from existing source.
-/

noncomputable section

namespace KNAll.Site.ExactReachableMacro

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-! ## Certificate scales

The two planar scales of the interpreter are the certificate's own corridor radius and transverse
half-width.  All four arithmetic side conditions demanded by the interpreter are then literal
`Certificate2.WellFormed` fields. -/

omit [NeZero d] in
theorem corridor_pos {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) : 0 < C.corridor := by
  have h := hwf.corridor_ge_44
  omega

omit [NeZero d] in
theorem five_corridor_le_halfWidth {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    5 * C.corridor ≤ C.halfWidth :=
  hwf.halfWidth_ge_five_corridor

omit [NeZero d] in
theorem two_corridor_le_halfWidth {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    2 * C.corridor ≤ C.halfWidth := by
  have h := hwf.halfWidth_ge_five_corridor
  omega

omit [NeZero d] in
theorem two_halfWidth_le_width {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    2 * C.halfWidth ≤ C.width := by
  rw [hwf.width_eq]

/-! ## The concrete interpreter -/

/-- The exact accepted-only exploration used by the interpreter: the concrete
`CoreAcceptedAssembly.exploration` at the centre-aware total direction maps.  Both scheduler
clauses are the proved `ExactDirectionMaps` theorems, so no direction hypothesis is carried. -/
def exploration (hd : 2 ≤ d) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (hr : 0 < r) (hrt : 2 * r ≤ t) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r) :
    ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) :=
  CoreAcceptedAssembly.exploration r t s K n q eps
    (ExactDirectionMaps.axis hd) ExactDirectionMaps.sign
    hd hr hrt hs hbudget
    (ExactDirectionMaps.scheduler_sign hd) (ExactDirectionMaps.scheduler_emb hd)

@[simp] theorem exploration_density (hd : 2 ≤ d) (r t s K n : Nat) (q : unitInterval)
    (eps : Real) (hr : 0 < r) (hrt : 2 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r) :
    (exploration hd r t s K n q eps hr hrt hs hbudget).density = fun _ : Site d => q := rfl

@[simp] theorem exploration_admissible (hd : 2 ≤ d) (r t s K n : Nat) (q : unitInterval)
    (eps : Real) (hr : 0 < r) (hrt : 2 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r) :
    (exploration hd r t s K n q eps hr hrt hs hbudget).Admissible =
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps := rfl

/-- **The one remaining premise of this module.**  It is the local, accepted-state one-step success
estimate for the concrete exploration above, quantified over box index and over accepted
non-terminal states only.  Nothing about arbitrary histories is asserted.

This is stated in exactly the shape concluded by
`ExactMacroGeometry.Family.acceptedExploration_success_v15`. -/
def LocalAcceptedSuccess (hd : 2 ≤ d) (r t s K : Nat) (q : unitInterval) (eps : Real)
    (hr : 0 < r) (hrt : 2 * r ≤ t) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r) : Prop :=
  ∀ (n : Nat) (base : BDDom.Transcript (Site d) (Site 2)),
    CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
    ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
    (CoreSafe.successParam : Real) ≤
      base.prob (fun _ : Site d => q)
        ((exploration hd r t s K n q eps hr hrt hs hbudget).success base)

/-! ## Deterministic and reachability components -/

/-- The genuine macro start is admissible for the interpreter at every box index.  The only input
is the start reservation estimate. -/
theorem start_admissible (hd : 2 ≤ d) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (hr : 0 < r) (hrt : 2 * r ≤ t) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hinit : CoreInitial.InitialCoreBounds (d := d) r t q eps) :
    (exploration hd r t s K n q eps hr hrt hs hbudget).Admissible
      (CoreAcceptedTransition.start d r t) :=
  CoreAcceptedTransition.start_admissible_of_initialCoreBounds (box 2 n) r t q eps hinit

/-- Every state literally reached by the interpreter from the genuine start carries the
lightweight physical certificate.  This is pure reachability content: the start is physical by
`physical_of_base_eq_start` and the accepted one-step rule preserves it. -/
theorem reachable_physical (hd : 2 ≤ d) (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hinit : CoreInitial.InitialCoreBounds (d := d) r t q eps)
    (k : BDDom.Transcript (Site d) (Site 2))
    (hk : CoreReachSafe.Reachable
      (exploration hd r t s K n q eps hr (by omega : 2 * r ≤ t) hs hbudget)
      (CoreAcceptedTransition.start d r t) k) :
    CoreReachSafe.Physical d r t k := by
  have hphysical0 : CoreReachSafe.Physical d r t (CoreAcceptedTransition.start d r t) :=
    CoreReachSafe.physical_of_base_eq_start hd rfl
  exact CoreReachSafe.physical_of_reachable_acceptedExploration
    r t s K n q eps (ExactDirectionMaps.axis hd) ExactDirectionMaps.sign
    hd hr ht hs hbudget
    (ExactDirectionMaps.scheduler_sign hd) (ExactDirectionMaps.scheduler_emb hd)
    (start_admissible hd r t s K n q eps hr (by omega : 2 * r ≤ t) hs hbudget hinit)
    hphysical0 hk

/-! ## The remaining premise is exactly the exact-family estimate

The next two theorems check that `LocalAcceptedSuccess` is stated in the shape the exact macro
geometry already concludes.  Only the finite `ValidAt` leaf checks of the per-head corridor and
stopped children are asked for; the frontier witness at the runtime centre is derived here from
admissibility and non-terminality, not assumed. -/

/-- `LocalAcceptedSuccess` follows from a per-accepted-state exact family together with its finite
`ValidAt` leaf checks.  This is `ExactMacroGeometry.Family.acceptedExploration_success_v15` with the
centre frontier witness supplied from the accepted invariant. -/
theorem localAcceptedSuccess_of_families
    (hd : 3 ≤ d) (r t s K : Nat) (p0 q : unitInterval) (eps : Real)
    (eta : Fin (d + 1) → Real) (rho delta2 : Real)
    (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hbeta : eps ≤ eta 0) (hfdelta : AtomTower.f eps ≤ delta2)
    (hrho0 : 0 < rho) (hrhoHalf : rho ≤ 1 / 2)
    (heps0 : 0 < eps) (heps : eps ≤ rho / 2)
    (heBeta : eps ≤ AtomTower.beta (2 * rho) d)
    (hpow : (1 - AtomTower.f eps) ^ K ≤ rho / 16)
    (hparam : (CoreSafe.successParam : Real) ≤ 1 - rho)
    (hfam : ∀ (n : Nat) (base : BDDom.Transcript (Site d) (Site 2))
      (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base),
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ hz : CoreFrontier.Frontier base.base (CoreStoppedReveal.centre n base),
      ∃ F : ExactMacroGeometry.Family p0 eta r t s K base.base
          (CoreAcceptedTransition.owner hadm.preReveal.frontier
            (CoreStoppedReveal.centre n base) hz)
          (CoreStoppedReveal.centre n base)
          (ExactDirectionMaps.axis (by omega : 2 ≤ d)) ExactDirectionMaps.sign
          rho eps delta2,
        (∀ Y, (F.outer Y).corridor.ValidAt q) ∧
        (∀ Y a, ((F.stopped Y).plan a).ValidAt q)) :
    LocalAcceptedSuccess (d := d) (by omega : 2 ≤ d) r t s K q eps hr
      (by omega : 2 * r ≤ t) hs hbudget := by
  intro n base hadm hactive
  have hzbd : CoreStoppedReveal.centre n base ∈
      base.boundary (zdGraph 2) (box 2 n) 0 :=
    MacroExp.pendZ_mem d n (MacroExp.boundary_nonempty_of_not_terminal d n hactive)
  have hzfront := CoreAcceptedTransition.frontier_of_mem_boundary hadm.sound hzbd
  obtain ⟨F, hcorridor, hstopped⟩ := hfam n base hadm hactive hzfront
  exact ExactMacroGeometry.Family.acceptedExploration_success_v15
    p0 q eta r t s K n rho eps delta2
    (ExactDirectionMaps.axis (by omega : 2 ≤ d)) ExactDirectionMaps.sign
    hd hr ht hs hbudget
    (ExactDirectionMaps.scheduler_sign (by omega : 2 ≤ d))
    (ExactDirectionMaps.scheduler_emb (by omega : 2 ≤ d))
    base hadm hactive hzfront F hbeta hfdelta hcorridor hstopped
    hrho0 hrhoHalf heps0 heps heBeta hpow hparam

/-- The same bridge at the fixed `ExactMacroNumerics` budget.  Three of the eight real-valued
hypotheses of the v15 estimate are then the numerics module's own theorems; what remains is the
alignment of the certificate tolerance `eps` with that budget. -/
theorem localAcceptedSuccess_of_families_v15
    (hd : 3 ≤ d) (r t s K : Nat) (p0 q : unitInterval) (eps : Real)
    (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (heps0 : 0 < eps) (heps : eps ≤ ExactMacroNumerics.rho / 2)
    (heBeta : eps ≤ AtomTower.beta (2 * ExactMacroNumerics.rho) d)
    (hbeta : eps ≤ ExactMacroNumerics.eta d 0)
    (hpow : (1 - AtomTower.f eps) ^ K ≤ ExactMacroNumerics.rho / 16)
    (hfam : ∀ (n : Nat) (base : BDDom.Transcript (Site d) (Site 2))
      (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base),
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ hz : CoreFrontier.Frontier base.base (CoreStoppedReveal.centre n base),
      ∃ F : ExactMacroGeometry.Family p0 (ExactMacroNumerics.eta d) r t s K base.base
          (CoreAcceptedTransition.owner hadm.preReveal.frontier
            (CoreStoppedReveal.centre n base) hz)
          (CoreStoppedReveal.centre n base)
          (ExactDirectionMaps.axis (by omega : 2 ≤ d)) ExactDirectionMaps.sign
          ExactMacroNumerics.rho eps (AtomTower.f eps),
        (∀ Y, (F.outer Y).corridor.ValidAt q) ∧
        (∀ Y a, ((F.stopped Y).plan a).ValidAt q)) :
    LocalAcceptedSuccess (d := d) (by omega : 2 ≤ d) r t s K q eps hr
      (by omega : 2 * r ≤ t) hs hbudget :=
  localAcceptedSuccess_of_families hd r t s K p0 q eps
    (ExactMacroNumerics.eta d) ExactMacroNumerics.rho (AtomTower.f eps)
    hr ht hs hbudget hbeta le_rfl
    ExactMacroNumerics.rho_pos ExactMacroNumerics.rho_le_half
    heps0 heps heBeta hpow ExactMacroNumerics.successParam_le_one_sub_rho hfam

/-- The stopped depth demanded by the v15 power bound exists for every tolerance in the budget,
and the corresponding stopped-reach fit is the single visible arithmetic condition on the
certificate corridor: `s * K ≤ r`.  Nothing here is assumed about the certificate. -/
theorem exists_depth_and_budget_fit (eps : Real)
    (heps0 : 0 < eps) (heps : eps ≤ ExactMacroNumerics.rho / 2) :
    ∃ K : Nat, 20 ≤ K ∧
      (1 - AtomTower.f eps) ^ K ≤ ExactMacroNumerics.rho / 16 ∧
      ∀ s r : Nat, s * K ≤ r → 10 * s * K ≤ 10 * r := by
  obtain ⟨K, hK20, hpow⟩ := ExactMacroNumerics.exists_K_pow_exhaustion
    ExactMacroNumerics.rho_pos ExactMacroNumerics.rho_le_half heps0 heps
  refine ⟨K, hK20, hpow, ?_⟩
  intro s r hsr
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hsr

/-! ## The assembled tuple -/

/-- **Assembly.**  A real `Certificate2` well formed and valid at `q`, together with finite stopped
scales `s`, `K` fitting the certificate corridor, the start reservation estimate and the single
local accepted-state success estimate, produces the exact tuple demanded by
`ReachableAdaptiveMacroPlanSoundness`.

`r` and `t` are the certificate's own `corridor` and `halfWidth`; no scale or width interface is
postulated.  Every clause except the last is proved here. -/
theorem reachable_tuple_of_localAcceptedSuccess
    (hd : 3 ≤ d) (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (hwf : C.WellFormed) (_hv : C.ValidAt2 q)
    (s K : Nat) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * C.corridor)
    (hinit : CoreInitial.InitialCoreBounds (d := d) C.corridor C.halfWidth q C.eps)
    (hsucc : LocalAcceptedSuccess (d := d) (by omega : 2 ≤ d)
      C.corridor C.halfWidth s K q C.eps
      (corridor_pos hwf) (two_corridor_le_halfWidth hwf) hs hbudget) :
    ∃ (r t : Nat)
      (h0 : CoreReachSafe.Tr (Site d) (Site 2))
      (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
        (box 2 n) 0 (MacroExp.tgt n)),
      0 < r ∧ 2 * t ≤ C.width ∧
      h0.base = MacroExp.start d r t ∧ h0.failed = ∅ ∧
      (∀ n, (E n).density = fun _ : Site d => q) ∧
      (∀ n, (E n).Admissible h0) ∧
      (∀ n k, CoreReachSafe.Reachable (E n) h0 k → CoreReachSafe.Physical d r t k) ∧
      (∀ n h, (E n).Admissible h →
        ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
        (CoreSafe.successParam : Real) ≤
          h.prob (fun _ : Site d => q) ((E n).success h)) := by
  have hd2 : 2 ≤ d := by omega
  have hr : 0 < C.corridor := corridor_pos hwf
  have ht : 5 * C.corridor ≤ C.halfWidth := five_corridor_le_halfWidth hwf
  have hrt : 2 * C.corridor ≤ C.halfWidth := two_corridor_le_halfWidth hwf
  refine ⟨C.corridor, C.halfWidth,
    CoreAcceptedTransition.start d C.corridor C.halfWidth,
    fun n => exploration hd2 C.corridor C.halfWidth s K n q C.eps hr hrt hs hbudget,
    hr, two_halfWidth_le_width hwf, rfl, rfl, fun _ => rfl, ?_, ?_, hsucc⟩
  · intro n
    exact start_admissible hd2 C.corridor C.halfWidth s K n q C.eps hr hrt hs hbudget hinit
  · intro n k hk
    exact reachable_physical hd2 C.corridor C.halfWidth s K n q C.eps hr ht hs hbudget hinit k hk

/-! ## Reduction of the start estimate to the certificate's own window family -/

/-- The start reservation estimate is not an extra axiom: with the canonical root scales it is
exactly `CoreInitial.InitialWindowBounds`, the certificate's own target-aware finite window family.
This corollary performs that reduction, so the only premise beyond finite certificate data
remaining after it is `LocalAcceptedSuccess`. -/
theorem reachable_tuple_of_initialWindows
    (hd : 3 ≤ d) (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (hwf : C.WellFormed) (hv : C.ValidAt2 q)
    (s K : Nat) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * C.corridor)
    (hwindow : CoreInitial.InitialWindowBounds C q (C.levels + 1))
    (hsucc : LocalAcceptedSuccess (d := d) (by omega : 2 ≤ d)
      C.corridor C.halfWidth s K q C.eps
      (corridor_pos hwf) (two_corridor_le_halfWidth hwf) hs hbudget) :
    ∃ (r t : Nat)
      (h0 : CoreReachSafe.Tr (Site d) (Site 2))
      (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
        (box 2 n) 0 (MacroExp.tgt n)),
      0 < r ∧ 2 * t ≤ C.width ∧
      h0.base = MacroExp.start d r t ∧ h0.failed = ∅ ∧
      (∀ n, (E n).density = fun _ : Site d => q) ∧
      (∀ n, (E n).Admissible h0) ∧
      (∀ n k, CoreReachSafe.Reachable (E n) h0 k → CoreReachSafe.Physical d r t k) ∧
      (∀ n h, (E n).Admissible h →
        ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
        (CoreSafe.successParam : Real) ≤
          h.prob (fun _ : Site d => q) ((E n).success h)) := by
  obtain ⟨hK, hfar, hclear, hwidth, hlong, hplanar, htrans⟩ :=
    CoreInitial.canonical_initial_scale_clearance C hwf
  have hinit : CoreInitial.InitialCoreBounds (d := d) C.corridor C.halfWidth q C.eps :=
    CoreInitial.initialCoreBounds_of_longBox_and_windows hd hwf hv hK (by omega)
      hlong hplanar htrans hwindow
  exact reachable_tuple_of_localAcceptedSuccess hd C q hwf hv s K hs hbudget hinit hsucc

/-! ## The capstone, with the remaining input displayed -/

/-- The still-open interpreter input, per certificate and parameter: finite stopped scales fitting
the certificate corridor, the start reservation estimate, and the local accepted-state success
estimate.  Both analytic components are visible; nothing is packed into a structure. -/
def MacroInterpreterInput (d : Nat) [NeZero d] (hd : 2 ≤ d) : Prop :=
  ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval) (hwf : C.WellFormed), C.ValidAt2 q →
    ∃ (s K : Nat) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * C.corridor),
      CoreInitial.InitialCoreBounds (d := d) C.corridor C.halfWidth q C.eps ∧
      LocalAcceptedSuccess hd C.corridor C.halfWidth s K q C.eps
        (corridor_pos hwf) (two_corridor_le_halfWidth hwf) hs hbudget

/-- The interpreter input discharges the reachable adaptive macro-plan interface. -/
theorem reachableAdaptiveMacroPlanSoundness_of_input (hd : 3 ≤ d)
    (hinput : MacroInterpreterInput d (by omega : 2 ≤ d)) :
    ReachableAdaptiveMacroPlanSoundness (d := d) := by
  intro C q hwf hv
  obtain ⟨s, K, hs, hbudget, hinit, hsucc⟩ := hinput C q hwf hv
  exact reachable_tuple_of_localAcceptedSuccess hd C q hwf hv s K hs hbudget hinit hsucc

/-- **Capstone.**  The interpreter input proves absence of site percolation at the critical point
in every dimension `d ≥ 3`. -/
theorem siteCriticality_of_input (hd : 3 ≤ d)
    (hinput : MacroInterpreterInput d (by omega : 2 ≤ d)) :
    thetaSite d (criticalProbSiteI d) = 0 :=
  siteCriticality_of_reachableAdaptiveMacroPlan hd
    (reachableAdaptiveMacroPlanSoundness_of_input hd hinput)

#print axioms KNAll.Site.ExactReachableMacro.localAcceptedSuccess_of_families
#print axioms KNAll.Site.ExactReachableMacro.localAcceptedSuccess_of_families_v15
#print axioms KNAll.Site.ExactReachableMacro.exists_depth_and_budget_fit
#print axioms KNAll.Site.ExactReachableMacro.start_admissible
#print axioms KNAll.Site.ExactReachableMacro.reachable_physical
#print axioms KNAll.Site.ExactReachableMacro.reachable_tuple_of_localAcceptedSuccess
#print axioms KNAll.Site.ExactReachableMacro.reachable_tuple_of_initialWindows
#print axioms KNAll.Site.ExactReachableMacro.reachableAdaptiveMacroPlanSoundness_of_input
#print axioms KNAll.Site.ExactReachableMacro.siteCriticality_of_input

end KNAll.Site.ExactReachableMacro

end
