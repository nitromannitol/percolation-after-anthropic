import Hypergraph.CoreStopBudget
import Hypergraph.CoreSafeBenchmark
import Hypergraph.CoreDirection
import Hypergraph.ExactTargetArithmetic

/-!
# Explicit numerical choices for the exact macro interpreter

The accepted exact interpreter uses `rho` for the *whole* one-owner batch error.  We set it to
the failure density tolerated by the planar damaged-site benchmark.  Its incoming tolerance is
the exact `d+1`-fold `/96` cascade at `2*rho`; the stopped one-level tolerance is one further
`AtomTower.f` step.  The exact-target `/64` corridor cascade is recorded separately and dominates
the `/96` cascade at every depth.

Only deterministic finite scale choices occur here.  In particular, this module contains no
probability hypotheses and is independent of the concrete stopped-region definition.
-/

noncomputable section

namespace KNAll.Site.ExactMacroNumerics

open KNAll.Site
open ExactTargetArithmetic

/-- Total allowed failure probability of one accepted macro examination. -/
def rho : Real := 9 / 2 ^ 37

/-- Incoming core tolerance: the exact v15 atom-tower cascade. -/
def deltaC (d : Nat) : Real := AtomTower.beta (2 * rho) d

/-- One stopped-level success tolerance. -/
def delta2 (d : Nat) : Real := AtomTower.f (deltaC d)

/-- Iteration of the exact-target source-error map `a ↦ a²/64`. -/
def targetCascade (a : Real) : Nat → Real
  | 0 => a
  | n + 1 => deltaOf (targetCascade a n)

@[simp] theorem targetCascade_zero (a : Real) : targetCascade a 0 = a := rfl

@[simp] theorem targetCascade_succ (a : Real) (n : Nat) :
    targetCascade a (n + 1) = deltaOf (targetCascade a n) := rfl

/-- Tolerances of the `d+1` exact corridor nodes, indexed from input to output.  The outer target
plan has output error `rho/16`, hence its input tolerance is `eta (Fin.last d)`. -/
def eta (d : Nat) (i : Fin (d + 1)) : Real :=
  targetCascade (rho / 16) (d + 1 - i.val)

theorem rho_pos : 0 < rho := by
  norm_num [rho]

theorem rho_le_half : rho ≤ 1 / 2 := by
  norm_num [rho]

theorem two_rho_pos : 0 < 2 * rho := by
  positivity [rho_pos]

theorem two_rho_le_one : 2 * rho ≤ 1 := by
  norm_num [rho]

theorem successParam_le_one_sub_rho :
    (CoreSafe.successParam : Real) ≤ 1 - rho := by
  rw [CoreSafe.coe_successParam]
  norm_num [rho]

theorem deltaC_pos (d : Nat) : 0 < deltaC d := by
  exact AtomTower.beta_pos two_rho_pos d

theorem deltaC_le_beta (d : Nat) : deltaC d ≤ AtomTower.beta (2 * rho) d :=
  le_rfl

/-- The incoming error also fits the half-batch allocation. -/
theorem deltaC_le_rho_half (d : Nat) : deltaC d ≤ rho / 2 := by
  rw [deltaC, CoreDirection.atom_beta_eq_corr_beta]
  calc
    CorrMove.beta (2 * rho) d ≤ (2 * rho) / 32 :=
      CorrMove.beta_le two_rho_pos two_rho_le_one d
    _ ≤ rho / 2 := by nlinarith [rho_pos]

theorem delta2_pos (d : Nat) : 0 < delta2 d := by
  exact AtomTower.f_pos (deltaC_pos d)

theorem delta2_le_one (d : Nat) : delta2 d ≤ 1 := by
  exact AtomTower.f_le_one_of_le_beta two_rho_pos two_rho_le_one
    (deltaC_pos d) (deltaC_le_beta d)

@[simp] theorem f_deltaC (d : Nat) : AtomTower.f (deltaC d) = delta2 d := rfl

/-- An exact target with output error `deltaC` has `/64` input tolerance, which is at least the
stopped tower's `/96` one-step tolerance. -/
theorem delta2_le_targetDelta (d : Nat) : delta2 d ≤ deltaOf (deltaC d) := by
  have hsquare : 0 ≤ (deltaC d) ^ 2 := sq_nonneg _
  unfold delta2 AtomTower.f deltaOf
  nlinarith

theorem targetCascade_pos {a : Real} (ha : 0 < a) :
    ∀ n, 0 < targetCascade a n := by
  intro n
  induction n with
  | zero => simpa using ha
  | succ n ih =>
      rw [targetCascade_succ, deltaOf]
      positivity

theorem targetCascade_le_one {a : Real} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∀ n, targetCascade a n ≤ 1 := by
  intro n
  induction n with
  | zero => simpa using ha1
  | succ n ih =>
      have hn0 := targetCascade_pos ha0 n
      rw [targetCascade_succ, deltaOf]
      nlinarith [sq_nonneg (targetCascade a n - 1)]

/-- At a common terminal tolerance, every `/96` atom-tower iterate is bounded by the
corresponding `/64` exact-target iterate. -/
theorem atomCascade_le_targetCascade {a : Real} (ha : 0 < a) :
    ∀ n, CorrMove.casc a n ≤ targetCascade a n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hc0 : 0 ≤ CorrMove.casc a n := (CorrMove.casc_pos ha n).le
      have ht0 : 0 ≤ targetCascade a n := (targetCascade_pos ha n).le
      have hprod : 0 ≤
          (targetCascade a n - CorrMove.casc a n) *
            (targetCascade a n + CorrMove.casc a n) :=
        mul_nonneg (sub_nonneg.2 ih) (add_nonneg ht0 hc0)
      rw [CorrMove.casc_succ, targetCascade_succ, CorrMove.f, deltaOf]
      nlinarith

/-- The exact target tolerances satisfy the literal quarter-stage recursion. -/
theorem eta_step (d : Nat) (a : Fin d) :
    deltaOf (eta d a.succ) = eta d a.castSucc := by
  change deltaOf (targetCascade (rho / 16) (d + 1 - (a.val + 1))) =
    targetCascade (rho / 16) (d + 1 - a.val)
  rw [show d + 1 - a.val = (d + 1 - (a.val + 1)) + 1 by omega,
    targetCascade_succ]

theorem eta_last (d : Nat) :
    eta d (Fin.last d) = deltaOf (rho / 16) := by
  simp [eta]

theorem eta_pos (d : Nat) (i : Fin (d + 1)) : 0 < eta d i := by
  apply targetCascade_pos
  positivity [rho_pos]

theorem eta_le_one (d : Nat) (i : Fin (d + 1)) : eta d i ≤ 1 := by
  apply targetCascade_le_one
  · positivity [rho_pos]
  · norm_num [rho]

/-- The exact-target `/64` input tolerance dominates the exact v15 `/96` incoming tolerance. -/
theorem deltaC_le_eta_zero (d : Nat) : deltaC d ≤ eta d 0 := by
  rw [deltaC, CoreDirection.atom_beta_eq_corr_beta, CorrMove.beta]
  change CorrMove.casc ((2 * rho) / 32) (d + 1) ≤
    targetCascade (rho / 16) (d + 1)
  rw [show (2 * rho) / 32 = rho / 16 by ring]
  exact atomCascade_le_targetCascade (by positivity [rho_pos]) (d + 1)

/-- All real-valued hypotheses of `ExactMacroGeometry.Family.acceptedExploration_success_v15`
for the fixed choices above. -/
theorem real_hypotheses (d : Nat) :
    0 < rho ∧ rho ≤ 1 / 2 ∧
      0 < deltaC d ∧ deltaC d ≤ rho / 2 ∧
      deltaC d ≤ AtomTower.beta (2 * rho) d ∧
      AtomTower.f (deltaC d) ≤ delta2 d ∧
      deltaC d ≤ eta d 0 ∧
      (CoreSafe.successParam : Real) ≤ 1 - rho := by
  exact ⟨rho_pos, rho_le_half, deltaC_pos d, deltaC_le_rho_half d,
    deltaC_le_beta d, le_rfl, deltaC_le_eta_zero d, successParam_le_one_sub_rho⟩

/-- Geometric exhaustion with a prescribed harmless lower bound on the stopped depth.  Enlarging
the depth by twenty preserves the power estimate because `1 - f(delta)` lies in `[0,1]`. -/
theorem exists_K_pow_exhaustion {rho' delta : Real}
    (hrho : 0 < rho') (hrhoHalf : rho' ≤ 1 / 2)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ rho' / 2) :
    ∃ K : Nat, 20 ≤ K ∧ (1 - AtomTower.f delta) ^ K ≤ rho' / 16 := by
  have hdeltaOne : delta ≤ 1 := by linarith
  have hmul : 0 ≤ delta * (1 - delta) :=
    mul_nonneg hdelta.le (sub_nonneg.2 hdeltaOne)
  have hf0 : 0 < AtomTower.f delta := AtomTower.f_pos hdelta
  have hf1 : AtomTower.f delta ≤ 1 := by
    unfold AtomTower.f
    nlinarith
  obtain ⟨k, hk⟩ := Budget.exists_levelCount (2 * rho') (AtomTower.f delta)
    (by positivity) hf0 hf1
  let K := k + 20
  have hbase0 : 0 ≤ 1 - AtomTower.f delta := sub_nonneg.2 hf1
  have hbase1 : 1 - AtomTower.f delta ≤ 1 := by linarith
  have hpow20 : (1 - AtomTower.f delta) ^ 20 ≤ 1 :=
    pow_le_one₀ hbase0 hbase1
  refine ⟨K, by simp [K], ?_⟩
  rw [show K = k + 20 by rfl, pow_add]
  calc
    (1 - AtomTower.f delta) ^ k * (1 - AtomTower.f delta) ^ 20
        ≤ (1 - AtomTower.f delta) ^ k * 1 :=
      mul_le_mul_of_nonneg_left hpow20 (pow_nonneg hbase0 _)
    _ = (1 - AtomTower.f delta) ^ k := by ring
    _ ≤ rho' / 16 := by
      calc
        (1 - AtomTower.f delta) ^ k ≤ (2 * rho') / 32 := hk.le
        _ = rho' / 16 := by ring

/-- Choose the stopped depth and all enclosing spatial scales.  `L`, `F`, and `R` are arbitrary
finite lower-scale inputs already produced by the analytic window extractors.  The conclusion
includes both the scheduler budget and all deterministic scale inequalities furnished by the
existing core stop-budget constructor. -/
theorem exists_spatial_scales_for_fixed_depth (d L F R K : Nat) (hK20 : 20 ≤ K) :
    ∃ s r t : Nat,
      0 < s ∧ 0 < r ∧
      r = K * s ∧
      2 * R ≤ s ∧
      10 * s * K ≤ 10 * r ∧
      10 * s * K ≤ 13 * r ∧
      L + 1 ≤ 10 * s ∧
      L + 1 ≤ 3 * r ∧
      5 * s * K + L + F + 2 ≤ 8 * r ∧
      F + 1 ≤ 2 * r ∧
      F + 1 ≤ t ∧
      5 * r ≤ t ∧
      44 ≤ r ∧
      100 * (d + 1) * (R + 1) < r ∧
      200 * (R + 1) ≤ r := by
  let s : Nat := 3 + L + F + 2 * R + 100 * (d + 1) * (R + 1)
  let r : Nat := K * s
  let t : Nat := 5 * r + F + 1
  have hs : 0 < s := by simp [s]
  have hsL : L + F + 2 ≤ s := by
    dsimp [s]
    omega
  have hsR : 2 * R ≤ s := by
    dsimp [s]
    omega
  have hsScale : 100 * (d + 1) * (R + 1) < s := by simp [s]
  have hK1 : 1 ≤ K := by omega
  have hsr : s ≤ r := by
    dsimp [r]
    exact Nat.le_mul_of_pos_left s (by omega)
  have hr : 0 < r := hs.trans_le hsr
  have hr44 : 44 ≤ r := by
    dsimp [r]
    have hs3 : 3 ≤ s := by
      dsimp [s]
      omega
    nlinarith
  have houter : 200 * (R + 1) ≤ r := by
    dsimp [r]
    have hsR' : 100 * (R + 1) ≤ s := by
      calc
        100 * (R + 1) ≤ 100 * (d + 1) * (R + 1) := by nlinarith
        _ ≤ s := hsScale.le
    nlinarith
  have hsKr : s * K = r := by simp [r, Nat.mul_comm]
  have hbudget : 10 * s * K ≤ 10 * r := by
    calc
      10 * s * K = 10 * (s * K) := by ring
      _ = 10 * r := by rw [hsKr]
      _ ≤ 10 * r := le_rfl
  refine ⟨s, r, t, hs, hr, rfl, hsR, hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hr44, ?_, houter⟩
  · omega
  · omega
  · omega
  · calc
      5 * s * K + L + F + 2 = 5 * (s * K) + (L + F + 2) := by ring
      _ = 5 * r + (L + F + 2) := by rw [hsKr]
      _ ≤ 8 * r := by omega
  · omega
  · dsimp [t]
    omega
  · dsimp [t]
    omega
  · exact hsScale.trans_le hsr

theorem exists_macro_scales (d L F R : Nat) :
    ∃ K s r t : Nat,
      20 ≤ K ∧
      (1 - AtomTower.f (deltaC d)) ^ K ≤ rho / 16 ∧
      0 < s ∧ 0 < r ∧
      r = K * s ∧
      2 * R ≤ s ∧
      10 * s * K ≤ 10 * r ∧
      10 * s * K ≤ 13 * r ∧
      L + 1 ≤ 10 * s ∧
      L + 1 ≤ 3 * r ∧
      5 * s * K + L + F + 2 ≤ 8 * r ∧
      F + 1 ≤ 2 * r ∧
      F + 1 ≤ t ∧
      5 * r ≤ t ∧
      44 ≤ r ∧
      100 * (d + 1) * (R + 1) < r ∧
      200 * (R + 1) ≤ r := by
  obtain ⟨K, hK20, hpow⟩ := exists_K_pow_exhaustion rho_pos rho_le_half
    (deltaC_pos d) (deltaC_le_rho_half d)
  obtain ⟨s, r, t, hs, hr, hrEq, hsR, hbudget, hfar, hclear, hwidth,
    htail, hplanar, htrans, ht, hr44, hscale, houter⟩ :=
    exists_spatial_scales_for_fixed_depth d L F R K hK20
  exact ⟨K, s, r, t, hK20, hpow, hs, hr, hrEq, hsR, hbudget, hfar, hclear,
    hwidth, htail, hplanar, htrans, ht, hr44, hscale, houter⟩

#print axioms KNAll.Site.ExactMacroNumerics.deltaC_le_eta_zero
#print axioms KNAll.Site.ExactMacroNumerics.real_hypotheses
#print axioms KNAll.Site.ExactMacroNumerics.exists_K_pow_exhaustion
#print axioms KNAll.Site.ExactMacroNumerics.exists_spatial_scales_for_fixed_depth
#print axioms KNAll.Site.ExactMacroNumerics.exists_macro_scales

end KNAll.Site.ExactMacroNumerics

end
