import Hypergraph.SelectionPacking
import Hypergraph.CorridorFreshness
import Hypergraph.CorridorMove

/-!
# The corridor estimates

The deterministic and numerical inputs of the one-step bound of `KN/MacroExploration.lean`, and
the application of `KN/TargetExtension.lean` inside a corridor.  Everything here is proved except
one structure, `ShellWindow`, which isolates the hittable-geometry input of the manuscript.

* *Freshness* is not proved here: `KN/CorridorFreshness.lean` turns the `cover` field of `Good`
  into `region_eq_pending_E`.  The source-side input is now probabilistic: `Good.reserve` gives a
  pinned lower bound for the incoming corridor, while `Good.cert` at `Good.zero_mem` shows that
  `emb 0` is recorded open.  Probabilistic reservations for other pending corridors persist across
  a fresh examination by `ProbInv.prob_step_eq_of_disjoint` and
  `MacroExp.inspected_disjoint_pending_E`.
* *The scales and the tolerances of a certificate.*  `Certificate2.WellFormed.fits` discharges
  `Corridor.Fits` at every level from the clause `halfWidth_ge`; `delta_le_eps_div_eight` and
  `eta_le_three_mul_sq` are the two numerical facts that turn the recorded cascade
  `δ = ε²/96`, `η = δ² (ε/8)` into the hypotheses `δ ≤ ε/8` and `η ≤ 3 (ε/8)²` of
  `TargetExt.targetExtension_eps`; `p₀_lt_one` reads `p₀ < 1` off the level clause.
* *The pinned law is a product law*: `prob_eq_real_pinW`.  A transcript's `prob` is a `pinnedProb`,
  while `targetExtension_eps` is stated for `prodBernoulli w`; the two agree with `w` the weights
  `1` on the recorded open sites, `0` on the recorded closed ones and `q` elsewhere, because every
  pattern of a finite set has positive probability at a parameter strictly inside `(0,1)`
  (`pos_real_localCylinder`).
* *The size of a seed*: `card_seed_le` shows a seed has at most `(4 M + 3)^{d-1}` sites, which is
  the number the clause `seedSize_ge` records.
* *The degree of the lattice*: `card_le_of_forall_adj`, the constant `Δ = 2 d`.
* *The target extension inside a corridor*: `lt_prob_connWithinSet_of_shellWindow`.  At a
  transcript whose fresh region carries the whole level family, with a source outside the outermost
  level, a connection to the innermost boxes of probability more than `1 - ε/8` becomes a
  connection to the target of probability more than `1 - ε`; `density_le_prob_of_shellWindow` reads
  this at the recorded density.  The deterministic ordered-crossing condition that the level
  induction of `TargetExt.sum_real_survive_inter_poor_le` needs is the gate condition
  `Corridor.gate`, discharged here for the level family `levelOf`.
* *The assembly*: `certificateSound2_of_stepBound`, from the one-step bound to
  `LeftImp2.CertificateSound2`.

## What is assumed, and where

`ShellWindow C q c Dom T` is the one structure this module does not build: for every level and
every contact of that level's outer boundary, an event decided by the middle box, whose shell
pattern already fixes an open site of the contact's face joined to the target inside the middle
box, holding with probability at least `1 - eta` at the constant parameter `q`.  This is the
hittable-geometry input of the manuscript: the face-hitting and coalescence experiments of
`KN/SiteIntrinsicInputs.lean` placed in the shell, with local uniqueness funnelling every crossing
of the shell into one cluster.  It mentions no exploration, no transcript and no macro-lattice.

Building it, and the entrance bound that supplies the hypothesis `hsrc` of
`lt_prob_connWithinSet_of_shellWindow` from the incoming probabilistic reservation, are the two
remaining steps between this module and `StepBound`; both are theorems about site percolation at a
fixed parameter inside a finite box, and neither is plumbing.
-/

noncomputable section

namespace KNAll.Site.MacroExp

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor


/-! ## The scales and the tolerances of a certificate

The certificate constants consumed here include `halfWidth_ge` for `Corridor.Fits`,
`halfWidth_ge_five_corridor` for the isotropic manuscript core, `seedSize_ge` for seed size, and
`contacts_ge` for greedy packing.  The tolerance cascade
`δ_C = ε/8`, `δ = ε²/96`, `η = δ² δ_C` is consumed through the two inequalities `δ ≤ ε/8` and
`η ≤ 3 (ε/8)²`, which are what `TargetExt.targetExtension_eps` asks of the recorded numbers. -/

section CertArith

variable {d : ℕ} [NeZero d]

/-- The `Fits` discharge at the scales of a well-formed certificate, at every level below
`levels`. -/
theorem _root_.KNAll.Site.LeftImp2.Certificate2.WellFormed.fits {C : LeftImp2.Certificate2 d}
    (hwf : C.WellFormed) {j : ℕ} (hj : j < C.levels) : Corridor.Fits (Corridor.scalesOf C) j :=
  Corridor.fits_scalesOf C hwf hwf.halfWidth_ge hj

/-- The retained exploration error is the manuscript-safe backward tolerance (8.10), or smaller. -/
theorem retained_tolerance_le_beta {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    C.eps ≤ C.beta := hwf.eps_le_beta

/-- The certificate's closed-form `beta` is definitionally the tolerance consumed by the
machine-checked corrected corridor move. -/
theorem beta_eq_corridorMove_beta {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    C.beta = CorrMove.beta (1 - (C.density : ℝ)) d := by
  rw [hwf.beta_eq, LeftImp2.betaOf, CorrMove.beta_closed_form]

/-- The deterministic option-1 geometry: the reservation target is the isotropic core inside the
larger anisotropic source-tree target. -/
theorem isotropicCore_subset_M_of_wellFormed {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    (z : Site 2) :
    LeftImp2.isotropicCore d C.corridor z ⊆
      M d C.corridor C.halfWidth z :=
  LeftImp2.isotropicCore_subset_M C.corridor C.halfWidth z
    hwf.halfWidth_ge_five_corridor

/-- The manuscript's `5r` cube is available only because `t ≥ 5r` is a certificate clause. -/
theorem isotropicCentralBox_subset_Q_of_wellFormed {C : LeftImp2.Certificate2 d}
    (hwf : C.WellFormed) (z : Site 2) :
    LeftImp2.isotropicCentralBox d C.corridor z ⊆
      Q d C.corridor C.halfWidth z :=
  LeftImp2.isotropicCentralBox_subset_Q C.corridor C.halfWidth z
    hwf.halfWidth_ge_five_corridor

/-- **The seed inequality tolerance is below `ε/8`.** -/
theorem delta_le_eps_div_eight {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    C.delta ≤ C.eps / 8 := by
  have h0 := hwf.eps_pos
  have h1 := hwf.eps_le_one
  rw [hwf.delta_eq]
  nlinarith

/-- **The recorded reliability tolerance is below the squared tolerance of the target
extension.**  Here `η = ε⁵/73728`; the stronger denominator makes the required comparison
immediate from `0 < ε ≤ 1`. -/
theorem eta_le_three_mul_sq {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    C.eta ≤ 3 * (C.eps / 8) ^ 2 := by
  have h0 := hwf.eps_pos
  have h1 := hwf.eps_le_one
  rw [hwf.eta_eq_pow]
  have h5 : C.eps ^ 5 ≤ C.eps ^ 2 := pow_le_pow_of_le_one h0.le h1 (by norm_num)
  have hsq : (0 : ℝ) ≤ C.eps ^ 2 := sq_nonneg _
  nlinarith

/-- **The extraction parameter is below `1`**: the level inequality forces it, since the contact
count is positive. -/
theorem p₀_lt_one {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) : (C.p₀ : ℝ) < 1 := by
  rcases lt_or_eq_of_le C.p₀.2.2 with h | h
  · exact h
  · exfalso
    have hlev := hwf.level
    have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hN : 0 < 2 * d * C.contacts := by
      have := hwf.contacts_pos; positivity
    rw [h, sub_self, zero_pow hN.ne'] at hlev
    norm_num at hlev

/-- The parameter of a valid certificate lies strictly inside the unit interval. -/
theorem coe_pos_of_validAt2 {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) : 0 < (q : ℝ) := by
  rcases lt_or_eq_of_le q.2.1 with hq | hq
  · exact hq
  · exact absurd hv (C.not_validAt2_of_coe_eq_zero hwf hq.symm)

theorem coe_lt_one_of_validAt2 {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {q : unitInterval} (hv : C.ValidAt2 q) : (q : ℝ) < 1 :=
  lt_of_le_of_lt hv.2.2 (p₀_lt_one hwf)

end CertArith

/-! ## Part (c): the pinned law of a transcript is a product law

`FRDom.Transcript.prob` is a `pinnedProb`: the recorded sites are overwritten by their recorded
states and an ordinary product probability is taken.  `TargetExt.targetExtension_eps` is stated for
a product law `prodBernoulli w` with `w` arbitrary off the levels.  The two agree: pinning the
finite set `F` to the pattern `ξ` is the product law with weights `1` on `F ∩ ξ`, `0` on `F \ ξ`
and `w` elsewhere, provided the pattern has positive probability. -/

section PinnedLaw

variable {ι : Type*}

/-- A cylinder is the intersection of an all-open event and an all-closed event. -/
theorem localCylinder_eq_inter (F : Finset ι) (ξ : Set ι) [DecidablePred (· ∈ ξ)] :
    localCylinder (↑F : Set ι) ξ =
      {ω : Set ι | (↑(F.filter (· ∈ ξ)) : Set ι) ⊆ ω} ∩
        {ω : Set ι | ∀ i ∈ F.filter (fun i => i ∉ ξ), i ∉ ω} := by
  ext ω
  simp only [localCylinder, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.coe_filter,
    Set.subset_def, Finset.mem_filter, Finset.mem_coe]
  constructor
  · intro h
    exact ⟨fun i hi => (h i (Finset.mem_coe.2 hi.1)).2 hi.2,
      fun i hi hiω => hi.2 ((h i (Finset.mem_coe.2 hi.1)).1 hiω)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases hiξ : i ∈ ξ
    · exact ⟨fun _ => hiξ, fun _ => h1 i ⟨hi, hiξ⟩⟩
    · exact ⟨fun hiω => absurd hiω (h2 i ⟨hi, hiξ⟩), fun hc => absurd hc hiξ⟩

/-- The all-closed event is determined by its finite set of coordinates. -/
theorem determinedBy_forall_notMem (N : Finset ι) :
    DeterminedBy {ω : Set ι | ∀ i ∈ N, i ∉ ω} (↑N : Set ι) := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  have h := TargetExt.forall_iff_of_inter_eq hagree
  simp only [Set.mem_setOf_eq]
  exact forall₂_congr fun i hi => not_congr (h i (Finset.mem_coe.2 hi))

/-- **Every pattern of a finite set has positive probability** at a constant parameter strictly
between `0` and `1`. -/
theorem pos_real_localCylinder (q : unitInterval) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (F : Finset ι) (ξ : Set ι) :
    0 < (prodBernoulli (fun _ : ι => q)).real (localCylinder (↑F : Set ι) ξ) := by
  classical
  have hdisj : Disjoint (F.filter (· ∈ ξ)) (F.filter (fun i => i ∉ ξ)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact (Finset.mem_filter.1 hi').2 (Finset.mem_filter.1 hi).2
  have hAm : MeasurableSet {ω : Set ι | (↑(F.filter (· ∈ ξ)) : Set ι) ⊆ ω} :=
    (KNAll.Site.determinedBy_allOpen (↑(F.filter (· ∈ ξ)) : Set ι)).measurableSet_of_finset
  have hBm : MeasurableSet {ω : Set ι | ∀ i ∈ F.filter (fun i => i ∉ ξ), i ∉ ω} :=
    (determinedBy_forall_notMem (F.filter (fun i => i ∉ ξ))).measurableSet_of_finset
  rw [localCylinder_eq_inter F ξ,
    prodBernoulli_real_inter_of_determinedBy_disjoint _ hdisj
      (KNAll.Site.determinedBy_allOpen _) (determinedBy_forall_notMem _) hAm hBm,
    prodBernoulli_real_subset, prodBernoulli_real_forall_notMem]
  have h1 : 0 < ∏ _i ∈ F.filter (· ∈ ξ), (q : ℝ) := by
    rw [Finset.prod_const]; positivity
  have h2 : 0 < ∏ _i ∈ F.filter (fun i => i ∉ ξ), (1 - (q : ℝ)) := by
    rw [Finset.prod_const]
    exact pow_pos (by linarith) _
  exact mul_pos h1 h2

/-- **Pinning is a product law.**  For a pattern of positive probability, the pinned probability of
a measurable event is its probability under the product law with the pinned weights. -/
theorem pinnedProb_eq_real_pinW (w : ι → unitInterval) (F : Finset ι) (ξ : Set ι)
    {A : Set (Set ι)} (hA : MeasurableSet A)
    (hpos : 0 < (prodBernoulli w).real (localCylinder (↑F : Set ι) ξ)) :
    pinnedProb w (↑F : Set ι) (fun i => i ∈ ξ) A
      = (prodBernoulli (pinW w (↑F : Set ι) ξ)).real A := by
  have h1 := TargetExt.real_inter_localCylinder_eq_mul_pinnedProb w F ξ hA
  have h2 := prodBernoulli_real_inter_localCylinder w F ξ hA
  rw [h1] at h2
  exact mul_left_cancel₀ (ne_of_gt hpos) h2

end PinnedLaw

/-! ## Part (c): the size of a seed

The seed of a contact spans the seed layer `D \ O` in the outward coordinate, which has depth
`ℓ = 1` at the scales of a certificate and so contributes a single site, and reaches from the
contact to the range of its cube in every other coordinate, a span of at most `2 (ℓ + 2 M) + 1`.
With `ℓ = 1` and `M = faceTarget` this is `(4 faceTarget + 3)^{d-1}`, the number recorded by the
clause `Certificate2.WellFormed.seedSize_ge`. -/

section SeedSize

variable {d : ℕ} [NeZero d]

/-- **The seed has at most `(4 M + 3)^{d-1}` sites** when the seed layer has depth `1`. -/
theorem card_seed_le {Sc : Scales d} (hℓ : Sc.ℓ = 1) {c : Site d} {j : ℕ} (hf : Fits Sc j)
    {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    (seed Sc c j x).card ≤ (4 * Sc.M + 3) ^ (d - 1) := by
  classical
  have hl1 : (Sc.ℓ : ℤ) = 1 := by rw [hℓ]; norm_num
  set i₀ : Fin d := cI Sc c j x with hi₀
  have hcard : (seed Sc c j x).card
      = ∏ q : Fin d, (Finset.Icc (seedLo Sc c j x q) (seedHi Sc c j x q)).card := by
    show (Fintype.piFinset fun q => Finset.Icc (seedLo Sc c j x q) (seedHi Sc c j x q)).card = _
    rw [Fintype.card_piFinset]
  -- the outward coordinate contributes one site
  have hone : (Finset.Icc (seedLo Sc c j x i₀) (seedHi Sc c j x i₀)).card = 1 := by
    have heq : seedLo Sc c j x i₀ = seedHi Sc c j x i₀ := by
      have hρ : ρO Sc j i₀ + 1 = ρD Sc j i₀ := by
        show ρD Sc j i₀ - (Sc.ℓ : ℤ) + 1 = ρD Sc j i₀
        rw [hl1]; ring
      simp only [seedLo, seedHi, if_pos hi₀, hρ, min_self, max_self]
    rw [heq, Finset.Icc_self, Finset.card_singleton]
  -- every other coordinate contributes at most `4 M + 3` sites
  have hrest : ∀ q : Fin d, q ≠ i₀ →
      (Finset.Icc (seedLo Sc c j x q) (seedHi Sc c j x q)).card ≤ 4 * Sc.M + 3 := by
    intro q hq
    have hq' : q ≠ cI Sc c j x := by rw [← hi₀]; exact hq
    obtain ⟨-, -, hxq⟩ := dir_spec hx
    have hxr := hxq q hq'
    have hM := hf.cube_le q
    have hρ : ρO Sc j q = ρD Sc j q - Sc.ℓ := rfl
    have hclamp : |cubeCentre Sc c j x q - x q| ≤ (Sc.ℓ : ℤ) + Sc.M := by
      unfold cubeCentre
      rw [if_neg hq', abs_le]
      simp only [min_def, max_def]
      split_ifs <;> constructor <;> linarith [hxr.1, hxr.2, hM]
    rw [abs_le] at hclamp
    rw [Int.card_Icc, Int.toNat_le]
    push_cast
    simp only [seedLo, seedHi, if_neg hq', min_def, max_def]
    split_ifs <;> omega
  rw [hcard, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), hone, one_mul]
  calc ∏ q ∈ Finset.univ.erase i₀, (Finset.Icc (seedLo Sc c j x q) (seedHi Sc c j x q)).card
      ≤ ∏ _q ∈ Finset.univ.erase i₀, (4 * Sc.M + 3) :=
        Finset.prod_le_prod' fun q hq => hrest q (Finset.ne_of_mem_erase hq)
    _ = (4 * Sc.M + 3) ^ (Finset.univ.erase i₀).card := Finset.prod_const _
    _ = (4 * Sc.M + 3) ^ (d - 1) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]

/-- **The seed bound at the scales of a certificate**, in the form
`TargetExt.targetExtension_eps` consumes: every seed has at most `seedSize` sites. -/
theorem card_seed_le_seedSize (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) {c : Site d}
    {j : ℕ} (hj : j < C.levels) (Dom : Finset (Site d)) :
    ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j),
      (seed (scalesOf C) c j x).card ≤ C.seedSize := by
  intro x hx
  refine le_trans (card_seed_le (Sc := scalesOf C) rfl (hwf.fits hj)
    (isContact_of_mem_outerBoundary (scalesOf C) c j Dom hx)) ?_
  exact hwf.seedSize_ge

end SeedSize

/-! ## The degree of the lattice -/

section Degree

variable {d : ℕ}

/-- **The lattice has degree at most `2 d`.**  This is the constant `Δ` of
`TargetExt.targetExtension_eps`. -/
theorem card_le_of_forall_adj {S : Finset (Site d)} {x : Site d}
    (hS : ∀ y ∈ S, (zdGraph d).Adj x y) : S.card ≤ 2 * d := by
  classical
  have hsub : S ⊆
      (Finset.univ : Finset (Fin d × Bool)).image
        fun p => if p.2 then x + Pi.single p.1 1 else x - Pi.single p.1 1 := by
    intro y hy
    have hadj : (zdGraph d).Adj x y := hS y hy
    obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff x y).1 hadj
    · exact Finset.mem_image.2 ⟨(i, true), Finset.mem_univ _, by simp [hi]⟩
    · refine Finset.mem_image.2 ⟨(i, false), Finset.mem_univ _, ?_⟩
      simp only [Bool.false_eq_true, if_false]
      rw [hi]
      exact add_sub_cancel_right y (Pi.single i 1)
  calc S.card
      ≤ ((Finset.univ : Finset (Fin d × Bool)).image
          fun p => if p.2 then x + Pi.single p.1 1 else x - Pi.single p.1 1).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ, mul_comm]

end Degree


/-! ## Part (d): the target extension inside the corridor

Everything the target extension of `KN/TargetExtension.lean` asks of the corridor is supplied here
from the certificate, except the reliability events themselves.  Those are the *shell windows*: for
each contact `x` of the outer boundary of the level box `D j`, an event `Gx j x` decided by the
middle box `O j`, whose shell pattern already fixes an open site of the face `U x` joined to the
target inside `O j`.  In the manuscript this is the hittable-geometry input (the face-hitting and
coalescence experiments of `KN/SiteIntrinsicInputs.lean` placed in the shell, local uniqueness
funnelling every crossing of the shell into one cluster); it is the one thing this module does not
build, and it is isolated in the structure `ShellWindow`.  Its probability clause is at the
tolerance `eta` the certificate records, and `eta_le_three_mul_sq` shows that tolerance is what
`targetExtension_eps` needs. -/

section Corridor

variable {d : ℕ} [NeZero d]

/-- **The shell windows of a corridor.**  For every level `j < levels` and every contact `x` of the
outer boundary of `D j`, a reliability event `Gx j x` decided by `O j`, whose shell pattern fixes an
open site of the face of `x` joined to the target `T` inside `O j`, and which holds with probability
at least `1 - eta` at the constant parameter `q`.

This is the hittable-geometry input of the manuscript, and the only proposition of this module that
is assumed rather than proved.  It mentions no exploration, no transcript and no macro-lattice: it
is a statement about site percolation at the parameter `q` in the boxes of one level. -/
structure ShellWindow (C : LeftImp2.Certificate2 d) (q : unitInterval) (c : Site d)
    (Dom : Finset (Site d)) (T : Set (Site d)) where
  /-- The reliability event of the contact `x` at level `j`. -/
  Gx : ℕ → Site d → Set (SiteConfig (Site d))
  /-- It is decided by the middle box of the level. -/
  det : ∀ j < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j),
    DeterminedBy (Gx j x) (↑(Obox (scalesOf C) c j) : Set (Site d))
  /-- Its shell pattern fixes an open face site joined to the target inside the middle box. -/
  relay : ∀ j < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j),
    ∀ ω ∈ Gx j x, ∃ u ∈ face (scalesOf C) c j x, u ∈ ω ∧ ∀ ω' ∈ Gx j x,
      ω' ∩ (↑(Obox (scalesOf C) c j \ Ibox (scalesOf C) c j) : Set (Site d))
          = ω ∩ ↑(Obox (scalesOf C) c j \ Ibox (scalesOf C) c j) →
        ω' ∈ TargetExt.toTarget (zdGraph d) (Obox (scalesOf C) c j) T u
  /-- It holds at the tolerance the certificate records. -/
  prob : ∀ j < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j),
    1 - C.eta ≤ (siteBernoulli (fun _ : Site d => q)).real (Gx j x)

/-- The levels are nested inside the outermost one. -/
theorem Dbox_subset_zero (Sc : Scales d) (c : Site d) (j : ℕ) : Dbox Sc c j ⊆ Dbox Sc c 0 :=
  rbox_mono fun q => by
    simp only [ρD, Nat.cast_zero, sub_zero]
    have : (0 : ℤ) ≤ j := Nat.cast_nonneg j
    omega

/-- No site lies on the outer boundary of the empty box. -/
theorem notMem_outerBoundary_empty (Dom : Finset (Site d)) (x : Site d) :
    x ∉ TargetExt.outerBoundary (zdGraph d) Dom (∅ : Finset (Site d)) := by
  classical
  simp [TargetExt.outerBoundary]

/-- A degenerate level, used to make the family of levels total: with the empty box there is no
contact, so every clause is vacuous. -/
def emptyLevel (Dom : Finset (Site d)) (o : Site d) (T : Set (Site d)) :
    TargetExt.LevelGeometry (zdGraph d) Dom o T where
  D := ∅
  O := ∅
  Int := ∅
  U := fun _ => ∅
  J := fun _ => ∅
  sel := fun K => K
  Gx := fun _ => ∅
  hIntO := Finset.Subset.refl _
  hOD := Finset.Subset.refl _
  hDDom := Finset.empty_subset _
  ho := Finset.notMem_empty o
  hU x hx := absurd hx (notMem_outerBoundary_empty Dom x)
  hJD x hx := absurd hx (notMem_outerBoundary_empty Dom x)
  hJO x hx := absurd hx (notMem_outerBoundary_empty Dom x)
  hW3 x hx := absurd hx (notMem_outerBoundary_empty Dom x)
  hsel_sub K := Finset.Subset.refl K
  hsel_disj K := by
    intro a _ b _ _
    simp
  hGdet x hx := absurd hx (notMem_outerBoundary_empty Dom x)
  hrelay x hx := absurd hx (notMem_outerBoundary_empty Dom x)

variable (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) (q : unitInterval)
  (c : Site d) (Dom : Finset (Site d)) (hDDom : ∀ j, Dbox (scalesOf C) c j ⊆ Dom)
  (o : Site d) (ho : o ∉ Dbox (scalesOf C) c 0) (T : Set (Site d))
  (W : ShellWindow C q c Dom T)

/-- **The family of levels of a corridor**, as `TargetExt.targetExtension_eps` consumes it: the
level structure of `KN/CorridorGeometry.lean` at the scales of the certificate for `j < levels`,
and the degenerate level beyond. -/
def levelOf (j : ℕ) : TargetExt.LevelGeometry (zdGraph d) Dom o T :=
  if hj : j < C.levels then
    Corridor.toLevelGeometry (scalesOf C) c j (hwf.fits hj) Dom (hDDom j) o
      (fun hc => ho (Dbox_subset_zero (scalesOf C) c j hc)) T (W.Gx j) (W.det j hj) (W.relay j hj)
  else emptyLevel Dom o T

variable {C hwf q c Dom hDDom o ho T W}

theorem levelOf_D {j : ℕ} (hj : j < C.levels) :
    (levelOf C hwf q c Dom hDDom o ho T W j).D = Dbox (scalesOf C) c j := by
  unfold levelOf
  rw [dif_pos hj]
  rfl

theorem levelOf_sel {j : ℕ} (hj : j < C.levels) :
    (levelOf C hwf q c Dom hDDom o ho T W j).sel = selC (scalesOf C) c j := by
  unfold levelOf
  rw [dif_pos hj]
  rfl

theorem levelOf_J {j : ℕ} (hj : j < C.levels) :
    (levelOf C hwf q c Dom hDDom o ho T W j).J = seed (scalesOf C) c j := by
  unfold levelOf
  rw [dif_pos hj]
  rfl

theorem levelOf_Gx {j : ℕ} (hj : j < C.levels) :
    (levelOf C hwf q c Dom hDDom o ho T W j).Gx = W.Gx j := by
  unfold levelOf
  rw [dif_pos hj]
  rfl

/-- The pinned law of a transcript at a constant parameter strictly inside the unit interval is
the product law with the recorded sites forced to their recorded states. -/
theorem prob_eq_real_pinW (h : Tr d) (q : unitInterval) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    {A : Set (SiteConfig (Site d))} (hA : MeasurableSet A) :
    h.prob (fun _ : Site d => q) A
      = (prodBernoulli (pinW (fun _ : Site d => q) (↑h.inspected : Set (Site d))
          (↑h.openSites : Set (Site d)))).real A := by
  rw [FRDom.Transcript.prob_eq]
  have hval : pinnedProb (fun _ : Site d => q) (↑h.inspected : Set (Site d)) h.state A
      = pinnedProb (fun _ : Site d => q) (↑h.inspected : Set (Site d))
          (fun i => i ∈ (↑h.openSites : Set (Site d))) A :=
    pinnedProb_congr_val _ _ (fun i _ => Iff.rfl) A
  rw [hval]
  exact pinnedProb_eq_real_pinW _ _ _ hA (pos_real_localCylinder q hq0 hq1 _ _)

/-- **The target extension inside the corridor.**  At a transcript whose fresh region carries the
whole level family of the certificate, with a source outside the outermost level, the shell windows
of the corridor turn a connection to the innermost boxes of probability more than `1 - eps/8` into a
connection to the target of probability more than `1 - eps`.

Every hypothesis of `TargetExt.targetExtension_eps` is discharged from the certificate: the degree
bound is `card_le_of_forall_adj`, the nesting and the gate are the level structure of
`KN/CorridorGeometry.lean` (the gate is the deterministic ordered-crossing condition that the
level induction of `TargetExt.sum_real_survive_inter_poor_le` needs), the selection bound is the
greedy packing of `KN/SelectionPacking.lean` against the clause `contacts_ge`, the seed bound is
`card_seed_le_seedSize` against the clause `seedSize_ge`, the level inequality and the seed
inequality are the clauses `level` and the `ValidAt2` seed clause through `delta_le_eps_div_eight`,
and the reliability bound is the `ShellWindow` clause through `eta_le_three_mul_sq`. -/
theorem lt_prob_connWithinSet_of_shellWindow
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hpack : C.seedCount * (8 * C.faceTarget + 5) ^ d ≤ C.contacts)
    (h : Tr d) (Reg : Finset (Site d)) (hfresh : Disjoint Reg h.inspected)
    (c : Site d) (hplace : ∀ j, Dbox (scalesOf C) c j ⊆ Reg)
    (o : Site d) (ho : o ∉ Dbox (scalesOf C) c 0)
    (T B : Set (Site d)) (hBsub : ∀ i < C.levels, B ⊆ ↑(Dbox (scalesOf C) c i))
    (W : ShellWindow C q c (h.inspected ∪ Reg) T)
    (hsrc : 1 - C.eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B)) :
    1 - C.eps < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o T) := by
  classical
  have hq0 := coe_pos_of_validAt2 hwf hv
  have hq1 := coe_lt_one_of_validAt2 hwf hv
  have hDDom : ∀ j, Dbox (scalesOf C) c j ⊆ h.inspected ∪ Reg := fun j =>
    (hplace j).trans Finset.subset_union_right
  rw [prob_eq_real_pinW h q hq0 hq1
    (measurableSet_connWithinSet (zdGraph d) (h.inspected ∪ Reg) o T)]
  rw [prob_eq_real_pinW h q hq0 hq1
    (measurableSet_connWithinSet (zdGraph d) (h.inspected ∪ Reg) o B)] at hsrc
  refine TargetExt.targetExtension_eps (zdGraph d) (h.inspected ∪ Reg) o T
    (Δ := 2 * d) (by
      intro x
      rw [Finset.filter_congr_decidable]
      exact card_le_of_forall_adj fun y hy => (Finset.mem_filter.1 hy).2) hwf.levels_pos
    (levelOf C hwf q c (h.inspected ∪ Reg) hDDom o ho T W) ?_ ?_ (B := B) ?_ q hq1 _ ?_
    C.contacts C.seedCount C.seedSize ?_ ?_ hwf.eps_pos hwf.eps_le_one ?_ ?_ ?_ hsrc
  · intro i hi
    rw [levelOf_D (show i + 1 < C.levels by omega), levelOf_D (show i < C.levels by omega)]
    exact Dbox_succ_subset _ _ i
  · intro i hi x hx y hy hadj
    rw [levelOf_D (show i < C.levels by omega)] at hx hy
    rw [levelOf_D (show i + 1 < C.levels by omega)]
    exact Corridor.gate (scalesOf C) c i hx hy hadj
  · intro i hi
    rw [levelOf_D hi]
    exact hBsub i hi
  · intro i hi y hy
    rw [levelOf_D hi] at hy
    have hyI : y ∉ (↑h.inspected : Set (Site d)) := fun hc =>
      Finset.disjoint_left.1 hfresh (hplace i hy) (Finset.mem_coe.1 hc)
    exact pinW_apply_of_not_mem _ _ hyI
  · intro i hi K hK hcard
    rw [levelOf_D hi] at hK
    rw [levelOf_sel hi]
    exact Corridor.le_card_selC_scalesOf C c i (h.inspected ∪ Reg) K hK hpack hcard
  · intro i hi x hx
    rw [levelOf_D hi] at hx
    rw [levelOf_J hi]
    exact card_seed_le_seedSize C hwf hi (h.inspected ∪ Reg) x hx
  · have hlev := hwf.level_of_le hv.2.2
    have hdelta := delta_le_eps_div_eight hwf
    have hpow : (0 : ℝ) ≤ (1 - (q : ℝ)) ^ (2 * d * C.contacts) := by
      have h1 : (0 : ℝ) ≤ 1 - (q : ℝ) := by linarith
      positivity
    have hL0 : (0 : ℝ) ≤ (C.levels : ℝ) := Nat.cast_nonneg _
    have hmul : (C.levels : ℝ) * C.delta * (1 - (q : ℝ)) ^ (2 * d * C.contacts)
        ≤ (C.levels : ℝ) * (C.eps / 8) * (1 - (q : ℝ)) ^ (2 * d * C.contacts) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdelta hL0) hpow
    linarith
  · exact le_trans hv.2.1.le (delta_le_eps_div_eight hwf)
  · intro i hi x hx
    rw [levelOf_D hi] at hx
    rw [levelOf_Gx hi]
    have h1 := W.prob i hi x hx
    have h2 := eta_le_three_mul_sq hwf
    linarith

/-- **The corridor estimate at the recorded density.**  The certificate's planar margin clause
`eps ≤ 1 - density` turns the target extension into the lower bound the exploration needs. -/
theorem density_le_prob_of_shellWindow
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hpack : C.seedCount * (8 * C.faceTarget + 5) ^ d ≤ C.contacts)
    (h : Tr d) (Reg : Finset (Site d)) (hfresh : Disjoint Reg h.inspected)
    (c : Site d) (hplace : ∀ j, Dbox (scalesOf C) c j ⊆ Reg)
    (o : Site d) (ho : o ∉ Dbox (scalesOf C) c 0)
    (T B : Set (Site d)) (hBsub : ∀ i < C.levels, B ⊆ ↑(Dbox (scalesOf C) c i))
    (W : ShellWindow C q c (h.inspected ∪ Reg) T)
    (hsrc : 1 - C.eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B)) :
    (C.density : ℝ) ≤ h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o T) := by
  have h1 := lt_prob_connWithinSet_of_shellWindow hwf hv hpack h Reg hfresh c hplace o ho T B
    hBsub W hsrc
  have h2 := hwf.eps_le
  have h3 := hwf.eps_pos
  linarith

end Corridor

/-! ## The assembly: from the one-step bound to the soundness of the certificate

`KN/MacroExploration.lean` proves everything from `StepBound` onwards.  The only step it leaves to
this module is the passage from its `CertificateSound` (for `LeftImp.Certificate`) to
`LeftImp2.CertificateSound2` (for the certificate that records the corridor scales), and that is
a rewording: the slab width of a `Certificate2` is `2 · halfWidth` by the clause `width_eq`. -/

section Assembly

variable {d : ℕ} [NeZero d]

/-- **The soundness of the certificate from the one-step bound.**  If for every well-formed
certificate valid at `q` there are a spacing, a transverse half-width fitting the recorded width,
and a planar density that percolates at which the one-step bound holds, then `CertificateSound2 d`
holds for `d ≥ 3`. -/
theorem certificateSound2_of_stepBound (hd : 3 ≤ d)
    (hs : ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval), C.WellFormed → C.ValidAt2 q →
      ∃ (r t : ℕ) (a : unitInterval), 0 < r ∧ 2 * t ≤ C.width ∧ 0 < thetaSite 2 a ∧
        StepBound d r t q a) :
    LeftImp2.CertificateSound2 d := by
  intro C q hwf hv
  obtain ⟨r, t, a, hr, ht, ha, hstep⟩ := hs C q hwf hv
  have hq : 0 < (q : ℝ) := coe_pos_of_validAt2 hwf hv
  have hthin := thetaSiteOn_thin_pos_of_stepBound (r := r) (t := t) (by omega) hr q a hq ha hstep
  exact lt_of_lt_of_le (slab_two_pos_of_thin hd t q hthin) (thetaSiteOn_slab_mono ht q)

end Assembly

end KNAll.Site.MacroExp

end

/-! ## Co-import check and axioms -/

noncomputable section CoImportCheck

open KNAll.Site KNAll.Site.MacroExp KNAll.Site.Corridor KNAll.Site.TargetExt KNAll.Site.LeftImp
  KNAll.Site.LeftImp2 KNAll.Site.FRDom
open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

-- (a) freshness, from `KN/CorridorFreshness.lean`: the pending corridor avoids everything
-- inspected, so the fresh region is the whole edge region
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (r t n : ℕ) (hr : 0 < r) (h : Tr d) (hg : Good d r t h)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    region d r t n h = E d r t (pendW d n h) (pendZ d n h) :=
  region_eq_pending_E hd r t n hr hg hT

/-- The former co-import check asserted a deterministic recorded-open source adjacent to the
incoming corridor.  That statement required the old `Good.stub` clause, and cannot be recovered
from the corrected `Good`: `Good.reserve` supplies a pinned probability lower bound, not a
realized open endpoint.  The usable replacement is that the fixed source `emb 0` is recorded open
and the whole incoming connection event has the reserved pinned probability. -/
example (d : ℕ) [NeZero d] (r t n : ℕ) (q : unitInterval) (δ : ℝ) (h : Tr d)
    (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    (emb 0 : Site d) ∈ h.openSites ∧
      1 - δ < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑(h.inspected ∪ region d r t n h) : Set (Site d))
          (emb 0) (↑(M d r t (pendZ d n h)) : Set (Site d))) := by
  constructor
  · obtain ⟨a, -, hconn⟩ := hg.cert 0 hg.zero_mem
    exact Finset.mem_coe.1 hconn.1.1
  · exact incoming_reservation_region hg hT

/-- Reading the incoming region is fresh for the transcript.  Consequently any event determined
away from that region retains exactly the same pinned probability; this is the persistence
principle used for the remaining probabilistic reservations. -/
example (d : ℕ) [NeZero d] (hd : 2 ≤ d) (r t n : ℕ) (hr : 0 < r)
    (q : unitInterval) (δ : ℝ) (h : Tr d) (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n))
    (b : Bool) (ω : Set (Site d)) {A : Set (Set (Site d))} {S : Set (Site d)}
    (hA : DeterminedBy A S) (hdisj : Disjoint (↑(region d r t n h) : Set (Site d)) S) :
    (h.step (pendZ d n h) (region d r t n h) b ω).prob (fun _ : Site d => q) A =
      h.prob (fun _ : Site d => q) A := by
  have hfresh : Disjoint (region d r t n h) h.inspected :=
    (inspected_disjoint_pending_E d r t n hd hr hg hT).symm.mono_left Finset.sdiff_subset
  exact ProbInv.prob_step_eq_of_disjoint h (fun _ : Site d => q) (pendZ d n h)
    (region d r t n h) b ω hfresh hA hdisj

-- (b) packing, from `KN/SelectionPacking.lean`, at the scales of a certificate
example (d : ℕ) [NeZero d] (C : Certificate2 d) (c : Site d) (j : ℕ) (Dom K : Finset (Site d))
    (hK : K ⊆ outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j))
    (hpack : C.seedCount * (8 * C.faceTarget + 5) ^ d ≤ C.contacts)
    (hcard : C.contacts ≤ K.card) :
    C.seedCount ≤ (selC (scalesOf C) c j K).card :=
  le_card_selC_scalesOf C c j Dom K hK hpack hcard

-- (c) the seed size, against the clause `seedSize_ge`
example (d : ℕ) [NeZero d] (C : Certificate2 d) (hwf : C.WellFormed) (c : Site d) {j : ℕ}
    (hj : j < C.levels) (Dom : Finset (Site d)) :
    ∀ x ∈ outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j),
      (seed (scalesOf C) c j x).card ≤ C.seedSize :=
  card_seed_le_seedSize C hwf hj Dom

-- (d) the target extension inside the corridor, parametric in the source
#check @KNAll.Site.MacroExp.lt_prob_connWithinSet_of_shellWindow
#check @KNAll.Site.MacroExp.density_le_prob_of_shellWindow

-- the assembly, from the one-step bound
#check @KNAll.Site.MacroExp.certificateSound2_of_stepBound

#print axioms KNAll.Site.MacroExp.card_seed_le
#print axioms KNAll.Site.MacroExp.card_seed_le_seedSize
#print axioms KNAll.Site.MacroExp.card_le_of_forall_adj
#print axioms KNAll.Site.MacroExp.pinnedProb_eq_real_pinW
#print axioms KNAll.Site.MacroExp.prob_eq_real_pinW
#print axioms KNAll.Site.MacroExp.eta_le_three_mul_sq
#print axioms KNAll.Site.MacroExp.delta_le_eps_div_eight
#print axioms KNAll.Site.MacroExp.retained_tolerance_le_beta
#print axioms KNAll.Site.MacroExp.beta_eq_corridorMove_beta
#print axioms KNAll.Site.MacroExp.isotropicCore_subset_M_of_wellFormed
#print axioms KNAll.Site.MacroExp.isotropicCentralBox_subset_Q_of_wellFormed
#print axioms KNAll.Site.MacroExp.p₀_lt_one
#print axioms KNAll.Site.MacroExp.levelOf_D
#print axioms KNAll.Site.MacroExp.lt_prob_connWithinSet_of_shellWindow
#print axioms KNAll.Site.MacroExp.density_le_prob_of_shellWindow
#print axioms KNAll.Site.MacroExp.certificateSound2_of_stepBound
#print axioms KNAll.Site.LeftImp2.Certificate2.WellFormed.fits

end CoImportCheck
