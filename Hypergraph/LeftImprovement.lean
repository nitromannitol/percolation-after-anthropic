import Hypergraph.GateTwoChain

/-!
# A concrete certificate for the below-parameter route

`KN/CertificateRefutation.lean` shows that `CertificateSoundness d` of `KN/RenormData.lean` is false:
`RenormData` allows `numBounds = 0`, whose `ValidAt` is vacuous at every parameter, including `q = 0`
where nothing percolates.  The interface quantified over every conceivable certificate, and one of
them was empty.

This module rebuilds the interface around a certificate that extraction actually produces, so that
soundness is a statement about that certificate and not about every list of real numbers.

* `Certificate d` carries the scales chosen at the supercritical parameter, a comparison density for
  the coarse plane, two tolerances, and a finite list of pairs `(experiment, threshold)`.
* `Certificate.ValidAt q` is the conjunction of the strict inequalities
  `threshold < experiment.prob q` over the list, and nothing else.
* `Certificate.WellFormed` is parameter-free.  It forbids the empty list, and it says which
  experiments the list has to contain and at which thresholds: the face-hitting experiment of
  `KN/SiteIntrinsicInputs.lean` at the source scale `m` and the face target `N_f`, with threshold
  `1 - faceTol`, and the coalescence experiment at the sphere radius `m + shell` and the coalescence
  target `N_c` for every pair of sites of the source box, with threshold `1 - coalTol`.  The two
  tolerances are tied to the comparison density by the budget
  `faceTol + 2d · (#pairs of the source box) · coalTol ≤ 1 - density`, which is the union bound over
  one block and its `2d` corridors, and the comparison density is one at which site percolation on
  the plane `ℤ^2` percolates.  The remaining clauses are the order of the scales and the fit of the
  blocks in the slab and on the macro lattice.
* `Certificate.not_validAt_zero`: a well-formed certificate is not valid at `q = 0`.  This is the
  regression test against the defect of the old interface: the face-hitting event needs an open
  site, so its probability at `q = 0` is `0`, below its threshold.
* `exists_certificate_margin`, the extraction: from `0 < thetaSite d p` alone, a well-formed
  certificate every bound of which holds at `p` with the explicit margin `coalTol / 2`, where
  `coalTol = (1 - density) / (4 (2d+1) · #pairs)`.  The inputs are `siteLocalInputs_of_thetaSite_pos`
  of `KN/SiteLocalFromUniqueness.lean`, reached through `KN.GateTwoChain`, and the two experiments
  in certificate form, `exists_faceExperiment_prob_ge` and `exists_coalescenceExperiment_prob_ge`;
  the comparison density is the parameter `exists_thetaSite_pos 2` supplies.
* `Certificate.exists_valid_nhds`, the stability: a certificate valid at `p` is valid on a
  neighbourhood of `p`.  This is `CylinderExperiment.abs_prob_sub_le` applied bound by bound, with
  the radius taken as the minimum along the list.
* `CertificateSound d`, the single remaining hypothesis: a well-formed certificate valid at `q` forces
  percolation in the slab of its width at `q`.  Nothing here proves it.
* `siteSlabReductionBelow_of_certificateSound` and `siteCriticality_of_certificateSound`, the
  assembly: `CertificateSound d → SiteSlabReductionBelow d`, and with the endgame of
  `KN/SiteEndgame.lean`, `CertificateSound d → SiteCriticality d` for `d ≥ 2`.

Two remarks on scope.  The slab `slab d k` is `{x | 0 ≤ x 0 ≤ k}`, which for `d = 2` is a strip, and
a strip of bounded width does not percolate at any parameter below `1`; so `SiteSlabReductionBelow 2`
is false, and since extraction and stability are proved for every `d`, `CertificateSound 2` is false
as well.  A proof of `CertificateSound d` has to use `3 ≤ d`.  Second, the comparison density is
required to percolate on the plane `ℤ^2` and not on the coarse lattice `ℤ^(d-1)` of the slab; the
plane embeds in every such lattice, so this is the stronger requirement and the one that costs
extraction nothing.
-/

noncomputable section

namespace KNAll.Site.LeftImp

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {d : ℕ}

/-! ## The certificate -/

/-- The finite data extracted from percolation at one parameter.  The scales are those of the two
experiments of `KN/SiteIntrinsicInputs.lean`; `width` and `spacing` are the slab width and the
spacing of the macro lattice the soundness argument works on; `density` is the density of the
comparison site percolation on the plane; and `bounds` is the list of experiments with the
thresholds their probabilities have to exceed. -/
structure Certificate (d : ℕ) where
  /-- The source scale `m`: the radius of the box whose `2d` faces the seed cluster has to hit, and
  of the box whose pairs of sites the coalescence experiments are about. -/
  source : ℕ
  /-- The thickness of the shell between the source box and the coalescence sphere. -/
  shell : ℕ
  /-- The target scale of the face-hitting experiment: the radius of the box it is decided on. -/
  faceTarget : ℕ
  /-- The target scale of the coalescence experiments: the radius of the box they are decided on. -/
  coalTarget : ℕ
  /-- The width `k` of the slab `slab d k`. -/
  width : ℕ
  /-- The spacing `r` of the macro lattice. -/
  spacing : ℕ
  /-- The density of the comparison site percolation on the plane. -/
  density : unitInterval
  /-- The tolerance of the face-hitting experiment. -/
  faceTol : ℝ
  /-- The tolerance of each coalescence experiment. -/
  coalTol : ℝ
  /-- The experiments, each with the number its probability has to exceed. -/
  bounds : List (CylinderExperiment d × ℝ)

/-- The radius of the coalescence sphere. -/
def Certificate.sphere (C : Certificate d) : ℕ := C.source + C.shell

/-- The number of ordered pairs of sites of the source box. -/
def Certificate.pairs (C : Certificate d) : ℕ := ((2 * C.source + 1) ^ d) ^ 2

theorem Certificate.pairs_eq_card (C : Certificate d) :
    C.pairs = (box d C.source ×ˢ box d C.source).card := by
  rw [Certificate.pairs, Finset.card_product, card_box, sq]

theorem Certificate.pairs_pos (C : Certificate d) : 0 < C.pairs := by
  rw [Certificate.pairs]; positivity

/-- **A certificate holds at `q`.**  Every listed threshold is strictly exceeded by the probability of
its experiment at the constant parameter `q`.  This is a finite conjunction of strict inequalities
between real numbers; no percolation event and no configuration appears in it. -/
def Certificate.ValidAt (C : Certificate d) (q : unitInterval) : Prop :=
  ∀ b ∈ C.bounds, b.2 < b.1.prob q

/-- **Well-formedness.**  Parameter-free: no probability at a parameter `q` appears.  The clauses are
the shape of the list, the order of the scales, the fit of the blocks, the arithmetic of the
tolerances against the comparison density, the percolation of that density on the plane, and the
presence in the list of the two experiments at the thresholds `1 - faceTol` and `1 - coalTol`. -/
structure Certificate.WellFormed (C : Certificate d) : Prop where
  /-- The list is not empty. -/
  bounds_ne_nil : C.bounds ≠ []
  /-- Every threshold lies in `[0, 1)`. -/
  threshold_mem : ∀ b ∈ C.bounds, 0 ≤ b.2 ∧ b.2 < 1
  /-- The source box is not a single site. -/
  source_pos : 0 < C.source
  /-- The coalescence sphere lies strictly outside the source box. -/
  shell_pos : 0 < C.shell
  /-- The face experiment is decided on a box containing the source box. -/
  source_le_faceTarget : C.source ≤ C.faceTarget
  /-- The coalescence experiments are decided on a box containing the coalescence sphere. -/
  sphere_le_coalTarget : C.sphere ≤ C.coalTarget
  /-- The face target is the larger of the two targets. -/
  coalTarget_le_faceTarget : C.coalTarget ≤ C.faceTarget
  /-- Blocks of the face target radius placed at the macro spacing are disjoint. -/
  spacing_ge : 2 * C.faceTarget + 1 ≤ C.spacing
  /-- A block of the face target radius fits in the slab. -/
  width_ge : 2 * C.faceTarget ≤ C.width
  /-- The comparison density is below `1`. -/
  density_lt_one : (C.density : ℝ) < 1
  /-- Site percolation on the plane percolates at the comparison density. -/
  density_percolates : 0 < thetaSite 2 C.density
  /-- The face tolerance is positive. -/
  faceTol_pos : 0 < C.faceTol
  /-- The coalescence tolerance is positive. -/
  coalTol_pos : 0 < C.coalTol
  /-- The union bound over one block and its `2d` corridors, each corridor carrying one experiment
  per pair of sites of the source box, leaves at least the comparison density. -/
  budget : C.faceTol + 2 * (d : ℝ) * (C.pairs : ℝ) * C.coalTol ≤ 1 - (C.density : ℝ)
  /-- The face-hitting experiment is listed, at threshold `1 - faceTol`. -/
  face_mem : (faceExperiment d C.source C.faceTarget, 1 - C.faceTol) ∈ C.bounds
  /-- Every coalescence experiment of the source box is listed, at threshold `1 - coalTol`. -/
  coalescence_mem : ∀ x ∈ box d C.source, ∀ y ∈ box d C.source,
    (coalescenceExperiment d C.sphere C.coalTarget x y, 1 - C.coalTol) ∈ C.bounds

/-- A certificate with no bounds is not well-formed: the construction of
`KN/CertificateRefutation.lean` cannot recur. -/
theorem Certificate.not_wellFormed_of_bounds_eq_nil {C : Certificate d} (h : C.bounds = []) :
    ¬ C.WellFormed :=
  fun hwf => hwf.bounds_ne_nil h

/-- The face tolerance of a well-formed certificate is at most `1`. -/
theorem Certificate.WellFormed.faceTol_le_one {C : Certificate d} (h : C.WellFormed) :
    C.faceTol ≤ 1 := by
  have hb := h.budget
  have hnn : (0 : ℝ) ≤ 2 * (d : ℝ) * (C.pairs : ℝ) * C.coalTol := by
    have := h.coalTol_pos
    positivity
  have hd0 : (0 : ℝ) ≤ (C.density : ℝ) := C.density.2.1
  linarith

/-! ## The regression test: no well-formed certificate is valid at `q = 0`

The face-hitting event asks for an open site joined to every face of the source box; when there is
at least one face, that site is open, and at `q = 0` no site is open.  So the face experiment has
probability `0` at `q = 0`, below its threshold `1 - faceTol ≥ 0`.
-/

/-- The face-hitting event does not contain the all-closed configuration when `d ≥ 1`. -/
theorem allClosed_notMem_localFaceEvent' [NeZero d] (m N : ℕ) :
    (∅ : SiteConfig (Site d)) ∉ localFaceEvent d m N := by
  intro h
  rw [mem_localFaceEvent_iff] at h
  obtain ⟨x, -, hx⟩ := h
  obtain ⟨z, -, hz⟩ := hx ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ true
  exact Set.notMem_empty x hz.1.1

/-- At parameter `0` the face experiment has probability `0`. -/
theorem faceExperiment_prob_eq_zero [NeZero d] (m N : ℕ) {q : unitInterval} (hq : (q : ℝ) = 0) :
    (faceExperiment d m N).prob q = 0 := by
  rw [faceExperiment_prob, measureReal_def,
    siteBernoulli_eq_zero_of_coe_eq_zero hq (allClosed_notMem_localFaceEvent' m N)]
  simp

/-- **A well-formed certificate is not valid at parameter `0`.** -/
theorem Certificate.not_validAt_of_coe_eq_zero [NeZero d] {C : Certificate d} (hC : C.WellFormed)
    {q : unitInterval} (hq : (q : ℝ) = 0) : ¬ C.ValidAt q := by
  intro hv
  have h : 1 - C.faceTol < (faceExperiment d C.source C.faceTarget).prob q := hv _ hC.face_mem
  rw [faceExperiment_prob_eq_zero C.source C.faceTarget hq] at h
  linarith [hC.faceTol_le_one]

theorem Certificate.not_validAt_zero [NeZero d] {C : Certificate d} (hC : C.WellFormed) :
    ¬ C.ValidAt 0 :=
  C.not_validAt_of_coe_eq_zero hC rfl

/-- The argument of `KN/CertificateRefutation.lean` has no purchase here: there is no well-formed
certificate valid at `0`. -/
theorem not_exists_wellFormed_validAt_zero [NeZero d] :
    ¬ ∃ C : Certificate d, C.WellFormed ∧ C.ValidAt 0 :=
  fun ⟨_, hwf, hv⟩ => Certificate.not_validAt_zero hwf hv

/-! ## Stability -/

/-- **One bound survives a small shift of the parameter.**  The probability moves by at most the
size of the support times the shift, so a shift below the margin divided by one more than that size
keeps the strict inequality. -/
theorem exists_nhds_of_lt (E : CylinderExperiment d) {t : ℝ} {p : unitInterval}
    (h : t < E.prob p) :
    ∃ ε > 0, ∀ q : unitInterval, |(q : ℝ) - (p : ℝ)| < ε → t < E.prob q := by
  have hcard : (0 : ℝ) < (E.support.card : ℝ) + 1 := by positivity
  refine ⟨(E.prob p - t) / ((E.support.card : ℝ) + 1), div_pos (sub_pos.2 h) hcard, ?_⟩
  intro q hq
  have hlip := E.abs_prob_sub_le p q
  have key : E.prob p - E.prob q < E.prob p - t := by
    calc E.prob p - E.prob q
        ≤ |E.prob p - E.prob q| := le_abs_self _
      _ ≤ (E.support.card : ℝ) * |(p : ℝ) - (q : ℝ)| := hlip
      _ ≤ ((E.support.card : ℝ) + 1) * |(q : ℝ) - (p : ℝ)| := by
          rw [abs_sub_comm]
          exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < ((E.support.card : ℝ) + 1) * ((E.prob p - t) / ((E.support.card : ℝ) + 1)) :=
          mul_lt_mul_of_pos_left hq hcard
      _ = E.prob p - t := by field_simp
  linarith

/-- **A list of bounds valid at `p` is valid near `p`**, with the radius the minimum of the radii of
its members. -/
theorem exists_valid_nhds_list :
    ∀ (L : List (CylinderExperiment d × ℝ)) {p : unitInterval}, (∀ b ∈ L, b.2 < b.1.prob p) →
      ∃ ε > 0, ∀ q : unitInterval, |(q : ℝ) - (p : ℝ)| < ε → ∀ b ∈ L, b.2 < b.1.prob q
  | [], _, _ => ⟨1, one_pos, fun _ _ b hb => by simp at hb⟩
  | b :: L, p, h => by
    rw [List.forall_mem_cons] at h
    obtain ⟨ε₁, hε₁, h₁⟩ := exists_nhds_of_lt b.1 h.1
    obtain ⟨ε₂, hε₂, h₂⟩ := exists_valid_nhds_list L h.2
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun q hq => ?_⟩
    rw [List.forall_mem_cons]
    exact ⟨h₁ q (lt_of_lt_of_le hq (min_le_left _ _)), h₂ q (lt_of_lt_of_le hq (min_le_right _ _))⟩

/-- **A certificate valid at `p` is valid near `p`.** -/
theorem Certificate.exists_valid_nhds (C : Certificate d) {p : unitInterval} (h : C.ValidAt p) :
    ∃ ε > 0, ∀ q : unitInterval, |(q : ℝ) - (p : ℝ)| < ε → C.ValidAt q :=
  exists_valid_nhds_list C.bounds h

/-! ## Extraction -/

/-- The face experiment grows with its target: a larger box allows more confined connections. -/
theorem faceExperiment_prob_mono (d m : ℕ) {N N' : ℕ} (h : N ≤ N') (q : unitInterval) :
    (faceExperiment d m N).prob q ≤ (faceExperiment d m N').prob q := by
  rw [faceExperiment_prob, faceExperiment_prob]
  exact measureReal_mono (localFaceEvent_monotone d m h)

/-- The certificate assembled from a source scale `m`, a sphere radius `M`, a coalescence target
`Nc`, a face target `Nf`, a comparison density and two tolerances.  The slab width is `2 Nf` and the
macro spacing `2 Nf + 1`.  The list holds the face experiment at threshold `1 - τf` followed by the
coalescence experiment of every ordered pair of sites of the source box at threshold `1 - τc`. -/
def certificateOf (d : ℕ) (m M Nc Nf : ℕ) (ρ : unitInterval) (τf τc : ℝ) : Certificate d where
  source := m
  shell := M - m
  faceTarget := Nf
  coalTarget := Nc
  width := 2 * Nf
  spacing := 2 * Nf + 1
  density := ρ
  faceTol := τf
  coalTol := τc
  bounds := (faceExperiment d m Nf, 1 - τf) ::
    ((box d m ×ˢ box d m).toList.map fun xy => (coalescenceExperiment d M Nc xy.1 xy.2, 1 - τc))

@[simp] theorem certificateOf_bounds (d m M Nc Nf : ℕ) (ρ : unitInterval) (τf τc : ℝ) :
    (certificateOf d m M Nc Nf ρ τf τc).bounds = (faceExperiment d m Nf, 1 - τf) ::
      ((box d m ×ˢ box d m).toList.map fun xy =>
        (coalescenceExperiment d M Nc xy.1 xy.2, 1 - τc)) := rfl

@[simp] theorem certificateOf_width (d m M Nc Nf : ℕ) (ρ : unitInterval) (τf τc : ℝ) :
    (certificateOf d m M Nc Nf ρ τf τc).width = 2 * Nf := rfl

@[simp] theorem certificateOf_coalTol (d m M Nc Nf : ℕ) (ρ : unitInterval) (τf τc : ℝ) :
    (certificateOf d m M Nc Nf ρ τf τc).coalTol = τc := rfl

@[simp] theorem certificateOf_faceTol (d m M Nc Nf : ℕ) (ρ : unitInterval) (τf τc : ℝ) :
    (certificateOf d m M Nc Nf ρ τf τc).faceTol = τf := rfl

@[simp] theorem certificateOf_density (d m M Nc Nf : ℕ) (ρ : unitInterval) (τf τc : ℝ) :
    (certificateOf d m M Nc Nf ρ τf τc).density = ρ := rfl

@[simp] theorem certificateOf_pairs (d m M Nc Nf : ℕ) (ρ : unitInterval) (τf τc : ℝ) :
    (certificateOf d m M Nc Nf ρ τf τc).pairs = ((2 * m + 1) ^ d) ^ 2 := rfl

/-- Membership in the list of `certificateOf`: the face pair, or a coalescence pair of two sites of
the source box. -/
theorem mem_certificateOf_bounds {m M Nc Nf : ℕ} {ρ : unitInterval} {τf τc : ℝ}
    {b : CylinderExperiment d × ℝ} :
    b ∈ (certificateOf d m M Nc Nf ρ τf τc).bounds ↔
      b = (faceExperiment d m Nf, 1 - τf) ∨
        ∃ x ∈ box d m, ∃ y ∈ box d m, b = (coalescenceExperiment d M Nc x y, 1 - τc) := by
  rw [certificateOf_bounds, List.mem_cons, List.mem_map]
  constructor
  · rintro (h | ⟨xy, hxy, rfl⟩)
    · exact Or.inl h
    · rw [Finset.mem_toList, Finset.mem_product] at hxy
      exact Or.inr ⟨xy.1, hxy.1, xy.2, hxy.2, rfl⟩
  · rintro (h | ⟨x, hx, y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(x, y), Finset.mem_toList.2 (Finset.mem_product.2 ⟨hx, hy⟩), rfl⟩

/-- **The assembled certificate is well-formed** once the scales are ordered, the density percolates
on the plane, and the tolerances are positive, ordered, and within the budget. -/
theorem certificateOf_wellFormed {m M Nc Nf : ℕ} {ρ : unitInterval} {τf τc : ℝ}
    (hm : 0 < m) (hMm : m < M) (hNc : M ≤ Nc) (hNf : Nc ≤ Nf)
    (hρ : (ρ : ℝ) < 1) (hρpos : 0 < thetaSite 2 ρ)
    (hτf : 0 < τf) (hτc : 0 < τc) (hτ : τc ≤ τf)
    (hbudget : τf + 2 * (d : ℝ) * ((((2 * m + 1) ^ d) ^ 2 : ℕ) : ℝ) * τc ≤ 1 - (ρ : ℝ)) :
    (certificateOf d m M Nc Nf ρ τf τc).WellFormed where
  bounds_ne_nil := List.cons_ne_nil _ _
  threshold_mem := by
    have hd0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.2.1
    have hnn : (0 : ℝ) ≤ 2 * (d : ℝ) * ((((2 * m + 1) ^ d) ^ 2 : ℕ) : ℝ) * τc := by positivity
    intro b hb
    rcases mem_certificateOf_bounds.1 hb with rfl | ⟨x, -, y, -, rfl⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  source_pos := hm
  shell_pos := by show 0 < M - m; omega
  source_le_faceTarget := by show m ≤ Nf; omega
  sphere_le_coalTarget := by show m + (M - m) ≤ Nc; omega
  coalTarget_le_faceTarget := hNf
  spacing_ge := le_rfl
  width_ge := le_rfl
  density_lt_one := hρ
  density_percolates := hρpos
  faceTol_pos := hτf
  coalTol_pos := hτc
  budget := hbudget
  face_mem := mem_certificateOf_bounds.2 (Or.inl rfl)
  coalescence_mem := by
    intro x hx y hy
    have hs : (certificateOf d m M Nc Nf ρ τf τc).sphere = M := by
      show m + (M - m) = M
      omega
    rw [hs]
    exact mem_certificateOf_bounds.2 (Or.inr ⟨x, hx, y, hy, rfl⟩)

/-- **Every bound of the assembled certificate holds with margin `τc / 2`** when the face experiment
holds with margin `τf / 2` and every coalescence experiment with margin `τc / 2`. -/
theorem certificateOf_margin {m M Nc Nf : ℕ} {ρ : unitInterval} {τf τc : ℝ} (hτ : τc ≤ τf)
    {p : unitInterval} (hface : 1 - τf / 2 ≤ (faceExperiment d m Nf).prob p)
    (hcoal : ∀ x ∈ box d m, ∀ y ∈ box d m,
      1 - τc / 2 ≤ (coalescenceExperiment d M Nc x y).prob p) :
    ∀ b ∈ (certificateOf d m M Nc Nf ρ τf τc).bounds, b.2 + τc / 2 ≤ b.1.prob p := by
  intro b hb
  rcases mem_certificateOf_bounds.1 hb with rfl | ⟨x, hx, y, hy, rfl⟩
  · show 1 - τf + τc / 2 ≤ (faceExperiment d m Nf).prob p
    linarith
  · show 1 - τc + τc / 2 ≤ (coalescenceExperiment d M Nc x y).prob p
    linarith [hcoal x hx y hy]

/-- **Extraction, with an explicit margin.**  From percolation at `p` alone: a well-formed certificate
whose every bound holds at `p` with margin `coalTol / 2`, where
`coalTol = (1 - density) / (4 (2d+1) · pairs)` and `coalTol ≤ faceTol`.

The choices, in the order the inputs allow them.  The comparison density is the parameter of
`exists_thetaSite_pos 2`.  The face tolerance is `(1 - density) / 2`; the face input at half that
tolerance gives a scale `m₀`, the source scale is `m₀ + 1`, and the face input gives a target
`N_f'`.  The coalescence tolerance is chosen once `m` is known; the coalescence input at half that
tolerance gives the sphere radius `M > m` and a target `N_c`.  The face target is `max N_f' N_c`,
which is legitimate because the face experiment grows with its target. -/
theorem exists_certificate_margin (d : ℕ) (p : unitInterval) (hpos : 0 < thetaSite d p) :
    ∃ C : Certificate d, C.WellFormed ∧ C.coalTol ≤ C.faceTol ∧
      C.coalTol = (1 - (C.density : ℝ)) / (4 * (2 * (d : ℝ) + 1) * (C.pairs : ℝ)) ∧
      ∀ b ∈ C.bounds, b.2 + C.coalTol / 2 ≤ b.1.prob p := by
  obtain ⟨ρ, hρ1, hρpos⟩ := exists_thetaSite_pos 2 le_rfl
  have hL := siteLocalInputs_of_thetaSite_pos d p hpos
  have ht : (0 : ℝ) < 1 - (ρ : ℝ) := sub_pos.2 hρ1
  obtain ⟨τf, hτf⟩ : ∃ τf : ℝ, τf = (1 - (ρ : ℝ)) / 2 := ⟨_, rfl⟩
  have hτf_pos : 0 < τf := by rw [hτf]; positivity
  obtain ⟨m₀, hm₀⟩ := exists_faceExperiment_prob_ge d p hL (τf / 2) (by positivity)
  obtain ⟨Nf', hNf', hface'⟩ := hm₀ (m₀ + 1) (Nat.le_succ m₀)
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = ((2 * (m₀ + 1) + 1) ^ d) ^ 2 := ⟨_, rfl⟩
  have hP_pos : (0 : ℝ) < (P : ℝ) := by rw [hP]; positivity
  obtain ⟨τc, hτc⟩ : ∃ τc : ℝ, τc = (1 - (ρ : ℝ)) / (4 * (2 * (d : ℝ) + 1) * (P : ℝ)) := ⟨_, rfl⟩
  have hτc_pos : 0 < τc := by rw [hτc]; positivity
  obtain ⟨M, hMm, Nc, hNcM, hcoal⟩ :=
    exists_coalescenceExperiment_prob_ge d p hL (m₀ + 1) (τc / 2) (by positivity)
  have hface : 1 - τf / 2 ≤ (faceExperiment d (m₀ + 1) (max Nf' Nc)).prob p :=
    le_trans hface' (faceExperiment_prob_mono d (m₀ + 1) (le_max_left _ _) p)
  -- The arithmetic of the tolerances.
  have hτ : τc ≤ τf := by
    rw [hτc, hτf]
    apply div_le_div_of_nonneg_left ht.le (by norm_num)
    have h1 : (1 : ℝ) ≤ (P : ℝ) := by
      have h0 : 0 < P := by rw [hP]; positivity
      exact Nat.one_le_cast.2 h0
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hkey : 2 * (d : ℝ) * (P : ℝ) * τc = (d : ℝ) * (1 - (ρ : ℝ)) / (2 * (2 * (d : ℝ) + 1)) := by
    rw [hτc]
    field_simp
    ring
  have hle : (d : ℝ) * (1 - (ρ : ℝ)) / (2 * (2 * (d : ℝ) + 1)) ≤ (1 - (ρ : ℝ)) / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hbudget : τf + 2 * (d : ℝ) * ((((2 * (m₀ + 1) + 1) ^ d) ^ 2 : ℕ) : ℝ) * τc
      ≤ 1 - (ρ : ℝ) := by
    rw [← hP, hkey, hτf]
    linarith
  refine ⟨certificateOf d (m₀ + 1) M Nc (max Nf' Nc) ρ τf τc, ?_, hτ, ?_, ?_⟩
  · exact certificateOf_wellFormed (Nat.succ_pos m₀) hMm hNcM (le_max_right _ _) hρ1 hρpos
      hτf_pos hτc_pos hτ hbudget
  · rw [certificateOf_coalTol, certificateOf_density, certificateOf_pairs, ← hP]
    exact hτc
  · exact certificateOf_margin hτ hface hcoal

/-- **Extraction.**  Percolation at `p` yields a well-formed certificate valid at `p`. -/
theorem exists_wellFormed_validAt (d : ℕ) (p : unitInterval) (hpos : 0 < thetaSite d p) :
    ∃ C : Certificate d, C.WellFormed ∧ C.ValidAt p := by
  obtain ⟨C, hwf, -, -, hmargin⟩ := exists_certificate_margin d p hpos
  refine ⟨C, hwf, fun b hb => lt_of_lt_of_le ?_ (hmargin b hb)⟩
  have := hwf.coalTol_pos
  linarith

/-- **Non-vacuity of the extracted certificate.**  Its list is not empty, and every bound holds at
`p` with a positive margin, namely `coalTol / 2` with
`coalTol = (1 - density) / (4 (2d+1) · pairs) > 0`. -/
theorem exists_certificate_nonvacuous (d : ℕ) (p : unitInterval) (hpos : 0 < thetaSite d p) :
    ∃ C : Certificate d, C.WellFormed ∧ C.bounds ≠ [] ∧ ∃ μ : ℝ, 0 < μ ∧
      μ = (1 - (C.density : ℝ)) / (4 * (2 * (d : ℝ) + 1) * (C.pairs : ℝ)) / 2 ∧
      ∀ b ∈ C.bounds, b.2 + μ ≤ b.1.prob p := by
  obtain ⟨C, hwf, -, hτc, hmargin⟩ := exists_certificate_margin d p hpos
  exact ⟨C, hwf, hwf.bounds_ne_nil, C.coalTol / 2, by linarith [hwf.coalTol_pos], by rw [hτc],
    hmargin⟩

/-- Well-formed certificates exist in every dimension `d ≥ 2`, at the parameter of
`exists_thetaSite_pos`. -/
theorem exists_wellFormed (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ∃ C : Certificate d, C.WellFormed := by
  obtain ⟨a, -, ha⟩ := exists_thetaSite_pos d hd
  obtain ⟨C, hwf, -⟩ := exists_wellFormed_validAt d a ha
  exact ⟨C, hwf⟩

/-! ## Soundness, the single remaining hypothesis -/

/-- **The geometric input.**  A well-formed certificate valid at `q` forces percolation in the slab
of its width at `q`.  This is the only proposition below that is not proved.

It is not the old `CertificateSoundness`: the certificate is well-formed, so its list contains the
face-hitting experiment and every coalescence experiment of its source box at thresholds within the
budget of a comparison density that percolates on the plane, and
`Certificate.not_validAt_zero` shows that validity fails at `q = 0`.  For `d = 2` the slab is a
strip, which never percolates below `1`, so this proposition is false in dimension `2` and a proof
of it has to use `3 ≤ d`. -/
def CertificateSound (d : ℕ) [NeZero d] : Prop :=
  ∀ (C : Certificate d) (q : unitInterval), C.WellFormed → C.ValidAt q →
    0 < thetaSiteOn (slabGraph d C.width) (slabOrigin d C.width) q

/-! ## Assembly -/

/-- **The below-parameter reduction from soundness alone.**  Percolation at `p` yields a well-formed
certificate valid at `p`; it stays valid on a neighbourhood of `p`, which contains parameters
strictly below `p`; soundness turns validity there into percolation in the slab. -/
theorem siteSlabReductionBelow_of_certificateSound (d : ℕ) [NeZero d]
    (hsound : CertificateSound d) : SiteSlabReductionBelow d := by
  intro p _ _ hpos
  obtain ⟨C, hwf, hC⟩ := exists_wellFormed_validAt d p hpos
  obtain ⟨ε, hε, hnhds⟩ := C.exists_valid_nhds hC
  obtain ⟨t, ht0, htε, htp⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ε / 2 ∧ t ≤ (p : ℝ) / 2 :=
    ⟨min (ε / 2) ((p : ℝ) / 2), lt_min (by linarith) (by linarith),
      min_le_left _ _, min_le_right _ _⟩
  have hp1' : (p : ℝ) ≤ 1 := p.2.2
  refine ⟨C.width, ⟨(p : ℝ) - t, Set.mem_Icc.2 ⟨by linarith, by linarith⟩⟩, ?_, ?_⟩
  · show (p : ℝ) - t < (p : ℝ)
    linarith
  · refine hsound C _ hwf (hnhds _ ?_)
    show |((p : ℝ) - t) - (p : ℝ)| < ε
    have hrw : ((p : ℝ) - t) - (p : ℝ) = -t := by ring
    rw [hrw, abs_neg, abs_of_pos ht0]
    linarith

/-- **The capstone.**  From `CertificateSound d` alone, site percolation on `ℤ^d`, `d ≥ 2`, has no
infinite cluster at its critical parameter. -/
theorem siteCriticality_of_certificateSound (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hsound : CertificateSound d) : SiteCriticality d :=
  siteCriticality_of_slabReductionBelow' d hd (siteSlabReductionBelow_of_certificateSound d hsound)

end KNAll.Site.LeftImp

end
