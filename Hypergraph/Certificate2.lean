import Hypergraph.LeftImprovement
import Hypergraph.MacroExploration
import Hypergraph.TargetExtension
import Hypergraph.SiteEndgame
import Hypergraph.MoveWindowInput

/-!
# The certificate with the tolerance cascade of the manuscript

`KN/LeftImprovement.lean` ties the two tolerances of its certificate to the planar comparison
density through the budget `faceTol + 2d · pairs · coalTol ≤ 1 - density`.  At the only planar
density the development supplies, `1 - 2⁻³²` from `exists_thetaSite_pos 2`, every recorded bound
sits at a threshold no larger than `1 - 2⁻³³`, while the Markov step `real_reliableFace_ge` of
`KN/TargetExtension.lean` squares the tolerance: the reliability events of `targetExtension_eps`
need probability at least `1 - 3 (ε/8)²`, and `ε ≤ 2⁻³²` puts that at `1 - 3 · 2⁻⁷⁰`.  The final
docstring of `KN/MacroExploration.lean` records this as the first obstruction to proving
`CertificateSound d` at the recorded numbers.

The obstruction is one of bookkeeping: the local inputs `exists_faceExperiment_prob_ge` and
`exists_coalescenceExperiment_prob_ge` of `KN/SiteIntrinsicInputs.lean` deliver any prescribed
tolerance.  This module records the whole cascade of the manuscript in the certificate.

* `Certificate2 d` extends `Certificate d` by the extraction parameter `p₀`, the retained
  margin `eps ≤ beta`, the three derived tolerances `deltaC = eps/8`, `delta = eps²/96`,
  `eta = delta² · deltaC`,
  the contact count `N`, the seed size `s` and seed count `k`, the level count `L`, a corridor radius
  and the slab half-width `t`.
* `Certificate2.WellFormed` is parameter-free.  It contains every clause of the old `WellFormed`
  (through `base`), the identities fixing the three derived tolerances, `32 * eps ≤ 1 - density`, the
  bounds `faceTol ≤ eta` and `coalTol ≤ eta`, the seed inequality `(1 - p₀^s)^k < delta`, the level
  inequality `L · delta · (1 - p₀)^(2dN) > 1`, the counts `N ≥ k (8 faceTarget + 5)^d` and
  `s ≥ (4 faceTarget + 3)^(d-1)` that the greedy selection and the seed boxes of
  `KN/CorridorGeometry.lean` need, the corridor radius and the macro spacing at least
  `L (2 faceTarget + 2)`, the innermost-radius condition
  `L + 2 faceTarget + 1 ≤ min corridor t`, and `width = 2t`.
  It also records `t ≥ 5r` and the option-1 isotropic core geometry.  The outward-sphere window
  family currently present below is only an intermediate three-factor family: it is not the
  quarter-face/aspect-88 family of Section 8 of `CORRIDOR_MOVE.md`.
* `Certificate2.ValidAt2 C q` is the conjunction of the strict inequalities over the list, the seed
  inequality at `q`, and `q ≤ p₀`.  The seed inequality is at `q` and not only at `p₀` because
  `q ↦ (1 - q^s)^k` is decreasing: the inequality at `p₀` does not transfer to `q < p₀`, while the
  level inequality does (`Certificate2.WellFormed.level_of_le`), and `targetExtension_eps` needs both
  at the parameter of the measure it is applied to.
* Extraction, stability, the two regressions, the level transfer, `CertificateSound2 d`, and the
  assembly `CertificateSound2 d → SiteSlabReductionBelow d → SiteCriticality d`.
* Non-vacuity: the extracted certificate takes `eps = beta` and
  `eta = eps⁵ / 73728`; `exists_wellFormed2_validAt2_explicit` produces such a certificate at
  the explicit planar density `1 - 2⁻³²`.

Two facts about the extraction hypotheses.  The level inequality with `N ≥ 1` forces `p₀ < 1`, and
`thetaSite d 1 > 0`, so extraction takes `p < 1` as a hypothesis; the assembly has it from
`SiteSlabReductionBelow`.  The seed inequality with `s ≥ 1` forces `p₀ > 0`, which follows from
`0 < thetaSite d p` by `thetaSite_eq_zero_of_lt` once `d ≠ 0`.
-/

noncomputable section

open scoped Classical

namespace KNAll.Site.LeftImp2

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site.LeftImp
open KNAll.Site.MoveWindowInput

variable {d : ℕ}

/-! ## The certificate -/

/-- The certificate of `KN/LeftImprovement.lean` together with the tolerance cascade and the scales
of the manuscript.  The base fields are `source`, `shell`, `faceTarget`, `coalTarget`, `width`,
`spacing`, `density`, `faceTol`, `coalTol` and `bounds`. -/
structure Certificate2 (d : ℕ) extends Certificate d where
  /-- The parameter the certificate was extracted at. -/
  p₀ : unitInterval
  /-- The retained reservation tolerance `e`, chosen at or below `beta`. -/
  eps : ℝ
  /-- `δ_C = e / 8`. -/
  deltaC : ℝ
  /-- `δ = e² / 96`. -/
  delta : ℝ
  /-- `η = δ² · δ_C`. -/
  eta : ℝ
  /-- The contact count `N`. -/
  contacts : ℕ
  /-- The seed size `s`. -/
  seedSize : ℕ
  /-- The seed count `k`. -/
  seedCount : ℕ
  /-- The level count `L`. -/
  levels : ℕ
  /-- The planar radius of a corridor. -/
  corridor : ℕ
  /-- The transverse half-width `t` of the slab; `width = 2 t`. -/
  halfWidth : ℕ
  /-- The manuscript-safe corridor tolerance
  `((1 - density) / 32)^(2^(d+1)) / 96^(2^(d+1)-1)`. -/
  beta : ℝ
  /-- The local-cube radius `M_j` used by target-extension call `j`. -/
  moveLocalRadius : Fin (d + 1) → ℕ
  /-- The radius of the selected finite target geometry for call `j`. -/
  moveTargetRadius : Fin (d + 1) → ℕ
  /-- The strictly outward face radius hit by the window of call `j`. -/
  moveHitRadius : Fin (d + 1) → ℕ
  /-- The number `L_j` of nested levels used by target-extension call `j`. -/
  moveLevelCount : Fin (d + 1) → ℕ
  /-- The finite certificate list before the target-hitting windows are appended. -/
  preMoveBounds : List (CylinderExperiment d × ℝ)

/-! ## The target-hitting move-window cylinders

The list below is deliberately built from a bounds-free numerical geometry record.  Thus the
experiments are fixed before they are appended to the final certificate list; no definition of an
experiment can inspect `C.bounds`.
-/

/-- All final numerical data used to manufacture cylinder experiments.  This record has no bounds
field, which is the point of using it during extraction. -/
structure FinalGeometry (d : ℕ) where
  source : ℕ
  shell : ℕ
  faceTarget : ℕ
  coalTarget : ℕ
  width : ℕ
  spacing : ℕ
  density : unitInterval
  faceTol : ℝ
  coalTol : ℝ
  p₀ : unitInterval
  eps : ℝ
  deltaC : ℝ
  delta : ℝ
  eta : ℝ
  contacts : ℕ
  seedSize : ℕ
  seedCount : ℕ
  levels : ℕ
  corridor : ℕ
  halfWidth : ℕ
  beta : ℝ
  moveLocalRadius : Fin (d + 1) → ℕ
  moveTargetRadius : Fin (d + 1) → ℕ
  moveHitRadius : Fin (d + 1) → ℕ
  moveLevelCount : Fin (d + 1) → ℕ

/-- Forget the final list while retaining every numerical field. -/
def Certificate2.finalGeometry (C : Certificate2 d) : FinalGeometry d where
  source := C.source
  shell := C.shell
  faceTarget := C.faceTarget
  coalTarget := C.coalTarget
  width := C.width
  spacing := C.spacing
  density := C.density
  faceTol := C.faceTol
  coalTol := C.coalTol
  p₀ := C.p₀
  eps := C.eps
  deltaC := C.deltaC
  delta := C.delta
  eta := C.eta
  contacts := C.contacts
  seedSize := C.seedSize
  seedCount := C.seedCount
  levels := C.levels
  corridor := C.corridor
  halfWidth := C.halfWidth
  beta := C.beta
  moveLocalRadius := C.moveLocalRadius
  moveTargetRadius := C.moveTargetRadius
  moveHitRadius := C.moveHitRadius
  moveLevelCount := C.moveLevelCount

/-- The backward tolerance of (8.10). -/
def betaOf (d : ℕ) (density : unitInterval) : ℝ :=
  (((1 - (density : ℝ)) / 32) ^ (2 ^ (d + 1))) /
    96 ^ (2 ^ (d + 1) - 1)

/-- The isotropic reservation target `Mtilde_z = c_z + Lambda_(3r)` from (0.6). -/
def isotropicCore (d r : ℕ) (z : Site 2) : Finset (Site d) :=
  MacroExp.abox (MacroExp.ctr d r z) (3 * r) (3 * r)

/-- The isotropic central cube `Qtilde_z = c_z + Lambda_(5r)` from (0.6). -/
def isotropicCentralBox (d r : ℕ) (z : Site 2) : Finset (Site d) :=
  MacroExp.abox (MacroExp.ctr d r z) (5 * r) (5 * r)

/-- With the explicitly recorded choice `t ≥ 5r`, the stronger isotropic reservation target
is contained in the source tree's anisotropic `MacroExp.M`. -/
theorem isotropicCore_subset_M (r t : ℕ) (z : Site 2) (hfive : 5 * r ≤ t) :
    isotropicCore d r z ⊆ MacroExp.M d r t z := by
  intro x hx
  rw [isotropicCore, MacroExp.mem_abox] at hx
  rw [MacroExp.M, MacroExp.mem_abox]
  intro i
  have hi := hx i
  unfold MacroExp.rad at hi ⊢
  split_ifs at hi ⊢ <;> omega

/-- The same numerical clause, rather than an assertion about an arbitrary anisotropic box,
proves availability of the manuscript's `5r` central cube inside `MacroExp.Q`. -/
theorem isotropicCentralBox_subset_Q (r t : ℕ) (z : Site 2) (hfive : 5 * r ≤ t) :
    isotropicCentralBox d r z ⊆ MacroExp.Q d r t z := by
  intro x hx
  rw [isotropicCentralBox, MacroExp.mem_abox] at hx
  rw [MacroExp.Q, MacroExp.mem_abox]
  intro i
  have hi := hx i
  unfold MacroExp.rad at hi ⊢
  split_ifs at hi ⊢ <;> omega

/-- The canonical coordinate radius of the source box of call `j`.  The first `j` coordinates
have been reduced, exactly as in Section 7.1; the common inflation radius is the recorded target
radius. -/
def moveSourceRadius (G : FinalGeometry d) (j : Fin (d + 1)) (i : Fin d) : ℕ :=
  if i.1 < j.1 then
    G.corridor + (G.corridor + 1) / 2 + j.1 * G.moveTargetRadius j
  else 3 * G.corridor + j.1 * G.moveTargetRadius j

/-- `B^src_{nu,j}` in normalized coordinates, centred at the macro centre selected by `nu`.
Thus the outgoing orientation changes the actual geometry, not merely the list index. -/
def moveSourceBox (G : FinalGeometry d) (nu : Site 2) (j : Fin (d + 1)) :
    Finset (Site d) :=
  let c := MacroExp.ctr d G.corridor nu
  Fintype.piFinset fun i => Finset.Icc
    (c i - (moveSourceRadius G j i : ℤ)) (c i + (moveSourceRadius G j i : ℤ))

/-- The displayed level box `(B^src)^{+(2 M_j + 2 + ell)}` of (8.3a). -/
def moveLevelBox (G : FinalGeometry d) (nu : Site 2) (j : Fin (d + 1)) (ell : ℕ) :
    Finset (Site d) :=
  let a := 2 * G.moveLocalRadius j + 2 + ell
  let c := MacroExp.ctr d G.corridor nu
  Fintype.piFinset fun i => Finset.Icc
    (c i - (moveSourceRadius G j i + a : ℕ))
      (c i + (moveSourceRadius G j i + a : ℕ))

/-- The radius of the complete recorded support, not merely of its coalescence cube. -/
def moveSupportRadius (G : FinalGeometry d) : ℕ :=
  max G.coalTarget G.faceTarget

/-- The contact window centre is the coordinatewise clamp of the outer contact to the erosion of
the level box by the radius of the complete support.  It depends on the orientation, call, level
and contact. -/
def moveWindowCentre (G : FinalGeometry d) (nu : Site 2) (j : Fin (d + 1)) (ℓ : ℕ)
    (x : Site d) : Site d :=
  let a := 2 * G.moveLocalRadius j + 2 + ℓ
  let c := MacroExp.ctr d G.corridor nu
  fun i =>
    let margin := moveSourceRadius G j i + a - moveSupportRadius G
    max (c i - (margin : ℤ)) (min (x i) (c i + (margin : ℤ)))

/-- The full-lattice neighbour set of a finite set, with no ambient-box truncation. -/
def fullLatticeNeighbours (D : Finset (Site d)) : Finset (Site d) :=
  D.biUnion fun x =>
    (Finset.univ : Finset (Fin d × Bool)).image fun ib =>
      if ib.2 then x + Pi.single ib.1 1 else x - Pi.single ib.1 1

/-- The full-lattice outer vertex boundary used in (8.3a). -/
def fullLatticeOuterBoundary (D : Finset (Site d)) : Finset (Site d) :=
  fullLatticeNeighbours D \ D

/-- Translation of a centred integer box. -/
def translatedBox (N : ℕ) (v : Site d) : Finset (Site d) :=
  (box d N).image fun z => z + v

/-- The finite vertex sphere, used as a genuine target rather than as the inner face inspected by
`localFaceEvent`. -/
def boxSphereFin (d N : ℕ) : Finset (Site d) :=
  (box d N).filter fun x => ∃ i : Fin d, x i = (N : ℤ) ∨ x i = -(N : ℤ)

theorem coe_boxSphereFin (d N : ℕ) :
    (↑(boxSphereFin d N) : Set (Site d)) = boxSphere d N := by
  ext x
  simp [boxSphereFin, boxSphere, mem_box]

theorem orthantFace_subset_boxSphereFin (a : Fin d) (τ : Fin d → ℤˣ) (N : ℕ) :
    orthantFace a τ N ⊆ boxSphereFin d N := by
  intro x hx
  rw [mem_orthantFace] at hx
  rw [boxSphereFin, Finset.mem_filter]
  refine ⟨hx.1, a, ?_⟩
  rcases Int.units_eq_one_or (τ a) with h | h
  · left
    simpa [h] using hx.2.1
  · right
    simp [h] at hx
    omega

/-- The finite support of the intermediate outward-sphere window.  This union of concentric boxes
is not yet the geometry-dependent support `S_(nu,j,ell,x)` of (8.2). -/
def moveWindowSupport (G : FinalGeometry d) (j : Fin (d + 1)) (v : Site d) :
    Finset (Site d) :=
  translatedBox G.coalTarget v ∪ translatedBox G.faceTarget v

/-- No ordered pair in the source box realizes the finite two-arm non-coalescence event. -/
def moveCoalescenceGood (G : FinalGeometry d) : Set (SiteConfig (Site d)) :=
  shellCoalescenceGood G.source (G.source + G.shell) G.coalTarget

/-- An intermediate three-factor outward-hit event, literally
`Gᶜᵒᵃˡ ∩ Gᶠᵃᶜᵉ ∩ Gᵗᵃʳᵍᵉᵗ`, translated to the contact window.

The face factor reaches the arm sphere `Lambda_(source+shell)` inside the complete local cube
`Lambda_coalTarget`; the target
factor separately reaches the strictly outward sphere `Lambda_(moveHitRadius j)` inside the
selected target support.  Neither factor is `localFaceEvent`.  The final Section 8.2 event must
replace that sphere by the selected quarter-face or aspect-88 far face. -/
def moveWindowEvent (G : FinalGeometry d) (j : Fin (d + 1)) (v : Site d) :
    Set (SiteConfig (Site d)) :=
  siteShift v ⁻¹'
    (shellWindowEvent G.source (G.source + G.shell) G.coalTarget
      (boxSphereFin d (G.source + G.shell)) (box d G.faceTarget)
      (boxSphereFin d (G.moveHitRadius j)))

theorem determinedBy_siteShift_preimage (v : Site d) {A : Set (SiteConfig (Site d))}
    {F : Finset (Site d)} (hA : DeterminedBy A (↑F : Set (Site d))) :
    DeterminedBy (siteShift v ⁻¹' A)
      (↑(F.image (fun z => z + v)) : Set (Site d)) := by
  classical
  rw [determinedBy_iff] at hA ⊢
  intro omega omega' hagree
  apply hA
  ext z
  have hz : z ∈ F → (z + v ∈ omega ↔ z + v ∈ omega') := by
    intro hzF
    have hzS : z + v ∈ (↑(F.image (fun y => y + v)) : Set (Site d)) := by
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨z, hzF, rfl⟩)
    have h := Set.ext_iff.1 hagree (z + v)
    simpa only [Set.mem_inter_iff, hzS, and_true] using h
  simp only [Set.mem_inter_iff, mem_siteShift, Finset.mem_coe]
  exact ⟨fun h => ⟨(hz h.2).1 h.1, h.2⟩, fun h => ⟨(hz h.2).2 h.1, h.2⟩⟩

theorem translatedBox_mono {N N' : ℕ} (hNN' : N ≤ N') (v : Site d) :
    translatedBox (d := d) N v ⊆ translatedBox N' v := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.mem_image.2 ⟨z, box_mono d hNN' hz, rfl⟩

/-- The clamped window has its complete support inside its actual level box.  In particular this
holds when `x` is a genuine outer-boundary contact: no containment of the contact itself is used. -/
theorem moveWindowSupport_subset_moveLevelBox (G : FinalGeometry d) (nu : Site 2)
    (j : Fin (d + 1)) (ℓ : ℕ) (x : Site d)
    (hrad : ∀ i, moveSupportRadius G ≤
      moveSourceRadius G j i + (2 * G.moveLocalRadius j + 2 + ℓ)) :
    moveWindowSupport G j (moveWindowCentre G nu j ℓ x) ⊆ moveLevelBox G nu j ℓ := by
  intro y hy
  have hysupport : y ∈ translatedBox (moveSupportRadius G) (moveWindowCentre G nu j ℓ x) := by
    rcases Finset.mem_union.1 hy with hy | hy
    · exact translatedBox_mono (le_max_left _ _) _ hy
    · exact translatedBox_mono (le_max_right _ _) _ hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hysupport
  rw [moveLevelBox, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hzi := mem_box.1 hz i
  let a := 2 * G.moveLocalRadius j + 2 + ℓ
  let R := moveSourceRadius G j i + a
  let c := MacroExp.ctr d G.corridor nu
  have hcR : moveSupportRadius G ≤ R := by simpa [R, a] using hrad i
  have hm : R - moveSupportRadius G + moveSupportRadius G = R := Nat.sub_add_cancel hcR
  have hmZ : ((R - moveSupportRadius G : ℕ) : ℤ) + (moveSupportRadius G : ℤ) =
      (R : ℤ) := by
    exact_mod_cast hm
  have hlo : c i - ((R - moveSupportRadius G : ℕ) : ℤ) ≤
      moveWindowCentre G nu j ℓ x i := by
    simp only [moveWindowCentre]
    change c i - ((R - moveSupportRadius G : ℕ) : ℤ) ≤
      max (c i - ((R - moveSupportRadius G : ℕ) : ℤ))
        (min (x i) (c i + ((R - moveSupportRadius G : ℕ) : ℤ)))
    exact le_max_left _ _
  have hhi : moveWindowCentre G nu j ℓ x i ≤
      c i + ((R - moveSupportRadius G : ℕ) : ℤ) := by
    simp only [moveWindowCentre]
    change max (c i - ((R - moveSupportRadius G : ℕ) : ℤ))
        (min (x i) (c i + ((R - moveSupportRadius G : ℕ) : ℤ))) ≤
      c i + ((R - moveSupportRadius G : ℕ) : ℤ)
    apply max_le
    · push_cast
      omega
    · exact min_le_right _ _
  change c i - (R : ℕ) ≤ z i + moveWindowCentre G nu j ℓ x i ∧
    z i + moveWindowCentre G nu j ℓ x i ≤ c i + (R : ℕ)
  push_cast at hzi hlo hhi ⊢
  omega

/-- The preceding containment specialized to an index that is literally enumerated by (8.4). -/
theorem moveWindowSupport_at_outerContact_subset (G : FinalGeometry d) (nu : Site 2)
    (j : Fin (d + 1)) (ℓ : ℕ) (x : Site d)
    (_hx : x ∈ fullLatticeOuterBoundary (moveLevelBox G nu j ℓ))
    (hrad : ∀ i, moveSupportRadius G ≤
      moveSourceRadius G j i + (2 * G.moveLocalRadius j + 2 + ℓ)) :
    moveWindowSupport G j (moveWindowCentre G nu j ℓ x) ⊆ moveLevelBox G nu j ℓ :=
  moveWindowSupport_subset_moveLevelBox G nu j ℓ x hrad

theorem determinedBy_moveCoalescenceGood (G : FinalGeometry d) :
    DeterminedBy (moveCoalescenceGood G) (↑(box d G.coalTarget) : Set (Site d)) := by
  simpa only [moveCoalescenceGood] using
    (determinedBy_shellCoalescenceGood (d := d) G.source
      (G.source + G.shell) G.coalTarget)

theorem measurableSet_moveCoalescenceGood (G : FinalGeometry d) :
    MeasurableSet (moveCoalescenceGood G) :=
  (determinedBy_moveCoalescenceGood G).measurableSet_of_finset

theorem determinedBy_moveWindowEvent (G : FinalGeometry d) (j : Fin (d + 1))
    (v : Site d) :
    DeterminedBy (moveWindowEvent G j v) (↑(moveWindowSupport G j v) : Set (Site d)) := by
  have h := determinedBy_siteShift_preimage v
    (determinedBy_shellWindowEvent G.source (G.source + G.shell) G.coalTarget
      (boxSphereFin d (G.source + G.shell)) (box d G.faceTarget)
      (boxSphereFin d (G.moveHitRadius j)))
  simpa only [moveWindowEvent, shellWindowSupport, moveWindowSupport, translatedBox,
    Finset.image_union] using h

theorem measurableSet_moveWindowEvent (G : FinalGeometry d) (j : Fin (d + 1)) (v : Site d) :
    MeasurableSet (moveWindowEvent G j v) := by
  unfold moveWindowEvent
  exact measurable_siteShift v (measurableSet_shellWindowEvent G.source
    (G.source + G.shell) G.coalTarget (boxSphereFin d (G.source + G.shell))
    (box d G.faceTarget) (boxSphereFin d (G.moveHitRadius j)))

theorem siteShift_translatedBox (N : ℕ) (v : Site d) :
    siteShift v (↑(translatedBox N v) : SiteConfig (Site d)) =
      (↑(box d N) : SiteConfig (Site d)) := by
  classical
  ext z
  simp only [mem_siteShift, Finset.mem_coe, translatedBox, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, hyz⟩
    have : y = z := add_right_cancel hyz
    simpa [this] using hy
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- The Section 8.1 counterconfiguration is rejected by every new window: opening exactly the old
source box cannot realize the separately recorded outward target hit. -/
theorem sourceOnly_not_mem_moveWindowEvent [NeZero d] (G : FinalGeometry d)
    (j : Fin (d + 1)) (v : Site d) (hhit : G.source < G.moveHitRadius j) :
    (↑(translatedBox G.source v) : SiteConfig (Site d)) ∉ moveWindowEvent G j v := by
  intro h
  unfold moveWindowEvent at h
  change siteShift v (↑(translatedBox G.source v) : SiteConfig (Site d)) ∈
    shellWindowEvent G.source (G.source + G.shell) G.coalTarget
      (boxSphereFin d (G.source + G.shell)) (box d G.faceTarget)
      (boxSphereFin d (G.moveHitRadius j)) at h
  rw [siteShift_translatedBox] at h
  obtain ⟨x, -, z, hzface, hzconn⟩ :=
    (mem_finiteTargetHit_iff (box d G.faceTarget) (box d G.source)
      (boxSphereFin d (G.moveHitRadius j)) _).1 h.2
  have hzopen := (TargetExt.mem_of_connWithin (zdGraph d) hzconn).1
  rw [boxSphereFin, Finset.mem_filter] at hzface
  obtain ⟨-, i, hzcoord⟩ := hzface
  have hzsource := mem_box.1 (Finset.mem_coe.1 hzopen) i
  have hhit' : (G.source : ℤ) < G.moveHitRadius j := by exact_mod_cast hhit
  rcases hzcoord with hzcoord | hzcoord <;> omega

/-- The deterministic Section 4 relay statement for the recorded window, in normalized
coordinates.  The chosen face endpoint is open and, for every other realization of the same
window with the same complete local-cube pattern, reaches the separately recorded target factor
inside the declared finite support. -/
theorem moveWindowEvent_relay_normalized (G : FinalGeometry d) (j : Fin (d + 1))
    (v : Site d) (hcoal : G.source + G.shell < G.coalTarget)
    (hhit : G.source + G.shell < G.moveHitRadius j) :
    ∀ ω ∈ moveWindowEvent G j v,
      ∃ u ∈ boxSphereFin d (G.source + G.shell), u ∈ siteShift v ω ∧
        ∀ ω' ∈ moveWindowEvent G j v,
          siteShift v ω' ∩ (↑(box d G.coalTarget) : Set (Site d)) =
              siteShift v ω ∩ ↑(box d G.coalTarget) →
            siteShift v ω' ∈ connWithinSet (zdGraph d)
              (↑(shellWindowSupport G.coalTarget (box d G.faceTarget)) : Set (Site d))
              u (↑(boxSphereFin d (G.moveHitRadius j)) : Set (Site d)) := by
  have hsource : G.source ≤ G.source + G.shell := Nat.le_add_right _ _
  have hMN : G.source + G.shell ≤ G.coalTarget := hcoal.le
  have hUface : ∀ u ∈ boxSphereFin d (G.source + G.shell),
      u ∈ boxSphere d (G.source + G.shell) := by
    intro u hu
    rw [← coe_boxSphereFin]
    exact Finset.mem_coe.2 hu
  have hTout : ∀ t ∈ boxSphereFin d (G.moveHitRadius j),
      t ∉ box d (G.source + G.shell) := by
    intro t ht hsmall
    rw [boxSphereFin, Finset.mem_filter] at ht
    obtain ⟨-, i, hi⟩ := ht
    have hti := mem_box.1 hsmall i
    have hc : ((G.source + G.shell : ℕ) : ℤ) < G.moveHitRadius j := by
      exact_mod_cast hhit
    rcases hi with hi | hi <;> omega
  intro ω hω
  have hnorm : siteShift v ω ∈
      shellWindowEvent G.source (G.source + G.shell) G.coalTarget
        (boxSphereFin d (G.source + G.shell)) (box d G.faceTarget)
        (boxSphereFin d (G.moveHitRadius j)) := hω
  obtain ⟨u, hu, huopen, hrelay⟩ :=
    shellWindowEvent_relay_of_face hsource hMN
      (boxSphereFin d (G.source + G.shell)) (box d G.faceTarget)
      (boxSphereFin d (G.moveHitRadius j)) hUface hTout (siteShift v ω) hnorm
  refine ⟨u, hu, huopen, ?_⟩
  intro ω' hω' hagree
  exact hrelay (siteShift v ω') hω' hagree

/-- The actual local-face set after translating a recorded window to the contact centre. -/
def moveWindowFace (G : FinalGeometry d) (v : Site d) : Finset (Site d) :=
  shiftFinset v (boxSphereFin d (G.source + G.shell))

/-- The actual target set of the presently recorded finite target geometry. -/
def moveWindowTarget (G : FinalGeometry d) (j : Fin (d + 1)) (v : Site d) :
    Finset (Site d) :=
  shiftFinset v (boxSphereFin d (G.moveHitRadius j))

/-- Determination by a larger finite set.  This is only a conditional adapter: centering the
current support at an outer-boundary contact makes its containment in `O ⊆ D` impossible, so this
theorem is not a `LevelGeometry.hGdet` discharge for the indexed family below. -/
theorem moveWindowEvent_hGdet (G : FinalGeometry d) (j : Fin (d + 1)) (v : Site d)
    (O : Finset (Site d)) (hSO : moveWindowSupport G j v ⊆ O) :
    DeterminedBy (moveWindowEvent G j v) (↑O : Set (Site d)) :=
  (determinedBy_moveWindowEvent G j v).mono (Finset.coe_subset.2 hSO)

/-- The determination field of `TargetExt.LevelGeometryD`: the declared support is required only
to lie in the level domain `D`, not in the smaller shell box `O`. -/
theorem moveWindowEvent_hGdet_D (G : FinalGeometry d) (j : Fin (d + 1)) (v : Site d)
    (D : Finset (Site d)) (hSD : moveWindowSupport G j v ⊆ D) :
    DeterminedBy (moveWindowEvent G j v) (↑(moveWindowSupport G j v) : Set (Site d)) ∧
      moveWindowSupport G j v ⊆ D :=
  ⟨determinedBy_moveWindowEvent G j v, hSD⟩

/-- `hS` and `hGdet` for a literal (8.4) outer-contact index. -/
theorem moveWindowEvent_hGdet_at_outerContact_D (G : FinalGeometry d) (nu : Site 2)
    (j : Fin (d + 1)) (ℓ : ℕ) (x : Site d)
    (hx : x ∈ fullLatticeOuterBoundary (moveLevelBox G nu j ℓ))
    (hrad : ∀ i, moveSupportRadius G ≤
      moveSourceRadius G j i + (2 * G.moveLocalRadius j + 2 + ℓ)) :
    DeterminedBy (moveWindowEvent G j (moveWindowCentre G nu j ℓ x))
        (↑(moveWindowSupport G j (moveWindowCentre G nu j ℓ x)) : Set (Site d)) ∧
      moveWindowSupport G j (moveWindowCentre G nu j ℓ x) ⊆ moveLevelBox G nu j ℓ :=
  moveWindowEvent_hGdet_D G j _ _
    (moveWindowSupport_at_outerContact_subset G nu j ℓ x hx hrad)

/-- A conditional relay lemma for the intermediate finite target.  The hypotheses are
only geometric inclusions: the complete local cube lies in the observed shell, the entire finite
support lies in `O`, and the recorded target face lies in the level target `T`.

In particular, the implication is pointwise and does not use its probability estimate.  It is not
the required consumer result: at a genuine outer-boundary contact its support-in-`O` premise is
unavailable, and the outward sphere is not the macro target. -/
theorem moveWindowEvent_hrelay (G : FinalGeometry d) (j : Fin (d + 1)) (v : Site d)
    (O Int : Finset (Site d)) (T : Set (Site d))
    (hcoal : G.source + G.shell < G.coalTarget)
    (hhit : G.source + G.shell < G.moveHitRadius j)
    (hlocal : translatedBox G.coalTarget v ⊆ O \ Int)
    (hsupport : moveWindowSupport G j v ⊆ O)
    (htarget : (↑(moveWindowTarget G j v) : Set (Site d)) ⊆ T) :
    ∀ ω ∈ moveWindowEvent G j v,
      ∃ u ∈ moveWindowFace G v, u ∈ ω ∧ ∀ ω' ∈ moveWindowEvent G j v,
        ω' ∩ (↑(O \ Int) : Set (Site d)) = ω ∩ ↑(O \ Int) →
          ω' ∈ TargetExt.toTarget (zdGraph d) O T u := by
  intro ω hω
  obtain ⟨u, hu, huopen, hrelay⟩ :=
    moveWindowEvent_relay_normalized G j v hcoal hhit ω hω
  refine ⟨u + v, ?_, huopen, ?_⟩
  · exact Finset.mem_image.2 ⟨u, hu, rfl⟩
  · intro ω' hω' hagree
    have hagreeLocal :
        siteShift v ω' ∩ (↑(box d G.coalTarget) : Set (Site d)) =
          siteShift v ω ∩ ↑(box d G.coalTarget) := by
      ext z
      by_cases hz : z ∈ box d G.coalTarget
      · have hztr : z + v ∈ O \ Int := hlocal (Finset.mem_image.2 ⟨z, hz, rfl⟩)
        have heq := Set.ext_iff.1 hagree (z + v)
        simpa only [Set.mem_inter_iff, mem_siteShift, Finset.mem_coe, hz, hztr,
          and_true] using heq
      · simp only [Set.mem_inter_iff, mem_siteShift, Finset.mem_coe, hz, and_false]
    have hnorm := hrelay ω' hω' hagreeLocal
    have hshift := (mem_connWithinSet_shift_iff v ω'
      (↑(shellWindowSupport G.coalTarget (box d G.faceTarget)) : Set (Site d)) u
      (↑(boxSphereFin d (G.moveHitRadius j)) : Set (Site d))).1 hnorm
    unfold TargetExt.toTarget
    rw [mem_connWithinSet_iff] at hshift ⊢
    obtain ⟨t, ht, hut⟩ := hshift
    refine ⟨t, htarget ?_, connWithin_mono_set (zdGraph d) ?_ (u + v) t hut⟩
    · rw [moveWindowTarget, coe_shiftFinset]
      exact ht
    · have heq : shiftSet v
          (↑(shellWindowSupport G.coalTarget (box d G.faceTarget)) : Set (Site d)) =
            (↑(moveWindowSupport G j v) : Set (Site d)) := by
        rw [← coe_shiftFinset]
        congr 1
        simp only [shiftFinset, shellWindowSupport, moveWindowSupport, translatedBox,
          Finset.image_union]
      rw [heq]
      exact Finset.coe_subset.2 hsupport

/-- The relay field of `TargetExt.LevelGeometryD`.  The complete local cube still lies in the
observed shell, but the full event support and the relay-to-target path need only lie in `D`.
This is the non-vacuous manuscript geometry: it never asks an outer contact itself to lie in `D`. -/
theorem moveWindowEvent_hrelay_D (G : FinalGeometry d) (j : Fin (d + 1)) (v : Site d)
    (D O Int : Finset (Site d)) (T : Set (Site d))
    (hcoal : G.source + G.shell < G.coalTarget)
    (hhit : G.source + G.shell < G.moveHitRadius j)
    (hlocal : translatedBox G.coalTarget v ⊆ O \ Int)
    (hsupport : moveWindowSupport G j v ⊆ D)
    (htarget : (↑(moveWindowTarget G j v) : Set (Site d)) ⊆ T) :
    ∀ ω ∈ moveWindowEvent G j v,
      ∃ u ∈ moveWindowFace G v, u ∈ ω ∧ ∀ ω' ∈ moveWindowEvent G j v,
        ω' ∩ (↑(O \ Int) : Set (Site d)) = ω ∩ ↑(O \ Int) →
          ω' ∈ TargetExt.toTarget (zdGraph d) D T u := by
  intro ω hω
  obtain ⟨u, hu, huopen, hrelay⟩ :=
    moveWindowEvent_relay_normalized G j v hcoal hhit ω hω
  refine ⟨u + v, Finset.mem_image.2 ⟨u, hu, rfl⟩, huopen, ?_⟩
  intro ω' hω' hagree
  have hagreeLocal :
      siteShift v ω' ∩ (↑(box d G.coalTarget) : Set (Site d)) =
        siteShift v ω ∩ ↑(box d G.coalTarget) := by
    ext z
    by_cases hz : z ∈ box d G.coalTarget
    · have hztr : z + v ∈ O \ Int := hlocal (Finset.mem_image.2 ⟨z, hz, rfl⟩)
      have heq := Set.ext_iff.1 hagree (z + v)
      simpa only [Set.mem_inter_iff, mem_siteShift, Finset.mem_coe, hz, hztr,
        and_true] using heq
    · simp only [Set.mem_inter_iff, mem_siteShift, Finset.mem_coe, hz, and_false]
  have hnorm := hrelay ω' hω' hagreeLocal
  have hshift := (mem_connWithinSet_shift_iff v ω'
    (↑(shellWindowSupport G.coalTarget (box d G.faceTarget)) : Set (Site d)) u
    (↑(boxSphereFin d (G.moveHitRadius j)) : Set (Site d))).1 hnorm
  unfold TargetExt.toTarget
  rw [mem_connWithinSet_iff] at hshift ⊢
  obtain ⟨t, ht, hut⟩ := hshift
  refine ⟨t, htarget ?_, connWithin_mono_set (zdGraph d) ?_ (u + v) t hut⟩
  · rw [moveWindowTarget, coe_shiftFinset]
    exact ht
  · have heq : shiftSet v
        (↑(shellWindowSupport G.coalTarget (box d G.faceTarget)) : Set (Site d)) =
          (↑(moveWindowSupport G j v) : Set (Site d)) := by
      rw [← coe_shiftFinset]
      congr 1
      simp only [shiftFinset, shellWindowSupport, moveWindowSupport, translatedBox,
        Finset.image_union]
    rw [heq]
    exact Finset.coe_subset.2 hsupport

/-- `hrelay` at a literal (8.4) outer contact, with `S ⊆ D` discharged by the clamped-centre
containment rather than assumed. -/
theorem moveWindowEvent_hrelay_at_outerContact_D (G : FinalGeometry d) (nu : Site 2)
    (j : Fin (d + 1)) (ℓ : ℕ) (x : Site d)
    (hx : x ∈ fullLatticeOuterBoundary (moveLevelBox G nu j ℓ))
    (O Int : Finset (Site d)) (T : Set (Site d))
    (hcoal : G.source + G.shell < G.coalTarget)
    (hhit : G.source + G.shell < G.moveHitRadius j)
    (hrad : ∀ i, moveSupportRadius G ≤
      moveSourceRadius G j i + (2 * G.moveLocalRadius j + 2 + ℓ))
    (hlocal : translatedBox G.coalTarget (moveWindowCentre G nu j ℓ x) ⊆ O \ Int)
    (htarget : (↑(moveWindowTarget G j (moveWindowCentre G nu j ℓ x)) : Set (Site d)) ⊆ T) :
    ∀ ω ∈ moveWindowEvent G j (moveWindowCentre G nu j ℓ x),
      ∃ u ∈ moveWindowFace G (moveWindowCentre G nu j ℓ x), u ∈ ω ∧
        ∀ ω' ∈ moveWindowEvent G j (moveWindowCentre G nu j ℓ x),
          ω' ∩ (↑(O \ Int) : Set (Site d)) = ω ∩ ↑(O \ Int) →
            ω' ∈ TargetExt.toTarget (zdGraph d) (moveLevelBox G nu j ℓ) T u := by
  exact moveWindowEvent_hrelay_D G j _ (moveLevelBox G nu j ℓ) O Int T hcoal hhit
    hlocal (moveWindowSupport_at_outerContact_subset G nu j ℓ x hx hrad) htarget

theorem prob_siteShift_preimage (p : unitInterval) (v : Site d)
    {A : Set (SiteConfig (Site d))} (hA : MeasurableSet A) :
    (siteBernoulli fun _ : Site d => p).real (siteShift v ⁻¹' A) =
      (siteBernoulli fun _ : Site d => p).real A := by
  have h := (measurePreserving_siteShift p v).measure_preimage hA.nullMeasurableSet
  rw [measureReal_def, measureReal_def, h]

/-- The three-component union bound for the intermediate outward-sphere window; translation does
not change its probability.  This has the arithmetic shape of (8.6), but not its aspect-88 target
geometry. -/
theorem prob_moveWindowEvent_ge (G : FinalGeometry d) (j : Fin (d + 1))
    (p : unitInterval) (χ : ℝ)
    (hcoal : 1 - χ < (siteBernoulli fun _ : Site d => p).real (moveCoalescenceGood G))
    (hface : 1 - χ < (siteBernoulli fun _ : Site d => p).real
      (finiteTargetHit (box d G.coalTarget) (box d G.source)
        (boxSphereFin d (G.source + G.shell))))
    (htarget : 1 - χ < (siteBernoulli fun _ : Site d => p).real
      (finiteTargetHit (box d G.faceTarget) (box d G.source)
        (boxSphereFin d (G.moveHitRadius j))))
    (v : Site d) :
    1 - 3 * χ <
      (siteBernoulli fun _ : Site d => p).real (moveWindowEvent G j v) := by
  have hbase := one_sub_three_mul_lt_prob_shellWindowEvent p G.source
    (G.source + G.shell) G.coalTarget (boxSphereFin d (G.source + G.shell))
    (box d G.faceTarget) (boxSphereFin d (G.moveHitRadius j))
    (by simpa only [moveCoalescenceGood] using hcoal) hface htarget
  rw [moveWindowEvent, prob_siteShift_preimage p v
    (measurableSet_shellWindowEvent G.source (G.source + G.shell) G.coalTarget
      (boxSphereFin d (G.source + G.shell)) (box d G.faceTarget)
      (boxSphereFin d (G.moveHitRadius j)))]
  exact hbase

/-- The strict retained-margin calculation for the intermediate event.  At extraction one takes
`χ = beta² / 4`; the three component estimates therefore put the recorded window strictly above
`1 - 3 beta² / 4`, which is itself strictly above its stored threshold `1 - 3 beta²`.  This is not
Equation (8.6) until the target component is replaced by the selected aspect geometry. -/
theorem prob_moveWindowEvent_extraction (G : FinalGeometry d) (j : Fin (d + 1))
    (p : unitInterval) (hbeta : 0 < G.beta)
    (hcoal : 1 - G.beta ^ 2 / 4 <
      (siteBernoulli fun _ : Site d => p).real (moveCoalescenceGood G))
    (hface : 1 - G.beta ^ 2 / 4 < (siteBernoulli fun _ : Site d => p).real
      (finiteTargetHit (box d G.coalTarget) (box d G.source)
        (boxSphereFin d (G.source + G.shell))))
    (htarget : 1 - G.beta ^ 2 / 4 < (siteBernoulli fun _ : Site d => p).real
      (finiteTargetHit (box d G.faceTarget) (box d G.source)
        (boxSphereFin d (G.moveHitRadius j))))
    (v : Site d) :
    1 - 3 * G.beta ^ 2 < 1 - 3 * G.beta ^ 2 / 4 ∧
      1 - 3 * G.beta ^ 2 / 4 <
        (siteBernoulli fun _ : Site d => p).real (moveWindowEvent G j v) := by
  constructor
  · nlinarith [sq_pos_of_pos hbeta]
  · have h := prob_moveWindowEvent_ge G j p (G.beta ^ 2 / 4) hcoal hface htarget v
    convert h using 1 <;> ring

/-- A single intermediate indexed cylinder.  The orientation and level select the macro centre
and the erosion depth used to move the contact window inside its level box. -/
def rawMoveWindowExperiment (G : FinalGeometry d) (nu : Site 2) (j : Fin (d + 1))
    (ell : ℕ) (x : Site d) : CylinderExperiment d where
  support := moveWindowSupport G j (moveWindowCentre G nu j ell x)
  event := moveWindowEvent G j (moveWindowCentre G nu j ell x)
  determined := determinedBy_moveWindowEvent G j (moveWindowCentre G nu j ell x)
  measurable' := measurableSet_moveWindowEvent G j (moveWindowCentre G nu j ell x)

/-- This enumerates the index set displayed in (8.5), but its entries are still the intermediate
outward-sphere cylinders above; enumeration alone does not make them the Section 8.2 family. -/
def moveWindowBounds (G : FinalGeometry d) : List (CylinderExperiment d × ℝ) :=
  (MacroExp.nbrs (0 : Site 2)).toList.flatMap fun nu =>
    (Finset.univ : Finset (Fin (d + 1))).toList.flatMap fun j =>
      (Finset.range (G.moveLevelCount j)).toList.flatMap fun ell =>
        (fullLatticeOuterBoundary (moveLevelBox G nu j ell)).toList.map fun x =>
          (rawMoveWindowExperiment G nu j ell x, 1 - 3 * G.beta ^ 2)

/-- The current intermediate outward-sphere family belonging to a certificate. -/
def Certificate2.moveWindowBounds (C : Certificate2 d) :
    List (CylinderExperiment d × ℝ) :=
  KNAll.Site.LeftImp2.moveWindowBounds C.finalGeometry

/-- `S_max` from (8.7), computed as the maximum starting from `1`. -/
def maxMoveSupportCard (G : FinalGeometry d) : ℕ :=
  (moveWindowBounds G).foldl (fun n b => max n b.1.support.card) 1

def Certificate2.maxMoveSupportCard (C : Certificate2 d) : ℕ :=
  KNAll.Site.LeftImp2.maxMoveSupportCard C.finalGeometry

/-- The explicit cylinder part of the stability radius (8.9). -/
def moveWindowStabilityRadius (G : FinalGeometry d) : ℝ :=
  9 * G.beta ^ 2 / (8 * maxMoveSupportCard G)

def Certificate2.moveStabilityRadius (C : Certificate2 d) : ℝ :=
  moveWindowStabilityRadius C.finalGeometry

/-! ## The recorded initial-corridor cylinder

The downstream spelling `InitEnt.wideLongBoxExperiment C r t y` cannot be imported here: that
module imports `Certificate2`.  The following primitive-parameter spelling is the same
minimal-support cylinder.  Writing the four geometric parameters separately also removes the
apparent self-reference when the four experiments are appended to the certificate's own `bounds`
list.
-/

/-- The innermost target box, whose planar and transverse radii are respectively the corridor
radius and half-width less `levels + 2 faceTarget + 1`. -/
def initialCorridorTarget (d L F r t : ℕ) (y : Site 2) : Finset (Site d) :=
  MacroExp.abox (MacroExp.ctr d r y) (r - (L + 2 * F + 1)) (t - (L + 2 * F + 1))

/-- The fresh entry face of the origin corridor. -/
def initialCorridorEntryFace (d r t : ℕ) (y : Site 2) : Finset (Site d) :=
  (MacroExp.E d r t 0 y).filter fun g =>
    ∃ s ∈ MacroExp.Q d r t 0, (zdGraph d).Adj s g

/-- The minimal-support wide long-box event of `InitEnt`. -/
def wideLongBoxEvent (d L F r t : ℕ) (y : Site 2) : Set (SiteConfig (Site d)) :=
  {omega | ∃ g ∈ initialCorridorEntryFace d r t y,
    omega ∈ connWithinSet (zdGraph d) (↑(MacroExp.E d r t 0 y) : Set (Site d)) g
      (↑(initialCorridorTarget d L F r t y) : Set (Site d))}

theorem determinedBy_wideLongBoxEvent (d L F r t : ℕ) (y : Site 2) :
    DeterminedBy (wideLongBoxEvent d L F r t y)
      (↑(MacroExp.E d r t 0 y) : Set (Site d)) := by
  rw [determinedBy_iff]
  intro omega omega' hagree
  simp only [wideLongBoxEvent, Set.mem_setOf_eq]
  apply exists_congr
  intro g
  apply and_congr_right
  intro _hg
  exact (determinedBy_iff _ _).1
    (determinedBy_connWithinSet (zdGraph d) (↑(MacroExp.E d r t 0 y) : Set (Site d)) g
      (↑(initialCorridorTarget d L F r t y) : Set (Site d))) omega omega' hagree

theorem measurableSet_wideLongBoxEvent (d L F r t : ℕ) (y : Site 2) :
    MeasurableSet (wideLongBoxEvent d L F r t y) :=
  (determinedBy_wideLongBoxEvent d L F r t y).measurableSet_of_finset

/-- The minimal-support finite cylinder recorded for an oriented initial corridor. -/
def rawWideLongBoxExperiment (d L F r t : ℕ) (y : Site 2) : CylinderExperiment d where
  support := MacroExp.E d r t 0 y
  event := wideLongBoxEvent d L F r t y
  determined := determinedBy_wideLongBoxEvent d L F r t y
  measurable' := measurableSet_wideLongBoxEvent d L F r t y

/-- The wide long-box experiment at the geometry stored in `C`. -/
def Certificate2.wideLongBoxExperiment (C : Certificate2 d) (y : Site 2) :
    CylinderExperiment d :=
  rawWideLongBoxExperiment d C.levels C.faceTarget C.corridor C.halfWidth y

/-- **A certificate holds at `q`.**  Every listed threshold is strictly exceeded by the probability
of its experiment at `q`, the seed inequality holds at `q`, and `q` is at most the extraction
parameter. -/
def Certificate2.ValidAt2 (C : Certificate2 d) (q : unitInterval) : Prop :=
  (∀ b ∈ C.bounds, b.2 < b.1.prob q) ∧
    (1 - (q : ℝ) ^ C.seedSize) ^ C.seedCount < C.delta ∧ q ≤ C.p₀

/-- **Well-formedness.**  Parameter-free: no probability at a parameter `q` appears. -/
structure Certificate2.WellFormed (C : Certificate2 d) : Prop where
  /-- Every clause of `Certificate.WellFormed`: the nonempty list, the thresholds in `[0, 1)`, the
  order of the scales, the fit of the blocks, the budget against the density, the percolation of
  the density on the plane, and the presence of the two experiments in the list. -/
  base : C.toCertificate.WellFormed
  /-- The planar margin is positive. -/
  eps_pos : 0 < C.eps
  /-- Thirty-two per-target failure margins fit below `1 - density`. -/
  eps_le : 32 * C.eps ≤ 1 - (C.density : ℝ)
  /-- The explicit value of the manuscript-safe tolerance. -/
  beta_eq : C.beta = betaOf d C.density
  /-- The retained reservation error satisfies (8.10). -/
  eps_le_beta : C.eps ≤ C.beta
  /-- `c_e = e / 8`. -/
  deltaC_eq : C.deltaC = C.eps / 8
  /-- `δ_e = e² / 96`. -/
  delta_eq : C.delta = C.eps ^ 2 / 96
  /-- `η = δ² · δ_C`. -/
  eta_eq : C.eta = C.delta ^ 2 * C.deltaC
  /-- The face tolerance is at most `η`. -/
  faceTol_le_eta : C.faceTol ≤ C.eta
  /-- The coalescence tolerance is at most `η`. -/
  coalTol_le_eta : C.coalTol ≤ C.eta
  /-- At least one contact is required. -/
  contacts_pos : 0 < C.contacts
  /-- Seeds are not empty. -/
  seedSize_pos : 0 < C.seedSize
  /-- Among `N` contacts the greedy selection at separation `1 + 2 faceTarget` keeps at least
  `N / (8 faceTarget + 5)^d`, so `N ≥ k (8 faceTarget + 5)^d` keeps at least `k`. -/
  contacts_ge : C.seedCount * (8 * C.faceTarget + 5) ^ d ≤ C.contacts
  /-- A seed is an interval box of depth `1` and side `2 (1 + 2 faceTarget) + 1`. -/
  seedSize_ge : (4 * C.faceTarget + 3) ^ (d - 1) ≤ C.seedSize
  /-- The seed inequality at the extraction parameter. -/
  seed : (1 - (C.p₀ : ℝ) ^ C.seedSize) ^ C.seedCount < C.delta
  /-- The level inequality at the extraction parameter. -/
  level : 1 < (C.levels : ℝ) * C.delta * (1 - (C.p₀ : ℝ)) ^ (2 * d * C.contacts)
  /-- The macro spacing is at least `L (2 faceTarget + 2)`. -/
  spacing_ge_levels : C.levels * (2 * C.faceTarget + 2) ≤ C.spacing
  /-- The corridor radius is at least `L (2 faceTarget + 2)`. -/
  corridor_ge : C.levels * (2 * C.faceTarget + 2) ≤ C.corridor
  /-- The absolute lower scale in (0.3). -/
  corridor_ge_44 : 44 ≤ C.corridor
  /-- The transverse half-width leaves room for `levels` levels, the seed layer and a cube. -/
  halfWidth_ge : C.levels + C.faceTarget + 1 ≤ C.halfWidth
  /-- Every coordinate radius of every inner level box is nonnegative. -/
  innerRadius_ge :
    C.levels + 2 * C.faceTarget + 1 ≤ min C.corridor C.halfWidth
  /-- The isotropic core `c_z + Lambda_(3r)` and cube `c_z + Lambda_(5r)` fit transversely. -/
  halfWidth_ge_five_corridor : 5 * C.corridor ≤ C.halfWidth
  /-- The extracted target-extension calls use the annular coalescence scale as `M_j`. -/
  moveLocalRadius_eq : ∀ j, C.moveLocalRadius j = C.source + C.shell
  /-- Every local inflation radius is nonzero. -/
  moveLocalRadius_ge : ∀ j, 1 ≤ C.moveLocalRadius j
  /-- The quantitative scale separation (0.3), for every one of the `d+1` calls. -/
  moveScale : ∀ j,
    100 * (d + 1) * (C.moveLocalRadius j + 1) < C.corridor
  /-- The selected target geometry of every call is supported in the recorded face box. -/
  moveTargetRadius_eq : ∀ j, C.moveTargetRadius j = C.faceTarget
  /-- The target-hitting face lies strictly outside the whole local coalescence support. -/
  moveHitRadius_eq : ∀ j, C.moveHitRadius j = C.coalTarget + 1
  /-- The simultaneous choice following (3.6) uses the common level count `L`. -/
  moveLevelCount_eq : ∀ j, C.moveLevelCount j = C.levels
  /-- Experiments are made from the final numerical geometry and only then appended. -/
  bounds_eq : C.bounds = C.preMoveBounds ++ C.moveWindowBounds
  /-- The four oriented initial-corridor cylinders are recorded at the threshold prescribed in
  `CORRIDOR_CROSSING.md`. -/
  wideLongBox_mem : 3 ≤ d → ∀ y ∈ MacroExp.nbrs (0 : Site 2),
    (C.wideLongBoxExperiment y, 1 - C.eps / 8) ∈ C.bounds
  /-- The slab width is twice the half-width. -/
  width_eq : C.width = 2 * C.halfWidth

/-! ## Consequences of well-formedness -/

theorem Certificate2.WellFormed.delta_pos {C : Certificate2 d} (h : C.WellFormed) : 0 < C.delta := by
  rw [h.delta_eq]; have := h.eps_pos; positivity

theorem Certificate2.WellFormed.deltaC_pos {C : Certificate2 d} (h : C.WellFormed) :
    0 < C.deltaC := by
  rw [h.deltaC_eq]; have := h.eps_pos; positivity

theorem Certificate2.WellFormed.eta_pos {C : Certificate2 d} (h : C.WellFormed) : 0 < C.eta := by
  rw [h.eta_eq]; have := h.delta_pos; have := h.deltaC_pos; positivity

/-- `η = ε⁵ / 73728`. -/
theorem Certificate2.WellFormed.eta_eq_pow {C : Certificate2 d} (h : C.WellFormed) :
    C.eta = C.eps ^ 5 / 73728 := by
  rw [h.eta_eq, h.delta_eq, h.deltaC_eq]; ring

theorem Certificate2.WellFormed.beta_pos {C : Certificate2 d} (h : C.WellFormed) :
    0 < C.beta := lt_of_lt_of_le h.eps_pos h.eps_le_beta

theorem Certificate2.WellFormed.beta_le_one {C : Certificate2 d} (h : C.WellFormed) :
    C.beta ≤ 1 := by
  rw [h.beta_eq, betaOf]
  have hrho0 : 0 ≤ (1 - (C.density : ℝ)) / 32 := by
    have := C.density.2.2
    positivity
  have hrho1 : (1 - (C.density : ℝ)) / 32 ≤ 1 := by
    have := C.density.2.1
    linarith
  have hp : ((1 - (C.density : ℝ)) / 32) ^ (2 ^ (d + 1)) ≤ 1 :=
    pow_le_one₀ hrho0 hrho1
  have hden : (1 : ℝ) ≤ 96 ^ (2 ^ (d + 1) - 1) := by
    exact one_le_pow₀ (by norm_num)
  exact (div_le_one (by positivity)).2 (le_trans hp hden)

theorem Certificate2.WellFormed.eps_le_one {C : Certificate2 d} (h : C.WellFormed) : C.eps ≤ 1 := by
  have := h.eps_le; have := C.density.2.1; linarith

theorem Certificate2.WellFormed.levels_pos {C : Certificate2 d} (h : C.WellFormed) : 0 < C.levels := by
  rcases Nat.eq_zero_or_pos C.levels with h0 | h0
  · exfalso; have := h.level; rw [h0] at this; norm_num at this
  · exact h0

/-- The actual extracted geometry satisfies the support-radius premise of the clamped window.
This uses the certificate's true order `coalTarget ≤ faceTarget`; it does not reverse that order. -/
theorem Certificate2.WellFormed.moveSupportRadius_le_levelRadius {C : Certificate2 d}
    (h : C.WellFormed) (j : Fin (d + 1)) (ℓ : ℕ) (i : Fin d) :
    moveSupportRadius C.finalGeometry ≤
      moveSourceRadius C.finalGeometry j i +
        (2 * C.finalGeometry.moveLocalRadius j + 2 + ℓ) := by
  have hFr : C.faceTarget ≤ C.corridor := by
    have hL : 1 ≤ C.levels := h.levels_pos
    have hF0 : C.faceTarget ≤ 2 * C.faceTarget + 2 := by omega
    have hmult : 2 * C.faceTarget + 2 ≤ C.levels * (2 * C.faceTarget + 2) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (2 * C.faceTarget + 2) hL
    have hF : C.faceTarget ≤ C.levels * (2 * C.faceTarget + 2) := hF0.trans hmult
    exact hF.trans h.corridor_ge
  change max C.coalTarget C.faceTarget ≤
    moveSourceRadius C.finalGeometry j i + (2 * C.moveLocalRadius j + 2 + ℓ)
  rw [max_eq_right h.base.coalTarget_le_faceTarget]
  simp only [moveSourceRadius, Certificate2.finalGeometry]
  split <;> omega

/-- The `hS`/`hGdet` discharge for the geometry of an actual well-formed certificate. -/
theorem Certificate2.moveWindowEvent_hGdet_at_outerContact_D (C : Certificate2 d)
    (hwf : C.WellFormed) (nu : Site 2) (j : Fin (d + 1)) (ℓ : ℕ) (x : Site d)
    (hx : x ∈ fullLatticeOuterBoundary (moveLevelBox C.finalGeometry nu j ℓ)) :
    DeterminedBy
        (moveWindowEvent C.finalGeometry j (moveWindowCentre C.finalGeometry nu j ℓ x))
        (↑(moveWindowSupport C.finalGeometry j
          (moveWindowCentre C.finalGeometry nu j ℓ x)) : Set (Site d)) ∧
      moveWindowSupport C.finalGeometry j (moveWindowCentre C.finalGeometry nu j ℓ x) ⊆
        moveLevelBox C.finalGeometry nu j ℓ :=
  _root_.KNAll.Site.LeftImp2.moveWindowEvent_hGdet_at_outerContact_D
    C.finalGeometry nu j ℓ x hx
      (fun i => hwf.moveSupportRadius_le_levelRadius j ℓ i)

/-- The D-relay adapter for an actual well-formed certificate.  Its only remaining geometric
premises are the manuscript ones: the local cube is in the observed shell and the selected target
is in `T`; support containment in `D` is discharged here. -/
theorem Certificate2.moveWindowEvent_hrelay_at_outerContact_D (C : Certificate2 d)
    (hwf : C.WellFormed) (nu : Site 2) (j : Fin (d + 1)) (ℓ : ℕ) (x : Site d)
    (hx : x ∈ fullLatticeOuterBoundary (moveLevelBox C.finalGeometry nu j ℓ))
    (O Int : Finset (Site d)) (T : Set (Site d))
    (hcoal : C.source + C.shell < C.coalTarget)
    (hlocal : translatedBox C.coalTarget (moveWindowCentre C.finalGeometry nu j ℓ x) ⊆
      O \ Int)
    (htarget :
      (↑(moveWindowTarget C.finalGeometry j
        (moveWindowCentre C.finalGeometry nu j ℓ x)) : Set (Site d)) ⊆ T) :
    ∀ ω ∈ moveWindowEvent C.finalGeometry j (moveWindowCentre C.finalGeometry nu j ℓ x),
      ∃ u ∈ moveWindowFace C.finalGeometry (moveWindowCentre C.finalGeometry nu j ℓ x),
        u ∈ ω ∧
          ∀ ω' ∈ moveWindowEvent C.finalGeometry j
              (moveWindowCentre C.finalGeometry nu j ℓ x),
            ω' ∩ (↑(O \ Int) : Set (Site d)) = ω ∩ ↑(O \ Int) →
              ω' ∈ TargetExt.toTarget (zdGraph d)
                (moveLevelBox C.finalGeometry nu j ℓ) T u := by
  have hhit : C.finalGeometry.source + C.finalGeometry.shell <
      C.finalGeometry.moveHitRadius j := by
    change C.source + C.shell < C.moveHitRadius j
    rw [hwf.moveHitRadius_eq]
    omega
  exact _root_.KNAll.Site.LeftImp2.moveWindowEvent_hrelay_at_outerContact_D
    C.finalGeometry nu j ℓ x hx O Int T hcoal hhit
      (fun i => hwf.moveSupportRadius_le_levelRadius j ℓ i) hlocal htarget

theorem Certificate2.WellFormed.seedCount_pos {C : Certificate2 d} (h : C.WellFormed) :
    0 < C.seedCount := by
  rcases Nat.eq_zero_or_pos C.seedCount with h0 | h0
  · exfalso
    have hs := h.seed
    rw [h0, pow_zero, h.delta_eq] at hs
    have := h.eps_le_one; have := h.eps_pos
    nlinarith
  · exact h0

/-- The recorded initial-corridor clause is a strict probability bound at every parameter where
the certificate is valid. -/
theorem Certificate2.WellFormed.wideLongBox_lt_prob {C : Certificate2 d}
    (h : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q) (hd : 3 ≤ d)
    {y : Site 2} (hy : y ∈ MacroExp.nbrs (0 : Site 2)) :
    1 - C.eps / 8 < (C.wideLongBoxExperiment y).prob q :=
  hv.1 _ (h.wideLongBox_mem hd y hy)

/-- Every one of the explicitly generated target-hitting windows occurs in the final bounds list. -/
theorem Certificate2.WellFormed.moveWindow_mem {C : Certificate2 d} (h : C.WellFormed)
    {b : CylinderExperiment d × ℝ} (hb : b ∈ C.moveWindowBounds) : b ∈ C.bounds := by
  rw [h.bounds_eq]
  exact List.mem_append_right _ hb

/-- Validity reads the recorded threshold of every target-hitting window. -/
theorem Certificate2.WellFormed.moveWindow_lt_prob {C : Certificate2 d}
    (h : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    {b : CylinderExperiment d × ℝ} (hb : b ∈ C.moveWindowBounds) :
    b.2 < b.1.prob q :=
  hv.1 b (h.moveWindow_mem hb)

/-- Extraction proves a stronger margin for the current intermediate family. -/
def Certificate2.MoveMarginAt (C : Certificate2 d) (p : unitInterval) : Prop :=
  ∀ b ∈ C.moveWindowBounds, 1 - 3 * C.beta ^ 2 / 4 < b.1.prob p

/-- No recorded move-window clause is vacuous.  The extraction margin and `beta ≤ 1` make every
one of their probabilities strictly positive, hence every event has a realizing configuration. -/
theorem Certificate2.moveWindow_event_nonempty {C : Certificate2 d} (hwf : C.WellFormed)
    {p : unitInterval} (hm : C.MoveMarginAt p) {b : CylinderExperiment d × ℝ}
    (hb : b ∈ C.moveWindowBounds) : b.1.event.Nonempty := by
  have hp := hm b hb
  have hβ := hwf.beta_le_one
  have hβ0 := hwf.beta_pos
  have hpos : 0 < b.1.prob p := by
    have hsq : C.beta ^ 2 ≤ 1 := by nlinarith [sq_nonneg C.beta]
    nlinarith
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [CylinderExperiment.prob, hne, measureReal_empty] at hpos
  exact lt_irrefl 0 hpos

theorem moveWindowBounds_threshold {G : FinalGeometry d}
    {b : CylinderExperiment d × ℝ} (hb : b ∈ moveWindowBounds G) :
    b.2 = 1 - 3 * G.beta ^ 2 := by
  simp only [moveWindowBounds, List.mem_flatMap, Finset.mem_toList, List.mem_map] at hb
  obtain ⟨nu, _, j, _, ell, _, x, _, rfl⟩ := hb
  rfl

theorem le_foldl_max_supportCard_initial (L : List (CylinderExperiment d × ℝ)) (n : ℕ) :
    n ≤ L.foldl (fun k a => max k a.1.support.card) n := by
  induction L generalizing n with
  | nil => exact le_rfl
  | cons a L ih =>
      exact le_trans (le_max_left n a.1.support.card) (ih (max n a.1.support.card))

theorem le_foldl_max_supportCard (L : List (CylinderExperiment d × ℝ)) (n : ℕ)
    {b : CylinderExperiment d × ℝ} (hb : b ∈ L) :
    b.1.support.card ≤ L.foldl (fun k a => max k a.1.support.card) n := by
  induction L generalizing n with
  | nil => simp at hb
  | cons a L ih =>
      simp only [List.mem_cons] at hb
      rcases hb with hba | hb
      · subst b
        exact le_trans (le_max_right n a.1.support.card)
          (le_foldl_max_supportCard_initial L (max n a.1.support.card))
      · exact ih (max n a.1.support.card) hb

theorem moveWindow_support_card_le_max {G : FinalGeometry d}
    {b : CylinderExperiment d × ℝ} (hb : b ∈ moveWindowBounds G) :
    b.1.support.card ≤ maxMoveSupportCard G :=
  le_foldl_max_supportCard _ 1 hb

theorem one_le_maxMoveSupportCard (G : FinalGeometry d) : 1 ≤ maxMoveSupportCard G := by
  exact le_foldl_max_supportCard_initial (moveWindowBounds G) 1

/-- **The cycle-free form of inner-box nonemptiness.**  `Corridor` and `LongBox` are downstream of
this file, so the conclusion is stated for the radius from which `Corridor.ρI` is definitionally
built.  Rewriting `Corridor.ρI`, `Corridor.scalesOf`, and `Corridor.ρD` turns this directly into
nonnegativity of every coordinate radius, and hence the centre witnesses nonemptiness. -/
theorem Certificate2.WellFormed.innerBox_nonempty {C : Certificate2 d} (h : C.WellFormed)
    {i : ℕ} (hi : i < C.levels) (j : Fin d) :
    0 ≤ MacroExp.rad C.corridor C.halfWidth j - (i : ℤ) - 1 -
      (2 * (C.faceTarget : ℤ) + 1) := by
  have hc : C.levels + 2 * C.faceTarget + 1 ≤ C.corridor :=
    le_trans h.innerRadius_ge (min_le_left _ _)
  have ht : C.levels + 2 * C.faceTarget + 1 ≤ C.halfWidth :=
    le_trans h.innerRadius_ge (min_le_right _ _)
  simp only [MacroExp.rad]
  split
  · omega
  · omega

/-- **The level inequality transfers downward**: for `q ≤ p₀`, `L · δ · (1 - q)^(2dN) > 1`. -/
theorem Certificate2.WellFormed.level_of_le {C : Certificate2 d} (h : C.WellFormed)
    {q : unitInterval} (hq : q ≤ C.p₀) :
    1 < (C.levels : ℝ) * C.delta * (1 - (q : ℝ)) ^ (2 * d * C.contacts) := by
  have hq' : (q : ℝ) ≤ (C.p₀ : ℝ) := hq
  have hp1 : (C.p₀ : ℝ) ≤ 1 := C.p₀.2.2
  have hpow : (1 - (C.p₀ : ℝ)) ^ (2 * d * C.contacts) ≤ (1 - (q : ℝ)) ^ (2 * d * C.contacts) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have hδ := h.delta_pos
  calc (1 : ℝ) < (C.levels : ℝ) * C.delta * (1 - (C.p₀ : ℝ)) ^ (2 * d * C.contacts) := h.level
    _ ≤ (C.levels : ℝ) * C.delta * (1 - (q : ℝ)) ^ (2 * d * C.contacts) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ## The regressions -/

/-- A certificate with no bounds is not well-formed. -/
theorem Certificate2.not_wellFormed_of_bounds_eq_nil {C : Certificate2 d} (h : C.bounds = []) :
    ¬ C.WellFormed :=
  fun hwf => hwf.base.bounds_ne_nil h

/-- **A well-formed certificate is not valid at parameter `0`.** -/
theorem Certificate2.not_validAt2_of_coe_eq_zero [NeZero d] {C : Certificate2 d} (hC : C.WellFormed)
    {q : unitInterval} (hq : (q : ℝ) = 0) : ¬ C.ValidAt2 q :=
  fun hv => C.toCertificate.not_validAt_of_coe_eq_zero hC.base hq hv.1

theorem Certificate2.not_validAt2_zero [NeZero d] {C : Certificate2 d} (hC : C.WellFormed) :
    ¬ C.ValidAt2 0 :=
  C.not_validAt2_of_coe_eq_zero hC rfl

theorem not_exists_wellFormed_validAt2_zero [NeZero d] :
    ¬ ∃ C : Certificate2 d, C.WellFormed ∧ C.ValidAt2 0 :=
  fun ⟨_, hwf, hv⟩ => Certificate2.not_validAt2_zero hwf hv

/-! ## Stability -/

/-- **The seed inequality survives a small shift of the parameter**: `q ↦ (1 - q^s)^k` is
continuous. -/
theorem exists_nhds_seed_lt {s k : ℕ} {δ : ℝ} {p : unitInterval}
    (h : (1 - (p : ℝ) ^ s) ^ k < δ) :
    ∃ ε > 0, ∀ q : unitInterval, |(q : ℝ) - (p : ℝ)| < ε → (1 - (q : ℝ) ^ s) ^ k < δ := by
  have hf : Continuous fun x : ℝ => (1 - x ^ s) ^ k := by fun_prop
  obtain ⟨ε, hε, hεf⟩ := Metric.continuousAt_iff.1 hf.continuousAt
    (δ - (1 - (p : ℝ) ^ s) ^ k) (by linarith)
  refine ⟨ε, hε, fun q hq => ?_⟩
  have hd := hεf (x := (q : ℝ)) (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at hd
  linarith [le_abs_self ((1 - (q : ℝ) ^ s) ^ k - (1 - (p : ℝ) ^ s) ^ k)]

/-- The margin `9 beta^2 / 4` and the Lipschitz constant `S_max` give (8.9). -/
theorem moveWindowBounds_valid_of_lt_radius (G : FinalGeometry d) (hbeta : 0 < G.beta)
    {p : unitInterval}
    (hmargin : ∀ b ∈ moveWindowBounds G,
      1 - 3 * G.beta ^ 2 / 4 < b.1.prob p)
    (q : unitInterval) (hq : |(q : ℝ) - (p : ℝ)| < moveWindowStabilityRadius G) :
    ∀ b ∈ moveWindowBounds G, b.2 < b.1.prob q := by
  intro b hb
  have hmaxNat : 0 < maxMoveSupportCard G :=
    lt_of_lt_of_le Nat.zero_lt_one (one_le_maxMoveSupportCard G)
  have hmax : (0 : ℝ) < maxMoveSupportCard G := by exact_mod_cast hmaxNat
  have hcardNat := moveWindow_support_card_le_max hb
  have hcard : (b.1.support.card : ℝ) ≤ maxMoveSupportCard G := by exact_mod_cast hcardNat
  have hloss : (b.1.support.card : ℝ) * |(p : ℝ) - (q : ℝ)| <
      9 * G.beta ^ 2 / 8 := by
    calc
      (b.1.support.card : ℝ) * |(p : ℝ) - (q : ℝ)|
          ≤ (maxMoveSupportCard G : ℝ) * |(p : ℝ) - (q : ℝ)| :=
        mul_le_mul_of_nonneg_right hcard (abs_nonneg _)
      _ < (maxMoveSupportCard G : ℝ) * moveWindowStabilityRadius G := by
        apply mul_lt_mul_of_pos_left _ hmax
        simpa only [abs_sub_comm] using hq
      _ = 9 * G.beta ^ 2 / 8 := by
        rw [moveWindowStabilityRadius]
        field_simp
  have hdiff : b.1.prob p - b.1.prob q < 9 * G.beta ^ 2 / 8 := by
    calc
      b.1.prob p - b.1.prob q ≤ |b.1.prob p - b.1.prob q| := le_abs_self _
      _ ≤ (b.1.support.card : ℝ) * |(p : ℝ) - (q : ℝ)| :=
        b.1.abs_prob_sub_le p q
      _ < 9 * G.beta ^ 2 / 8 := hloss
  have hm := hmargin b hb
  rw [moveWindowBounds_threshold hb]
  nlinarith only [hdiff, hm]

/-- **A certificate valid at its extraction point is valid on a left neighbourhood.**  The radius
is the minimum of the old finite-list radius, the explicit move-window radius (8.9), and the seed
radius. -/
theorem Certificate2.exists_valid_nhds2 (C : Certificate2 d) {p : unitInterval}
    (hwf : C.WellFormed) (h : C.ValidAt2 p) (hmargin : C.MoveMarginAt p) :
    ∃ ε > 0, ∀ q : unitInterval, (p : ℝ) - ε < (q : ℝ) → q ≤ p → C.ValidAt2 q := by
  have hpre : ∀ b ∈ C.preMoveBounds, b.2 < b.1.prob p := by
    intro b hb
    exact h.1 b (by rw [hwf.bounds_eq]; exact List.mem_append_left _ hb)
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_valid_nhds_list C.preMoveBounds hpre
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_nhds_seed_lt h.2.1
  have hmovePos : 0 < C.moveStabilityRadius := by
    rw [Certificate2.moveStabilityRadius, moveWindowStabilityRadius]
    positivity [hwf.beta_pos, one_le_maxMoveSupportCard C.finalGeometry]
  let ε := min (min ε₁ C.moveStabilityRadius) ε₂
  have hε : 0 < ε := lt_min (lt_min hε₁ hmovePos) hε₂
  refine ⟨ε, hε, fun q hq hqp => ?_⟩
  have hqp' : (q : ℝ) ≤ (p : ℝ) := hqp
  have habs : |(q : ℝ) - (p : ℝ)| < ε := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hold := h₁ q (lt_of_lt_of_le habs (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hmove : ∀ b ∈ C.moveWindowBounds, b.2 < b.1.prob q := by
    apply moveWindowBounds_valid_of_lt_radius C.finalGeometry hwf.beta_pos
      hmargin q
    exact lt_of_lt_of_le habs (le_trans (min_le_left _ _) (min_le_right _ _))
  refine ⟨?_, h₂ q (lt_of_lt_of_le habs (min_le_right _ _)), le_trans hqp h.2.2⟩
  intro b hb
  rw [hwf.bounds_eq] at hb
  rcases List.mem_append.1 hb with hb | hb
  · exact hold b hb
  · exact hmove b hb

/-! ## Parallel straight channels -/

namespace InitialCorridorChannels

/-- The point with directed planar coordinate `c`, transverse coordinate `u`, and all other
coordinates zero. -/
def point (jp jt : Fin d) (u c : ℤ) : Site d :=
  fun j => if j = jp then c else if j = jt then u else 0

@[simp] theorem point_jp {jp jt : Fin d} (u c : ℤ) : point jp jt u c jp = c := by
  simp [point]

@[simp] theorem point_jt {jp jt : Fin d} (hne : jt ≠ jp) (u c : ℤ) :
    point jp jt u c jt = u := by
  simp [point, hne]

theorem point_other {jp jt : Fin d} {j : Fin d} (h1 : j ≠ jp) (h2 : j ≠ jt) (u c : ℤ) :
    point jp jt u c j = 0 := by
  simp [point, h1, h2]

/-- A straight channel, represented as a coordinate interval box. -/
def channel (jp jt : Fin d) (lo hi u : ℤ) : Finset (Site d) :=
  Fintype.piFinset fun j => Finset.Icc
    (min (point jp jt u lo j) (point jp jt u hi j))
    (max (point jp jt u lo j) (point jp jt u hi j))

theorem mem_channel {jp jt : Fin d} (hne : jt ≠ jp) {lo hi u : ℤ} {x : Site d} :
    x ∈ channel jp jt lo hi u ↔
      (min lo hi ≤ x jp ∧ x jp ≤ max lo hi) ∧ x jt = u ∧
        ∀ j, j ≠ jp → j ≠ jt → x j = 0 := by
  simp only [channel, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · intro hx
    refine ⟨?_, ?_, ?_⟩
    · simpa using hx jp
    · have h := hx jt
      simp only [point_jt hne] at h
      simp at h
      omega
    · intro j h1 h2
      have h := hx j
      simp only [point_other h1 h2] at h
      simp at h
      omega
  · rintro ⟨hjp, hjt, hother⟩ j
    by_cases h1 : j = jp
    · subst h1; simpa using hjp
    · by_cases h2 : j = jt
      · subst h2
        simp only [point_jt hne, hjt]
        simp
      · simp only [point_other h1 h2, hother j h1 h2]
        simp

theorem point_mem_channel {jp jt : Fin d} (hne : jt ≠ jp) {lo hi u c : ℤ}
    (h1 : min lo hi ≤ c) (h2 : c ≤ max lo hi) :
    point jp jt u c ∈ channel jp jt lo hi u := by
  rw [mem_channel hne]
  refine ⟨⟨by simpa using h1, by simpa using h2⟩, by simp [point_jt hne], ?_⟩
  intro j hj1 hj2
  exact point_other hj1 hj2 u c

/-- A channel has at most the number of integer coordinates in its directed interval. -/
theorem channel_card_le {jp jt : Fin d} (hne : jt ≠ jp) (lo hi u : ℤ) :
    (channel jp jt lo hi u).card ≤ (max lo hi + 1 - min lo hi).toNat := by
  classical
  rw [← Int.card_Icc (min lo hi) (max lo hi)]
  refine Finset.card_le_card_of_injOn (fun x => x jp) ?_ ?_
  · intro x hx
    exact Finset.mem_coe.2 (Finset.mem_Icc.2
      ((mem_channel hne).1 (Finset.mem_coe.1 hx)).1)
  · intro x hx y hy hxy
    rw [Finset.mem_coe, mem_channel hne] at hx hy
    funext j
    by_cases h1 : j = jp
    · subst h1; exact hxy
    · by_cases h2 : j = jt
      · subst h2; rw [hx.2.1, hy.2.1]
      · rw [hx.2.2 j h1 h2, hy.2.2 j h1 h2]

/-- Channels at distinct transverse heights are disjoint. -/
theorem channel_disjoint {jp jt : Fin d} (hne : jt ≠ jp) (lo hi : ℤ) {u v : ℤ}
    (huv : u ≠ v) : Disjoint (channel jp jt lo hi u) (channel jp jt lo hi v) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have h1 := ((mem_channel hne).1 hx).2.1
  have h2 := ((mem_channel hne).1 hx').2.1
  exact huv (h1.symm.trans h2)

/-- The step-towards operation stays inside a channel containing both endpoints. -/
theorem stepTo_mem_channel {jp jt : Fin d} {lo hi u : ℤ} {x y : Site d}
    (hx : x ∈ channel jp jt lo hi u) (hy : y ∈ channel jp jt lo hi u)
    {i : Fin d} (hne : x i ≠ y i) : MacroExp.stepTo x y i ∈ channel jp jt lo hi u := by
  simp only [channel, Fintype.mem_piFinset, Finset.mem_Icc] at hx hy ⊢
  intro j
  by_cases hj : j = i
  · rw [hj, MacroExp.stepTo_apply_self]
    have h1 := hx i
    have h2 := hy i
    split_ifs <;> omega
  · rw [MacroExp.stepTo_apply_of_ne x y hj]
    exact hx j

/-- An all-open straight channel connects its endpoints inside the channel. -/
theorem connWithin_channel_of_allOpen {jp jt : Fin d} {lo hi u : ℤ}
    {omega : SiteConfig (Site d)}
    (hopen : (↑(channel jp jt lo hi u) : Set (Site d)) ⊆ omega) :
    ∀ (n : ℕ) (x y : Site d), x ∈ channel jp jt lo hi u →
      y ∈ channel jp jt lo hi u → MacroExp.dist1 x y ≤ n →
      omega ∈ connWithin (zdGraph d) (↑(channel jp jt lo hi u) : Set (Site d)) x y := by
  intro n
  induction n with
  | zero =>
    intro x y hx hy hd
    have hxy : x = y := by
      funext j
      have h0 : MacroExp.dist1 x y = 0 := Nat.le_zero.1 hd
      unfold MacroExp.dist1 at h0
      have := (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ j)
      omega
    subst hxy
    exact ⟨⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩,
      SimpleGraph.Reachable.refl _⟩
  | succ n ih =>
    intro x y hx hy hd
    by_cases hxy : x = y
    · subst hxy
      exact ⟨⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩,
        SimpleGraph.Reachable.refl _⟩
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra h
        push Not at h
        exact hxy (funext h)
      have hstep := MacroExp.dist1_stepTo hi
      have hmem := stepTo_mem_channel hx hy hi
      have hrec := ih (MacroExp.stepTo x y i) y hmem hy (by omega)
      refine ⟨⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩, ?_⟩
      refine (SimpleGraph.Adj.reachable ?_).trans hrec.2
      exact (openSiteGraph_adj_iff' (zdGraph d) _ x _).2
        ⟨MacroExp.adj_stepTo x y i, ⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩,
          ⟨hopen (Finset.mem_coe.2 hmem), Finset.mem_coe.2 hmem⟩⟩

/-- Every site in a finite channel is open. -/
def allOpen (F : Finset (Site d)) : Set (SiteConfig (Site d)) :=
  {omega | (↑F : Set (Site d)) ⊆ omega}

theorem determinedBy_allOpen (F : Finset (Site d)) :
    DeterminedBy (allOpen F) (↑F : Set (Site d)) :=
  KNAll.Site.determinedBy_allOpen (↑F : Set (Site d))

theorem measurableSet_allOpen (F : Finset (Site d)) : MeasurableSet (allOpen F) :=
  (determinedBy_allOpen F).measurableSet_of_finset

theorem prob_allOpen (p : unitInterval) (F : Finset (Site d)) :
    (prodBernoulli (fun _ : Site d => p)).real (allOpen F) = (p : ℝ) ^ F.card := by
  rw [allOpen, prodBernoulli_real_subset, Finset.prod_const]

/-- The exact finite-product estimate for a union of disjoint all-open channels. -/
theorem le_prob_iUnion_allOpen {κ : Type*} [DecidableEq κ] (p : unitInterval)
    (s : Finset κ) (S : κ → Finset (Site d))
    (hdisj : (s : Set κ).PairwiseDisjoint S) (N : ℕ)
    (hcard : ∀ k ∈ s, (S k).card ≤ N) :
    1 - (1 - (p : ℝ) ^ N) ^ s.card ≤
      (prodBernoulli (fun _ : Site d => p)).real
        (⋃ k ∈ s, allOpen (S k)) := by
  classical
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hmeasU : MeasurableSet
      (⋃ k ∈ s, allOpen (S k)) :=
    Finset.measurableSet_biUnion s fun k _ => measurableSet_allOpen (S k)
  have hcompl : (⋃ k ∈ s, allOpen (S k))ᶜ =
      ⋂ k ∈ s, (allOpen (S k))ᶜ := by
    rw [Set.compl_iUnion₂]
  have hprod :
      (prodBernoulli (fun _ : Site d => p)).real
          (⋂ k ∈ s, (allOpen (S k))ᶜ) =
        ∏ k ∈ s, (prodBernoulli (fun _ : Site d => p)).real
          (allOpen (S k))ᶜ := by
    have huniv : DeterminedBy (Set.univ : Set (SiteConfig (Site d)))
        (⋃ k ∈ s, (↑(S k) : Set (Site d)))ᶜ := by
      rw [determinedBy_iff]
      intro _ _ _
      exact Iff.rfl
    have h := prodBernoulli_real_inter_biInter_of_determinedBy
      (fun _ : Site d => p) s S hdisj
      (fun k _ => (determinedBy_allOpen (S k)).compl)
      (fun k _ => (measurableSet_allOpen (S k)).compl)
      huniv MeasurableSet.univ
    rw [Set.univ_inter, probReal_univ, one_mul] at h
    exact h
  have hbound :
      ∏ k ∈ s, (prodBernoulli (fun _ : Site d => p)).real
          (allOpen (S k))ᶜ ≤
        (1 - (p : ℝ) ^ N) ^ s.card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun k _ => ?_) (fun k hk => ?_)
    · rw [measureReal_compl (measurableSet_allOpen (S k)), probReal_univ, prob_allOpen]
      have : (p : ℝ) ^ (S k).card ≤ 1 := pow_le_one₀ hp0 hp1
      linarith
    · rw [measureReal_compl (measurableSet_allOpen (S k)), probReal_univ, prob_allOpen]
      have : (p : ℝ) ^ N ≤ (p : ℝ) ^ (S k).card :=
        pow_le_pow_of_le_one hp0 hp1 (hcard k hk)
      linarith
  have hfail :
      (prodBernoulli (fun _ : Site d => p)).real
          (⋃ k ∈ s, allOpen (S k))ᶜ ≤
        (1 - (p : ℝ) ^ N) ^ s.card := by
    rw [hcompl, hprod]
    exact hbound
  rw [measureReal_compl hmeasU, probReal_univ] at hfail
  linarith

/-! ### Geometry of the note's fresh channels -/

def sign (b : Bool) : ℤ := if b then 1 else -1

/-- The last forced-open site in `Q 0`. -/
def sourceCoord (r : ℕ) (b : Bool) : ℤ := sign b * (5 * r : ℤ)

/-- The first fresh site of a channel. -/
def firstCoord (r : ℕ) (b : Bool) : ℤ := sign b * ((5 * r : ℤ) + 1)

/-- The near face of the innermost target. -/
def targetCoord (r A : ℕ) (b : Bool) : ℤ := sign b * ((19 * r : ℤ) + A)

theorem ctr_zero (r : ℕ) : MacroExp.ctr d r (0 : Site 2) = (0 : Site d) := by
  funext j
  simp [MacroExp.ctr]

theorem ctr_mvUnit_self (r : ℕ) {i : Fin 2} (b : Bool) {j : Fin d}
    (hj : j.val = i.val) :
    MacroExp.ctr d r (MacroExp.mvUnit i b) j = 20 * (r : ℤ) * sign b := by
  have hjlt : j.val < 2 := by rw [hj]; exact i.isLt
  rw [MacroExp.ctr_apply_of_lt r _ hjlt]
  have hji : (⟨j.val, hjlt⟩ : Fin 2) = i := Fin.ext hj
  rw [hji]
  simp [MacroExp.mvUnit, sign]

theorem ctr_mvUnit_other (r : ℕ) {i : Fin 2} (b : Bool) {j : Fin d}
    (hj : j.val ≠ i.val) : MacroExp.ctr d r (MacroExp.mvUnit i b) j = 0 := by
  by_cases hjlt : j.val < 2
  · rw [MacroExp.ctr_apply_of_lt r _ hjlt]
    have hne : (⟨j.val, hjlt⟩ : Fin 2) ≠ i := fun hc => hj (congrArg Fin.val hc)
    simp [MacroExp.mvUnit, hne]
  · exact MacroExp.ctr_apply_of_not_lt r _ hjlt

theorem source_mem_Q {jp jt : Fin d} {i : Fin 2} {b : Bool} {r t : ℕ} {u : ℤ}
    (hjp : jp.val = i.val) (hjt : jt.val = 2) (_hne : jt ≠ jp)
    (hu1 : -(t : ℤ) ≤ u) (hu2 : u ≤ (t : ℤ)) :
    point jp jt u (sourceCoord r b) ∈ MacroExp.Q d r t 0 := by
  rw [MacroExp.Q, MacroExp.mem_abox]
  intro j
  rw [ctr_zero]
  simp only [Pi.zero_apply, zero_sub, zero_add, point]
  by_cases h1 : j = jp
  · have hjv : j.val = i.val := by rw [h1, hjp]
    have hr : MacroExp.rad (5 * r) t j = (5 * r : ℤ) := by
      unfold MacroExp.rad
      rw [if_pos (by omega)]
      push_cast
      ring
    rw [if_pos h1, hr]
    cases b <;> simp [sourceCoord, sign]
  · rw [if_neg h1]
    by_cases h2 : j = jt
    · have hr : MacroExp.rad (5 * r) t j = (t : ℤ) := by
        unfold MacroExp.rad
        rw [if_neg (by omega)]
      rw [if_pos h2, hr]
      omega
    · rw [if_neg h2]
      unfold MacroExp.rad
      split_ifs <;> omega

theorem source_adj_first {jp jt : Fin d} {b : Bool} {r : ℕ} {u : ℤ} :
    (zdGraph d).Adj (point jp jt u (sourceCoord r b))
      (point jp jt u (firstCoord r b)) := by
  rw [zdGraph_adj_iff]
  refine ⟨jp, ?_⟩
  cases b
  · right
    funext j
    by_cases h : j = jp
    · subst h
      simp [sourceCoord, firstCoord, sign, point]
    · simp [point, h]
  · left
    funext j
    by_cases h : j = jp
    · subst h
      simp [sourceCoord, firstCoord, sign, point]
    · simp [point, h]

theorem channel_subset_E {jp jt : Fin d} {i : Fin 2} {b : Bool} {r t A : ℕ} {u : ℤ}
    (hjp : jp.val = i.val) (hjt : jt.val = 2) (hne : jt ≠ jp)
    (hA0 : 0 < A) (hA : A ≤ r) (hu1 : -(t : ℤ) ≤ u) (hu2 : u ≤ (t : ℤ)) :
    channel jp jt (firstCoord r b) (targetCoord r A b) u ⊆
      MacroExp.E d r t 0 (MacroExp.mvUnit i b) := by
  intro x hx
  rw [MacroExp.E, Finset.mem_sdiff]
  constructor
  · rw [MacroExp.mem_hbox]
    intro j
    rw [ctr_zero]
    simp only [Pi.zero_apply]
    have hxm := (mem_channel hne).1 hx
    by_cases h1 : j = jp
    · have hjv : j.val = i.val := by rw [h1, hjp]
      have hr : MacroExp.rad (5 * r) t j = (5 * r : ℤ) := by
        unfold MacroExp.rad
        rw [if_pos (by omega)]
        push_cast
        ring
      rw [hr, ctr_mvUnit_self r b hjv, h1]
      have hp := hxm.1
      cases b <;> simp [firstCoord, targetCoord, sign] at hp ⊢ <;> omega
    · by_cases h2 : j = jt
      · have hjv : j.val ≠ i.val := by omega
        have hr : MacroExp.rad (5 * r) t j = (t : ℤ) := by
          unfold MacroExp.rad
          rw [if_neg (by omega)]
        rw [hr, ctr_mvUnit_other r b hjv, h2, hxm.2.1]
        omega
      · have hjv : j.val ≠ i.val := by
          intro hc
          exact h1 (Fin.ext (by rw [hc, hjp]))
        rw [ctr_mvUnit_other r b hjv, hxm.2.2 j h1 h2]
        unfold MacroExp.rad
        split_ifs <;> omega
  · intro hxQ
    rw [MacroExp.Q, MacroExp.mem_abox] at hxQ
    have hxj := hxQ jp
    rw [ctr_zero] at hxj
    simp only [Pi.zero_apply] at hxj
    have hjplt : jp.val < 2 := by rw [hjp]; exact i.isLt
    rw [MacroExp.rad, if_pos hjplt] at hxj
    have hxp := ((mem_channel hne).1 hx).1
    cases b <;> simp [firstCoord, targetCoord, sign] at hxp <;> push_cast at hxj <;> omega

theorem target_mem {jp jt : Fin d} {i : Fin 2} {b : Bool} {L F r t A : ℕ} {u : ℤ}
    (hjp : jp.val = i.val) (hjt : jt.val = 2) (_hne : jt ≠ jp)
    (hA : A = L + 2 * F + 1) (hAr : A ≤ r) (hAt : A ≤ t)
    (hu1 : -((t : ℤ) - (A : ℤ)) ≤ u) (hu2 : u ≤ (t : ℤ) - (A : ℤ)) :
    point jp jt u (targetCoord r A b) ∈
      initialCorridorTarget d L F r t (MacroExp.mvUnit i b) := by
  rw [initialCorridorTarget, MacroExp.mem_abox]
  intro j
  have hrsub : ((r - (L + 2 * F + 1) : ℕ) : ℤ) = (r : ℤ) - (A : ℤ) := by
    rw [← hA]
    omega
  have htsub : ((t - (L + 2 * F + 1) : ℕ) : ℤ) = (t : ℤ) - (A : ℤ) := by
    rw [← hA]
    omega
  simp only [point]
  by_cases h1 : j = jp
  · have hjv : j.val = i.val := by rw [h1, hjp]
    have hjlt : j.val < 2 := by omega
    rw [if_pos h1, ctr_mvUnit_self r b hjv, MacroExp.rad, if_pos hjlt, hrsub]
    cases b <;> simp [targetCoord, sign] <;> omega
  · rw [if_neg h1]
    by_cases h2 : j = jt
    · have hjv : j.val ≠ i.val := by omega
      have hjnlt : ¬ j.val < 2 := by omega
      rw [if_pos h2, ctr_mvUnit_other r b hjv, MacroExp.rad, if_neg hjnlt, htsub]
      omega
    · have hjv : j.val ≠ i.val := by
        intro hc
        exact h1 (Fin.ext (by rw [hc, hjp]))
      rw [if_neg h2, ctr_mvUnit_other r b hjv]
      unfold MacroExp.rad
      split_ifs
      · rw [hrsub]
        omega
      · rw [htsub]
        omega

/-- One of the note's fresh straight channels realizes the minimal-support wide long-box event. -/
theorem allOpen_channel_subset_event [NeZero d] {L F r t A : ℕ}
    (hA : A = L + 2 * F + 1) (hAr : A ≤ r) (hAt : A ≤ t)
    {jp jt : Fin d} {i : Fin 2} {b : Bool} {u : ℤ}
    (hjp : jp.val = i.val) (hjt : jt.val = 2) (hne : jt ≠ jp)
    (hu1 : -((t : ℤ) - (A : ℤ)) ≤ u) (hu2 : u ≤ (t : ℤ) - (A : ℤ)) :
    allOpen (channel jp jt (firstCoord r b) (targetCoord r A b) u) ⊆
      wideLongBoxEvent d L F r t (MacroExp.mvUnit i b) := by
  classical
  set Ch := channel jp jt (firstCoord r b) (targetCoord r A b) u with hCh
  set sPt := point jp jt u (sourceCoord r b) with hsPt
  set gPt := point jp jt u (firstCoord r b) with hgPt
  set tPt := point jp jt u (targetCoord r A b) with htPt
  have hAt' : (A : ℤ) ≤ (t : ℤ) := by exact_mod_cast hAt
  have hu1t : -(t : ℤ) ≤ u := by omega
  have hu2t : u ≤ (t : ℤ) := by omega
  have hsQ : sPt ∈ MacroExp.Q d r t 0 := source_mem_Q hjp hjt hne hu1t hu2t
  have hgCh : gPt ∈ Ch := point_mem_channel hne (min_le_left _ _) (le_max_left _ _)
  have htCh : tPt ∈ Ch := point_mem_channel hne (min_le_right _ _) (le_max_right _ _)
  have hChE : Ch ⊆ MacroExp.E d r t 0 (MacroExp.mvUnit i b) :=
    channel_subset_E hjp hjt hne (by rw [hA]; omega) hAr hu1t hu2t
  have htB : tPt ∈ initialCorridorTarget d L F r t (MacroExp.mvUnit i b) :=
    target_mem hjp hjt hne hA hAr hAt hu1 hu2
  have hadj : (zdGraph d).Adj sPt gPt := source_adj_first
  have hgFace : gPt ∈ initialCorridorEntryFace d r t (MacroExp.mvUnit i b) := by
    rw [initialCorridorEntryFace, Finset.mem_filter]
    exact ⟨hChE hgCh, sPt, hsQ, hadj⟩
  intro omega homega
  refine ⟨gPt, hgFace, ?_⟩
  have hgt : omega ∈ connWithin (zdGraph d) (↑Ch : Set (Site d)) gPt tPt :=
    connWithin_channel_of_allOpen homega (MacroExp.dist1 gPt tPt) gPt tPt hgCh htCh le_rfl
  have hChDom : (↑Ch : Set (Site d)) ⊆
      (↑(MacroExp.E d r t 0 (MacroExp.mvUnit i b)) : Set (Site d)) :=
    Finset.coe_subset.2 hChE
  exact (mem_connWithinSet_iff (zdGraph d)
    (↑(MacroExp.E d r t 0 (MacroExp.mvUnit i b)) : Set (Site d)) gPt _ omega).2
      ⟨tPt, Finset.mem_coe.2 htB,
        connWithin_mono_set (zdGraph d) hChDom gPt tPt hgt⟩

/-- The note's inequality (2.2): `2K+1` disjoint fresh channels, each of exactly at most
`ell = 14r+A` sites, give the stated product bound. -/
theorem le_wideLongBoxExperiment_prob [NeZero d] (hd : 3 ≤ d)
    (L F r t A K : ℕ) (hA : A = L + 2 * F + 1) (hAr : A ≤ r) (ht : t = A + K)
    (p : unitInterval) {y : Site 2} (hy : y ∈ MacroExp.nbrs (0 : Site 2)) :
    1 - (1 - (p : ℝ) ^ (14 * r + A)) ^ (2 * K + 1) ≤
      (rawWideLongBoxExperiment d L F r t y).prob p := by
  classical
  obtain ⟨i, b, hyeq⟩ := MacroExp.mem_nbrs_iff.1 hy
  rw [zero_add] at hyeq
  subst hyeq
  set jp : Fin d := ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩ with hjpdef
  set jt : Fin d := ⟨2, by omega⟩ with hjtdef
  have hjp : jp.val = i.val := rfl
  have hjt : jt.val = 2 := rfl
  have hne : jt ≠ jp := by
    intro hc
    have hc' := congrArg Fin.val hc
    omega
  set I : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) with hIdef
  set Ch : ℤ → Finset (Site d) := fun u =>
    channel jp jt (firstCoord r b) (targetCoord r A b) u with hChdef
  have hIcard : I.card = 2 * K + 1 := by
    rw [hIdef, Int.card_Icc]
    omega
  have hdisj : (↑I : Set ℤ).PairwiseDisjoint Ch := by
    intro u _ v _ huv
    exact channel_disjoint hne _ _ huv
  have hcard : ∀ u ∈ I, (Ch u).card ≤ 14 * r + A := by
    intro u _
    refine le_trans (channel_card_le hne _ _ u) ?_
    cases b <;> simp [firstCoord, targetCoord, sign] <;> omega
  have hAt : A ≤ t := by omega
  have hsub : (⋃ u ∈ I, allOpen (Ch u)) ⊆
      (rawWideLongBoxExperiment d L F r t (MacroExp.mvUnit i b)).event := by
    refine Set.iUnion₂_subset fun u hu => ?_
    rw [hIdef, Finset.mem_Icc] at hu
    have hcast : (K : ℤ) = (t : ℤ) - (A : ℤ) := by omega
    exact allOpen_channel_subset_event hA hAr hAt hjp hjt hne
      (by rw [← hcast]; exact hu.1) (by rw [← hcast]; exact hu.2)
  have hmono :
      (prodBernoulli (fun _ : Site d => p)).real (⋃ u ∈ I, allOpen (Ch u)) ≤
        (rawWideLongBoxExperiment d L F r t (MacroExp.mvUnit i b)).prob p :=
    measureReal_mono hsub (measure_ne_top _ _)
  refine le_trans ?_ hmono
  have hchannels := le_prob_iUnion_allOpen p I Ch hdisj (14 * r + A) hcard
  rwa [hIcard] at hchannels

end InitialCorridorChannels

/-! ## Extraction -/

/-- The certificate assembled from the base data of `certificateOf`, with the spacing raised to
`L (2 Nf + 2) + 2 Nf + 1`, corridor radius enlarged to satisfy (0.3), supplied half-width `t`,
width `2t`, and the four
initial-corridor cylinders appended to the old list. -/
def certificateOf2 (d : ℕ) (m M Nc Nf : ℕ) (ρ : unitInterval) (τf τc : ℝ) (p : unitInterval)
    (ε : ℝ) (N s k L t : ℕ) : Certificate2 d :=
  let r := max (max 44 (100 * (d + 1) * (M + 1) + 1))
    (max (L * (2 * Nf + 2)) (L + 2 * Nf + 1))
  let pre := (certificateOf d m M Nc Nf ρ τf τc).bounds ++
    if 3 ≤ d then
      (MacroExp.nbrs (0 : Site 2)).toList.map fun y =>
        (rawWideLongBoxExperiment d L Nf r t y, 1 - ε / 8)
    else []
  let G : FinalGeometry d :=
    { source := m
      shell := M - m
      faceTarget := Nf
      coalTarget := Nc
      width := 2 * t
      spacing := L * (2 * Nf + 2) + 2 * Nf + 1
      density := ρ
      faceTol := τf
      coalTol := τc
      p₀ := p
      eps := ε
      deltaC := ε / 8
      delta := ε ^ 2 / 96
      eta := (ε ^ 2 / 96) ^ 2 * (ε / 8)
      contacts := N
      seedSize := s
      seedCount := k
      levels := L
      corridor := r
      halfWidth := t
      beta := betaOf d ρ
      moveLocalRadius := fun _ => M
      moveTargetRadius := fun _ => Nf
      moveHitRadius := fun _ => Nc + 1
      moveLevelCount := fun _ => L }
  { toCertificate := { certificateOf d m M Nc Nf ρ τf τc with
      spacing := G.spacing
      width := G.width
      bounds := pre ++ moveWindowBounds G }
    p₀ := G.p₀
    eps := G.eps
    deltaC := G.deltaC
    delta := G.delta
    eta := G.eta
    contacts := G.contacts
    seedSize := G.seedSize
    seedCount := G.seedCount
    levels := G.levels
    corridor := G.corridor
    halfWidth := G.halfWidth
    beta := G.beta
    moveLocalRadius := G.moveLocalRadius
    moveTargetRadius := G.moveTargetRadius
    moveHitRadius := G.moveHitRadius
    moveLevelCount := G.moveLevelCount
    preMoveBounds := pre }

set_option maxHeartbeats 1000000 in
/-- **Extraction at a prescribed planar density.**  From `0 < thetaSite d p`, `p < 1`, and a
density `a < 1` at which the plane percolates: a well-formed certificate valid at `p`, with
`p₀ = p`, `density = a` and `eps = betaOf d a`.

The choices, in the order the inputs allow them.  `ε = betaOf d a`, then `δ_C, δ, η` by the cascade.
The face tolerance is `η / 2`; the face input at `η / 4` gives `m₀`, the source scale is `m₀ + 1`,
and the face input gives `N_f'`.  The coalescence tolerance is `η / (4 (2d+1) · pairs)`; the
coalescence input at half of it gives the sphere radius `M > m` and a target `N_c`.  The face
target is `N_f = max N_f' N_c`.  Then the seed size `s = (4 N_f + 3)^{d-1}`; the seed count `k` with
`(1 - p^s)^k < δ`, which exists because `p > 0`; the contact count `N = k (8 N_f + 5)^d`; the level
count `L` with `L · δ (1-p)^{2dN} > 1`, which exists because `p < 1`; the corridor radius
`r` is the maximum of the level-fit bound and (0.3); the fresh-channel length
`ell = 14r + L + 2N_f + 1`; and a half-width enlarged until the product failure bound is below
`eps/16`. -/
theorem exists_wellFormed2_validAt2_of_density (d : ℕ) [NeZero d] (p : unitInterval)
    (hp1 : (p : ℝ) < 1) (hpos : 0 < thetaSite d p)
    (a : unitInterval) (ha1 : (a : ℝ) < 1) (hapos : 0 < thetaSite 2 a) :
    ∃ C : Certificate2 d, C.WellFormed ∧ C.ValidAt2 p ∧ C.p₀ = p ∧ C.density = a ∧
      C.eps = betaOf d a ∧ C.MoveMarginAt p := by
  -- `p > 0`, since nothing percolates at `0`.
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hp0 : 0 < (p : ℝ) := by
    rcases lt_or_eq_of_le p.2.1 with h | h
    · exact h
    · exfalso
      refine hpos.ne' (thetaSite_eq_zero_of_lt d p ?_)
      rw [← h]; positivity
  have hL := siteLocalInputs_of_thetaSite_pos d p hpos
  -- The cascade.
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = betaOf d a := ⟨_, rfl⟩
  have halpha_pos : 0 < (1 - (a : ℝ)) / 32 := by linarith
  have hpow_pos : 0 < ((1 - (a : ℝ)) / 32) ^ (2 ^ (d + 1)) :=
    pow_pos halpha_pos _
  have hden_pos : (0 : ℝ) < 96 ^ (2 ^ (d + 1) - 1) := by positivity
  have hε_pos : 0 < ε := by rw [hε, betaOf]; exact div_pos hpow_pos hden_pos
  have hε_le : ε ≤ 1 := by
    rw [hε, betaOf]
    have halpha_le : (1 - (a : ℝ)) / 32 ≤ 1 := by
      have := a.2.1
      linarith
    have hp_le : ((1 - (a : ℝ)) / 32) ^ (2 ^ (d + 1)) ≤ 1 :=
      pow_le_one₀ halpha_pos.le halpha_le
    have hden_le : (1 : ℝ) ≤ 96 ^ (2 ^ (d + 1) - 1) :=
      one_le_pow₀ (by norm_num)
    exact (div_le_one hden_pos).2 (le_trans hp_le hden_le)
  have hε_alpha : ε ≤ (1 - (a : ℝ)) / 32 := by
    rw [hε, betaOf]
    have halpha_le : (1 - (a : ℝ)) / 32 ≤ 1 := by
      have := a.2.1
      linarith
    have hexp : 1 ≤ 2 ^ (d + 1) := by
      exact Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by norm_num))
    have hp_le : ((1 - (a : ℝ)) / 32) ^ (2 ^ (d + 1)) ≤
        ((1 - (a : ℝ)) / 32) ^ 1 :=
      pow_le_pow_of_le_one halpha_pos.le halpha_le hexp
    have hden_le : (1 : ℝ) ≤ 96 ^ (2 ^ (d + 1) - 1) :=
      one_le_pow₀ (by norm_num)
    apply (div_le_iff₀ hden_pos).2
    exact (hp_le.trans_eq (pow_one _)).trans
      (le_mul_of_one_le_right halpha_pos.le hden_le)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε ^ 2 / 96 := ⟨_, rfl⟩
  have hδ_pos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (ε ^ 2 / 96) ^ 2 * (ε / 8) := ⟨_, rfl⟩
  have hη_pos : 0 < η := by rw [hη]; positivity
  have hη_le : η ≤ ε := by
    rw [hη]
    have h2 : ε ^ 2 ≤ 1 := by nlinarith
    have h4 : (ε ^ 2 / 96) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  -- The boxes.
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, χ = ε ^ 2 / 4 := ⟨_, rfl⟩
  have hχ_pos : 0 < χ := by rw [hχ]; positivity
  obtain ⟨kFace, nFace, hkFace, hquarter⟩ :=
    exists_forall_lt_prob_orthantHit (d := d) p hpos hχ_pos
  obtain ⟨τf, hτf⟩ : ∃ τf : ℝ, τf = η / 2 := ⟨_, rfl⟩
  have hτf_pos : 0 < τf := by rw [hτf]; positivity
  obtain ⟨m₀, hm₀⟩ := exists_faceExperiment_prob_ge d p hL (τf / 2) (by positivity)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = max (m₀ + 1) (max kFace nFace) := ⟨_, rfl⟩
  have hm₀m : m₀ ≤ m := by rw [hm]; omega
  have hkFacem : kFace ≤ m := by rw [hm]; omega
  have hnFacem : nFace ≤ m := by rw [hm]; omega
  have hm_pos : 0 < m := by omega
  obtain ⟨Nface, hNface, hface₀⟩ := hm₀ m hm₀m
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = ((2 * m + 1) ^ d) ^ 2 := ⟨_, rfl⟩
  have hP_pos : (0 : ℝ) < (P : ℝ) := by rw [hP]; positivity
  obtain ⟨τc, hτc⟩ : ∃ τc : ℝ, τc = η / (4 * (2 * (d : ℝ) + 1) * (P : ℝ)) := ⟨_, rfl⟩
  have hτc_pos : 0 < τc := by rw [hτc]; positivity
  obtain ⟨M, hMm, Nc, hNcM, hcoal⟩ :=
    exists_coalescenceExperiment_prob_ge d p hL m (τc / 2) (by positivity)
  obtain ⟨Nhit, hNhit, hhit₀⟩ := hm₀ (Nc + 1) (by omega)
  obtain ⟨Nf', hNf'⟩ : ∃ Nf' : ℕ, Nf' = max Nface Nhit := ⟨_, rfl⟩
  have hface' : 1 - τf / 2 ≤ (faceExperiment d m Nf').prob p := by
    rw [hNf']
    exact le_trans hface₀ (faceExperiment_prob_mono d m (le_max_left _ _) p)
  have hhit' : 1 - τf / 2 ≤ (faceExperiment d (Nc + 1) Nf').prob p := by
    rw [hNf']
    exact le_trans hhit₀ (faceExperiment_prob_mono d (Nc + 1) (le_max_right _ _) p)
  have hface : 1 - τf / 2 ≤ (faceExperiment d m (max Nf' Nc)).prob p :=
    le_trans hface' (faceExperiment_prob_mono d m (le_max_left _ _) p)
  have hhit : 1 - τf / 2 ≤ (faceExperiment d (Nc + 1) (max Nf' Nc)).prob p :=
    le_trans hhit' (faceExperiment_prob_mono d (Nc + 1) (le_max_left _ _) p)
  -- The seed size `s`, the seed count `k`, the contact count `N`, the level count `L`.
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = (4 * max Nf' Nc + 3) ^ (d - 1) := ⟨_, rfl⟩
  have hs_pos : 0 < s := by rw [hs]; positivity
  have hps : 0 < (p : ℝ) ^ s := pow_pos hp0 s
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ_pos (show 1 - (p : ℝ) ^ s < 1 by linarith)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = k * (8 * max Nf' Nc + 5) ^ d := ⟨_, rfl⟩
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso; rw [h0, pow_zero, hδ] at hk; nlinarith
    · exact h0
  have hN_pos : 0 < N := by rw [hN]; positivity
  have hc_pos : 0 < δ * (1 - (p : ℝ)) ^ (2 * d * N) := by
    have : 0 < 1 - (p : ℝ) := by linarith
    positivity
  obtain ⟨L, hL'⟩ := exists_nat_gt (1 / (δ * (1 - (p : ℝ)) ^ (2 * d * N)))
  have hlevel : 1 < (L : ℝ) * δ * (1 - (p : ℝ)) ^ (2 * d * N) := by
    rw [div_lt_iff₀ hc_pos] at hL'
    linarith
  -- The note's channels.  Their fresh length is `ell = 14r + A`; choose `K` so the product of
  -- the `K`-channel failure probabilities is below `eps/16`, then use all `2K+1` heights.
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = L + 2 * max Nf' Nc + 1 := ⟨_, rfl⟩
  have hA_pos : 0 < A := by rw [hA]; omega
  obtain ⟨r, hr⟩ : ∃ r : ℕ,
      r = max (max 44 (100 * (d + 1) * (M + 1) + 1))
        (max (L * (2 * max Nf' Nc + 2)) (L + 2 * max Nf' Nc + 1)) := ⟨_, rfl⟩
  have hAr : A ≤ r := by
    rw [hA, hr]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨ell, hell⟩ : ∃ ell : ℕ, ell = 14 * r + A := ⟨_, rfl⟩
  have hell_pos : 0 < ell := by rw [hell]; omega
  obtain ⟨alpha, halpha⟩ : ∃ alpha : ℝ, alpha = (p : ℝ) ^ ell := ⟨_, rfl⟩
  have halpha_pos : 0 < alpha := by rw [halpha]; exact pow_pos hp0 ell
  have halpha_le : alpha ≤ 1 := by
    rw [halpha]
    exact pow_le_one₀ p.2.1 p.2.2
  have hfailBase0 : 0 ≤ 1 - alpha := by linarith
  have hfailBase1 : 1 - alpha < 1 := by linarith
  obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 16 by positivity) hfailBase1
  have hK₀_pos : 0 < K₀ := by
    rcases Nat.eq_zero_or_pos K₀ with h0 | h0
    · rw [h0, pow_zero] at hK₀
      linarith
    · exact h0
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = K₀ + 5 * r := ⟨_, rfl⟩
  have hK_pos : 0 < K := by rw [hKdef]; omega
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = A + K := ⟨_, rfl⟩
  have hfailure : (1 - (p : ℝ) ^ (14 * r + A)) ^ (2 * K + 1) < ε / 16 := by
    rw [← hell, ← halpha]
    exact lt_of_le_of_lt
      (pow_le_pow_of_le_one hfailBase0 (by linarith : 1 - alpha ≤ 1)
        (by rw [hKdef]; omega : K₀ ≤ 2 * K + 1)) hK₀
  -- The arithmetic of the tolerances.
  have hτ : τc ≤ τf := by
    rw [hτc, hτf]
    apply div_le_div_of_nonneg_left hη_pos.le (by norm_num)
    have h1 : (1 : ℝ) ≤ (P : ℝ) := by
      have h0 : 0 < P := by rw [hP]; positivity
      exact Nat.one_le_cast.2 h0
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hkey : 2 * (d : ℝ) * (P : ℝ) * τc = (d : ℝ) * η / (2 * (2 * (d : ℝ) + 1)) := by
    rw [hτc]
    field_simp
    ring
  have hle : (d : ℝ) * η / (2 * (2 * (d : ℝ) + 1)) ≤ η / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hbudget : τf + 2 * (d : ℝ) * ((((2 * m + 1) ^ d) ^ 2 : ℕ) : ℝ) * τc
      ≤ 1 - (a : ℝ) := by
    rw [← hP, hkey, hτf]
    linarith
  have hτf_le : τf ≤ η := by rw [hτf]; linarith
  have hτc_le : τc ≤ η := le_trans hτ hτf_le
  have hPτc : (P : ℝ) * τc = η / (4 * (2 * (d : ℝ) + 1)) := by
    rw [hτc]
    field_simp
  have hPτc_le : (P : ℝ) * τc ≤ η / 4 := by
    rw [hPτc]
    exact div_le_div_of_nonneg_left hη_pos.le (by norm_num)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have hwindowLoss : τf + (P : ℝ) * (τc / 2) ≤ η := by
    nlinarith [hτf_le, hPτc_le]
  have heta_window : η < 3 * ε ^ 2 / 4 := by
    let x : ℝ := ε ^ 2 / 96
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hx1 : x ≤ 1 := by dsimp [x]; nlinarith [sq_nonneg ε]
    have hxe : x ≤ ε ^ 2 := by dsimp [x]; nlinarith [sq_nonneg ε]
    have hxx : x ^ 2 ≤ ε ^ 2 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hx1 hx0
        _ = x := mul_one x
        _ ≤ ε ^ 2 := hxe
    have he8 : ε / 8 ≤ 1 / 8 := by linarith
    have heta_le : η ≤ ε ^ 2 / 8 := by
      rw [hη]
      change x ^ 2 * (ε / 8) ≤ ε ^ 2 / 8
      calc
        x ^ 2 * (ε / 8) ≤ ε ^ 2 * (ε / 8) :=
          mul_le_mul_of_nonneg_right hxx (by positivity)
        _ ≤ ε ^ 2 * (1 / 8) :=
          mul_le_mul_of_nonneg_left he8 (sq_nonneg ε)
        _ = ε ^ 2 / 8 := by ring
    have heps_sq : 0 < ε ^ 2 := sq_pos_of_pos hε_pos
    calc
      η ≤ ε ^ 2 / 8 := heta_le
      _ < 3 * ε ^ 2 / 4 := by nlinarith only [heps_sq]
  have hbase := certificateOf_wellFormed (d := d) (Nf := max Nf' Nc) hm_pos hMm hNcM (le_max_right _ _)
    ha1 hapos hτf_pos hτc_pos hτ hbudget
  have hcorrProb (hd : 3 ≤ d) (y : Site 2) (hy : y ∈ MacroExp.nbrs (0 : Site 2)) :
      1 - ε / 16 < (rawWideLongBoxExperiment d L (max Nf' Nc) r t y).prob p := by
    have hchan := InitialCorridorChannels.le_wideLongBoxExperiment_prob hd
      L (max Nf' Nc) r t A K hA hAr ht p hy
    linarith
  let C := certificateOf2 d m M Nc (max Nf' Nc) a τf τc p ε N s k L t
  have hCsource : C.finalGeometry.source = m := rfl
  have hCface : C.finalGeometry.faceTarget = max Nf' Nc := rfl
  have hChit (j : Fin (d + 1)) : C.finalGeometry.moveHitRadius j = Nc + 1 := rfl
  have hCfaceBase : C.faceTarget = max Nf' Nc := rfl
  have hCcoal : C.finalGeometry.coalTarget = Nc := rfl
  have hCshell : C.finalGeometry.shell = M - m := rfl
  have hCcorridor : C.corridor = r := by
    change max (max 44 (100 * (d + 1) * (M + 1) + 1))
      (max (L * (2 * max Nf' Nc + 2)) (L + 2 * max Nf' Nc + 1)) = r
    exact hr.symm
  have hChalfWidth : C.halfWidth = t := rfl
  have hClevels : C.levels = L := rfl
  have hCeps : C.eps = ε := rfl
  have hCbeta : C.beta = ε := by
    change betaOf d a = ε
    exact hε.symm
  have hpreEq : C.preMoveBounds =
      (certificateOf d m M Nc (max Nf' Nc) a τf τc).bounds ++
        (if 3 ≤ d then
          (MacroExp.nbrs (0 : Site 2)).toList.map fun y =>
            (rawWideLongBoxExperiment d L (max Nf' Nc) r t y, 1 - ε / 8)
        else []) := by
    simp [C, certificateOf2, hr]
  have hboundsEq : C.bounds = C.preMoveBounds ++ C.moveWindowBounds := rfl
  have hFGbeta : C.finalGeometry.beta = ε := hCbeta
  have hmoveMargin : C.MoveMarginAt p := by
    intro b hb
    simp only [Certificate2.moveWindowBounds] at hb
    simp only [moveWindowBounds, List.mem_flatMap, Finset.mem_toList, List.mem_map] at hb
    obtain ⟨nu, hnu, j, hj, ell', hell', x', hx', rfl⟩ := hb
    change 1 - 3 * C.beta ^ 2 / 4 <
      (siteBernoulli fun _ : Site d => p).real
        (moveWindowEvent C.finalGeometry j
          (moveWindowCentre C.finalGeometry nu j ell' x'))
    let aτ : FaceIndex d :=
      (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, fun _ => 1)
    have hnFaceHit : nFace ≤ Nc + 1 := by omega
    have horthFace := hquarter M (le_trans hnFacem hMm.le) aτ
    have horthTarget := hquarter (Nc + 1) hnFaceHit aτ
    have hgeomFace : 1 - χ <
        (siteBernoulli fun _ : Site d => p).real
          (finiteTargetHit (box d C.finalGeometry.coalTarget)
            (box d C.finalGeometry.source)
            (boxSphereFin d (C.finalGeometry.source + C.finalGeometry.shell))) := by
      rw [hCcoal, hCsource, hCshell, Nat.add_sub_of_le hMm.le]
      refine horthFace.trans_le (measureReal_mono ?_ (measure_ne_top _ _))
      exact _root_.KNAll.Site.MoveWindowInput.finiteTargetHit_mono
        (box_mono d hNcM) (box_mono d hkFacem)
        (orthantFace_subset_boxSphereFin aτ.1 aτ.2 M)
    have hhitFace : Nc + 1 ≤ max Nf' Nc := by
      rw [hNf']
      exact le_trans hNhit (le_trans (le_max_right Nface Nhit) (le_max_left _ _))
    have hgeomTarget : 1 - χ <
        (siteBernoulli fun _ : Site d => p).real
          (finiteTargetHit (box d C.finalGeometry.faceTarget)
            (box d C.finalGeometry.source)
            (boxSphereFin d (C.finalGeometry.moveHitRadius j))) := by
      rw [hCface, hCsource, hChit]
      refine horthTarget.trans_le (measureReal_mono ?_ (measure_ne_top _ _))
      exact _root_.KNAll.Site.MoveWindowInput.finiteTargetHit_mono (box_mono d hhitFace)
        (box_mono d hkFacem) (orthantFace_subset_boxSphereFin aτ.1 aτ.2 (Nc + 1))
    have hcoalTotal : (P : ℝ) * (τc / 2) < χ := by
      have heps_sq : 0 < ε ^ 2 := sq_pos_of_pos hε_pos
      calc
        (P : ℝ) * (τc / 2) = ((P : ℝ) * τc) / 2 := by ring
        _ ≤ (η / 4) / 2 := div_le_div_of_nonneg_right hPτc_le (by norm_num)
        _ < ((3 * ε ^ 2 / 4) / 4) / 2 := by
          exact div_lt_div_of_pos_right
            (div_lt_div_of_pos_right heta_window (by norm_num)) (by norm_num)
        _ < χ := by rw [hχ]; nlinarith only [heps_sq]
    have hpairTol : τc / 2 < χ / (P : ℝ) := by
      rw [lt_div_iff₀ hP_pos]
      simpa only [mul_comm] using hcoalTotal
    have hgeomCoalPairs : ∀ x ∈ box d C.finalGeometry.source,
        ∀ y ∈ box d C.finalGeometry.source,
        (siteBernoulli fun _ : Site d => p).real
          (localCoalescenceEvent d
            (C.finalGeometry.source + C.finalGeometry.shell)
            C.finalGeometry.coalTarget x y) < χ / (P : ℝ) := by
      intro x hx y hy
      have hM : m + (M - m) = M := Nat.add_sub_of_le (Nat.le_of_lt hMm)
      rw [hCsource] at hx hy
      rw [hCsource, hCshell, hCcoal, hM]
      have hbad := hcoal x hx y hy
      rw [coalescenceExperiment_prob] at hbad
      linarith
    have hpair : (((((2 * C.finalGeometry.source + 1) ^ d) ^ 2 : ℕ) : ℝ)) = (P : ℝ) := by
      rw [hCsource, hP]
    have hgeomCoal : 1 - χ <
        (siteBernoulli fun _ : Site d => p).real
          (moveCoalescenceGood C.finalGeometry) := by
      rw [moveCoalescenceGood]
      apply one_sub_lt_prob_shellCoalescenceGood p C.finalGeometry.source
        (C.finalGeometry.source + C.finalGeometry.shell) C.finalGeometry.coalTarget hχ_pos
      intro x hx y hy
      rw [hpair]
      exact hgeomCoalPairs x hx y hy
    have hpw := prob_moveWindowEvent_ge C.finalGeometry j p χ
      hgeomCoal hgeomFace hgeomTarget (moveWindowCentre C.finalGeometry nu j ell' x')
    rw [hCbeta]
    nlinarith only [hpw, hχ]
  have hbase' : C.toCertificate.WellFormed := by
    refine { hbase with
      bounds_ne_nil := ?_
      threshold_mem := ?_
      spacing_ge := ?_
      width_ge := ?_
      face_mem := ?_
      coalescence_mem := ?_ }
    · rw [hboundsEq, hpreEq]
      simp [hbase.bounds_ne_nil]
    · intro b hb
      change b ∈ C.preMoveBounds ++ C.moveWindowBounds at hb
      have hb' := List.mem_append.1 hb
      rcases hb' with hpre | hmove
      rw [hpreEq] at hpre
      · rcases List.mem_append.1 hpre with hold | hwide
        · exact hbase.threshold_mem b hold
        · by_cases hd : 3 ≤ d
          · rw [if_pos hd] at hwide
            obtain ⟨y, -, rfl⟩ := List.mem_map.1 hwide
            constructor <;> dsimp <;> linarith
          · simp [hd] at hwide
      · have ht := moveWindowBounds_threshold hmove
        have hsmall : ε ≤ 1 / 32 := by
          have ha0 : (0 : ℝ) ≤ (a : ℝ) := a.2.1
          linarith [hε_alpha]
        have he2 : ε ^ 2 ≤ (1 / 32 : ℝ) ^ 2 := by
          rw [pow_two, pow_two]
          exact mul_le_mul hsmall hsmall hε_pos.le (by norm_num)
        rw [ht]
        rw [hFGbeta]
        constructor
        · calc
            0 ≤ 1 - 3 * (1 / 32 : ℝ) ^ 2 := by norm_num
            _ ≤ 1 - 3 * ε ^ 2 :=
              sub_le_sub_left (mul_le_mul_of_nonneg_left he2 (by norm_num)) 1
        · exact sub_lt_self 1 (mul_pos (by norm_num) (sq_pos_of_pos hε_pos))
    · show 2 * max Nf' Nc + 1 ≤ L * (2 * max Nf' Nc + 2) + 2 * max Nf' Nc + 1
      omega
    · show 2 * max Nf' Nc ≤ 2 * t
      rw [ht, hA]
      omega
    · rw [hboundsEq]
      apply List.mem_append_left
      rw [hpreEq]
      apply List.mem_append_left
      exact hbase.face_mem
    · intro x hx y hy
      rw [hboundsEq]
      apply List.mem_append_left
      rw [hpreEq]
      apply List.mem_append_left
      exact hbase.coalescence_mem x hx y hy
  refine ⟨C, ?_, ?_, rfl, rfl, hε, hmoveMargin⟩
  · refine
      { base := hbase'
        eps_pos := hε_pos
        eps_le := ?_
        beta_eq := rfl
        eps_le_beta := hCbeta.ge
        deltaC_eq := rfl
        delta_eq := rfl
        eta_eq := rfl
        faceTol_le_eta := ?_
        coalTol_le_eta := ?_
        contacts_pos := hN_pos
        seedSize_pos := hs_pos
        contacts_ge := ?_
        seedSize_ge := ?_
        seed := ?_
        level := ?_
        spacing_ge_levels := ?_
        corridor_ge := ?_
        corridor_ge_44 := ?_
        halfWidth_ge := ?_
        innerRadius_ge := ?_
        halfWidth_ge_five_corridor := ?_
        moveLocalRadius_eq := fun _ => by
          change M = m + (M - m)
          omega
        moveLocalRadius_ge := fun _ => by
          change 1 ≤ M
          omega
        moveScale := fun _ => ?_
        moveTargetRadius_eq := fun _ => rfl
        moveHitRadius_eq := fun _ => rfl
        moveLevelCount_eq := fun _ => rfl
        bounds_eq := hboundsEq
        wideLongBox_mem := ?_
        width_eq := rfl }
    · show 32 * ε ≤ 1 - (a : ℝ)
      calc
        32 * ε ≤ 32 * ((1 - (a : ℝ)) / 32) :=
          mul_le_mul_of_nonneg_left hε_alpha (by norm_num)
        _ = 1 - (a : ℝ) := by ring
    · show τf ≤ (ε ^ 2 / 96) ^ 2 * (ε / 8)
      rw [← hη]; exact hτf_le
    · show τc ≤ (ε ^ 2 / 96) ^ 2 * (ε / 8)
      rw [← hη]; exact hτc_le
    · show k * (8 * max Nf' Nc + 5) ^ d ≤ N
      rw [hN]
    · show (4 * max Nf' Nc + 3) ^ (d - 1) ≤ s
      rw [hs]
    · show (1 - (p : ℝ) ^ s) ^ k < ε ^ 2 / 96
      rw [← hδ]; exact hk
    · show 1 < (L : ℝ) * (ε ^ 2 / 96) * (1 - (p : ℝ)) ^ (2 * d * N)
      rw [← hδ]; exact hlevel
    · show L * (2 * max Nf' Nc + 2) ≤ L * (2 * max Nf' Nc + 2) + 2 * max Nf' Nc + 1
      omega
    · show L * (2 * max Nf' Nc + 2) ≤
        max (max 44 (100 * (d + 1) * (M + 1) + 1))
          (max (L * (2 * max Nf' Nc + 2)) (L + 2 * max Nf' Nc + 1))
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    · show 44 ≤ max (max 44 (100 * (d + 1) * (M + 1) + 1))
        (max (L * (2 * max Nf' Nc + 2)) (L + 2 * max Nf' Nc + 1))
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    · show L + max Nf' Nc + 1 ≤ t
      rw [ht, hA]
      omega
    · show L + 2 * max Nf' Nc + 1 ≤
        min (max (max 44 (100 * (d + 1) * (M + 1) + 1))
              (max (L * (2 * max Nf' Nc + 2)) (L + 2 * max Nf' Nc + 1)))
          t
      rw [← hA]
      exact le_min (le_trans (le_max_right _ _) (le_max_right _ _)) (by rw [ht]; omega)
    · rw [hCcorridor, hChalfWidth, ht, hKdef]
      omega
    · change 100 * (d + 1) * (M + 1) <
        max (max 44 (100 * (d + 1) * (M + 1) + 1))
          (max (L * (2 * max Nf' Nc + 2)) (L + 2 * max Nf' Nc + 1))
      have hle : 100 * (d + 1) * (M + 1) + 1 ≤
          max 44 (100 * (d + 1) * (M + 1) + 1) := le_max_right _ _
      omega
    · intro hd y hy
      rw [hboundsEq]
      apply List.mem_append_left
      rw [hpreEq]
      apply List.mem_append_right
      rw [if_pos hd]
      apply List.mem_map.2
      refine ⟨y, Finset.mem_toList.2 hy, ?_⟩
      rw [Certificate2.wideLongBoxExperiment, hClevels, hCfaceBase, hCcorridor,
        hChalfWidth, hCeps]
  · refine ⟨fun b hb => ?_, ?_, le_rfl⟩
    · change b ∈ C.preMoveBounds ++ C.moveWindowBounds at hb
      have hb' := List.mem_append.1 hb
      rcases hb' with hpre | hmove
      rw [hpreEq] at hpre
      · rcases List.mem_append.1 hpre with hold | hwide
        · have hm := certificateOf_margin (d := d) (ρ := a) hτ hface hcoal b hold
          linarith
        · by_cases hd : 3 ≤ d
          · rw [if_pos hd] at hwide
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hwide
            have := hcorrProb hd y (Finset.mem_toList.1 hy)
            linarith
          · simp [hd] at hwide
      · have ht := moveWindowBounds_threshold hmove
        have hm := hmoveMargin b hmove
        rw [ht]
        rw [hFGbeta]
        have hm' : 1 - 3 * ε ^ 2 / 4 < b.1.prob p := by
          rw [← hCbeta]
          exact hm
        exact lt_trans (by nlinarith only [sq_pos_of_pos hε_pos]) hm'
    · show (1 - (p : ℝ) ^ s) ^ k < ε ^ 2 / 96
      rw [← hδ]; exact hk

/-- **Extraction.**  From `0 < thetaSite d p` and `p < 1`: a well-formed certificate valid at `p`
with `p₀ = p`, at the planar density of `exists_thetaSite_pos 2`. -/
theorem exists_wellFormed2_validAt2 (d : ℕ) [NeZero d] (p : unitInterval) (hp1 : (p : ℝ) < 1)
    (hpos : 0 < thetaSite d p) :
    ∃ C : Certificate2 d, C.WellFormed ∧ C.ValidAt2 p ∧ C.p₀ = p := by
  obtain ⟨a, ha1, hapos⟩ := exists_thetaSite_pos 2 le_rfl
  obtain ⟨C, hwf, hv, hp, -, -, -⟩ :=
    exists_wellFormed2_validAt2_of_density d p hp1 hpos a ha1 hapos
  exact ⟨C, hwf, hv, hp⟩

/-- Extraction with the stronger window margin used by the explicit stability radius. -/
theorem exists_wellFormed2_validAt2_moveMargin (d : ℕ) [NeZero d]
    (p : unitInterval) (hp1 : (p : ℝ) < 1) (hpos : 0 < thetaSite d p) :
    ∃ C : Certificate2 d,
      C.WellFormed ∧ C.ValidAt2 p ∧ C.p₀ = p ∧ C.MoveMarginAt p := by
  obtain ⟨a, ha1, hapos⟩ := exists_thetaSite_pos 2 le_rfl
  obtain ⟨C, hwf, hv, hp, -, -, hmargin⟩ :=
    exists_wellFormed2_validAt2_of_density d p hp1 hpos a ha1 hapos
  exact ⟨C, hwf, hv, hp, hmargin⟩

/-! ## Non-vacuity at the explicit planar density `1 - 2⁻³²` -/

/-- The rebuilt reliability tolerance is positive and has its stated exact value. -/
theorem eta_of_beta {C : Certificate2 d} (hwf : C.WellFormed)
    (heps : C.eps = C.beta) :
    C.eta = C.beta ^ 5 / 73728 ∧ 0 < C.eta := by
  exact ⟨by rw [hwf.eta_eq_pow, heps], hwf.eta_pos⟩

/-- The planar density of `exists_thetaSite_pos 2` is `siteParam 2 incParam = 1 - 2⁻³²`. -/
theorem coe_siteParam_two_incParam : ((siteParam 2 incParam : unitInterval) : ℝ) = 1 - 1 / 2 ^ 32 := by
  rw [coe_siteParam, coe_incParam]; norm_num

/-- Site percolation on the plane percolates at `1 - 2⁻³²`; the proof of `exists_thetaSite_pos`,
with its witness made explicit. -/
theorem thetaSite_two_siteParam_pos : 0 < thetaSite 2 (siteParam 2 incParam) := by
  have hq : 0 < theta (zdGraph 2) 0 (bondParam incParam) :=
    theta_zd_pos_of_le le_rfl (bondParam incParam) (by rw [coe_bondParam, coe_incParam]; norm_num)
  have hbond := prodBernoulli_map_bondOfInc 2 incParam
  have hsite := prodBernoulli_map_siteOfInc 2 incParam
  have hmb := measurable_bondOfInc 2
  have hms := measurable_siteOfInc 2
  have hsub : bondOfInc 2 ⁻¹' (percolatesAt (0 : Site 2))
      ⊆ siteOfInc 2 ⁻¹' {ω : SiteConfig (Site 2) | (siteCluster (zdGraph 2) ω 0).Infinite} :=
    fun ω hω => infinite_siteCluster_of_percolatesAt 2 ω hω
  have hth : theta (zdGraph 2) 0 (bondParam incParam)
      = ((prodBernoulli fun _ : Inc 2 => incParam).map (bondOfInc 2)).real
          (percolatesAt (0 : Site 2)) := by
    rw [hbond]; rfl
  have hts : thetaSite 2 (siteParam 2 incParam)
      = ((prodBernoulli fun _ : Inc 2 => incParam).map (siteOfInc 2)).real
          {ω : SiteConfig (Site 2) | (siteCluster (zdGraph 2) ω 0).Infinite} := by
    rw [hsite]; rfl
  calc (0 : ℝ) < theta (zdGraph 2) 0 (bondParam incParam) := hq
    _ = (prodBernoulli fun _ : Inc 2 => incParam).real
          (bondOfInc 2 ⁻¹' percolatesAt (0 : Site 2)) := by
        rw [hth, map_measureReal_apply hmb (measurableSet_percolatesAt_holds 0)]
    _ ≤ (prodBernoulli fun _ : Inc 2 => incParam).real
          (siteOfInc 2 ⁻¹' {ω : SiteConfig (Site 2) | (siteCluster (zdGraph 2) ω 0).Infinite}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = thetaSite 2 (siteParam 2 incParam) := by
        rw [hts, map_measureReal_apply hms (measurableSet_siteInfinite _ _)]

/-- **Non-vacuity, explicitly.**  The retained error is exactly the manuscript-safe `beta`, and
the seed/level tolerance and reliability tolerance are rebuilt from it. -/
theorem exists_wellFormed2_validAt2_explicit (d : ℕ) [NeZero d] (p : unitInterval)
    (hp1 : (p : ℝ) < 1) (hpos : 0 < thetaSite d p) :
    ∃ C : Certificate2 d, C.WellFormed ∧ C.ValidAt2 p ∧ C.p₀ = p ∧
      (C.density : ℝ) = 1 - 1 / 2 ^ 32 ∧ C.beta = betaOf d C.density ∧
      C.eps = C.beta ∧ C.delta = C.eps ^ 2 / 96 ∧
      C.eta = C.eps ^ 5 / 73728 ∧ 0 < C.eta ∧ C.MoveMarginAt p := by
  obtain ⟨C, hwf, hv, hp, hdens, heps, hmargin⟩ :=
    exists_wellFormed2_validAt2_of_density d p hp1 hpos
    (siteParam 2 incParam) (by rw [coe_siteParam_two_incParam]; norm_num) thetaSite_two_siteParam_pos
  have ha : (C.density : ℝ) = 1 - 1 / 2 ^ 32 := by rw [hdens, coe_siteParam_two_incParam]
  have hepsbeta : C.eps = C.beta := by rw [heps, hwf.beta_eq, hdens]
  exact ⟨C, hwf, hv, hp, ha, hwf.beta_eq, hepsbeta, hwf.delta_eq,
    hwf.eta_eq_pow, hwf.eta_pos, hmargin⟩

/-! ## Soundness, the single remaining hypothesis -/

/-- **The geometric input.**  A well-formed certificate valid at `q` forces percolation in the slab
of its width at `q`.  Nothing below proves it.  As for `CertificateSound d`, a proof has to use
`3 ≤ d`, since a strip of bounded width never percolates below `1`. -/
def CertificateSound2 (d : ℕ) [NeZero d] : Prop :=
  ∀ (C : Certificate2 d) (q : unitInterval), C.WellFormed → C.ValidAt2 q →
    0 < thetaSiteOn (slabGraph d C.width) (slabOrigin d C.width) q

/-! ## Assembly -/

/-- **The below-parameter reduction from soundness alone.** -/
theorem siteSlabReductionBelow_of_certificateSound2 (d : ℕ) [NeZero d]
    (hsound : CertificateSound2 d) : SiteSlabReductionBelow d := by
  intro p _ hp1 hpos
  obtain ⟨C, hwf, hC, -, hmargin⟩ :=
    exists_wellFormed2_validAt2_moveMargin d p hp1 hpos
  obtain ⟨ε, hε, hnhds⟩ := C.exists_valid_nhds2 hwf hC hmargin
  obtain ⟨t, ht0, htε, htp⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ε / 2 ∧ t ≤ (p : ℝ) / 2 :=
    ⟨min (ε / 2) ((p : ℝ) / 2), lt_min (by linarith) (by linarith),
      min_le_left _ _, min_le_right _ _⟩
  have hp1' : (p : ℝ) ≤ 1 := p.2.2
  refine ⟨C.width, ⟨(p : ℝ) - t, Set.mem_Icc.2 ⟨by linarith, by linarith⟩⟩, ?_, ?_⟩
  · show (p : ℝ) - t < (p : ℝ)
    linarith
  · refine hsound C _ hwf (hnhds _ ?_ ?_)
    · show (p : ℝ) - ε < (p : ℝ) - t
      linarith
    · show (p : ℝ) - t ≤ (p : ℝ)
      linarith

/-- **The capstone.**  From `CertificateSound2 d` alone, site percolation on `ℤ^d`, `d ≥ 2`, has no
infinite cluster at its critical parameter. -/
theorem siteCriticality_of_certificateSound2 (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hsound : CertificateSound2 d) : SiteCriticality d :=
  siteCriticality_of_slabReductionBelow' d hd (siteSlabReductionBelow_of_certificateSound2 d hsound)

end KNAll.Site.LeftImp2

end

/-! ## Co-import check -/

noncomputable section CoImportCheck

open KNAll.Site KNAll.Site.MacroExp KNAll.Site.TargetExt KNAll.Site.LeftImp KNAll.Site.LeftImp2
open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

#check @KNAll.Site.TargetExt.targetExtension_eps
#check @KNAll.Site.MacroExp.certificateSound_of_stepBound
#check @KNAll.Site.LeftImp.siteCriticality_of_certificateSound

#print axioms KNAll.Site.LeftImp2.exists_wellFormed2_validAt2
#print axioms KNAll.Site.LeftImp2.exists_wellFormed2_validAt2_explicit
#print axioms KNAll.Site.LeftImp2.Certificate2.exists_valid_nhds2
#print axioms KNAll.Site.LeftImp2.sourceOnly_not_mem_moveWindowEvent
#print axioms KNAll.Site.LeftImp2.isotropicCore_subset_M
#print axioms KNAll.Site.LeftImp2.isotropicCentralBox_subset_Q
#print axioms KNAll.Site.LeftImp2.Certificate2.not_validAt2_zero
#print axioms KNAll.Site.LeftImp2.Certificate2.not_wellFormed_of_bounds_eq_nil
#print axioms KNAll.Site.LeftImp2.Certificate2.WellFormed.level_of_le
#print axioms KNAll.Site.LeftImp2.siteSlabReductionBelow_of_certificateSound2
#print axioms KNAll.Site.LeftImp2.siteCriticality_of_certificateSound2

end CoImportCheck
