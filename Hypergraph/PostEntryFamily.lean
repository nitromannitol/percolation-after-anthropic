import Hypergraph.PerLevel
import Hypergraph.CorridorEstimates
import Hypergraph.SelectionPacking

/-!
# A longitudinal post-entry family

This file constructs the deterministic family required by the domain-relative `hpost` clause of
`PerLevel.hone_accepted`.  Its boxes occupy only the fresh outgoing tail.  At stopped level `j`
the first longitudinal coordinate of the outer box is strictly beyond the revealed prefix
`5 r + 10 s j`; successive target-extension levels erode that tail in the planar coordinates but
do not erode the two artificial slab faces.  The latter is legitimate precisely because the gate
is relative to `Dom`: every point of `Dom` is in `MacroExp.thin d t`.

The target-aware event below first chooses, from the observed shell, an open endpoint of an actual
crossing of a contact cube.  It then asks that this chosen endpoint reach the whole distant
`Stopped.stubTarget` inside the middle box.  Thus it does not require a predetermined site to be
open.  The deterministic determination and relay clauses are proved here.  The sole probabilistic
input left explicit is `PostWindowBound`, the finite-cylinder estimate from Sections 4--6 and 9 of
`CORRIDOR_MOVE.md`; the current certificate records only the distinct corridor-move windows.
-/

noncomputable section

namespace KNAll.Site.PostFam

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor

variable {d : ℕ} [NeZero d]

/-! ## The shell-determined target-aware event -/

/-- Sites of `U` which are open and are reached from some open site of `A` inside `R`. -/
def relayCandidates (R A U : Finset (Site d)) (omega : SiteConfig (Site d)) :
    Finset (Site d) := by
  classical
  exact U.filter fun u =>
    u ∈ omega ∧ ∃ a ∈ A, omega ∈ connWithin (zdGraph d) (↑R : Set (Site d)) a u

/-- A canonical relay chosen only after the shell exhibits a crossing endpoint. -/
def relayChoice (R A U : Finset (Site d)) (omega : SiteConfig (Site d)) : Site d :=
  if h : (relayCandidates R A U omega).Nonempty then Classical.choose h else 0

theorem relayChoice_spec {R A U : Finset (Site d)} {omega : SiteConfig (Site d)}
    (h : (relayCandidates R A U omega).Nonempty) :
    relayChoice R A U omega ∈ U ∧ relayChoice R A U omega ∈ omega := by
  classical
  rw [relayChoice, dif_pos h]
  have hs := Finset.mem_filter.1 (Classical.choose_spec h)
  exact ⟨hs.1, hs.2.1⟩

/-- The explicit post-entry window: a shell-visible crossing endpoint is chosen and that endpoint
connects, inside `O`, to the actual target `T`. -/
def postWindowEvent (R A U O : Finset (Site d)) (T : Set (Site d)) :
    Set (SiteConfig (Site d)) :=
  {omega | (relayCandidates R A U omega).Nonempty ∧
    omega ∈ TargetExt.toTarget (zdGraph d) O T (relayChoice R A U omega)}

theorem relayCandidates_congr {R A U S : Finset (Site d)}
    (hR : R ⊆ S) (hU : U ⊆ S) {omega omega' : SiteConfig (Site d)}
    (hagree : omega ∩ (↑S : Set (Site d)) = omega' ∩ ↑S) :
    relayCandidates R A U omega = relayCandidates R A U omega' := by
  classical
  ext u
  simp only [relayCandidates, Finset.mem_filter]
  have hu : u ∈ U → (u ∈ omega ↔ u ∈ omega') := by
    intro huU
    have huS : u ∈ (↑S : Set (Site d)) := by
      exact Finset.mem_coe.2 (hU huU)
    have h := Set.ext_iff.1 hagree u
    simpa only [Set.mem_inter_iff, huS, and_true] using h
  have hconn : ∀ a u, omega ∈ connWithin (zdGraph d) (↑R : Set (Site d)) a u ↔
      omega' ∈ connWithin (zdGraph d) (↑R : Set (Site d)) a u := by
    intro a u
    exact (determinedBy_iff _ _).1
      ((determinedBy_connWithin (zdGraph d) (↑R : Set (Site d)) a u).mono
        (Finset.coe_subset.2 hR)) omega omega' hagree
  constructor
  · rintro ⟨huU, huomega, a, ha, hau⟩
    exact ⟨huU, (hu huU).1 huomega, a, ha, (hconn a u).1 hau⟩
  · rintro ⟨huU, huomega, a, ha, hau⟩
    exact ⟨huU, (hu huU).2 huomega, a, ha, (hconn a u).2 hau⟩

theorem relayChoice_congr {R A U S : Finset (Site d)}
    (hR : R ⊆ S) (hU : U ⊆ S) {omega omega' : SiteConfig (Site d)}
    (hagree : omega ∩ (↑S : Set (Site d)) = omega' ∩ ↑S) :
    relayChoice R A U omega = relayChoice R A U omega' := by
  unfold relayChoice
  rw [relayCandidates_congr hR hU hagree]

theorem determinedBy_postWindowEvent {R A U O : Finset (Site d)} {T : Set (Site d)}
    (hR : R ⊆ O) (hU : U ⊆ O) :
    DeterminedBy (postWindowEvent R A U O T) (↑O : Set (Site d)) := by
  rw [determinedBy_iff]
  intro omega omega' hagree
  have hcand := relayCandidates_congr (A := A) hR hU hagree
  have hchoice := relayChoice_congr (A := A) hR hU hagree
  have htarget :
      omega ∈ TargetExt.toTarget (zdGraph d) O T (relayChoice R A U omega) ↔
        omega' ∈ TargetExt.toTarget (zdGraph d) O T (relayChoice R A U omega') := by
    rw [hchoice]
    exact (determinedBy_iff _ _).1
      (TargetExt.determinedBy_toTarget (zdGraph d) O T (relayChoice R A U omega'))
      omega omega' hagree
  simp only [postWindowEvent, Set.mem_setOf_eq]
  rw [hcand, htarget]

theorem measurableSet_postWindowEvent {R A U O : Finset (Site d)} {T : Set (Site d)}
    (hR : R ⊆ O) (hU : U ⊆ O) :
    MeasurableSet (postWindowEvent R A U O T) :=
  (determinedBy_postWindowEvent hR hU).measurableSet_of_finset

/-- The chosen endpoint is fixed by the shell pattern, so the explicit event has exactly the
pointwise relay property required by `TargetExt.LevelGeometry`. -/
theorem postWindowEvent_relay {R A U O Int : Finset (Site d)} {T : Set (Site d)}
    (hR : R ⊆ O \ Int) (hU : U ⊆ O \ Int) :
    ∀ omega ∈ postWindowEvent R A U O T,
      ∃ u ∈ U, u ∈ omega ∧ ∀ omega' ∈ postWindowEvent R A U O T,
        omega' ∩ (↑(O \ Int) : Set (Site d)) = omega ∩ ↑(O \ Int) →
          omega' ∈ TargetExt.toTarget (zdGraph d) O T u := by
  intro omega homega
  have huspec := relayChoice_spec homega.1
  refine ⟨relayChoice R A U omega, huspec.1, huspec.2, ?_⟩
  intro omega' homega' hagree
  have hchoice := relayChoice_congr (A := A) hR hU hagree
  simpa only [hchoice] using homega'.2

/-! ## Longitudinal tail boxes -/

/-- The longitudinal half-length of a post-entry tail before target-extension erosion.  Its
chosen value makes the two axial endpoints `5r + 10sj + 1` and `21r - 1`. -/
def tailHalfLength (r s j : ℕ) : ℤ := 8 * (r : ℤ) - 5 * (s : ℤ) * j - 1

/-- The centre of the fresh tail interval, expressed in the signed outgoing coordinate. -/
def tailCentre (c : Site d) (i : Fin d) (sigma : ℤ) (r s j : ℕ) : Site d :=
  c + Pi.single i
    (sigma * (5 * (r : ℤ) + 10 * (s : ℤ) * j + 1 + tailHalfLength r s j))

/-- The `m`-th tail radius.  Both planar directions erode by one at every level.  The artificial
slab directions retain radius `t`; points of the relative ambient domain never lie beyond those
faces. -/
def tailRho (C : LeftImp2.Certificate2 d) (i : Fin d) (r t s j m : ℕ) : Fin d → ℤ :=
  fun q =>
    if q = i then tailHalfLength r s j - m
    else if q.val < 2 then 2 * (r : ℤ) + C.levels - m
    else (t : ℤ)

/-- At each outer level we reuse the already verified contact-cube and seed geometry, but with a
new scale record whose outer radius is the appropriate one-sided tail box. -/
def tailScales (C : LeftImp2.Certificate2 d) (i : Fin d) (r t s j m : ℕ) : Scales d where
  ρ₀ := tailRho C i r t s j m
  ℓ := 1
  s := 2 * C.faceTarget + 1
  M := C.faceTarget

/-- The concrete outer domain of post-entry level `m`. -/
def tailD (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d) (sigma : ℤ)
    (r t s j m : ℕ) : Finset (Site d) :=
  Dbox (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0

/-- The middle shell box of post-entry level `m`. -/
def tailO (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d) (sigma : ℤ)
    (r t s j m : ℕ) : Finset (Site d) :=
  Obox (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0

/-- The inner shell box of post-entry level `m`. -/
def tailInt (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d) (sigma : ℤ)
    (r t s j m : ℕ) : Finset (Site d) :=
  Ibox (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0

/-- The local source patch used only to select a shell-visible crossing endpoint. -/
def tailSourcePatch (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d) (sigma : ℤ)
    (r t s j m : ℕ) (x : Site d) : Finset (Site d) :=
  rbox (cubeCentre (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0 x)
    (fun _ => (C.source : ℤ))

/-- The explicit target-aware event at one contact of one tail level. -/
def tailWindow (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d) (sigma : ℤ)
    (r t s j m : ℕ) (T : Set (Site d)) (x : Site d) : Set (SiteConfig (Site d)) :=
  let Sc := tailScales C i r t s j m
  let cc := tailCentre c i sigma r s j
  postWindowEvent (cube Sc cc 0 x) (tailSourcePatch C c i sigma r t s j m x)
    (face Sc cc 0 x) (Obox Sc cc 0) T

/-- The target-aware event is decided by the middle tail box. -/
theorem determinedBy_tailWindow (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : ℤ) (r t s j m : ℕ) (T : Set (Site d))
    (hfit : Fits (tailScales C i r t s j m) 0) {Dom : Finset (Site d)} {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (tailD C c i sigma r t s j m)) :
    DeterminedBy (tailWindow C c i sigma r t s j m T x)
      (↑(tailO C c i sigma r t s j m) : Set (Site d)) := by
  let Sc := tailScales C i r t s j m
  let cc := tailCentre c i sigma r s j
  have hcontact : IsContact cc (ρD Sc 0) x := by
    exact isContact_of_mem_outerBoundary Sc cc 0 Dom (by simpa [tailD, Sc, cc] using hx)
  have hcube : cube Sc cc 0 x ⊆ Obox Sc cc 0 \ Ibox Sc cc 0 :=
    cube_subset_shell hfit hcontact
  have hface : face Sc cc 0 x ⊆ Obox Sc cc 0 \ Ibox Sc cc 0 :=
    face_subset_shell hfit hcontact
  exact determinedBy_postWindowEvent
    (hcube.trans Finset.sdiff_subset) (hface.trans Finset.sdiff_subset)

/-- The target-aware event has the shell-pattern relay property used by target extension. -/
theorem tailWindow_relay (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : ℤ) (r t s j m : ℕ) (T : Set (Site d))
    (hfit : Fits (tailScales C i r t s j m) 0) {Dom : Finset (Site d)} {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (tailD C c i sigma r t s j m)) :
    ∀ omega ∈ tailWindow C c i sigma r t s j m T x,
      ∃ u ∈ face (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0 x,
        u ∈ omega ∧ ∀ omega' ∈ tailWindow C c i sigma r t s j m T x,
          omega' ∩ (↑(tailO C c i sigma r t s j m \ tailInt C c i sigma r t s j m) :
              Set (Site d)) =
            omega ∩ ↑(tailO C c i sigma r t s j m \ tailInt C c i sigma r t s j m) →
          omega' ∈ TargetExt.toTarget (zdGraph d) (tailO C c i sigma r t s j m) T u := by
  let Sc := tailScales C i r t s j m
  let cc := tailCentre c i sigma r s j
  have hcontact : IsContact cc (ρD Sc 0) x :=
    isContact_of_mem_outerBoundary Sc cc 0 Dom (by simpa [tailD, Sc, cc] using hx)
  have hcube : cube Sc cc 0 x ⊆ Obox Sc cc 0 \ Ibox Sc cc 0 :=
    cube_subset_shell hfit hcontact
  have hface : face Sc cc 0 x ⊆ Obox Sc cc 0 \ Ibox Sc cc 0 :=
    face_subset_shell hfit hcontact
  simpa only [tailWindow, tailO, tailInt, Sc, cc] using
    (postWindowEvent_relay (T := T) hcube hface)

/-! ## One packaged level -/

/-- One member of the post-entry family.  All seed paths and the greedy packing are the concrete
ones from `CorridorGeometry`; only the outer box has been changed to the one-sided tail. -/
def tailLevel (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d) (sigma : ℤ)
    (r t s j m : ℕ) (Dom : Finset (Site d)) (o : Site d) (T : Set (Site d))
    (hfit : Fits (tailScales C i r t s j m) 0)
    (hDDom : tailD C c i sigma r t s j m ⊆ Dom)
    (ho : o ∉ tailD C c i sigma r t s j m) :
    TargetExt.LevelGeometry (zdGraph d) Dom o T :=
  toLevelGeometry (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0 hfit
    Dom hDDom o ho T (tailWindow C c i sigma r t s j m T)
    (fun _x hx => determinedBy_tailWindow C c i sigma r t s j m T hfit hx)
    (fun _x hx => tailWindow_relay C c i sigma r t s j m T hfit hx)

@[simp] theorem tailLevel_D (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : ℤ) (r t s j m : ℕ) (Dom : Finset (Site d)) (o : Site d)
    (T : Set (Site d)) (hfit) (hDDom) (ho) :
    (tailLevel C c i sigma r t s j m Dom o T hfit hDDom ho).D =
      tailD C c i sigma r t s j m := rfl

@[simp] theorem tailLevel_Gx (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : ℤ) (r t s j m : ℕ) (Dom : Finset (Site d)) (o : Site d)
    (T : Set (Site d)) (hfit) (hDDom) (ho) (x : Site d) :
    (tailLevel C c i sigma r t s j m Dom o T hfit hDDom ho).Gx x =
      tailWindow C c i sigma r t s j m T x := rfl

@[simp] theorem tailLevel_sel (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : ℤ) (r t s j m : ℕ) (Dom : Finset (Site d)) (o : Site d)
    (T : Set (Site d)) (hfit) (hDDom) (ho) (L : Finset (Site d)) :
    (tailLevel C c i sigma r t s j m Dom o T hfit hDDom ho).sel L =
      selC (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0 L := rfl

@[simp] theorem tailLevel_J (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : ℤ) (r t s j m : ℕ) (Dom : Finset (Site d)) (o : Site d)
    (T : Set (Site d)) (hfit) (hDDom) (ho) (x : Site d) :
    (tailLevel C c i sigma r t s j m Dom o T hfit hDDom ho).J x =
      seed (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0 x := rfl

/-- **The exact missing certificate input.**  These are the post-entry windows of Section 9,
with component loss `3 * delta^2`; they are not any of the `d+1` move windows currently stored in
`Certificate2.moveWindowBounds`. -/
def PostWindowBound (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (c : Site d) (i : Fin d) (sigma : ℤ) (r t s j : ℕ)
    (Dom : Finset (Site d)) (T : Set (Site d)) : Prop :=
  ∀ m, m < C.levels → ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (tailD C c i sigma r t s j m),
    1 - 3 * C.delta ^ 2 ≤
      (siteBernoulli (fun _ : Site d => q)).real
        (tailWindow C c i sigma r t s j m T x)

/-! ## Deterministic tail geometry -/

theorem tailD_succ_subset (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : ℤ) (r t s j m : ℕ) :
    tailD C c i sigma r t s j (m + 1) ⊆ tailD C c i sigma r t s j m := by
  unfold tailD Dbox
  apply rbox_mono
  intro q
  simp only [ρD, tailScales, tailRho, Nat.cast_zero, sub_zero]
  split_ifs
  · push_cast; omega
  · push_cast; omega
  · exact le_rfl

/-- The scale inequalities selected after the stopped level count make every contact cube fit in
its shell. -/
theorem tail_fits (C : LeftImp2.Certificate2 d) {r t s K j m : ℕ}
    (hj : j < K) (hm : m < C.levels)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t) (i : Fin d) :
    Fits (tailScales C i r t s j m) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp only [ρO, ρD, tailScales, tailRho, Nat.cast_zero, sub_zero]
    by_cases hqi : q = i
    · rw [if_pos hqi]
      push_cast
      have hsj : 5 * s * j ≤ 5 * s * K := Nat.mul_le_mul_left (5 * s) hj.le
      have hm' : m + 1 ≤ C.levels := Nat.succ_le_iff.2 hm
      have hsj' : 5 * (s : ℤ) * j ≤ 5 * (s : ℤ) * K := by exact_mod_cast hsj
      have hmz : (m : ℤ) + 1 ≤ C.levels := by exact_mod_cast hm'
      have hlongz : 5 * (s : ℤ) * K + C.levels + C.faceTarget + 2 ≤ 8 * r := by
        exact_mod_cast hlong
      unfold tailHalfLength
      push_cast
      omega
    · rw [if_neg hqi]
      by_cases hq2 : q.val < 2
      · rw [if_pos hq2]
        push_cast
        omega
      · rw [if_neg hq2]
        push_cast
        omega
  · simp [tailScales]
  · simp [tailScales]

theorem tailCentre_apply_self {c : Site d} {i : Fin d} {sigma : ℤ} {r s j : ℕ} :
    tailCentre c i sigma r s j i =
      c i + sigma * (5 * (r : ℤ) + 10 * (s : ℤ) * j + 1 + tailHalfLength r s j) := by
  simp [tailCentre]

theorem tailCentre_apply_of_ne {c : Site d} {i q : Fin d} (hqi : q ≠ i)
    {sigma : ℤ} {r s j : ℕ} :
    tailCentre c i sigma r s j q = c q := by
  simp [tailCentre, hqi]

theorem lam_tailCentre {c : Site d} {i : Fin d} {sigma : ℤ}
    (hsigma : sigma = 1 ∨ sigma = -1) {r s j : ℕ} :
    Stopped.lam c i sigma (tailCentre c i sigma r s j) =
      5 * (r : ℤ) + 10 * (s : ℤ) * j + 1 + tailHalfLength r s j := by
  have hsigma2 : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
  simp only [Stopped.lam, tailCentre_apply_self, add_sub_cancel_left, ← mul_assoc,
    hsigma2, one_mul]

/-- Coordinate bounds for membership in a tail level. -/
theorem tailD_bounds {C : LeftImp2.Certificate2 d} {c x : Site d} {i : Fin d}
    {sigma : ℤ} {r t s j m : ℕ} (hx : x ∈ tailD C c i sigma r t s j m) :
    ∀ q,
      tailCentre c i sigma r s j q - tailRho C i r t s j m q ≤ x q ∧
        x q ≤ tailCentre c i sigma r s j q + tailRho C i r t s j m q := by
  simpa only [tailD, Dbox, ρD, tailScales, Nat.cast_zero, sub_zero] using
    (mem_rbox.1 hx)

theorem mem_tailD_of_bounds {C : LeftImp2.Certificate2 d} {c x : Site d} {i : Fin d}
    {sigma : ℤ} {r t s j m : ℕ}
    (hx : ∀ q,
      tailCentre c i sigma r s j q - tailRho C i r t s j m q ≤ x q ∧
        x q ≤ tailCentre c i sigma r s j q + tailRho C i r t s j m q) :
    x ∈ tailD C c i sigma r t s j m := by
  rw [tailD, Dbox, mem_rbox]
  simpa only [ρD, tailScales, Nat.cast_zero, sub_zero] using hx

/-- The next stopped cross-section remains inside every eroded tail level. -/
theorem stubFace_subset_tailD (C : LeftImp2.Certificate2 d) {c : Site d} {i : Fin d}
    {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1) {r t s K j m : ℕ}
    (hj : j < K) (hm : m < C.levels)
    (hfar : 10 * s * K ≤ 13 * r) (hrt : 2 * r ≤ t)
    (hclear : C.levels ≤ 10 * s)
    (hwidth : C.levels ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r) :
    Stopped.stubFace c i sigma r t (10 * s * (j + 1)) ⊆
      tailD C c i sigma r t s j m := by
  intro x hx
  rw [Stopped.mem_stubFace hsigma] at hx
  apply mem_tailD_of_bounds
  intro q
  by_cases hqi : q = i
  · subst q
    have hsj : 5 * s * j ≤ 5 * s * K := Nat.mul_le_mul_left (5 * s) hj.le
    have hten : m + 1 ≤ 10 * s := (Nat.succ_le_iff.2 hm).trans hclear
    have hnext : 10 * s * (j + 1) ≤ 13 * r := by
      exact (Nat.mul_le_mul_left (10 * s) (Nat.succ_le_iff.2 hj)).trans hfar
    have hsjz : 5 * (s : ℤ) * j ≤ 5 * (s : ℤ) * K := by exact_mod_cast hsj
    have htenz : (m : ℤ) + 1 ≤ 10 * s := by exact_mod_cast hten
    have hmwidth : (m : ℤ) + 1 ≤ 3 * r := by
      exact_mod_cast (Nat.succ_le_iff.2 hm).trans hwidth
    have hnextz : 10 * (s : ℤ) * (j + 1) ≤ 13 * r := by exact_mod_cast hnext
    have hnextz' : 10 * (s : ℤ) + 10 * (s : ℤ) * j ≤ 13 * r := by
      nlinarith [hnextz]
    have hlongz : 5 * (s : ℤ) * K + C.levels + C.faceTarget + 2 ≤ 8 * r := by
      exact_mod_cast hlong
    have hfaceCast : (((5 * r + 10 * s * (j + 1) : ℕ) : ℤ)) =
        5 * (r : ℤ) + 10 * (s : ℤ) * (j + 1) := by push_cast; ring
    rw [hfaceCast] at hx
    ring_nf at hsjz htenz hmwidth hnextz' hlongz
    rcases hsigma with hsig | hsig
    · subst sigma
      simp only [Stopped.lam, one_mul] at hx
      have hxcoord : x i = c i + 5 * (r : ℤ) + 10 * (s : ℤ) * (j + 1) := by
        omega
      simp only [tailCentre_apply_self, tailRho, if_pos rfl, one_mul]
      unfold tailHalfLength
      rw [hxcoord]
      ring_nf
      push_cast
      omega
    · subst sigma
      simp only [Stopped.lam, neg_one_mul] at hx
      have hxcoord : x i = c i - (5 * (r : ℤ) + 10 * (s : ℤ) * (j + 1)) := by
        omega
      simp only [tailCentre_apply_self, tailRho, if_pos rfl, neg_one_mul]
      unfold tailHalfLength
      rw [hxcoord]
      ring_nf
      push_cast
      omega
  · have hxq := hx.2 q hqi
    rw [abs_le] at hxq
    push_cast at hxq
    rw [tailCentre_apply_of_ne hqi, tailRho, if_neg hqi]
    by_cases hq2 : q.val < 2
    · rw [if_pos hq2]
      push_cast
      omega
    · rw [if_neg hq2]
      have hrtz : 2 * (r : ℤ) ≤ (t : ℤ) := by exact_mod_cast hrt
      omega

/-- Every tail site is strictly beyond the revealed prefix and remains before signed depth `21r`.
The strict first inequality is the freshness mechanism. -/
theorem tailD_lam_bounds (C : LeftImp2.Certificate2 d) {c x : Site d} {i : Fin d}
    {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1) {r t s K j m : ℕ}
    (hj : j < K) (hm : m < C.levels)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hx : x ∈ tailD C c i sigma r t s j m) :
    5 * (r : ℤ) + 10 * (s : ℤ) * j < Stopped.lam c i sigma x ∧
      Stopped.lam c i sigma x < 21 * (r : ℤ) := by
  have hxi := tailD_bounds (i := i) hx i
  have hsj : 5 * (s : ℤ) * j ≤ 5 * (s : ℤ) * K := by
    exact_mod_cast Nat.mul_le_mul_left (5 * s) hj.le
  have hmz : (m : ℤ) + 1 ≤ C.levels := by exact_mod_cast Nat.succ_le_iff.2 hm
  have hlongz : 5 * (s : ℤ) * K + C.levels + C.faceTarget + 2 ≤ 8 * r := by
    exact_mod_cast hlong
  rw [tailRho, if_pos rfl] at hxi
  rw [tailCentre_apply_self] at hxi
  unfold tailHalfLength at hxi
  rcases hsigma with rfl | rfl <;>
    simp only [Stopped.lam, one_mul, neg_one_mul] <;>
    ring_nf at hxi hsj hlongz ⊢ <;> omega

/-- Every concrete tail box lies in the outgoing edge region. -/
theorem tailD_subset_E (hd : 2 ≤ d) (C : LeftImp2.Certificate2 d)
    {z y : Site 2} {i : Fin d} {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    {r t s K j m : ℕ} (hj : j < K) (hm : m < C.levels)
    (hwidth : C.levels ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r) :
    tailD C (MacroExp.ctr d r z) i sigma r t s j m ⊆ MacroExp.E d r t z y := by
  intro x hx
  let c := MacroExp.ctr d r z
  have hiplanar : i.val < 2 := Stopped.dir_planar hsigma hemb
  have hlam := tailD_lam_bounds C hsigma hj hm hlong hx
  rw [MacroExp.E, Finset.mem_sdiff]
  constructor
  · rw [MacroExp.mem_hbox]
    intro q
    have hctr := Stopped.ctr_sub_apply (d := d) r y z q
    by_cases hqi : q = i
    · subst q
      have hcy : MacroExp.ctr d r y i = c i + 20 * (r : ℤ) * sigma := by
        rw [hemb, Pi.single_eq_same] at hctr
        dsimp only [c]
        omega
      clear hctr
      have hrad : MacroExp.rad (5 * r) t i = 5 * (r : ℤ) := by
        unfold MacroExp.rad
        rw [if_pos hiplanar]
        push_cast
        ring
      change min (c i) (MacroExp.ctr d r y i) - MacroExp.rad (5 * r) t i ≤ x i ∧
        x i ≤ max (c i) (MacroExp.ctr d r y i) + MacroExp.rad (5 * r) t i
      have hrnonneg : (0 : ℤ) ≤ 20 * (r : ℤ) := by positivity
      have hsjnonneg : (0 : ℤ) ≤ 10 * (s : ℤ) * j := by positivity
      rcases hsigma with hsig | hsig
      · subst sigma
        simp only [Stopped.lam, one_mul] at hlam
        change 5 * (r : ℤ) + 10 * (s : ℤ) * j < x i - c i ∧
          x i - c i < 21 * (r : ℤ) at hlam
        rw [hcy, hrad, min_eq_left (by linarith), max_eq_right (by linarith)]
        omega
      · subst sigma
        simp only [Stopped.lam, neg_one_mul] at hlam
        change 5 * (r : ℤ) + 10 * (s : ℤ) * j < -(x i - c i) ∧
          -(x i - c i) < 21 * (r : ℤ) at hlam
        rw [hcy, hrad, min_eq_right (by linarith), max_eq_left (by linarith)]
        omega
    · rw [hemb, Pi.single_eq_of_ne hqi] at hctr
      have hcy : MacroExp.ctr d r y q = c q := by dsimp only [c]; omega
      have hb := tailD_bounds hx q
      rw [tailCentre_apply_of_ne hqi, tailRho, if_neg hqi] at hb
      by_cases hq2 : q.val < 2
      · rw [if_pos hq2] at hb
        have hradius : 2 * (r : ℤ) + C.levels - m ≤ 5 * r := by
          push_cast
          omega
        have hrad : MacroExp.rad (5 * r) t q = 5 * (r : ℤ) := by
          unfold MacroExp.rad
          rw [if_pos hq2]
          push_cast
          ring
        rw [hcy, hrad, min_self, max_self]
        omega
      · rw [if_neg hq2] at hb
        have hrad : MacroExp.rad (5 * r) t q = (t : ℤ) := by
          unfold MacroExp.rad
          rw [if_neg hq2]
        rw [hcy, hrad, min_self, max_self]
        exact hb
  · intro hxQ
    rw [MacroExp.Q, MacroExp.mem_abox] at hxQ
    have hQi := hxQ i
    have hrad : MacroExp.rad (5 * r) t i = 5 * (r : ℤ) := by
      unfold MacroExp.rad
      rw [if_pos hiplanar]
      push_cast
      ring
    rw [hrad] at hQi
    have habs : |x i - c i| ≤ 5 * (r : ℤ) := by
      change |x i - MacroExp.ctr d r z i| ≤ 5 * (r : ℤ)
      rw [abs_le]
      omega
    rw [← Stopped.lam_abs hsigma c i x] at habs
    have habslam : Stopped.lam c i sigma x ≤ 5 * (r : ℤ) :=
      (le_abs_self _).trans habs
    have hlamlow : 5 * (r : ℤ) < Stopped.lam c i sigma x := by
      change 5 * (r : ℤ) <
        Stopped.lam (MacroExp.ctr d r z) i sigma x
      exact lt_of_le_of_lt (by
        have : 0 ≤ 10 * (s : ℤ) * j := by positivity
        linarith) hlam.1
    exact (not_lt_of_ge habslam) hlamlow

/-- The tail begins one lattice step after the part of the stub already revealed at level `j`. -/
theorem tailD_disjoint_stub (C : LeftImp2.Certificate2 d) {c : Site d} {i : Fin d}
    {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1) {r t s K j m : ℕ}
    (hj : j < K) (hm : m < C.levels)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r) :
    Disjoint (tailD C c i sigma r t s j m) (Stopped.stub c i sigma r t (10 * s * j)) := by
  rw [Finset.disjoint_left]
  intro x hxD hxstub
  have hlam := (tailD_lam_bounds C hsigma hj hm hlong hxD).1
  have hstub := (Stopped.mem_stub hsigma).1 hxstub
  have hcast : (((5 * r + 10 * s * j : ℕ) : ℤ)) =
      5 * (r : ℤ) + 10 * (s : ℤ) * j := by push_cast; ring
  rw [hcast] at hstub
  exact (not_lt_of_ge hstub.2.1) hlam

/-- The corrected, domain-relative gate.  In either planar coordinate the next box has been
eroded by one, so an adjacent point outside the current box cannot meet it.  In a transverse
coordinate there is deliberately no erosion; instead every point of the ambient domain is in the
slab, hence already lies between those two faces. -/
theorem tail_gate_rel (C : LeftImp2.Certificate2 d) {z : Site 2} {i : Fin d}
    (hiplanar : i.val < 2) {sigma : ℤ} {r t s j m : ℕ} {Dom : Finset (Site d)}
    (hDomThin : (↑Dom : Set (Site d)) ⊆ MacroExp.thin d t) :
    ∀ x ∈ Dom, x ∉ tailD C (MacroExp.ctr d r z) i sigma r t s j m →
      ∀ v ∈ tailD C (MacroExp.ctr d r z) i sigma r t s j m, (zdGraph d).Adj x v →
        v ∉ tailD C (MacroExp.ctr d r z) i sigma r t s j (m + 1) := by
  intro x hxDom hxout v _hv hadj hvnext
  apply hxout
  apply mem_tailD_of_bounds
  intro q
  have hvb := tailD_bounds hvnext q
  by_cases hq2 : q.val < 2
  · have hstep := LevelOpus.abs_sub_le_one_of_adj hadj q
    rw [abs_le] at hstep
    have hrho : tailRho C i r t s j (m + 1) q + 1 = tailRho C i r t s j m q := by
      unfold tailRho
      by_cases hqi : q = i
      · rw [if_pos hqi, if_pos hqi]
        push_cast
        ring
      · rw [if_neg hqi, if_neg hqi, if_pos hq2, if_pos hq2]
        push_cast
        ring
    rw [← hrho]
    constructor <;> omega
  · have hxthin := hDomThin (Finset.mem_coe.2 hxDom)
    have hq0 : q ≠ (0 : Fin d) := by
      intro hq
      have := congrArg Fin.val hq
      simp only [Fin.val_zero] at this
      omega
    have hq1 : q ≠ (1 : Fin d) := by
      intro hq
      have := congrArg Fin.val hq
      have hd1 : 1 < d := by omega
      change q.val = 1 % d at this
      rw [Nat.mod_eq_of_lt hd1] at this
      omega
    have hxq := hxthin q hq0 hq1
    have hqi : q ≠ i := by
      intro hq
      subst q
      exact hq2 hiplanar
    rw [tailCentre_apply_of_ne hqi, tailRho, if_neg hqi, if_neg hq2]
    have hcq : MacroExp.ctr d r z q = 0 := MacroExp.ctr_apply_of_not_lt r z hq2
    rw [hcq]
    rw [abs_le] at hxq
    simpa only [zero_sub, zero_add] using hxq

/-- A planar stub is contained in the ambient thin slab. -/
theorem stub_subset_thin (hd : 2 ≤ d) {z : Site 2} {i : Fin d}
    (hiplanar : i.val < 2) {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1)
    {r t a : ℕ} (hrt : 2 * r ≤ t) :
    (↑(Stopped.stub (MacroExp.ctr d r z) i sigma r t a) : Set (Site d)) ⊆
      MacroExp.thin d t := by
  intro x hx q hq0 hq1
  have hnlt : ¬ q.val < 2 := MacroExp.two_le_val_of_ne hq0 hq1 hd
  have hqi : q ≠ i := by
    intro hqi
    subst q
    exact hnlt hiplanar
  have hb := ((Stopped.mem_stub hsigma).1 (Finset.mem_coe.1 hx)).2.2 q hqi
  rw [MacroExp.ctr_apply_of_not_lt r z hnlt] at hb
  have hrtz : ((2 * r : ℕ) : ℤ) ≤ (t : ℤ) := by exact_mod_cast hrt
  exact (by simpa only [sub_zero] using hb.trans hrtz)

/-- The full relative domain at a stopped level remains in the thin slab. -/
theorem accepted_levelDom_subset_thin (hd : 2 ≤ d) {r t s n : ℕ}
    {h : MacroExp.Tr d} {q0 : unitInterval} {delta : ℝ}
    (hg : MacroExp.Good d r t h q0 delta) (omega0 : SiteConfig (Site d))
    {z y : Site 2} {i : Fin d} (hiplanar : i.val < 2) {sigma : ℤ}
    (hsigma : sigma = 1 ∨ sigma = -1) (hrt : 2 * r ≤ t)
    (j : ℕ) (omega : SiteConfig (Site d)) :
    (↑((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0) z i sigma j omega).inspected ∪
        MacroExp.E d r t z y) : Set (Site d)) ⊆ MacroExp.thin d t := by
  intro x hx
  rw [Finset.mem_coe, Finset.mem_union, Stopped.levelTr_inspected,
    Finset.mem_union] at hx
  rcases hx with (hx | hx) | hx
  · exact Stopped.accepted_inspected_thin hd hg omega0 (Finset.mem_coe.2 hx)
  · exact stub_subset_thin hd hiplanar hsigma hrt (Finset.mem_coe.2 hx)
  · exact MacroExp.E_subset_thin hd r t z y (Finset.mem_coe.2 hx)

/-- A tail level is fresh for the actual post-reveal transcript. -/
theorem tailD_fresh_levelTr (hd : 2 ≤ d) (C : LeftImp2.Certificate2 d)
    {q0 : unitInterval} {delta : ℝ} {r t s K n j m : ℕ} (hr : 0 < r)
    {h : MacroExp.Tr d} (hg : MacroExp.Good d r t h q0 delta)
    (hwspec : MacroExp.pendW d n h ∈ h.openV ∧
      (zdGraph 2).Adj (MacroExp.pendW d n h) (MacroExp.pendZ d n h))
    (omega0 : SiteConfig (Site d)) {y : Site 2}
    (hy : y ∈ MacroExp.pending d (MacroExp.accepted d r t n h omega0)
      (MacroExp.pendZ d n h)) {i : Fin d} {sigma : ℤ}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - MacroExp.pendZ d n h) : Site d) = Pi.single i sigma)
    (hj : j < K) (hm : m < C.levels)
    (hwidth : C.levels ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (omega : SiteConfig (Site d)) :
    Disjoint
      (tailD C (MacroExp.ctr d r (MacroExp.pendZ d n h)) i sigma r t s j m)
      (Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
        (MacroExp.pendZ d n h) i sigma j omega).inspected := by
  have hDE :
      tailD C (MacroExp.ctr d r (MacroExp.pendZ d n h)) i sigma r t s j m ⊆
        MacroExp.E d r t (MacroExp.pendZ d n h) y :=
    tailD_subset_E (t := t) hd C hsigma hemb hj hm hwidth hlong
  have hacc := Stopped.accepted_fresh_E hd hr hg hwspec omega0 hy
  rw [Stopped.levelTr_inspected, Finset.disjoint_union_right]
  exact ⟨hacc.symm.mono_left hDE,
    tailD_disjoint_stub C hsigma hj hm hlong⟩

/-- The embedded origin belongs to every accepted post-reveal transcript. -/
theorem emb_zero_mem_accepted_levelTr {r t s n j : ℕ} {h : MacroExp.Tr d}
    {q0 : unitInterval} {delta : ℝ} (hg : MacroExp.Good d r t h q0 delta)
    (omega0 : SiteConfig (Site d)) (i : Fin d) (sigma : ℤ)
    (z : Site 2) (omega : SiteConfig (Site d)) :
    (MacroExp.emb 0 : Site d) ∈
      (Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
        z i sigma j omega).inspected := by
  obtain ⟨a, -, hconn⟩ := hg.cert 0 hg.zero_mem
  have ho : (MacroExp.emb 0 : Site d) ∈ h.openSites := Finset.mem_coe.1 hconn.1.1
  rw [Stopped.levelTr_inspected, MacroExp.accepted, FRDom.Transcript.step_inspected]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (h.openSites_subset ho))

/-- A concrete site shared by the actual distant target and every used middle tail box. -/
def targetAnchor (c : Site d) (i : Fin d) (sigma : ℤ) (r : ℕ) : Site d :=
  c + Pi.single i (sigma * ((18 * r : ℕ) : ℤ))

theorem targetAnchor_mem_stubTarget {c : Site d} {i : Fin d} {sigma : ℤ}
    (hsigma : sigma = 1 ∨ sigma = -1) {r t : ℕ} :
    targetAnchor c i sigma r ∈ Stopped.stubTarget c i sigma r t (17 * r) := by
  have hsigma2 : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
  have hlam : Stopped.lam c i sigma (targetAnchor c i sigma r) = ((18 * r : ℕ) : ℤ) := by
    simp only [targetAnchor, Stopped.lam, Pi.add_apply, Pi.single_eq_same, add_sub_cancel_left]
    rw [← mul_assoc, hsigma2, one_mul]
  rw [Stopped.stubTarget, Finset.mem_filter, Stopped.mem_stub hsigma, hlam]
  refine ⟨⟨by push_cast; omega, ?_, ?_⟩, by push_cast; omega⟩
  · push_cast
    omega
  · intro q hqi
    simp [targetAnchor, Pi.single_eq_of_ne hqi]

/-- The same concrete target anchor is inside `O_m`.  The two `+1` margins are necessary: without
them the deepest middle box can stop one lattice step short of the target at signed depth `18r`. -/
theorem targetAnchor_mem_tailO (C : LeftImp2.Certificate2 d) {c : Site d} {i : Fin d}
    {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1) {r t s K j m : ℕ}
    (hr : 0 < r) (hj : j < K) (hm : m < C.levels)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (htrans : C.faceTarget + 1 ≤ t) :
    targetAnchor c i sigma r ∈ tailO C c i sigma r t s j m := by
  rw [tailO, Obox, mem_rbox]
  intro q
  simp only [ρO, ρD, tailScales, Nat.cast_zero, sub_zero]
  by_cases hqi : q = i
  · subst q
    have hsj : 10 * s * (j + 1) ≤ 10 * s * K :=
      Nat.mul_le_mul_left (10 * s) (Nat.succ_le_iff.2 hj)
    have hmclear : m + 2 ≤ 10 * s := by omega
    have hmwidth : m + 2 ≤ 3 * r := by omega
    have hsjz : 10 * (s : ℤ) * (j + 1) ≤ 13 * r := by
      exact_mod_cast hsj.trans hfar
    have hmclearz : (m : ℤ) + 2 ≤ 10 * s := by exact_mod_cast hmclear
    have hmwidthz : (m : ℤ) + 2 ≤ 3 * r := by exact_mod_cast hmwidth
    have hsigma2 : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
    simp only [tailCentre_apply_self, tailRho, if_pos rfl, targetAnchor, Pi.add_apply,
      Pi.single_eq_same]
    unfold tailHalfLength
    push_cast
    rcases hsigma with rfl | rfl <;> ring_nf at hsjz hmclearz hmwidthz ⊢ <;> omega
  · rw [tailCentre_apply_of_ne hqi, tailRho, if_neg hqi]
    simp only [targetAnchor, Pi.add_apply, Pi.single_eq_of_ne hqi, add_zero]
    by_cases hq2 : q.val < 2
    · rw [if_pos hq2]
      have hnonneg : (1 : ℤ) ≤ 2 * r + C.levels - m := by
        push_cast
        omega
      constructor <;> omega
    · rw [if_neg hq2]
      have ht : (1 : ℤ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
      constructor <;> omega

/-- Both stopped targets mentioned by `hpost` are concretely nonempty, and the distant one meets
the actual relay box at every used level. -/
theorem stopped_targets_nonempty (C : LeftImp2.Certificate2 d) {c : Site d} {i : Fin d}
    {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1) {r t s K j m : ℕ}
    (hr : 0 < r) (hj : j < K) (hm : m < C.levels)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (htrans : C.faceTarget + 1 ≤ t) :
    (Stopped.stubFace c i sigma r t (10 * s * (j + 1))).Nonempty ∧
      ((↑(Stopped.stubTarget c i sigma r t (17 * r)) : Set (Site d)) ∩
        ↑(tailO C c i sigma r t s j m)).Nonempty := by
  refine ⟨Stopped.stubFace_nonempty c i hsigma r t _, ?_⟩
  refine ⟨targetAnchor c i sigma r, Finset.mem_coe.2 (targetAnchor_mem_stubTarget hsigma),
    Finset.mem_coe.2 ?_⟩
  exact targetAnchor_mem_tailO C hsigma hr hj hm hfar hclear hwidth htrans

/-- The centre of the contact cube, shifted to its outward face. -/
def localFaceAnchor (Sc : Scales d) (c : Site d) (j : ℕ) (x : Site d) : Site d :=
  cubeCentre Sc c j x + Pi.single (cI Sc c j x) (cσ Sc c j x * (Sc.M : ℤ))

theorem localFaceAnchor_mem_face {Sc : Scales d} {c : Site d} {j : ℕ} {x : Site d}
    (hx : IsContact c (ρD Sc j) x) :
    localFaceAnchor Sc c j x ∈ face Sc c j x := by
  obtain ⟨hsigma, -, -⟩ := dir_spec hx
  rw [face, Finset.mem_filter]
  constructor
  · rw [cube, mem_rbox]
    intro q
    simp only [localFaceAnchor, Pi.add_apply]
    by_cases hq : q = cI Sc c j x
    · subst q
      rw [Pi.single_eq_same]
      have hM : (0 : ℤ) ≤ Sc.M := by positivity
      rcases hsigma with hsigma | hsigma <;>
        rw [show cσ Sc c j x = dirσ c (ρD Sc j) x from rfl, hsigma] <;>
        constructor <;> omega
    · rw [Pi.single_eq_of_ne hq]
      simp
  · simp only [localFaceAnchor, Pi.add_apply, Pi.single_eq_same]
    unfold cubeCentre
    rw [if_pos rfl]
    rcases hsigma with hsigma | hsigma <;>
      rw [show cσ Sc c j x = dirσ c (ρD Sc j) x from rfl, hsigma] <;> ring

theorem cubeCentre_mem_sourcePatch (C : LeftImp2.Certificate2 d)
    (c : Site d) (i : Fin d) (sigma : ℤ) (r t s j m : ℕ) (x : Site d) :
    cubeCentre (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0 x ∈
      tailSourcePatch C c i sigma r t s j m x := by
  rw [tailSourcePatch, mem_rbox]
  intro q
  simp

/-- In particular, the explicit reliability event is not empty.  The all-open configuration
contains a shell crossing, the canonical relay is in `O`, and it joins the concrete `18r` anchor
inside `O`. -/
theorem tailWindow_nonempty (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed)
    {c : Site d} {i : Fin d} {sigma : ℤ} (hsigma : sigma = 1 ∨ sigma = -1)
    {r t s K j m : ℕ} (hr : 0 < r) (hj : j < K) (hm : m < C.levels)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    {Dom : Finset (Site d)} {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (tailD C c i sigma r t s j m)) :
    (tailWindow C c i sigma r t s j m
      (↑(Stopped.stubTarget c i sigma r t (17 * r)) : Set (Site d)) x).Nonempty := by
  classical
  let Sc := tailScales C i r t s j m
  let cc := tailCentre c i sigma r s j
  let a := cubeCentre Sc cc 0 x
  let u := localFaceAnchor Sc cc 0 x
  let v := targetAnchor c i sigma r
  let allOpen : SiteConfig (Site d) := fun _ => True
  have hfit : Fits Sc 0 := tail_fits C hj hm hlong hplanar htrans i
  have hcontact : IsContact cc (ρD Sc 0) x :=
    isContact_of_mem_outerBoundary Sc cc 0 Dom (by simpa only [Sc, cc, tailD] using hx)
  have hu : u ∈ face Sc cc 0 x := localFaceAnchor_mem_face hcontact
  have hua : u ∈ cube Sc cc 0 x := face_subset_cube x hu
  have ha : a ∈ cube Sc cc 0 x := by
    rw [cube, mem_rbox]
    intro q
    simp [a]
  have haSource : a ∈ tailSourcePatch C c i sigma r t s j m x := by
    exact cubeCentre_mem_sourcePatch C c i sigma r t s j m x
  have hconnAU : allOpen ∈
      connWithin (zdGraph d) (↑(cube Sc cc 0 x) : Set (Site d)) a u := by
    exact connWithin_rbox_of_allOpen (by intro _ _; trivial) (dist1 a u) a u ha hua le_rfl
  have hcand : (relayCandidates (cube Sc cc 0 x)
      (tailSourcePatch C c i sigma r t s j m x) (face Sc cc 0 x)
      allOpen).Nonempty := by
    refine ⟨u, ?_⟩
    rw [relayCandidates, Finset.mem_filter]
    exact ⟨hu, trivial, a, haSource, hconnAU⟩
  have hchoice := relayChoice_spec hcand
  have hchoiceO : relayChoice (cube Sc cc 0 x)
      (tailSourcePatch C c i sigma r t s j m x) (face Sc cc 0 x) allOpen ∈ Obox Sc cc 0 := by
    exact Finset.sdiff_subset (face_subset_shell hfit hcontact hchoice.1)
  have hvT : v ∈ Stopped.stubTarget c i sigma r t (17 * r) :=
    targetAnchor_mem_stubTarget hsigma
  have hvO : v ∈ Obox Sc cc 0 := by
    exact targetAnchor_mem_tailO C hsigma hr hj hm hfar hclear hwidth htrans
  refine ⟨allOpen, hcand, ?_⟩
  rw [TargetExt.toTarget, mem_connWithinSet_iff]
  refine ⟨v, Finset.mem_coe.2 hvT, ?_⟩
  exact connWithin_rbox_of_allOpen (by intro _ _; trivial)
    (dist1 (relayChoice (cube Sc cc 0 x)
      (tailSourcePatch C c i sigma r t s j m x) (face Sc cc 0 x) allOpen) v)
    _ v hchoiceO hvO le_rfl

/-! ## The constructed family and all seven clauses -/

/-- Totalize the finite family by reusing level zero outside its used range. -/
def clipLevel (C : LeftImp2.Certificate2 d) (m : ℕ) : ℕ :=
  if m < C.levels then m else 0

theorem clipLevel_lt (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) (m : ℕ) :
    clipLevel C m < C.levels := by
  unfold clipLevel
  split_ifs with hm
  · exact hm
  · exact hwf.levels_pos

@[simp] theorem clipLevel_eq (C : LeftImp2.Certificate2 d) {m : ℕ} (hm : m < C.levels) :
    clipLevel C m = m := by simp [clipLevel, hm]

set_option maxHeartbeats 2000000 in
/-- At one stopped level, the displayed `lv` is the longitudinal tail family.  The six
deterministic clauses are proved from the listed scale-clearance inequalities and freshness of the
pending outgoing corridor.  The seventh clause is exactly `PostWindowBound`. -/
theorem exists_postEntryFamily_at_level
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q q0 : unitInterval} {delta : ℝ}
    {r t s K n j : ℕ} {h : MacroExp.Tr d} {y : Site 2} {i : Fin d} {sigma : ℤ}
    {omega0 omega : SiteConfig (Site d)}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t) (hj : j < K)
    (hg : MacroExp.Good d r t h q0 delta)
    (hwspec : MacroExp.pendW d n h ∈ h.openV ∧
      (zdGraph 2).Adj (MacroExp.pendW d n h) (MacroExp.pendZ d n h))
    (hy : y ∈ MacroExp.pending d (MacroExp.accepted d r t n h omega0)
      (MacroExp.pendZ d n h))
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - MacroExp.pendZ d n h) : Site d) = Pi.single i sigma)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : PostWindowBound C q
      (MacroExp.ctr d r (MacroExp.pendZ d n h)) i sigma r t s j
      ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
        MacroExp.E d r t (MacroExp.pendZ d n h) y)
      (↑(Stopped.stubTarget (MacroExp.ctr d r (MacroExp.pendZ d n h))
        i sigma r t (17 * r)) : Set (Site d))) :
    ∃ lv : ℕ → TargetExt.LevelGeometry (zdGraph d)
      ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
        (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
          MacroExp.E d r t (MacroExp.pendZ d n h) y)
      (MacroExp.emb 0)
      (↑(Stopped.stubTarget (MacroExp.ctr d r (MacroExp.pendZ d n h))
        i sigma r t (17 * r)) : Set (Site d)),
      (∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D) ∧
      (∀ m, m + 1 < C.levels →
        ∀ x ∈ ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
            MacroExp.E d r t (MacroExp.pendZ d n h) y),
        x ∉ (lv m).D → ∀ v ∈ (lv m).D,
        (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D) ∧
      (∀ m < C.levels,
        (↑(Stopped.stubFace (MacroExp.ctr d r (MacroExp.pendZ d n h)) i sigma r t
          (10 * s * (j + 1))) : Set (Site d)) ⊆ ↑(lv m).D) ∧
      (∀ m < C.levels, Disjoint (lv m).D
        (Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) i sigma j omega).inspected) ∧
      (∀ m < C.levels, ∀ L ⊆ TargetExt.outerBoundary (zdGraph d)
        ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
            MacroExp.E d r t (MacroExp.pendZ d n h) y)
        (lv m).D, C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card) ∧
      (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
        ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
            MacroExp.E d r t (MacroExp.pendZ d n h) y)
        (lv m).D, ((lv m).J x).card ≤ C.seedSize) ∧
      (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
        ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
            MacroExp.E d r t (MacroExp.pendZ d n h) y)
        (lv m).D, 1 - 3 * C.delta ^ 2 ≤
          (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x)) := by
  let z := MacroExp.pendZ d n h
  let c := MacroExp.ctr d r z
  let Dom := (Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
    z i sigma j omega).inspected ∪ MacroExp.E d r t z y
  let T : Set (Site d) :=
    ↑(Stopped.stubTarget c i sigma r t (17 * r))
  have hiplanar : i.val < 2 := Stopped.dir_planar hsigma hemb
  have hclear0 : C.levels ≤ 10 * s := by omega
  have hwidth0 : C.levels ≤ 3 * r := by omega
  have hthin : (↑Dom : Set (Site d)) ⊆ MacroExp.thin d t := by
    exact accepted_levelDom_subset_thin hd hg omega0 hiplanar hsigma hrt j omega
  have hfitAll : ∀ m, Fits (tailScales C i r t s j (clipLevel C m)) 0 := by
    intro m
    exact tail_fits C hj (clipLevel_lt C hwf m) hlong hplanar htrans i
  have hsubAll : ∀ m, tailD C c i sigma r t s j (clipLevel C m) ⊆ Dom := by
    intro m x hx
    apply Finset.mem_union_right
    exact tailD_subset_E (t := t) hd C hsigma hemb hj (clipLevel_lt C hwf m)
      hwidth0 hlong hx
  have hfreshAll : ∀ m, Disjoint (tailD C c i sigma r t s j (clipLevel C m))
      (Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
        z i sigma j omega).inspected := by
    intro m
    exact tailD_fresh_levelTr hd C hr hg hwspec omega0 hy hsigma hemb hj
      (clipLevel_lt C hwf m) hwidth0 hlong omega
  have hoAll : ∀ m, MacroExp.emb 0 ∉ tailD C c i sigma r t s j (clipLevel C m) := by
    intro m hom
    exact Finset.disjoint_left.1 (hfreshAll m) hom
      (emb_zero_mem_accepted_levelTr hg omega0 i sigma z omega)
  let lv : ℕ → TargetExt.LevelGeometry (zdGraph d) Dom (MacroExp.emb 0) T := fun m =>
    tailLevel C c i sigma r t s j (clipLevel C m) Dom (MacroExp.emb 0) T
      (hfitAll m) (hsubAll m) (hoAll m)
  refine ⟨lv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    simpa only [lv, tailLevel_D, clipLevel_eq C hm, clipLevel_eq C hm0] using
      (tailD_succ_subset C c i sigma r t s j m)
  · intro m hm x hxDom hxout v hv hadj
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    have hxout' : x ∉ tailD C c i sigma r t s j m := by
      simpa only [lv, tailLevel_D, clipLevel_eq C hm0] using hxout
    have hv' : v ∈ tailD C c i sigma r t s j m := by
      simpa only [lv, tailLevel_D, clipLevel_eq C hm0] using hv
    have hout := tail_gate_rel (z := z) C hiplanar (sigma := sigma) (r := r) (s := s)
      (j := j) (m := m) (Dom := Dom) hthin x hxDom hxout' v hv' hadj
    simpa only [lv, tailLevel_D, clipLevel_eq C hm] using hout
  · intro m hm x hx
    rw [Finset.mem_coe] at hx ⊢
    simpa only [lv, tailLevel_D, clipLevel_eq C hm] using
      (stubFace_subset_tailD C hsigma hj hm hfar hrt hclear0 hwidth0 hlong hx)
  · intro m hm
    simpa only [lv, tailLevel_D, clipLevel_eq C hm] using hfreshAll m
  · intro m hm L hL hcard
    simp only [lv, tailLevel_sel, clipLevel_eq C hm]
    simp only [lv, tailLevel_D, clipLevel_eq C hm] at hL
    apply le_card_selC_of_subset_outerBoundary
      (tailScales C i r t s j m) (tailCentre c i sigma r s j) 0 Dom L
      (k := C.seedCount) (N := C.contacts)
    · simpa only [Dom, c, z, tailD] using hL
    · have heq : 4 * (1 + 2 * C.faceTarget) + 1 = 8 * C.faceTarget + 5 := by omega
      simpa only [tailScales, heq] using hwf.contacts_ge
    · exact hcard
  · intro m hm x hx
    simp only [lv, tailLevel_J, clipLevel_eq C hm]
    simp only [lv, tailLevel_D, clipLevel_eq C hm] at hx
    refine (MacroExp.card_seed_le (Sc := tailScales C i r t s j m) rfl
      (tail_fits C hj hm hlong hplanar htrans i) ?_).trans ?_
    · exact isContact_of_mem_outerBoundary _ _ _ Dom
        (by simpa only [Dom, c, z, tailD] using hx)
    · simpa only [tailScales] using hwf.seedSize_ge
  · intro m hm x hx
    simp only [lv, tailLevel_Gx, clipLevel_eq C hm]
    simp only [lv, tailLevel_D, clipLevel_eq C hm] at hx
    exact hwindow m hm x (by simpa only [z, c, Dom, T] using hx)

/-- The requested `hpost`, with the corrected domain-relative gate, for every stopped level and
every revealed pattern.  The witness returned by this theorem is definitionally the clipped
`tailLevel` family displayed in `exists_postEntryFamily_at_level`. -/
theorem hpost
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q q0 : unitInterval} {delta : ℝ}
    {r t s K n : ℕ} {h : MacroExp.Tr d} {y : Site 2} {i : Fin d} {sigma : ℤ}
    {omega0 : SiteConfig (Site d)}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hg : MacroExp.Good d r t h q0 delta)
    (hwspec : MacroExp.pendW d n h ∈ h.openV ∧
      (zdGraph 2).Adj (MacroExp.pendW d n h) (MacroExp.pendZ d n h))
    (hy : y ∈ MacroExp.pending d (MacroExp.accepted d r t n h omega0)
      (MacroExp.pendZ d n h))
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - MacroExp.pendZ d n h) : Site d) = Pi.single i sigma)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      PostWindowBound C q (MacroExp.ctr d r (MacroExp.pendZ d n h)) i sigma r t s j
        ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
            (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
          MacroExp.E d r t (MacroExp.pendZ d n h) y)
        (↑(Stopped.stubTarget (MacroExp.ctr d r (MacroExp.pendZ d n h))
          i sigma r t (17 * r)) : Set (Site d))) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      ∃ lv : ℕ → TargetExt.LevelGeometry (zdGraph d)
        ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
            MacroExp.E d r t (MacroExp.pendZ d n h) y)
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r (MacroExp.pendZ d n h))
          i sigma r t (17 * r)) : Set (Site d)),
        (∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D) ∧
        (∀ m, m + 1 < C.levels →
          ∀ x ∈ ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
            (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
              MacroExp.E d r t (MacroExp.pendZ d n h) y),
          x ∉ (lv m).D → ∀ v ∈ (lv m).D,
          (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D) ∧
        (∀ m < C.levels,
          (↑(Stopped.stubFace (MacroExp.ctr d r (MacroExp.pendZ d n h)) i sigma r t
            (10 * s * (j + 1))) : Set (Site d)) ⊆ ↑(lv m).D) ∧
        (∀ m < C.levels, Disjoint (lv m).D
          (Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
            (MacroExp.pendZ d n h) i sigma j omega).inspected) ∧
        (∀ m < C.levels, ∀ L ⊆ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
            (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
              MacroExp.E d r t (MacroExp.pendZ d n h) y)
          (lv m).D, C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card) ∧
        (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
            (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
              MacroExp.E d r t (MacroExp.pendZ d n h) y)
          (lv m).D, ((lv m).J x).card ≤ C.seedSize) ∧
        (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
            (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
              MacroExp.E d r t (MacroExp.pendZ d n h) y)
          (lv m).D, 1 - 3 * C.delta ^ 2 ≤
            (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x)) := by
  intro j hj omega
  exact exists_postEntryFamily_at_level hwf hd hr hrt hj hg hwspec hy hsigma hemb
    hfar hclear hwidth hlong hplanar htrans (hwindow j hj omega)

/-- The explicit scale-clearance assumptions are arithmetically consistent; for example these
simultaneous choices satisfy all six of them.  Thus the remaining `PostWindowBound` is not hiding
a contradiction among geometric inequalities. -/
theorem exists_scale_clearance (C : LeftImp2.Certificate2 d) :
    ∃ r t s K : ℕ,
      0 < r ∧ 0 < K ∧
      10 * s * K ≤ 13 * r ∧
      2 * r ≤ t ∧
      C.levels + 1 ≤ 10 * s ∧
      C.levels + 1 ≤ 3 * r ∧
      5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r ∧
      C.faceTarget + 1 ≤ 2 * r ∧
      C.faceTarget + 1 ≤ t := by
  refine ⟨10 * (C.levels + C.faceTarget + 2), 20 * (C.levels + C.faceTarget + 2),
    C.levels + 1, 1, ?_⟩
  omega

/-- The loss in the missing window estimate uses exactly the certificate's manuscript tolerance
`delta = eps^2 / 96`. -/
theorem postWindow_loss_eq {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) :
    3 * C.delta ^ 2 = 3 * (C.eps ^ 2 / 96) ^ 2 := by
  rw [hwf.delta_eq]

/-!
## Regression audit

1. **No designated open site.** `postWindowEvent` asks for a nonempty finite set of crossing
   endpoints and `relayChoice` selects one after seeing the shell.  `tailWindow_nonempty` exhibits
   an all-open witness; no fixed unread site's state is imposed.  Thus neither the single-tip nor
   widened-tip refutation applies: the target in `toTarget` is the actual whole `stubTarget`, not a
   singleton and not the outward face of `Q z'`.
2. **No empty or unreachable target.** `stopped_targets_nonempty` uses
   `Stopped.stubFace_nonempty` and `targetAnchor_mem_stubTarget`; its second conjunct proves that
   the concrete target anchor at signed depth `18*r` also lies in every used `tailO`.  The two
   one-site clearance margins in `hclear` and `hwidth` are essential for this statement.
3. **No stale conditional estimate.** `PostWindowBound` is an unconditional product-measure
   bound.  `tailD_fresh_levelTr` proves freshness against the actual `levelTr` transcript, after
   the reveal whose fresh queried set is certified by `Stopped.revealSet_fresh`.  No probability
   estimate is transported across an overlapping read.
4. **No hidden inconsistent geometry.** `exists_scale_clearance` gives simultaneous witnesses,
   and `tailWindow_nonempty` proves that each event itself is nonempty.  What remains genuinely
   absent is the quantitative finite-cylinder estimate `PostWindowBound`; it is not implied by the
   current `Certificate2.moveWindowBounds`, whose experiments are the distinct corridor-move
   windows.
-/

#print axioms KNAll.Site.PostFam.tailWindow_nonempty
#print axioms KNAll.Site.PostFam.exists_postEntryFamily_at_level
#print axioms KNAll.Site.PostFam.hpost

end KNAll.Site.PostFam

end
