import Hypergraph.CorePostSupported
import Hypergraph.MoveWindowInput
import Hypergraph.ShellWindowBuild
import Hypergraph.SiteLocalFromUniqueness
import Percolation.Literature.SharpnessDCTProofs

/-!
# Concrete translated target-aware lattice windows

This module turns the two genuine supercritical site inputs into the three finite factors used by
`TargetAware.window`.  The target factor is only an oriented face orthant of a larger cube.  It is
therefore the base input for the later finite quarter-face cascade, not an assumed long-box or
post-entry estimate.

The construction is uniform under translations.  Every event has an explicit finite support and
the all-open configuration is exhibited as a witness.  No pinned-site or hyperedge gluing
inequality is used.
-/

noncomputable section

namespace KNAll.Site.TargetAwareLattice

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.MoveWindowInput

variable {d : Nat} [NeZero d]
variable {p : unitInterval} {chi : Real}

/-! ## Boundary and coalescence adapters -/

/-- The concrete finite sphere is contained in the inner vertex boundary of the cube. -/
theorem boxSphereFin_subset_innerBoundary (n : Nat) :
    LeftImp2.boxSphereFin d n ⊆ innerBoundary (zdGraph d) (box d n) := by
  intro x hx
  rw [LeftImp2.boxSphereFin, Finset.mem_filter] at hx
  obtain ⟨hxbox, i, hi⟩ := hx
  apply DCT16.mem_innerBoundary_box_of_natAbs_eq hxbox (i := i)
  rcases hi with hi | hi <;> rw [hi] <;> simp

/-- Every oriented face orthant is part of the inner boundary of its cube. -/
theorem orthantFace_subset_innerBoundary (a : Fin d) (tau : Fin d → Intˣ) (n : Nat) :
    orthantFace a tau n ⊆ innerBoundary (zdGraph d) (box d n) :=
  (LeftImp2.orthantFace_subset_boxSphereFin a tau n).trans
    (boxSphereFin_subset_innerBoundary n)

/-- A face-orthant hit is one of the finite hits used by `TargetAware.window`. -/
theorem orthantHit_subset_finiteHit (m n : Nat) (aTau : FaceIndex d) :
    orthantHit m n aTau ⊆
      TargetAware.finiteHit (zdGraph d) (box d n) (box d m)
        (orthantFace aTau.1 aTau.2 n) := by
  intro omega homega
  exact homega

/-- Local coalescence at the intermediate arm radius implies the boundary-based coalescence
factor of a larger target-aware cube.  The important point is that the connection furnished by
the local input stays in `box d N0`, hence also in the larger cube `box d N`. -/
theorem finiteCoalescenceGood_of_shellCoalescenceGood
    {m M N0 N : Nat} (hmM : m ≤ M) (hMN0 : M ≤ N0) (hN0N : N0 ≤ N) (hMN : M < N) :
    shellCoalescenceGood (d := d) m M N0 ⊆
      TargetAware.finiteCoalescenceGood (zdGraph d) (box d m) (box d N) := by
  intro omega hgood
  intro hbad
  obtain ⟨x, hx, hbad⟩ := Set.mem_iUnion₂.1 hbad
  obtain ⟨y, hy, hfailure⟩ := Set.mem_iUnion₂.1 hbad
  have hxmem : x ∈ box d m := Finset.mem_coe.1 hx
  have hymem : y ∈ box d m := Finset.mem_coe.1 hy
  obtain ⟨bx, hbx, hxbx⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑(box d N) : Set (Site d)) x
      (↑(innerBoundary (zdGraph d) (box d N)) : Set (Site d)) omega).1 hfailure.1.1
  obtain ⟨bY, hbY, hybY⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑(box d N) : Set (Site d)) y
      (↑(innerBoundary (zdGraph d) (box d N)) : Set (Site d)) omega).1 hfailure.1.2
  have hbxout : bx ∉ box d M :=
    DCT16.notMem_box_of_mem_innerBoundary_box hMN (Finset.mem_coe.1 hbx)
  have hbYout : bY ∉ box d M :=
    DCT16.notMem_box_of_mem_innerBoundary_box hMN (Finset.mem_coe.1 hbY)
  have hxarm := connWithinSet_boxSphere_of_connWithin hmM hMN0 hxmem hbxout hxbx
  have hyarm := connWithinSet_boxSphere_of_connWithin hmM hMN0 hymem hbYout hybY
  have hnconn : omega ∉ connWithin (zdGraph d) (↑(box d N0) : Set (Site d)) x y := by
    intro hxy
    exact hfailure.2
      (connWithin_mono_set (zdGraph d) (coe_box_mono d hN0N) x y hxy)
  exact hgood (Set.mem_iUnion₂.2 ⟨(x, y), Finset.mem_product.2 ⟨hxmem, hymem⟩,
    ⟨⟨hxarm, hyarm⟩, hnconn⟩⟩)

/-- The intrinsic coalescence input supplies the exact target-aware coalescence factor, with an
arbitrarily prescribed strict loss. -/
theorem exists_finiteCoalescenceGood_lt_prob
    (p : unitInterval) (H : SiteIntrinsicInputs d p) (m : Nat) {chi : Real} (hchi : 0 < chi) :
    ∃ M > m, ∃ N0 ≥ M, ∀ N, N0 + 1 ≤ N →
      1 - chi < (siteBernoulli (fun _ : Site d => p)).real
        (TargetAware.finiteCoalescenceGood (zdGraph d) (box d m) (box d N)) := by
  let cardSq : Real := (((((2 * m + 1) ^ d) ^ 2 : Nat) : Real))
  have hcard : 0 < cardSq := by dsimp [cardSq]; positivity
  obtain ⟨M, hmM, N0, hMN0, hpair⟩ := H.coalescence m (chi / (2 * cardSq)) (by positivity)
  refine ⟨M, hmM, N0, hMN0, fun N hN => ?_⟩
  have hpair' : ∀ x ∈ box d m, ∀ y ∈ box d m,
      (siteBernoulli (fun _ : Site d => p)).real (localCoalescenceEvent d M N0 x y) <
        chi / (((((2 * m + 1) ^ d) ^ 2 : Nat) : Real)) := by
    intro x hx y hy
    have h := hpair x hx y hy
    dsimp [cardSq] at h
    calc
      _ ≤ chi / (2 * (((((2 * m + 1) ^ d) ^ 2 : Nat) : Real))) := h
      _ = (chi / 2) / (((((2 * m + 1) ^ d) ^ 2 : Nat) : Real)) := by ring
      _ < chi / (((((2 * m + 1) ^ d) ^ 2 : Nat) : Real)) :=
        div_lt_div_of_pos_right (by linarith) hcard
  have hshell := one_sub_lt_prob_shellCoalescenceGood p m M N0 hchi hpair'
  have hN0N : N0 ≤ N := Nat.le_of_succ_le hN
  have hMN : M < N := lt_of_le_of_lt hMN0 (Nat.lt_of_succ_le hN)
  have hsub := finiteCoalescenceGood_of_shellCoalescenceGood
    (d := d) hmM.le hMN0 hN0N hMN
  exact hshell.trans_le (measureReal_mono hsub (measure_ne_top _ _))

/-! ## Simultaneous base scales -/

/-- Scales at which local uniqueness and every oriented finite face hit hold simultaneously. -/
structure BaseScales (p : unitInterval) (chi : Real) where
  source : Nat
  armRadius : Nat
  localRadius : Nat
  source_lt_arm : source < armRadius
  arm_lt_local : armRadius < localRadius
  coalescence :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (TargetAware.finiteCoalescenceGood (zdGraph d) (box d source) (box d localRadius))
  quarter : ∀ n, localRadius ≤ n → ∀ aTau : FaceIndex d,
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (TargetAware.finiteHit (zdGraph d) (box d n) (box d source)
        (orthantFace aTau.1 aTau.2 n))

/-- A supplied intrinsic local-uniqueness input and supercriticality give common base scales.
The former can be a transported `SiteLocalInputs`; the latter is used only for the oriented
quarter-face estimate. -/
theorem exists_baseScales_of_intrinsic
    (p : unitInterval) (H : SiteIntrinsicInputs d p) (htheta : 0 < thetaSite d p)
    {chi : Real} (hchi : 0 < chi) : Nonempty (BaseScales (d := d) p chi) := by
  obtain ⟨m, nFace, hmFace, hquarter⟩ :=
    exists_forall_lt_prob_orthantHit (d := d) p htheta hchi
  obtain ⟨M, hmM, N0, hMN0, hcoal⟩ :=
    exists_finiteCoalescenceGood_lt_prob (d := d) p H m hchi
  let N := max (N0 + 1) nFace
  have hN0N : N0 + 1 ≤ N := le_max_left _ _
  have hnFaceN : nFace ≤ N := le_max_right _ _
  refine ⟨{
    source := m
    armRadius := M
    localRadius := N
    source_lt_arm := hmM
    arm_lt_local := lt_of_le_of_lt hMN0 (lt_of_lt_of_le (Nat.lt_succ_self N0) hN0N)
    coalescence := hcoal N hN0N
    quarter := ?_ }⟩
  intro n hNn aTau
  have hhit := hquarter n (hnFaceN.trans hNn) aTau
  exact hhit.trans_le
    (measureReal_mono (orthantHit_subset_finiteHit m n aTau) (measure_ne_top _ _))

/-- `SiteLocalInputs` is enough for the local-uniqueness half of the construction. -/
theorem exists_baseScales_of_siteLocalInputs
    (p : unitInterval) (H : SiteLocalInputs d p) (htheta : 0 < thetaSite d p)
    {chi : Real} (hchi : 0 < chi) : Nonempty (BaseScales (d := d) p chi) :=
  exists_baseScales_of_intrinsic p (siteIntrinsicInputs_of_siteLocalInputs d p H) htheta hchi

/-- Supercriticality alone supplies both local inputs and hence the simultaneous base scales. -/
theorem exists_baseScales_of_thetaSite_pos
    (p : unitInterval) (htheta : 0 < thetaSite d p) {chi : Real} (hchi : 0 < chi) :
    Nonempty (BaseScales (d := d) p chi) :=
  exists_baseScales_of_siteLocalInputs p (siteLocalInputs_of_thetaSite_pos d p htheta)
    htheta hchi

/-! ## The normalized target-aware window -/

/-- A concrete point in every oriented face orthant. -/
def orthantPoint (a : Fin d) (tau : Fin d → Intˣ) (n : Nat) : Site d :=
  Pi.single a ((tau a : Int) * (n : Int))

theorem orthantPoint_mem (a : Fin d) (tau : Fin d → Intˣ) (n : Nat) :
    orthantPoint a tau n ∈ orthantFace a tau n := by
  rw [mem_orthantFace]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_box]
    intro j
    by_cases hja : j = a
    · subst j
      rcases Int.units_eq_one_or (tau a) with h | h <;> simp [orthantPoint, h]
    · simp [orthantPoint, Pi.single_eq_of_ne hja]
  · rcases Int.units_eq_one_or (tau a) with h | h <;> simp [orthantPoint, h]
  · intro j hja
    simp [orthantPoint, Pi.single_eq_of_ne hja]

/-- The literal normalized three-factor event. -/
def baseWindow (S : BaseScales (d := d) p chi) (n : Nat)
    (localFace targetFace : FaceIndex d) : Set (SiteConfig (Site d)) :=
  TargetAware.window (zdGraph d) (box d S.source) (box d S.localRadius) (box d n)
    (orthantFace localFace.1 localFace.2 S.localRadius)
    (orthantFace targetFace.1 targetFace.2 n)

/-- All properties of one normalized base window, including support ownership and the explicit
all-open witness. -/
structure BaseWindowFacts (S : BaseScales (d := d) p chi) (n : Nat)
    (localFace targetFace : FaceIndex d) : Prop where
  local_lt_target : S.localRadius < n
  determined : DeterminedBy (baseWindow S n localFace targetFace) (↑(box d n) : Set (Site d))
  relay : ∀ omega ∈ baseWindow S n localFace targetFace,
    TargetAware.canonicalRelay (zdGraph d) (box d S.source) (box d S.localRadius)
        (orthantFace localFace.1 localFace.2 S.localRadius) omega ∈
          orthantFace localFace.1 localFace.2 S.localRadius ∧
    TargetAware.canonicalRelay (zdGraph d) (box d S.source) (box d S.localRadius)
        (orthantFace localFace.1 localFace.2 S.localRadius) omega ∈ omega ∧
    ∀ omega' ∈ baseWindow S n localFace targetFace,
      omega' ∩ (↑(box d S.localRadius) : Set (Site d)) =
          omega ∩ ↑(box d S.localRadius) →
      omega' ∈ connWithinSet (zdGraph d) (↑(box d n) : Set (Site d))
        (TargetAware.canonicalRelay (zdGraph d) (box d S.source) (box d S.localRadius)
          (orthantFace localFace.1 localFace.2 S.localRadius) omega)
        (↑(orthantFace targetFace.1 targetFace.2 n) : Set (Site d))
  coalescence_bound :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (TargetAware.finiteCoalescenceGood (zdGraph d)
        (box d S.source) (box d S.localRadius))
  face_bound :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (TargetAware.finiteHit (zdGraph d) (box d S.localRadius) (box d S.source)
        (orthantFace localFace.1 localFace.2 S.localRadius))
  target_bound :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (TargetAware.finiteHit (zdGraph d) (box d n) (box d S.source)
        (orthantFace targetFace.1 targetFace.2 n))
  window_bound :
    1 - 3 * chi < (siteBernoulli (fun _ : Site d => p)).real
      (baseWindow S n localFace targetFace)
  allOpen_mem : (Set.univ : SiteConfig (Site d)) ∈ baseWindow S n localFace targetFace

theorem baseWindow_facts (S : BaseScales (d := d) p chi) (n : Nat)
    (hn : S.localRadius < n) (localFace targetFace : FaceIndex d) :
    BaseWindowFacts S n localFace targetFace := by
  have hsourceLocal : S.source ≤ S.localRadius :=
    S.source_lt_arm.le.trans S.arm_lt_local.le
  have hsourceTarget : S.source ≤ n := hsourceLocal.trans hn.le
  have htargetDisjoint :
      Disjoint (orthantFace targetFace.1 targetFace.2 n) (box d S.localRadius) := by
    rw [Finset.disjoint_left]
    intro x hxTarget hxLocal
    exact DCT16.notMem_box_of_mem_innerBoundary_box hn
      (orthantFace_subset_innerBoundary targetFace.1 targetFace.2 n hxTarget) hxLocal
  have hrelay := TargetAware.canonicalRelay_toTarget (zdGraph d)
    (box_mono d hsourceLocal)
    (orthantFace_subset_innerBoundary localFace.1 localFace.2 S.localRadius)
    htargetDisjoint (box_mono d hn.le) Finset.Subset.rfl
  have hface := S.quarter S.localRadius le_rfl localFace
  have htarget := S.quarter n hn.le targetFace
  have hwindow := TargetAware.one_sub_three_mul_lt_prob_window (zdGraph d)
    (fun _ : Site d => p) (box d S.source) (box d S.localRadius) (box d n)
    (orthantFace localFace.1 localFace.2 S.localRadius)
    (orthantFace targetFace.1 targetFace.2 n) S.coalescence hface htarget
  have hzeroSource : (0 : Site d) ∈ box d S.source := by rw [mem_box]; simp
  have hlocalPoint := orthantPoint_mem localFace.1 localFace.2 S.localRadius
  have htargetPoint := orthantPoint_mem targetFace.1 targetFace.2 n
  have hall : (Set.univ : SiteConfig (Site d)) ∈ baseWindow S n localFace targetFace := by
    apply TargetAware.univ_mem_window (zdGraph d)
    · intro a ha a' ha'
      exact ShellBuild.connWithin_box_of_allOpen (by simp) (box_mono d hsourceLocal ha)
        (box_mono d hsourceLocal ha')
    · exact ⟨0, hzeroSource, orthantPoint localFace.1 localFace.2 S.localRadius,
        hlocalPoint, ShellBuild.connWithin_box_of_allOpen (by simp)
          (box_mono d hsourceLocal hzeroSource)
          (mem_orthantFace.1 hlocalPoint).1⟩
    · exact ⟨0, hzeroSource, orthantPoint targetFace.1 targetFace.2 n,
        htargetPoint, ShellBuild.connWithin_box_of_allOpen (by simp)
          (box_mono d hsourceTarget hzeroSource)
          (mem_orthantFace.1 htargetPoint).1⟩
  refine {
    local_lt_target := hn
    determined := TargetAware.determinedBy_window (zdGraph d) (box_mono d hn.le) Finset.Subset.rfl
    relay := hrelay
    coalescence_bound := S.coalescence
    face_bound := hface
    target_bound := htarget
    window_bound := hwindow
    allOpen_mem := hall }

/-! ## Translation and owned support -/

def shiftedSource (S : BaseScales (d := d) p chi) (v : Site d) : Finset (Site d) :=
  shiftFinset v (box d S.source)

def shiftedLocalBox (S : BaseScales (d := d) p chi) (v : Site d) : Finset (Site d) :=
  shiftFinset v (box d S.localRadius)

def shiftedOwner (n : Nat) (v : Site d) : Finset (Site d) :=
  shiftFinset v (box d n)

def shiftedFace (S : BaseScales (d := d) p chi) (v : Site d)
    (aTau : FaceIndex d) : Finset (Site d) :=
  shiftFinset v (orthantFace aTau.1 aTau.2 S.localRadius)

def shiftedTarget (n : Nat) (v : Site d) (aTau : FaceIndex d) : Finset (Site d) :=
  shiftFinset v (orthantFace aTau.1 aTau.2 n)

/-- The three translated factors are kept as named events, so their provenance is visible to an
audit and to later adapters. -/
def shiftedCoalescence (S : BaseScales (d := d) p chi) (v : Site d) :
    Set (SiteConfig (Site d)) :=
  siteShift v ⁻¹' TargetAware.finiteCoalescenceGood (zdGraph d)
    (box d S.source) (box d S.localRadius)

def shiftedFaceHit (S : BaseScales (d := d) p chi) (v : Site d)
    (aTau : FaceIndex d) : Set (SiteConfig (Site d)) :=
  siteShift v ⁻¹' TargetAware.finiteHit (zdGraph d) (box d S.localRadius)
    (box d S.source) (orthantFace aTau.1 aTau.2 S.localRadius)

def shiftedTargetHit (S : BaseScales (d := d) p chi) (n : Nat) (v : Site d)
    (aTau : FaceIndex d) : Set (SiteConfig (Site d)) :=
  siteShift v ⁻¹' TargetAware.finiteHit (zdGraph d) (box d n)
    (box d S.source) (orthantFace aTau.1 aTau.2 n)

def shiftedBaseWindow (S : BaseScales (d := d) p chi) (n : Nat) (v : Site d)
    (localFace targetFace : FaceIndex d) : Set (SiteConfig (Site d)) :=
  siteShift v ⁻¹' baseWindow S n localFace targetFace

theorem shiftedBaseWindow_eq_inter (S : BaseScales (d := d) p chi) (n : Nat)
    (v : Site d) (localFace targetFace : FaceIndex d) :
    shiftedBaseWindow S n v localFace targetFace =
      (shiftedCoalescence S v ∩ shiftedFaceHit S v localFace) ∩
        shiftedTargetHit S n v targetFace := by
  rfl

theorem prob_shift_preimage (p : unitInterval) (v : Site d)
    {A : Set (SiteConfig (Site d))} (hA : MeasurableSet A) :
    (siteBernoulli (fun _ : Site d => p)).real (siteShift v ⁻¹' A) =
      (siteBernoulli (fun _ : Site d => p)).real A := by
  have h := (measurePreserving_siteShift p v).measure_preimage hA.nullMeasurableSet
  rw [measureReal_def, measureReal_def, h]

theorem prob_shiftedCoalescence (S : BaseScales (d := d) p chi) (v : Site d) :
    (siteBernoulli (fun _ : Site d => p)).real (shiftedCoalescence S v) =
      (siteBernoulli (fun _ : Site d => p)).real
        (TargetAware.finiteCoalescenceGood (zdGraph d)
          (box d S.source) (box d S.localRadius)) := by
  exact prob_shift_preimage p v
    (TargetAware.measurableSet_finiteCoalescenceGood (zdGraph d)
      (box d S.source) (box d S.localRadius))

theorem prob_shiftedFaceHit (S : BaseScales (d := d) p chi) (v : Site d)
    (aTau : FaceIndex d) :
    (siteBernoulli (fun _ : Site d => p)).real (shiftedFaceHit S v aTau) =
      (siteBernoulli (fun _ : Site d => p)).real
        (TargetAware.finiteHit (zdGraph d) (box d S.localRadius) (box d S.source)
          (orthantFace aTau.1 aTau.2 S.localRadius)) := by
  exact prob_shift_preimage p v
    (TargetAware.measurableSet_finiteHit (zdGraph d) (box d S.localRadius)
      (box d S.source) (orthantFace aTau.1 aTau.2 S.localRadius))

theorem prob_shiftedTargetHit (S : BaseScales (d := d) p chi) (n : Nat) (v : Site d)
    (aTau : FaceIndex d) :
    (siteBernoulli (fun _ : Site d => p)).real (shiftedTargetHit S n v aTau) =
      (siteBernoulli (fun _ : Site d => p)).real
        (TargetAware.finiteHit (zdGraph d) (box d n) (box d S.source)
          (orthantFace aTau.1 aTau.2 n)) := by
  exact prob_shift_preimage p v
    (TargetAware.measurableSet_finiteHit (zdGraph d) (box d n)
      (box d S.source) (orthantFace aTau.1 aTau.2 n))

/-- The translated window has exactly one declared owner, namely the translated outer cube. -/
structure ShiftedWindowFacts (S : BaseScales (d := d) p chi) (n : Nat) (v : Site d)
    (localFace targetFace : FaceIndex d) : Prop where
  local_lt_target : S.localRadius < n
  local_subset_owner : shiftedLocalBox S v ⊆ shiftedOwner n v
  source_subset_local : shiftedSource S v ⊆ shiftedLocalBox S v
  face_subset_local : shiftedFace S v localFace ⊆ shiftedLocalBox S v
  target_subset_owner : shiftedTarget n v targetFace ⊆ shiftedOwner n v
  determined : DeterminedBy (shiftedBaseWindow S n v localFace targetFace)
    (↑(shiftedOwner n v) : Set (Site d))
  relay : ∀ omega ∈ shiftedBaseWindow S n v localFace targetFace,
    ∃ u ∈ shiftedFace S v localFace, u ∈ omega ∧
      ∀ omega' ∈ shiftedBaseWindow S n v localFace targetFace,
        omega' ∩ (↑(shiftedLocalBox S v) : Set (Site d)) =
            omega ∩ ↑(shiftedLocalBox S v) →
        omega' ∈ connWithinSet (zdGraph d) (↑(shiftedOwner n v) : Set (Site d)) u
          (↑(shiftedTarget n v targetFace) : Set (Site d))
  coalescence_bound :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real (shiftedCoalescence S v)
  face_bound :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (shiftedFaceHit S v localFace)
  target_bound :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (shiftedTargetHit S n v targetFace)
  window_bound :
    1 - 3 * chi < (siteBernoulli (fun _ : Site d => p)).real
      (shiftedBaseWindow S n v localFace targetFace)
  allOpen_mem : (Set.univ : SiteConfig (Site d)) ∈
    shiftedBaseWindow S n v localFace targetFace

theorem shiftedBaseWindow_relay (S : BaseScales (d := d) p chi) (n : Nat)
    (hn : S.localRadius < n) (v : Site d) (localFace targetFace : FaceIndex d) :
    ∀ omega ∈ shiftedBaseWindow S n v localFace targetFace,
      ∃ u ∈ shiftedFace S v localFace, u ∈ omega ∧
        ∀ omega' ∈ shiftedBaseWindow S n v localFace targetFace,
          omega' ∩ (↑(shiftedLocalBox S v) : Set (Site d)) =
              omega ∩ ↑(shiftedLocalBox S v) →
          omega' ∈ connWithinSet (zdGraph d) (↑(shiftedOwner n v) : Set (Site d)) u
            (↑(shiftedTarget n v targetFace) : Set (Site d)) := by
  intro omega homega
  let F := baseWindow_facts S n hn localFace targetFace
  let u := TargetAware.canonicalRelay (zdGraph d) (box d S.source) (box d S.localRadius)
    (orthantFace localFace.1 localFace.2 S.localRadius) (siteShift v omega)
  obtain ⟨huFace, huOpen, hrelay⟩ := F.relay (siteShift v omega) homega
  refine ⟨u + v, ?_, huOpen, ?_⟩
  · exact Finset.mem_image.2 ⟨u, huFace, rfl⟩
  · intro omega' homega' hagree
    have hagree0 :
        siteShift v omega' ∩ (↑(box d S.localRadius) : Set (Site d)) =
          siteShift v omega ∩ ↑(box d S.localRadius) := by
      ext z
      by_cases hz : z ∈ box d S.localRadius
      · have hzShift : z + v ∈ shiftedLocalBox S v :=
          Finset.mem_image.2 ⟨z, hz, rfl⟩
        have heq := Set.ext_iff.1 hagree (z + v)
        simpa only [Set.mem_inter_iff, mem_siteShift, Finset.mem_coe, hz, hzShift,
          and_true] using heq
      · simp only [Set.mem_inter_iff, mem_siteShift, Finset.mem_coe, hz, and_false]
    have hnorm := hrelay (siteShift v omega') homega' hagree0
    have hshift := (mem_connWithinSet_shift_iff v omega'
      (↑(box d n) : Set (Site d)) u
      (↑(orthantFace targetFace.1 targetFace.2 n) : Set (Site d))).1 hnorm
    simpa only [shiftedOwner, shiftedTarget, coe_shiftFinset] using hshift

theorem shiftedBaseWindow_facts (S : BaseScales (d := d) p chi) (n : Nat)
    (hn : S.localRadius < n) (v : Site d) (localFace targetFace : FaceIndex d) :
    ShiftedWindowFacts S n v localFace targetFace := by
  let F := baseWindow_facts S n hn localFace targetFace
  refine {
    local_lt_target := hn
    local_subset_owner := ?_
    source_subset_local := ?_
    face_subset_local := ?_
    target_subset_owner := ?_
    determined := ?_
    relay := shiftedBaseWindow_relay S n hn v localFace targetFace
    coalescence_bound := ?_
    face_bound := ?_
    target_bound := ?_
    window_bound := ?_
    allOpen_mem := ?_ }
  · exact Finset.image_subset_image (box_mono d hn.le)
  · exact Finset.image_subset_image
      (box_mono d (S.source_lt_arm.le.trans S.arm_lt_local.le))
  · exact Finset.image_subset_image fun x hx => (mem_orthantFace.1 hx).1
  · exact Finset.image_subset_image fun x hx => (mem_orthantFace.1 hx).1
  · have hdet := LeftImp2.determinedBy_siteShift_preimage v F.determined
    simpa only [shiftedBaseWindow, shiftedOwner, shiftFinset] using hdet
  · rw [prob_shiftedCoalescence]
    exact F.coalescence_bound
  · rw [prob_shiftedFaceHit]
    exact F.face_bound
  · rw [prob_shiftedTargetHit]
    exact F.target_bound
  · have hm : MeasurableSet (baseWindow S n localFace targetFace) :=
      TargetAware.measurableSet_window (zdGraph d) (box d S.source)
        (box d S.localRadius) (box d n)
        (orthantFace localFace.1 localFace.2 S.localRadius)
        (orthantFace targetFace.1 targetFace.2 n)
    rw [shiftedBaseWindow, prob_shift_preimage p v hm]
    exact F.window_bound
  · change siteShift v (Set.univ : SiteConfig (Site d)) ∈
      baseWindow S n localFace targetFace
    have hshift : siteShift v (Set.univ : SiteConfig (Site d)) = Set.univ := by
      ext x
      simp only [mem_siteShift, Set.mem_univ, iff_self]
    rw [hshift]
    exact F.allOpen_mem

/-! ## Adapter to the quarter faces used by `CorrMove.FaceTarget` -/

/-- Choose genuine sign units inside a `CorrMove.qface`.  At the distinguished coordinate the
choice is the asserted outward sign; in transverse coordinates it is the sign of `tau`. -/
def qfaceUnits (a : Fin d) (sigma : Int) (tau : Fin d → Int) : Fin d → Intˣ := fun j =>
  if j = a then (if sigma = 1 then 1 else -1)
  else if 0 ≤ tau j then 1 else -1

/-- A translated standard orthant is contained in every nonempty quarter face described by the
manuscript's integer sign data.  The statement allows zero transverse entries of `tau`; in that
case the quarter face is larger and either standard sign works. -/
theorem shifted_orthantFace_subset_qface (v : Site d) (n : Nat) (a : Fin d)
    (sigma : Int) (tau : Fin d → Int) (hsigma : sigma = 1 ∨ sigma = -1) :
    shiftFinset v (orthantFace a (qfaceUnits a sigma tau) n) ⊆
      CorrMove.qface v (n : Int) a sigma tau := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  rw [CorrMove.mem_qface]
  rw [mem_orthantFace] at hy
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have hj := (mem_box.1 hy.1) j
    simpa only [Pi.add_apply, add_sub_cancel_right] using (abs_le.2 hj)
  · have ha := hy.2.1
    rcases hsigma with rfl | rfl <;> simp [qfaceUnits] at ha ⊢ <;> assumption
  · intro j hja
    have hj := hy.2.2 j hja
    by_cases htau : 0 ≤ tau j
    · simp only [Pi.add_apply, add_sub_cancel_right]
      simp [qfaceUnits, hja, htau] at hj
      exact mul_nonneg htau hj
    · have htau' : tau j < 0 := lt_of_not_ge htau
      simp only [Pi.add_apply, add_sub_cancel_right]
      simp [qfaceUnits, hja, htau] at hj
      exact mul_nonneg_of_nonpos_of_nonpos htau'.le hj

/-- Translation of a centred natural-radius cube agrees with `CorrMove.cube`. -/
theorem shiftFinset_box_eq_cube (v : Site d) (n : Nat) :
    shiftFinset v (box d n) = CorrMove.cube v (n : Int) := by
  ext x
  rw [CorrMove.mem_cube]
  simp only [shiftFinset, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := mem_box.1 hy
    simpa only [Pi.add_apply, add_sub_cancel_right] using fun j => abs_le.2 (hy' j)
  · intro hx
    refine ⟨x - v, ?_, by simp⟩
    rw [mem_box]
    intro j
    have hj := hx j
    simpa only [Pi.sub_apply] using (abs_le.1 hj)

/-- Every translated target orthant furnished above lies in the corresponding concrete
`CorrMove.qface`. -/
theorem shiftedTarget_subset_qface (n : Nat) (v : Site d) (a : Fin d)
    (sigma : Int) (tau : Fin d → Int) (hsigma : sigma = 1 ∨ sigma = -1) :
    shiftedTarget n v (a, qfaceUnits a sigma tau) ⊆
      CorrMove.qface v (n : Int) a sigma tau :=
  shifted_orthantFace_subset_qface v n a sigma tau hsigma

/-! ## Finite oriented window certificates and common descent

The scale object above contains estimates at every larger radius because that is the convenient
supercritical statement.  A below-parameter certificate must not try to transport this infinite
family.  Instead it records the finitely many oriented calls that a fixed geometric construction
will actually make.  Each call below includes its strict scale inequality, so its declared support
is exactly the translated target cube.
-/

/-- One concrete translated and oriented window call. -/
structure WindowCall (S : BaseScales (d := d) p chi) where
  targetRadius : Nat
  centre : Site d
  localFace : FaceIndex d
  targetFace : FaceIndex d
  local_lt_target : S.localRadius < targetRadius

/-- The translated local-coalescence factor as its own finite experiment. -/
def coalescenceExperiment (S : BaseScales (d := d) p chi) (v : Site d) :
    CylinderExperiment d where
  support := shiftedLocalBox S v
  event := shiftedCoalescence S v
  determined := by
    have h := LeftImp2.determinedBy_siteShift_preimage v
      (TargetAware.determinedBy_finiteCoalescenceGood (zdGraph d)
        (box d S.source) (box d S.localRadius))
    simpa only [shiftedCoalescence, shiftedLocalBox, shiftFinset] using h
  measurable' := by
    exact (LeftImp2.determinedBy_siteShift_preimage v
      (TargetAware.determinedBy_finiteCoalescenceGood (zdGraph d)
        (box d S.source) (box d S.localRadius))).measurableSet_of_finset

/-- The translated local oriented-face factor as its own finite experiment. -/
def faceHitExperiment (S : BaseScales (d := d) p chi) (v : Site d)
    (aTau : FaceIndex d) : CylinderExperiment d where
  support := shiftedLocalBox S v
  event := shiftedFaceHit S v aTau
  determined := by
    have h := LeftImp2.determinedBy_siteShift_preimage v
      (TargetAware.determinedBy_finiteHit (zdGraph d) (box d S.localRadius)
        (box d S.source) (orthantFace aTau.1 aTau.2 S.localRadius))
    simpa only [shiftedFaceHit, shiftedLocalBox, shiftFinset] using h
  measurable' := by
    exact (LeftImp2.determinedBy_siteShift_preimage v
      (TargetAware.determinedBy_finiteHit (zdGraph d) (box d S.localRadius)
        (box d S.source) (orthantFace aTau.1 aTau.2 S.localRadius))).measurableSet_of_finset

/-- The translated oriented target-hit factor as its own finite experiment. -/
def targetHitExperiment (S : BaseScales (d := d) p chi) (n : Nat) (v : Site d)
    (aTau : FaceIndex d) : CylinderExperiment d where
  support := shiftedOwner n v
  event := shiftedTargetHit S n v aTau
  determined := by
    have h := LeftImp2.determinedBy_siteShift_preimage v
      (TargetAware.determinedBy_finiteHit (zdGraph d) (box d n)
        (box d S.source) (orthantFace aTau.1 aTau.2 n))
    simpa only [shiftedTargetHit, shiftedOwner, shiftFinset] using h
  measurable' := by
    exact (LeftImp2.determinedBy_siteShift_preimage v
      (TargetAware.determinedBy_finiteHit (zdGraph d) (box d n)
        (box d S.source) (orthantFace aTau.1 aTau.2 n))).measurableSet_of_finset

theorem coalescenceExperiment_lt_prob
    (S : BaseScales (d := d) p chi) (v : Site d) :
    1 - chi < (coalescenceExperiment S v).prob p := by
  change 1 - chi < (siteBernoulli (fun _ : Site d => p)).real (shiftedCoalescence S v)
  rw [prob_shiftedCoalescence]
  exact S.coalescence

theorem faceHitExperiment_lt_prob
    (S : BaseScales (d := d) p chi) (v : Site d) (aTau : FaceIndex d) :
    1 - chi < (faceHitExperiment S v aTau).prob p := by
  change 1 - chi < (siteBernoulli (fun _ : Site d => p)).real (shiftedFaceHit S v aTau)
  rw [prob_shiftedFaceHit]
  exact S.quarter S.localRadius le_rfl aTau

theorem targetHitExperiment_lt_prob
    (S : BaseScales (d := d) p chi) (c : WindowCall S) :
    1 - chi < (targetHitExperiment S c.targetRadius c.centre c.targetFace).prob p := by
  change 1 - chi < (siteBernoulli (fun _ : Site d => p)).real
    (shiftedTargetHit S c.targetRadius c.centre c.targetFace)
  rw [prob_shiftedTargetHit]
  exact S.quarter c.targetRadius c.local_lt_target.le c.targetFace

/-- The three analytically primitive factors for every selected call.  Keeping this list separate
from the assembled-window list means a descended certificate can populate the transparent
`CoreTargetAware.LevelWindow.hcoal/hface/htargetHit` fields. -/
def componentBounds (S : BaseScales (d := d) p chi) (calls : List (WindowCall S)) :
    List (CylinderExperiment d × Real) :=
  calls.flatMap fun c =>
    [(coalescenceExperiment S c.centre, 1 - chi),
      (faceHitExperiment S c.centre c.localFace, 1 - chi),
      (targetHitExperiment S c.targetRadius c.centre c.targetFace, 1 - chi)]

theorem componentBounds_valid_at_extraction
    (S : BaseScales (d := d) p chi) (calls : List (WindowCall S)) :
    ∀ b ∈ componentBounds S calls, b.2 < b.1.prob p := by
  intro b hb
  rw [componentBounds, List.mem_flatMap] at hb
  obtain ⟨c, hc, hb⟩ := hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with (rfl | rfl | rfl)
  · exact coalescenceExperiment_lt_prob S c.centre
  · exact faceHitExperiment_lt_prob S c.centre c.localFace
  · exact targetHitExperiment_lt_prob S c

/-- Read the three descended component bounds back at any selected call. -/
theorem componentBounds_at_call
    (S : BaseScales (d := d) p chi) (calls : List (WindowCall S))
    (q : unitInterval)
    (hvalid : ∀ b ∈ componentBounds S calls, b.2 < b.1.prob q)
    (c : WindowCall S) (hc : c ∈ calls) :
    1 - chi < (coalescenceExperiment S c.centre).prob q ∧
      1 - chi < (faceHitExperiment S c.centre c.localFace).prob q ∧
      1 - chi < (targetHitExperiment S c.targetRadius c.centre c.targetFace).prob q := by
  constructor
  · exact hvalid (coalescenceExperiment S c.centre, 1 - chi) (by
      rw [componentBounds, List.mem_flatMap]
      exact ⟨c, hc, by simp⟩)
  constructor
  · exact hvalid (faceHitExperiment S c.centre c.localFace, 1 - chi) (by
      rw [componentBounds, List.mem_flatMap]
      exact ⟨c, hc, by simp⟩)
  · exact hvalid
      (targetHitExperiment S c.targetRadius c.centre c.targetFace, 1 - chi) (by
        rw [componentBounds, List.mem_flatMap]
        exact ⟨c, hc, by simp⟩)

/-- The primitive component list, too, survives at one common smaller positive parameter. -/
theorem exists_lt_parameter_componentBounds
    (S : BaseScales (d := d) p chi) (calls : List (WindowCall S))
    (hp0 : 0 < (p : Real)) :
    ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p : Real) ∧
      ∀ b ∈ componentBounds S calls, b.2 < b.1.prob q := by
  obtain ⟨eps, heps, hstable⟩ := LeftImp.exists_valid_nhds_list
    (componentBounds S calls) (componentBounds_valid_at_extraction S calls)
  let t : Real := min (eps / 2) ((p : Real) / 2)
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have hteps : t < eps := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htp : t ≤ (p : Real) / 2 := min_le_right _ _
  have hq0 : 0 ≤ (p : Real) - t := by linarith
  have hq1 : (p : Real) - t ≤ 1 := by linarith [p.2.2]
  let q : unitInterval := ⟨(p : Real) - t, Set.mem_Icc.2 ⟨hq0, hq1⟩⟩
  refine ⟨q, ?_, ?_, hstable q ?_⟩
  · change 0 < (p : Real) - t
    linarith
  · change (p : Real) - t < (p : Real)
    linarith
  · change |((p : Real) - t) - (p : Real)| < eps
    rw [show ((p : Real) - t) - (p : Real) = -t by ring, abs_neg, abs_of_pos ht0]
    exact hteps

/-- The finite cylinder experiment belonging to one oriented window call. -/
def windowExperiment (S : BaseScales (d := d) p chi) (c : WindowCall S) :
    CylinderExperiment d where
  support := shiftedOwner c.targetRadius c.centre
  event := shiftedBaseWindow S c.targetRadius c.centre c.localFace c.targetFace
  determined :=
    (shiftedBaseWindow_facts S c.targetRadius c.local_lt_target c.centre
      c.localFace c.targetFace).determined
  measurable' :=
    (shiftedBaseWindow_facts S c.targetRadius c.local_lt_target c.centre
      c.localFace c.targetFace).determined.measurableSet_of_finset

@[simp] theorem windowExperiment_support
    (S : BaseScales (d := d) p chi) (c : WindowCall S) :
    (windowExperiment S c).support = shiftedOwner c.targetRadius c.centre := rfl

@[simp] theorem windowExperiment_event
    (S : BaseScales (d := d) p chi) (c : WindowCall S) :
    (windowExperiment S c).event =
      shiftedBaseWindow S c.targetRadius c.centre c.localFace c.targetFace := rfl

/-- Every recorded oriented experiment has the advertised strict bound at its extraction
parameter. -/
theorem windowExperiment_lt_prob
    (S : BaseScales (d := d) p chi) (c : WindowCall S) :
    1 - 3 * chi < (windowExperiment S c).prob p := by
  exact (shiftedBaseWindow_facts S c.targetRadius c.local_lt_target c.centre
    c.localFace c.targetFace).window_bound

/-- A finite list of the exact translated/oriented calls used downstream. -/
def windowBounds (S : BaseScales (d := d) p chi) (calls : List (WindowCall S)) :
    List (CylinderExperiment d × Real) :=
  calls.map fun c => (windowExperiment S c, 1 - 3 * chi)

/-- The whole finite list is valid at the extraction parameter. -/
theorem windowBounds_valid_at_extraction
    (S : BaseScales (d := d) p chi) (calls : List (WindowCall S)) :
    ∀ b ∈ windowBounds S calls, b.2 < b.1.prob p := by
  intro b hb
  rw [windowBounds] at hb
  obtain ⟨c, _, rfl⟩ := List.mem_map.1 hb
  exact windowExperiment_lt_prob S c

/-- One common neighbourhood transports every member of a finite translated/oriented family.
This is the finite-cylinder stability step missing from an outward-sphere-only certificate. -/
theorem exists_windowBounds_valid_nhds
    (S : BaseScales (d := d) p chi) (calls : List (WindowCall S)) :
    ∃ eps > 0, ∀ q : unitInterval, |(q : Real) - (p : Real)| < eps →
      ∀ b ∈ windowBounds S calls, b.2 < b.1.prob q :=
  LeftImp.exists_valid_nhds_list (windowBounds S calls)
    (windowBounds_valid_at_extraction S calls)

/-- A common strictly smaller positive parameter at which all finitely recorded oriented windows
remain valid.  Notice that this conclusion transports only the selected finite call list, not the
infinite `BaseScales.quarter` family. -/
theorem exists_lt_parameter_windowBounds
    (S : BaseScales (d := d) p chi) (calls : List (WindowCall S))
    (hp0 : 0 < (p : Real)) :
    ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p : Real) ∧
      ∀ b ∈ windowBounds S calls, b.2 < b.1.prob q := by
  obtain ⟨eps, heps, hstable⟩ := exists_windowBounds_valid_nhds S calls
  let t : Real := min (eps / 2) ((p : Real) / 2)
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have hteps : t < eps := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htp : t ≤ (p : Real) / 2 := min_le_right _ _
  have hq0 : 0 ≤ (p : Real) - t := by linarith
  have hq1 : (p : Real) - t ≤ 1 := by linarith [p.2.2]
  let q : unitInterval := ⟨(p : Real) - t, Set.mem_Icc.2 ⟨hq0, hq1⟩⟩
  refine ⟨q, ?_, ?_, hstable q ?_⟩
  · change 0 < (p : Real) - t
    linarith
  · change (p : Real) - t < (p : Real)
    linarith
  · change |((p : Real) - t) - (p : Real)| < eps
    rw [show ((p : Real) - t) - (p : Real) = -t by ring, abs_neg, abs_of_pos ht0]
    exact hteps

/-- The normalized finite list containing all ordered pairs of local and target orthants at one
chosen target radius.  Translation invariance lets later adapters reuse these bounds at any
centre, while retaining the orientation information lost by an outward-sphere event. -/
def normalizedOrientedCalls (S : BaseScales (d := d) p chi) (n : Nat)
    (hn : S.localRadius < n) : List (WindowCall S) :=
  (Finset.univ : Finset (FaceIndex d × FaceIndex d)).toList.map fun faces =>
    { targetRadius := n
      centre := 0
      localFace := faces.1
      targetFace := faces.2
      local_lt_target := hn }

def normalizedOrientedBounds (S : BaseScales (d := d) p chi) (n : Nat)
    (hn : S.localRadius < n) : List (CylinderExperiment d × Real) :=
  windowBounds S (normalizedOrientedCalls S n hn)

theorem normalizedOrientedBounds_valid_at_extraction
    (S : BaseScales (d := d) p chi) (n : Nat) (hn : S.localRadius < n) :
    ∀ b ∈ normalizedOrientedBounds S n hn, b.2 < b.1.prob p :=
  windowBounds_valid_at_extraction S (normalizedOrientedCalls S n hn)

/-- All normalized oriented windows at the chosen radius descend simultaneously to one strictly
smaller positive parameter. -/
theorem exists_lt_parameter_normalizedOrientedBounds
    (S : BaseScales (d := d) p chi) (n : Nat) (hn : S.localRadius < n)
    (hp0 : 0 < (p : Real)) :
    ∃ q : unitInterval, 0 < (q : Real) ∧ (q : Real) < (p : Real) ∧
      ∀ b ∈ normalizedOrientedBounds S n hn, b.2 < b.1.prob q :=
  exists_lt_parameter_windowBounds S (normalizedOrientedCalls S n hn) hp0

/-! ## Exact end-to-end existential form -/

/-- Supercriticality gives a translated three-factor Problem-A window at every centre, every
local orthant, and every strictly larger target scale/orientation.  This is the strongest base
family available before the finite 700-step quarter-face cascade. -/
theorem exists_shiftedWindowFamily_of_thetaSite_pos
    (p : unitInterval) (htheta : 0 < thetaSite d p) {chi : Real} (hchi : 0 < chi) :
    ∃ S : BaseScales (d := d) p chi,
      ∀ n, S.localRadius < n → ∀ v : Site d, ∀ localFace targetFace : FaceIndex d,
        ShiftedWindowFacts S n v localFace targetFace := by
  obtain ⟨S⟩ := exists_baseScales_of_thetaSite_pos (d := d) p htheta hchi
  exact ⟨S, fun n hn v localFace targetFace =>
    shiftedBaseWindow_facts S n hn v localFace targetFace⟩

#print axioms KNAll.Site.TargetAwareLattice.exists_finiteCoalescenceGood_lt_prob
#print axioms KNAll.Site.TargetAwareLattice.exists_baseScales_of_thetaSite_pos
#print axioms KNAll.Site.TargetAwareLattice.baseWindow_facts
#print axioms KNAll.Site.TargetAwareLattice.shiftedBaseWindow_facts
#print axioms KNAll.Site.TargetAwareLattice.exists_lt_parameter_componentBounds
#print axioms KNAll.Site.TargetAwareLattice.exists_lt_parameter_windowBounds
#print axioms KNAll.Site.TargetAwareLattice.exists_lt_parameter_normalizedOrientedBounds
#print axioms KNAll.Site.TargetAwareLattice.exists_shiftedWindowFamily_of_thetaSite_pos

end KNAll.Site.TargetAwareLattice

end
