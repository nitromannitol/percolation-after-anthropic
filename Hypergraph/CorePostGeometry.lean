import Hypergraph.PostEntryFamily
import Hypergraph.CoreReservation
import Hypergraph.InitialBridge

/-!
# Longitudinal target-extension geometry for core reservations

This file is deliberately deterministic.  It repackages the longitudinal tail boxes of
`PostEntryFamily` for the support-in-`D` interface `TargetExt.LevelGeometryD`, with target the
radius-`2r` core at the next macro vertex.  The only quantitative input is named
`CorePostWindowBound`; no probability estimate for that input is asserted here.

The all-open witness below shows that a window at a genuine relative outer-boundary contact is
nonempty.  Thus the named probability input is not made true by an empty event or an unreachable
target.
-/

noncomputable section

namespace KNAll.Site.CorePost

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor

variable {d : Nat} [NeZero d]

/-- The old tail level already has its window determined in `O` and its relay path in `O`.
Viewing `O` as a subset of `D` therefore gives the non-vacuous support-in-`D` geometry. -/
def tailLevelD (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d) (sigma : Int)
    (r t s j m : Nat) (Dom : Finset (Site d)) (o : Site d) (T : Set (Site d))
    (hfit : Fits (PostFam.tailScales C i r t s j m) 0)
    (hDDom : PostFam.tailD C c i sigma r t s j m ⊆ Dom)
    (hoDom : o ∈ Dom)
    (ho : o ∉ PostFam.tailD C c i sigma r t s j m) :
    TargetExt.LevelGeometryD (zdGraph d) Dom o T := by
  let lv := PostFam.tailLevel C c i sigma r t s j m Dom o T hfit hDDom ho
  exact
    { D := lv.D
      O := lv.O
      Int := lv.Int
      U := lv.U
      J := lv.J
      sel := lv.sel
      Gx := lv.Gx
      S := fun _ => lv.O
      hIntO := lv.hIntO
      hOD := lv.hOD
      hDDom := lv.hDDom
      hoDom := hoDom
      ho := lv.ho
      hU := lv.hU
      hJD := lv.hJD
      hJO := lv.hJO
      hW3 := lv.hW3
      hsel_sub := lv.hsel_sub
      hsel_disj := lv.hsel_disj
      hS := fun _ _ => lv.hOD
      hGdet := lv.hGdet
      hrelay := by
        intro x hx omega homega
        obtain ⟨u, hu, huopen, hrelay⟩ := lv.hrelay x hx omega homega
        refine ⟨u, hu, huopen, ?_⟩
        intro omega' homega' hagree
        exact connWithinSet_mono_set (zdGraph d) (Finset.coe_subset.2 lv.hOD) u T
          (hrelay omega' homega' hagree) }

@[simp] theorem tailLevelD_D (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : Int) (r t s j m : Nat) (Dom : Finset (Site d)) (o : Site d)
    (T : Set (Site d)) (hfit) (hDDom) (hoDom) (ho) :
    (tailLevelD C c i sigma r t s j m Dom o T hfit hDDom hoDom ho).D =
      PostFam.tailD C c i sigma r t s j m := rfl

@[simp] theorem tailLevelD_Gx (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : Int) (r t s j m : Nat) (Dom : Finset (Site d)) (o : Site d)
    (T : Set (Site d)) (hfit) (hDDom) (hoDom) (ho) (x : Site d) :
    (tailLevelD C c i sigma r t s j m Dom o T hfit hDDom hoDom ho).Gx x =
      PostFam.tailWindow C c i sigma r t s j m T x := rfl

@[simp] theorem tailLevelD_sel (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : Int) (r t s j m : Nat) (Dom : Finset (Site d)) (o : Site d)
    (T : Set (Site d)) (hfit) (hDDom) (hoDom) (ho) (L : Finset (Site d)) :
    (tailLevelD C c i sigma r t s j m Dom o T hfit hDDom hoDom ho).sel L =
      selC (PostFam.tailScales C i r t s j m) (PostFam.tailCentre c i sigma r s j) 0 L := rfl

@[simp] theorem tailLevelD_J (C : LeftImp2.Certificate2 d) (c : Site d) (i : Fin d)
    (sigma : Int) (r t s j m : Nat) (Dom : Finset (Site d)) (o : Site d)
    (T : Set (Site d)) (hfit) (hDDom) (hoDom) (ho) (x : Site d) :
    (tailLevelD C c i sigma r t s j m Dom o T hfit hDDom hoDom ho).J x =
      seed (PostFam.tailScales C i r t s j m) (PostFam.tailCentre c i sigma r s j) 0 x := rfl

/-- The depth-`18r` anchor is on the boundary of the radius-`2r` core centred at the next macro
vertex. -/
theorem targetAnchor_mem_coreTarget {r : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    PostFam.targetAnchor (MacroExp.ctr d r z) i sigma r ∈ CoreRes.target (d := d) r y := by
  rw [CoreRes.target, CorrMove.mem_cube]
  intro q
  have hctr := Stopped.ctr_sub_apply (d := d) r y z q
  rw [hemb] at hctr
  by_cases hqi : q = i
  · subst q
    rw [Pi.single_eq_same] at hctr
    have hdiff :
        PostFam.targetAnchor (MacroExp.ctr d r z) i sigma r i -
            MacroExp.ctr d r y i = -(2 * (r : Int)) * sigma := by
      simp only [PostFam.targetAnchor, Pi.add_apply, Pi.single_eq_same]
      push_cast
      linarith
    rw [hdiff]
    rcases hsigma with rfl | rfl <;> simp <;> omega
  · rw [Pi.single_eq_of_ne hqi] at hctr
    have hdiff :
        PostFam.targetAnchor (MacroExp.ctr d r z) i sigma r q -
            MacroExp.ctr d r y q = 0 := by
      simp only [PostFam.targetAnchor, Pi.add_apply, Pi.single_eq_of_ne hqi, add_zero]
      linarith
    rw [hdiff, abs_zero]
    positivity

/-- The exact missing finite-cylinder estimate for the core target.  It is intentionally a
definition, not a theorem: extraction must record and prove each one of these inequalities. -/
def CorePostWindowBound (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (c : Site d) (i : Fin d) (sigma : Int) (r t s j : Nat)
    (Dom : Finset (Site d)) (y : Site 2) : Prop :=
  ∀ m, m < C.levels → ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (PostFam.tailD C c i sigma r t s j m),
    1 - 3 * C.delta ^ 2 ≤
      (siteBernoulli (fun _ : Site d => q)).real
        (PostFam.tailWindow C c i sigma r t s j m
          (↑(CoreRes.target (d := d) r y) : Set (Site d)) x)

/-- A genuine-contact core window has an explicit all-open witness.  No designated relay is
fixed before the shell is observed. -/
theorem coreTailWindow_nonempty (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed)
    {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    {r t s K j m : Nat} (hr : 0 < r) (hj : j < K) (hm : m < C.levels)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    {Dom : Finset (Site d)} {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j m)) :
    (PostFam.tailWindow C (MacroExp.ctr d r z) i sigma r t s j m
      (↑(CoreRes.target (d := d) r y) : Set (Site d)) x).Nonempty := by
  classical
  let c := MacroExp.ctr d r z
  let Sc := PostFam.tailScales C i r t s j m
  let cc := PostFam.tailCentre c i sigma r s j
  let a := cubeCentre Sc cc 0 x
  let u := PostFam.localFaceAnchor Sc cc 0 x
  let v := PostFam.targetAnchor c i sigma r
  let allOpen : SiteConfig (Site d) := fun _ => True
  have hfit : Fits Sc 0 := PostFam.tail_fits C hj hm hlong hplanar htrans i
  have hcontact : IsContact cc (ρD Sc 0) x :=
    isContact_of_mem_outerBoundary Sc cc 0 Dom
      (by simpa only [Sc, cc, c, PostFam.tailD] using hx)
  have hu : u ∈ face Sc cc 0 x := PostFam.localFaceAnchor_mem_face hcontact
  have hua : u ∈ cube Sc cc 0 x := face_subset_cube x hu
  have ha : a ∈ cube Sc cc 0 x := by
    rw [cube, mem_rbox]
    intro q
    simp [a]
  have haSource : a ∈ PostFam.tailSourcePatch C c i sigma r t s j m x :=
    PostFam.cubeCentre_mem_sourcePatch C c i sigma r t s j m x
  have hconnAU : allOpen ∈
      connWithin (zdGraph d) (↑(cube Sc cc 0 x) : Set (Site d)) a u :=
    connWithin_rbox_of_allOpen (by intro _ _; trivial) (dist1 a u) a u ha hua le_rfl
  have hcand : (PostFam.relayCandidates (cube Sc cc 0 x)
      (PostFam.tailSourcePatch C c i sigma r t s j m x) (face Sc cc 0 x)
      allOpen).Nonempty := by
    refine ⟨u, ?_⟩
    rw [PostFam.relayCandidates, Finset.mem_filter]
    exact ⟨hu, trivial, a, haSource, hconnAU⟩
  have hchoice := PostFam.relayChoice_spec hcand
  have hchoiceO : PostFam.relayChoice (cube Sc cc 0 x)
      (PostFam.tailSourcePatch C c i sigma r t s j m x) (face Sc cc 0 x) allOpen ∈
        Obox Sc cc 0 :=
    Finset.sdiff_subset (face_subset_shell hfit hcontact hchoice.1)
  have hvT : v ∈ CoreRes.target (d := d) r y := by
    simpa only [v, c] using targetAnchor_mem_coreTarget (d := d) hsigma hemb
  have hvO : v ∈ Obox Sc cc 0 := by
    change v ∈ PostFam.tailO C c i sigma r t s j m
    simpa only [v, c] using
      PostFam.targetAnchor_mem_tailO C hsigma hr hj hm hfar hclear hwidth htrans
  refine ⟨allOpen, hcand, ?_⟩
  rw [TargetExt.toTarget, mem_connWithinSet_iff]
  refine ⟨v, Finset.mem_coe.2 hvT, ?_⟩
  exact connWithin_rbox_of_allOpen (by intro _ _; trivial)
    (dist1 (PostFam.relayChoice (cube Sc cc 0 x)
      (PostFam.tailSourcePatch C c i sigma r t s j m x) (face Sc cc 0 x) allOpen) v)
    _ v hchoiceO hvO le_rfl

/-- The next stopped face is a valid source set for every core-tail level. -/
theorem stoppedFace_subset_tailLevelD_D
    (C : LeftImp2.Certificate2 d) {c : Site d} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {r t s K j m : Nat}
    (hj : j < K) (hm : m < C.levels)
    (hfar : 10 * s * K ≤ 13 * r) (hrt : 2 * r ≤ t)
    (hclear : C.levels ≤ 10 * s)
    (hwidth : C.levels ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    {Dom : Finset (Site d)} {o : Site d} {T : Set (Site d)}
    (hfit) (hDDom) (hoDom) (ho) :
    Stopped.stubFace c i sigma r t (10 * s * (j + 1)) ⊆
      (tailLevelD C c i sigma r t s j m Dom o T hfit hDDom hoDom ho).D := by
  simpa only [tailLevelD_D] using
    PostFam.stubFace_subset_tailD C hsigma hj hm hfar hrt hclear hwidth hlong

/-! The initial broad box also fits in the same longitudinal family.  This is useful for turning
the already-proved initial long-box estimate into the first core reservation. -/

theorem initialInnerBox_subset_tailD
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb y : Site d) = Pi.single i sigma)
    {s m : Nat} (hm : m < C.levels) :
    LongBox.innerBox C (MacroExp.ctr d C.corridor y) ⊆
      PostFam.tailD C (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0 m := by
  intro x hx
  rw [← InitBridge.initialCorridorTarget_eq_innerBox C hwf y,
    LeftImp2.initialCorridorTarget, MacroExp.mem_abox] at hx
  apply PostFam.mem_tailD_of_bounds
  intro q
  have hctr := Stopped.ctr_sub_apply (d := d) C.corridor y 0 q
  simp only [sub_zero] at hctr
  rw [hemb] at hctr
  have hemb0 : (MacroExp.emb (y - 0) : Site d) = Pi.single i sigma := by
    simpa only [sub_zero] using hemb
  have hiplanar : i.val < 2 := Stopped.dir_planar hsigma hemb0
  by_cases hqi : q = i
  · subst q
    rw [Pi.single_eq_same] at hctr
    have hxq := hx i
    have hrad : MacroExp.rad
        (C.corridor - (C.levels + 2 * C.faceTarget + 1))
        (C.halfWidth - (C.levels + 2 * C.faceTarget + 1)) i =
        (C.corridor - (C.levels + 2 * C.faceTarget + 1) : Nat) := by
      unfold MacroExp.rad
      rw [if_pos hiplanar]
    rw [hrad] at hxq
    simp only [PostFam.tailCentre_apply_self, PostFam.tailRho, if_pos rfl]
    unfold PostFam.tailHalfLength
    have hA : C.levels + 2 * C.faceTarget + 1 ≤ C.corridor :=
      hwf.innerRadius_ge.trans (min_le_left _ _)
    have hmA : m + 1 ≤ C.levels + 2 * C.faceTarget + 1 := by omega
    have hr : 44 ≤ C.corridor := hwf.corridor_ge_44
    rcases hsigma with rfl | rfl <;> norm_num at hctr hxq ⊢ <;> push_cast at hxq ⊢ <;> omega
  · rw [Pi.single_eq_of_ne hqi] at hctr
    have hxq := hx q
    rw [PostFam.tailCentre_apply_of_ne hqi, PostFam.tailRho, if_neg hqi]
    by_cases hq2 : q.val < 2
    · rw [if_pos hq2]
      have hrad : MacroExp.rad
          (C.corridor - (C.levels + 2 * C.faceTarget + 1))
          (C.halfWidth - (C.levels + 2 * C.faceTarget + 1)) q =
          (C.corridor - (C.levels + 2 * C.faceTarget + 1) : Nat) := by
        unfold MacroExp.rad
        rw [if_pos hq2]
      rw [hrad] at hxq
      have hA : C.levels + 2 * C.faceTarget + 1 ≤ C.corridor :=
        hwf.innerRadius_ge.trans (min_le_left _ _)
      push_cast at hxq ⊢
      omega
    · rw [if_neg hq2]
      have hrad : MacroExp.rad
          (C.corridor - (C.levels + 2 * C.faceTarget + 1))
          (C.halfWidth - (C.levels + 2 * C.faceTarget + 1)) q =
          (C.halfWidth - (C.levels + 2 * C.faceTarget + 1) : Nat) := by
        unfold MacroExp.rad
        rw [if_neg hq2]
      rw [hrad] at hxq
      have hA : C.levels + 2 * C.faceTarget + 1 ≤ C.halfWidth :=
        hwf.innerRadius_ge.trans (min_le_right _ _)
      push_cast at hxq ⊢
      omega

/-- `initialInnerBox_subset_tailD` in the literal `LevelGeometryD.hB` shape. -/
theorem initialInnerBox_subset_tailLevelD_D
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed)
    {y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb y : Site d) = Pi.single i sigma)
    {s m : Nat} (hm : m < C.levels)
    {Dom : Finset (Site d)} {o : Site d} {T : Set (Site d)}
    (hfit) (hDDom) (hoDom) (ho) :
    LongBox.innerBox C (MacroExp.ctr d C.corridor y) ⊆
      (tailLevelD C (MacroExp.ctr d C.corridor 0) i sigma
        C.corridor C.halfWidth s 0 m Dom o T hfit hDDom hoDom ho).D := by
  simpa only [tailLevelD_D] using
    initialInnerBox_subset_tailD hwf hsigma hemb hm

#print axioms KNAll.Site.CorePost.tailLevelD
#print axioms KNAll.Site.CorePost.targetAnchor_mem_coreTarget
#print axioms KNAll.Site.CorePost.coreTailWindow_nonempty
#print axioms KNAll.Site.CorePost.stoppedFace_subset_tailLevelD_D
#print axioms KNAll.Site.CorePost.initialInnerBox_subset_tailD
#print axioms KNAll.Site.CorePost.initialInnerBox_subset_tailLevelD_D

end KNAll.Site.CorePost

end
