import Hypergraph.CorePostFamily
import Hypergraph.CorePerLevelNoGluing

/-!
# The concrete core post-entry family without pinned gluing

The target-aware `PostFam.tailWindow` has its support and relay path inside `tailO`.  This file
packages the same deterministic tail geometry directly as `TargetExt.LevelGeometry`, retaining
that stronger fact instead of weakening it to `LevelGeometryD`.  It then feeds the gluing-free
core contrapositive from `CorePerLevelNoGluing`.
-/

noncomputable section

namespace KNAll.Site.CorePostNoGluing

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor

variable {d : Nat} [NeZero d]

/-- The seven fields needed at one stopped level, using the shell-supported interface. -/
structure FamilyAt (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (sigma : Int)
    (j : Nat) (omega : SiteConfig (Site d)) where
  lv : Nat → TargetExt.LevelGeometry (zdGraph d)
    (CorePost.levelDom r t s h z y i sigma j omega) (MacroExp.emb 0)
    (↑(CoreRes.target (d := d) r y) : Set (Site d))
  nest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D
  gateRel : ∀ m, m + 1 < C.levels →
    ∀ x ∈ CorePost.levelDom r t s h z y i sigma j omega, x ∉ (lv m).D →
    ∀ v ∈ (lv m).D, (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D
  source : ∀ m < C.levels,
    (↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1))) :
      Set (Site d)) ⊆ ↑(lv m).D
  fresh : ∀ m < C.levels,
    Disjoint (lv m).D (Stopped.levelTr d r t s h z i sigma j omega).inspected
  select : ∀ m < C.levels, ∀ L ⊆ TargetExt.outerBoundary (zdGraph d)
    (CorePost.levelDom r t s h z y i sigma j omega) (lv m).D,
      C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card
  seed : ∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
    (CorePost.levelDom r t s h z y i sigma j omega) (lv m).D,
      ((lv m).J x).card ≤ C.seedSize
  reliable : ∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
    (CorePost.levelDom r t s h z y i sigma j omega) (lv m).D,
      1 - 3 * C.delta ^ 2 ≤
        (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x)

/-- The concrete longitudinal family.  Every deterministic field is discharged; the only
analytic premise is the explicitly named finite-cylinder bound. -/
noncomputable def familyAt_of_corePostWindowBound
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    {j : Nat} {omega : SiteConfig (Site d)}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t) (hj : j < K)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hthin : (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh : Disjoint h.inspected (MacroExp.E d r t z y))
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : CorePost.CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
      (CorePost.levelDom r t s h z y i sigma j omega) y) :
    FamilyAt C q r t s h z y i sigma j omega := by
  let Dom := CorePost.levelDom r t s h z y i sigma j omega
  let T : Set (Site d) := ↑(CoreRes.target (d := d) r y)
  have hiplanar : i.val < 2 := Stopped.dir_planar hsigma hemb
  have hthinDom : (↑Dom : Set (Site d)) ⊆ MacroExp.thin d t := by
    intro x hx
    simp only [Finset.mem_coe, Dom, CorePost.levelDom, Finset.mem_union,
      Stopped.levelTr_inspected] at hx
    rcases hx with (hx | hx) | hx
    · exact hthin (Finset.mem_coe.2 hx)
    · exact PostFam.stub_subset_thin hd hiplanar hsigma hrt (Finset.mem_coe.2 hx)
    · exact MacroExp.E_subset_thin hd r t z y (Finset.mem_coe.2 hx)
  have hfitAll : ∀ m, Fits (PostFam.tailScales C i r t s j (PostFam.clipLevel C m)) 0 := by
    intro m
    exact PostFam.tail_fits C hj (PostFam.clipLevel_lt C hwf m) hlong hplanar htrans i
  have hsubAll : ∀ m,
      PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j (PostFam.clipLevel C m) ⊆ Dom := by
    intro m x hx
    apply Finset.mem_union_right
    exact PostFam.tailD_subset_E (t := t) hd C hsigma hemb hj
      (PostFam.clipLevel_lt C hwf m) (by omega) hlong hx
  have hfreshAll : ∀ m,
      Disjoint
        (PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j
          (PostFam.clipLevel C m))
        (Stopped.levelTr d r t s h z i sigma j omega).inspected := by
    intro m
    have hDE :
        PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j
            (PostFam.clipLevel C m) ⊆ MacroExp.E d r t z y :=
      PostFam.tailD_subset_E (t := t) hd C hsigma hemb hj
        (PostFam.clipLevel_lt C hwf m) (by omega) hlong
    rw [Stopped.levelTr_inspected, Finset.disjoint_union_right]
    exact ⟨hfresh.symm.mono_left hDE,
      PostFam.tailD_disjoint_stub C hsigma hj (PostFam.clipLevel_lt C hwf m) hlong⟩
  have hoAll : ∀ m,
      (MacroExp.emb 0 : Site d) ∉
        PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j
          (PostFam.clipLevel C m) := by
    intro m hom
    exact Finset.disjoint_left.1 (hfreshAll m) hom
      (by
        rw [Stopped.levelTr_inspected]
        exact Finset.mem_union_left _ (h.openSites_subset horigin))
  let lv : Nat → TargetExt.LevelGeometry (zdGraph d) Dom (MacroExp.emb 0) T := fun m =>
    PostFam.tailLevel C (MacroExp.ctr d r z) i sigma r t s j (PostFam.clipLevel C m)
      Dom (MacroExp.emb 0) T (hfitAll m) (hsubAll m) (hoAll m)
  refine
    { lv := lv
      nest := ?_
      gateRel := ?_
      source := ?_
      fresh := ?_
      select := ?_
      seed := ?_
      reliable := ?_ }
  · intro m hm
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm,
      PostFam.clipLevel_eq C hm0] using
      (PostFam.tailD_succ_subset C (MacroExp.ctr d r z) i sigma r t s j m)
  · intro m hm x hxDom hxout v hv hadj
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    have hxout' : x ∉ PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j m := by
      simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm0] using hxout
    have hv' : v ∈ PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j m := by
      simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm0] using hv
    have hout := PostFam.tail_gate_rel (z := z) C hiplanar (sigma := sigma)
      (r := r) (s := s) (j := j) (m := m) (Dom := Dom) hthinDom
      x hxDom hxout' v hv' hadj
    simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] using hout
  · intro m hm x hx
    rw [Finset.mem_coe] at hx ⊢
    simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] using
      (PostFam.stubFace_subset_tailD C hsigma hj hm (by omega) hrt (by omega) (by omega)
        hlong hx)
  · intro m hm
    simpa only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] using hfreshAll m
  · intro m hm L hL hcard
    simp only [lv, PostFam.tailLevel_sel, PostFam.clipLevel_eq C hm]
    simp only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] at hL
    apply le_card_selC_of_subset_outerBoundary
      (PostFam.tailScales C i r t s j m)
      (PostFam.tailCentre (MacroExp.ctr d r z) i sigma r s j) 0 Dom L
      (k := C.seedCount) (N := C.contacts)
    · simpa only [PostFam.tailD] using hL
    · have heq : 4 * (1 + 2 * C.faceTarget) + 1 = 8 * C.faceTarget + 5 := by omega
      simpa only [PostFam.tailScales, heq] using hwf.contacts_ge
    · exact hcard
  · intro m hm x hx
    simp only [lv, PostFam.tailLevel_J, PostFam.clipLevel_eq C hm]
    simp only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] at hx
    refine (MacroExp.card_seed_le
      (Sc := PostFam.tailScales C i r t s j m) rfl
      (PostFam.tail_fits C hj hm hlong hplanar htrans i) ?_).trans ?_
    · exact isContact_of_mem_outerBoundary _ _ _ Dom
        (by simpa only [PostFam.tailD] using hx)
    · simpa only [PostFam.tailScales] using hwf.seedSize_ge
  · intro m hm x hx
    simp only [lv, PostFam.tailLevel_Gx, PostFam.clipLevel_eq C hm]
    simp only [lv, PostFam.tailLevel_D, PostFam.clipLevel_eq C hm] at hx
    exact hwindow m hm x (by simpa only [Dom, T] using hx)

/-- The all-level family in the exact existential shape expected by the gluing-free core
contrapositive. -/
theorem hpost_of_corePostWindowBound
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hthin : (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh : Disjoint h.inspected (MacroExp.E d r t z y))
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      CorePost.CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
        (CorePost.levelDom r t s h z y i sigma j omega) y) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      ∃ lv : Nat → TargetExt.LevelGeometry (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
          (MacroExp.emb 0) (↑(CoreRes.target (d := d) r y) : Set (Site d)),
        (∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D) ∧
        (∀ m, m + 1 < C.levels →
          ∀ x ∈ ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
            MacroExp.E d r t z y), x ∉ (lv m).D →
          ∀ v ∈ (lv m).D, (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D) ∧
        (∀ m < C.levels,
          (↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1))) :
            Set (Site d)) ⊆ ↑(lv m).D) ∧
        (∀ m < C.levels,
          Disjoint (lv m).D (Stopped.levelTr d r t s h z i sigma j omega).inspected) ∧
        (∀ m < C.levels, ∀ L ⊆ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
            MacroExp.E d r t z y) (lv m).D,
            C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card) ∧
        (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
            MacroExp.E d r t z y) (lv m).D,
            ((lv m).J x).card ≤ C.seedSize) ∧
        (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
            MacroExp.E d r t z y) (lv m).D,
            1 - 3 * C.delta ^ 2 ≤
              (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x)) := by
  intro j hj omega
  let F := familyAt_of_corePostWindowBound hwf hd hr hrt hj hsigma hemb hthin hfresh horigin
    hfar hclear hwidth hlong hplanar htrans (hwindow j hj omega)
  exact ⟨F.lv, F.nest, F.gateRel, F.source, F.fresh, F.select, F.seed, F.reliable⟩

/-- Direct gluing-free post-entry estimate. -/
theorem hone_of_corePostWindowBound
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q)
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (hthin : (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh : Disjoint h.inspected (MacroExp.E d r t z y))
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      CorePost.CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
        (CorePost.levelDom r t s h z y i sigma j omega) y) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state omega ∈
          CoreStopped.levelBad r t s h z y i sigma q C.eps j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
          (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - C.delta := by
  apply CorePerLevelNoGluing.hone_of_postEntry hwf hv hwf.delta_eq hr hrt hfar hsigma hemb hQ
  exact hpost_of_corePostWindowBound hwf hd hr hrt hsigma hemb hthin hfresh horigin hfar hclear
    hwidth hlong hplanar htrans hwindow

#print axioms KNAll.Site.CorePostNoGluing.familyAt_of_corePostWindowBound
#print axioms KNAll.Site.CorePostNoGluing.hpost_of_corePostWindowBound
#print axioms KNAll.Site.CorePostNoGluing.hone_of_corePostWindowBound

end KNAll.Site.CorePostNoGluing

end
