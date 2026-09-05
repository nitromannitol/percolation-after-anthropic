import Hypergraph.CorePostGeometry
import Hypergraph.CorePerLevel

/-!
# The complete deterministic core post-entry family

`CorePostWindowBound` is the one analytic input.  This module turns it into the exact family of
`TargetExt.LevelGeometryD` objects consumed by `CorePerLevel.hone_of_postEntry_D`.  All nesting,
relative-gate, source-containment, freshness, packing and seed-size fields are discharged here.
-/

noncomputable section

namespace KNAll.Site.CorePost

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor

variable {d : Nat} [NeZero d]

/-- The actual ambient domain after stopped level `j` has been exposed. -/
def levelDom (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2)
    (i : Fin d) (sigma : Int) (j : Nat) (omega : SiteConfig (Site d)) :
    Finset (Site d) :=
  (Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y

/-- The complete seven-field family at one stopped level. -/
structure FamilyAt (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (r t s : Nat) (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (sigma : Int)
    (j : Nat) (omega : SiteConfig (Site d)) where
  lv : Nat → TargetExt.LevelGeometryD (zdGraph d)
    (levelDom r t s h z y i sigma j omega) (MacroExp.emb 0)
    (↑(CoreRes.target (d := d) r y) : Set (Site d))
  nest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D
  gateRel : ∀ m, m + 1 < C.levels →
    ∀ x ∈ levelDom r t s h z y i sigma j omega, x ∉ (lv m).D →
    ∀ v ∈ (lv m).D, (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D
  source : ∀ m < C.levels,
    (↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1))) :
      Set (Site d)) ⊆ ↑(lv m).D
  fresh : ∀ m < C.levels,
    Disjoint (lv m).D (Stopped.levelTr d r t s h z i sigma j omega).inspected
  select : ∀ m < C.levels, ∀ L ⊆ TargetExt.outerBoundary (zdGraph d)
    (levelDom r t s h z y i sigma j omega) (lv m).D,
      C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card
  seed : ∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
    (levelDom r t s h z y i sigma j omega) (lv m).D,
      ((lv m).J x).card ≤ C.seedSize
  reliable : ∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
    (levelDom r t s h z y i sigma j omega) (lv m).D,
      1 - 3 * C.delta ^ 2 ≤
        (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x)

/-- `FamilyAt` is exactly the existential tuple expected by the per-level theorem. -/
theorem FamilyAt.exists_tuple {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {r t s : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    {j : Nat} {omega : SiteConfig (Site d)}
    (F : FamilyAt C q r t s h z y i sigma j omega) :
    ∃ lv : Nat → TargetExt.LevelGeometryD (zdGraph d)
        (levelDom r t s h z y i sigma j omega) (MacroExp.emb 0)
        (↑(CoreRes.target (d := d) r y) : Set (Site d)),
      (∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D) ∧
      (∀ m, m + 1 < C.levels →
        ∀ x ∈ levelDom r t s h z y i sigma j omega, x ∉ (lv m).D →
        ∀ v ∈ (lv m).D, (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D) ∧
      (∀ m < C.levels,
        (↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1))) :
          Set (Site d)) ⊆ ↑(lv m).D) ∧
      (∀ m < C.levels,
        Disjoint (lv m).D (Stopped.levelTr d r t s h z i sigma j omega).inspected) ∧
      (∀ m < C.levels, ∀ L ⊆ TargetExt.outerBoundary (zdGraph d)
        (levelDom r t s h z y i sigma j omega) (lv m).D,
          C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card) ∧
      (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
        (levelDom r t s h z y i sigma j omega) (lv m).D,
          ((lv m).J x).card ≤ C.seedSize) ∧
      (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
        (levelDom r t s h z y i sigma j omega) (lv m).D,
          1 - 3 * C.delta ^ 2 ≤
            (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x)) :=
  ⟨F.lv, F.nest, F.gateRel, F.source, F.fresh, F.select, F.seed, F.reliable⟩

/-- The named analytic window bound supplies the complete family at one stopped level. -/
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
    (hwindow : CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
      (levelDom r t s h z y i sigma j omega) y) :
    FamilyAt C q r t s h z y i sigma j omega := by
  let Dom := levelDom r t s h z y i sigma j omega
  let T : Set (Site d) := ↑(CoreRes.target (d := d) r y)
  have hiplanar : i.val < 2 := Stopped.dir_planar hsigma hemb
  have hthinDom : (↑Dom : Set (Site d)) ⊆ MacroExp.thin d t := by
    intro x hx
    simp only [Finset.mem_coe, Dom, levelDom, Finset.mem_union,
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
        (PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j (PostFam.clipLevel C m))
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
  have hoDom : (MacroExp.emb 0 : Site d) ∈ Dom := by
    apply Finset.mem_union_left
    rw [Stopped.levelTr_inspected]
    exact Finset.mem_union_left _ (h.openSites_subset horigin)
  have hoAll : ∀ m,
      (MacroExp.emb 0 : Site d) ∉
        PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j (PostFam.clipLevel C m) := by
    intro m hom
    exact Finset.disjoint_left.1 (hfreshAll m) hom
      (by
        rw [Stopped.levelTr_inspected]
        exact Finset.mem_union_left _ (h.openSites_subset horigin))
  let lv : Nat → TargetExt.LevelGeometryD (zdGraph d) Dom (MacroExp.emb 0) T := fun m =>
    tailLevelD C (MacroExp.ctr d r z) i sigma r t s j (PostFam.clipLevel C m)
      Dom (MacroExp.emb 0) T (hfitAll m) (hsubAll m) hoDom (hoAll m)
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
    simpa only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm,
      PostFam.clipLevel_eq C hm0] using
      (PostFam.tailD_succ_subset C (MacroExp.ctr d r z) i sigma r t s j m)
  · intro m hm x hxDom hxout v hv hadj
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    have hxout' : x ∉ PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j m := by
      simpa only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm0] using hxout
    have hv' : v ∈ PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j m := by
      simpa only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm0] using hv
    have hout := PostFam.tail_gate_rel (z := z) C hiplanar (sigma := sigma)
      (r := r) (s := s) (j := j) (m := m) (Dom := Dom) hthinDom
      x hxDom hxout' v hv' hadj
    simpa only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm] using hout
  · intro m hm x hx
    rw [Finset.mem_coe] at hx ⊢
    simpa only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm] using
      (PostFam.stubFace_subset_tailD C hsigma hj hm (by omega) hrt (by omega) (by omega)
        hlong hx)
  · intro m hm
    simpa only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm] using hfreshAll m
  · intro m hm L hL hcard
    simp only [lv, tailLevelD_sel, PostFam.clipLevel_eq C hm]
    simp only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm] at hL
    apply le_card_selC_of_subset_outerBoundary
      (PostFam.tailScales C i r t s j m) (PostFam.tailCentre (MacroExp.ctr d r z) i sigma r s j)
      0 Dom L (k := C.seedCount) (N := C.contacts)
    · simpa only [PostFam.tailD] using hL
    · have heq : 4 * (1 + 2 * C.faceTarget) + 1 = 8 * C.faceTarget + 5 := by omega
      simpa only [PostFam.tailScales, heq] using hwf.contacts_ge
    · exact hcard
  · intro m hm x hx
    simp only [lv, tailLevelD_J, PostFam.clipLevel_eq C hm]
    simp only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm] at hx
    refine (MacroExp.card_seed_le
      (Sc := PostFam.tailScales C i r t s j m) rfl
      (PostFam.tail_fits C hj hm hlong hplanar htrans i) ?_).trans ?_
    · exact isContact_of_mem_outerBoundary _ _ _ Dom
        (by simpa only [PostFam.tailD] using hx)
    · simpa only [PostFam.tailScales] using hwf.seedSize_ge
  · intro m hm x hx
    simp only [lv, tailLevelD_Gx, PostFam.clipLevel_eq C hm]
    simp only [lv, tailLevelD_D, PostFam.clipLevel_eq C hm] at hx
    exact hwindow m hm x (by simpa only [Dom, T] using hx)

/-- The direct all-stopped-level bridge required by `CorePerLevel.hone_of_postEntry_D`. -/
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
      CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
        (levelDom r t s h z y i sigma j omega) y) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      ∃ lv : Nat → TargetExt.LevelGeometryD (zdGraph d)
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
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
          (lv m).D, C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card) ∧
        (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
          (lv m).D, ((lv m).J x).card ≤ C.seedSize) ∧
        (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
          (lv m).D, 1 - 3 * C.delta ^ 2 ≤
            (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x)) := by
  intro j hj omega
  have F := familyAt_of_corePostWindowBound hwf hd hr hrt hj hsigma hemb hthin hfresh horigin
    hfar hclear hwidth hlong hplanar htrans (hwindow j hj omega)
  simpa only [levelDom] using F.exists_tuple

#print axioms KNAll.Site.CorePost.familyAt_of_corePostWindowBound
#print axioms KNAll.Site.CorePost.hpost_of_corePostWindowBound

end KNAll.Site.CorePost

end
