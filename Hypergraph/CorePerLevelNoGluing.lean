import Hypergraph.CorePerLevel

/-!
# The core stopped-level estimate without pinned gluing

`PostFam.tailWindow` is determined by its middle box and its selected relay reaches the target
inside that same middle box.  Consequently the core target can use the original
`TargetExt.LevelGeometry` interface and the product-independence proof
`PerLevel.targetExtension_contrapositive_rel`; the weaker support-in-`D` interface and
`PinnedSiteGluing` are not needed for this branch.

This module keeps the target equal to the radius-`2r` core used by `CoreStopped.levelBad`.
-/

noncomputable section

namespace KNAll.Site.CorePerLevelNoGluing

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## One stopped level -/

/-- If the current stopped level fails to reserve the next radius-`2r` core, then its crossing
probability is at most `1 - C.delta`.  The shell window is required to relay inside its middle
box, so the proof uses only product independence. -/
theorem prob_crossEvent_le_of_coreLevelBad {d : Nat} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int} {j : Nat}
    (omega : SiteConfig (Site d)) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hnext : 10 * s * (j + 1) ≤ 17 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (lv : Nat → TargetExt.LevelGeometry (zdGraph d)
      ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
      (MacroExp.emb 0) (↑(CoreRes.target (d := d) r y) : Set (Site d)))
    (hnest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D)
    (hgateRel : ∀ m, m + 1 < C.levels →
      ∀ x ∈ ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
        MacroExp.E d r t z y), x ∉ (lv m).D →
      ∀ v ∈ (lv m).D, (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D)
    (hface : ∀ m < C.levels,
      (↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1))) :
        Set (Site d)) ⊆ ↑(lv m).D)
    (hfresh : ∀ m < C.levels,
      Disjoint (lv m).D (Stopped.levelTr d r t s h z i sigma j omega).inspected)
    (hsel : ∀ m < C.levels, ∀ K ⊆ TargetExt.outerBoundary (zdGraph d)
      ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
      (lv m).D, C.contacts ≤ K.card → C.seedCount ≤ ((lv m).sel K).card)
    (hseed : ∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
      ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
      (lv m).D, ((lv m).J x).card ≤ C.seedSize)
    (hreliable : ∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
      ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
      (lv m).D, 1 - 3 * C.delta ^ 2 ≤
        (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x))
    (hbad : substitute (↑h.inspected : Set (Site d)) h.state omega ∈
      CoreStopped.levelBad r t s h z y i sigma q C.eps j) :
    (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
      (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - C.delta := by
  classical
  let k := Stopped.levelTr d r t s h z i sigma j omega
  let Dom := k.inspected ∪ MacroExp.E d r t z y
  let B : Set (Site d) :=
    ↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)))
  let T : Set (Site d) := ↑(CoreRes.target (d := d) r y)
  have htarget : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) T) ≤
        1 - C.eps := by
    have hb := (CoreStopped.substitute_mem_levelBad_iff r t s h z y i sigma q C.eps j
      omega).1 hbad
    simpa only [CoreStopped.levelBad, CoreRes.event, Set.mem_setOf_eq, k, Dom, T] using hb
  have hsource : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) B) ≤
        1 - C.delta := by
    exact PerLevel.targetExtension_contrapositive_rel hwf hv hdelta k Dom (MacroExp.emb 0)
      B T lv hnest (by simpa only [k, Dom] using hgateRel) hface hfresh hsel hseed
      hreliable htarget
  calc
    k.prob (fun _ : Site d => q) (Stopped.crossEvent d r t s h z i sigma j)
        ≤ k.prob (fun _ : Site d => q)
          (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) B) :=
      ProbInv.prob_mono k _ (by
        simpa only [k, Dom, B] using
          PerLevel.crossEvent_subset_postSource omega hr hrt hnext hsigma hemb hQ)
    _ ≤ 1 - C.delta := hsource

/-! ## The complete one-level family -/

/-- Package a middle-box-supported post-entry family into the exact `hone` function consumed by
the incoming-atom tower.  Unlike `CorePerLevel.hone_of_postEntry_D`, this theorem has no
`PinnedSiteGluing` argument. -/
theorem hone_of_postEntry {d : Nat} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hr : 0 < r) (hrt : 2 * r ≤ t) (hfar : 10 * s * K ≤ 13 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (hpost : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
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
              (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x))) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state omega ∈
          CoreStopped.levelBad r t s h z y i sigma q C.eps j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
          (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - C.delta := by
  intro j hj omega hbad
  obtain ⟨lv, hnest, hgateRel, hface, hfresh, hsel, hseed, hreliable⟩ :=
    hpost j hj omega
  have hnext : 10 * s * (j + 1) ≤ 17 * r := by
    have hjK : j + 1 ≤ K := Nat.succ_le_iff.2 hj
    have hsK : 10 * s * (j + 1) ≤ 10 * s * K := Nat.mul_le_mul_left (10 * s) hjK
    omega
  exact prob_crossEvent_le_of_coreLevelBad hwf hv hdelta omega hr hrt hnext hsigma hemb hQ
    lv hnest hgateRel hface hfresh hsel hseed hreliable hbad

#print axioms KNAll.Site.CorePerLevelNoGluing.prob_crossEvent_le_of_coreLevelBad
#print axioms KNAll.Site.CorePerLevelNoGluing.hone_of_postEntry

end KNAll.Site.CorePerLevelNoGluing

end
