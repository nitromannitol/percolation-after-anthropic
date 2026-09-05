import Hypergraph.PerLevel
import Hypergraph.CoreStopped

/-!
# The post-entry estimate for core reservations

This is the support-in-`D` analogue of `KN.PerLevel`.  A bad stopped level now means that the
current pinned law does not reach the radius-`2r` core of the next macro block.  The target is
therefore exactly the event tested by `CoreStopped.levelBad`; no enlargement to the old
anisotropic reservation target is used.

The only additional input, exposed in every theorem below, is `PinnedSiteGluing`.  It is required
by the support-in-`D` target-extension theorem and is not silently supplied by this file.
-/

noncomputable section

namespace KNAll.Site.CorePerLevel

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## The target-extension contrapositive -/

/-- Contrapositive of the support-in-`D` target-extension theorem under the pinned law of the
current transcript.  The source is explicitly required to be recorded open; this supplies the
weight-one hypothesis used by pinned-site gluing. -/
theorem targetExtension_contrapositive_D {d : Nat} [NeZero d]
    (hgl : PinnedSiteGluing)
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hdelta : C.delta = C.eps ^ 2 / 96)
    (h : MacroExp.Tr d) (Dom : Finset (Site d)) (o : Site d) (ho : o ∈ h.openSites)
    (B T : Set (Site d))
    (lv : Nat → TargetExt.LevelGeometryD (zdGraph d) Dom o T)
    (hnest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D)
    (hgateRel : ∀ m, m + 1 < C.levels → ∀ x ∈ Dom, x ∉ (lv m).D →
      ∀ y ∈ (lv m).D, (zdGraph d).Adj x y → y ∉ (lv (m + 1)).D)
    (hB : ∀ m < C.levels, B ⊆ ↑(lv m).D)
    (hfresh : ∀ m < C.levels, Disjoint (lv m).D h.inspected)
    (hsel : ∀ m < C.levels, ∀ K ⊆ TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      C.contacts ≤ K.card → C.seedCount ≤ ((lv m).sel K).card)
    (hseed : ∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      ((lv m).J x).card ≤ C.seedSize)
    (hreliable : ∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      1 - 3 * C.delta ^ 2 ≤
        (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x))
    (htarget : h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o T) ≤ 1 - C.eps) :
    h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o B) ≤ 1 - C.delta := by
  classical
  by_contra hnot
  have hsrc : 1 - C.delta < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o B) := lt_of_not_ge hnot
  have hq0 : 0 < (q : Real) := MacroExp.coe_pos_of_validAt2 hwf hv
  have hq1 : (q : Real) < 1 := MacroExp.coe_lt_one_of_validAt2 hwf hv
  rw [MacroExp.prob_eq_real_pinW h q hq0 hq1
    (measurableSet_connWithinSet (zdGraph d) Dom o B)] at hsrc
  have hdelta13 : C.delta ≤ 1 / 3 := by
    have heprod : 0 ≤ C.eps * (1 - C.eps) :=
      mul_nonneg hwf.eps_pos.le (sub_nonneg.2 hwf.eps_le_one)
    rw [hdelta]
    nlinarith
  let w : Site d → unitInterval :=
    pinW (fun _ : Site d => q) (↑h.inspected : Set (Site d))
      (↑h.openSites : Set (Site d))
  have hwo : w o = 1 := by
    dsimp only [w]
    exact pinW_apply_of_mem_of_mem _
      (Finset.mem_coe.2 (h.openSites_subset ho)) (Finset.mem_coe.2 ho)
  have hout := TargetExt.targetExtension_D (zdGraph d) hgl Dom o T
    (Δ := 2 * d) (by
      intro x
      rw [Finset.filter_congr_decidable]
      exact MacroExp.card_le_of_forall_adj fun y hy => (Finset.mem_filter.1 hy).2)
    hwf.levels_pos lv hnest hgateRel hB q hq1 w hwo (by
      intro m hm y hy
      dsimp only [w]
      rw [pinW_apply_of_not_mem]
      intro hyI
      exact Finset.disjoint_left.1 (hfresh m hm) hy (Finset.mem_coe.1 hyI))
    C.contacts C.seedCount C.seedSize hsel hseed hwf.delta_pos hdelta13
    (hwf.level_of_le hv.2.2).le hv.2.1.le hreliable hsrc
  have hout' : (1 - 3 * C.delta) * (1 - 3 * C.delta) * (1 - C.delta) ≤
      h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o T) := by
    rw [MacroExp.prob_eq_real_pinW h q hq0 hq1
      (measurableSet_connWithinSet (zdGraph d) Dom o T)]
    simpa only [w] using hout
  have hnum := PerLevel.one_sub_eps_lt_extension_factor hwf.eps_pos hwf.eps_le_one hdelta
  exact (not_lt_of_ge htarget) (lt_of_lt_of_le hnum hout')

/-! ## One stopped level -/

/-- If the current level fails to carry a core reservation at error `C.eps`, then its probability
of crossing the next stopped face is at most `1 - C.delta`.  The target-extension geometry is
allowed to use a support contained in its declared middle box `D`. -/
theorem prob_crossEvent_le_of_coreLevelBad_D {d : Nat} [NeZero d]
    (hgl : PinnedSiteGluing)
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int} {j : Nat}
    (omega : SiteConfig (Site d)) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hnext : 10 * s * (j + 1) ≤ 17 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (lv : Nat → TargetExt.LevelGeometryD (zdGraph d)
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
  have hkorigin : (MacroExp.emb 0 : Site d) ∈ k.openSites := by
    change (MacroExp.emb 0 : Site d) ∈
      h.openSites ∪ (Stopped.revealSet d r t s h z i sigma j).filter (fun x => x ∈ omega)
    exact Finset.mem_union_left _ horigin
  have hsource : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) B) ≤
        1 - C.delta := by
    exact targetExtension_contrapositive_D hgl hwf hv hdelta k Dom (MacroExp.emb 0)
      hkorigin B T lv hnest (by simpa only [k, Dom] using hgateRel) hface hfresh hsel hseed
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

/-- Package the support-in-`D` finite-window construction at every stopped level into the exact
`hone` function consumed by the atom tower.  This theorem performs no probability transport: each
family is instantiated at the actual `levelTr` transcript at which its conclusion is used. -/
theorem hone_of_postEntry_D {d : Nat} [NeZero d]
    (hgl : PinnedSiteGluing)
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hr : 0 < r) (hrt : 2 * r ≤ t) (hfar : 10 * s * K ≤ 13 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hpost : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
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
            (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x))) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state omega ∈
          CoreStopped.levelBad r t s h z y i sigma q C.eps j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
          (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - C.delta := by
  intro j hj omega hbad
  obtain ⟨lv, hnest, hgateRel, hface, hfresh, hsel, hseed, hreliable⟩ := hpost j hj omega
  have hnext : 10 * s * (j + 1) ≤ 17 * r := by
    have hjK : j + 1 ≤ K := Nat.succ_le_iff.2 hj
    have hsK : 10 * s * (j + 1) ≤ 10 * s * K := Nat.mul_le_mul_left (10 * s) hjK
    omega
  exact prob_crossEvent_le_of_coreLevelBad_D hgl hwf hv hdelta omega hr hrt hnext hsigma hemb hQ
    horigin lv hnest hgateRel hface hfresh hsel hseed hreliable hbad

#print axioms KNAll.Site.CorePerLevel.targetExtension_contrapositive_D
#print axioms KNAll.Site.CorePerLevel.prob_crossEvent_le_of_coreLevelBad_D
#print axioms KNAll.Site.CorePerLevel.hone_of_postEntry_D

end KNAll.Site.CorePerLevel

end
