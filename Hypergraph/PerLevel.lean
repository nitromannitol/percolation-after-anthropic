import Hypergraph.StoppedLevel

/-!
# The post-entry estimate at one stopped level

This file proves the contrapositive target-extension estimate used as `hone` by
`Stopped.prob_directionEvent_compl_le_accepted`.  The target-extension input tolerance is exactly

`delta = eps ^ 2 / 96`.

The finite post-entry windows are deliberately arguments of `hone_of_postEntry`; they are not the
`d + 1` corridor-move windows.  No new certificate or proxy structure is introduced.  Each family
is an existing `TargetExt.LevelGeometry` family, and its last hypothesis asks for component
failure at most `3 * delta ^ 2`.
-/

noncomputable section

namespace KNAll.Site.PerLevel

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## The exact numerical contrapositive -/

/-- With `delta = eps²/96`, the quantitative conclusion of `TargetExt.targetExtension` is strictly
larger than `1 - eps`. -/
theorem one_sub_eps_lt_extension_factor {eps delta : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hdelta : delta = eps ^ 2 / 96) :
    1 - eps < (1 - 3 * delta) * (1 - 3 * delta) * (1 - delta) := by
  have heprod : 0 ≤ eps * (1 - eps) := mul_nonneg heps0.le (sub_nonneg.2 heps1)
  have hdelta0 : 0 ≤ delta := by rw [hdelta]; positivity
  have hdelta13 : delta ≤ 1 / 3 := by rw [hdelta]; nlinarith
  have htail : 0 ≤ delta ^ 2 * (5 - 3 * delta) :=
    mul_nonneg (sq_nonneg delta) (by linarith)
  have hfactor : 1 - 7 * delta ≤
      (1 - 3 * delta) * (1 - 3 * delta) * (1 - delta) := by
    nlinarith
  have hloss : 7 * delta < eps := by
    rw [hdelta]
    nlinarith
  linarith

/-- The finite target-extension theorem, applied to the pinned law of the *current* transcript and
then contraposed.  All sites of every level box are required to be fresh for that transcript; no
conditional estimate is transported through a later read. -/
theorem targetExtension_contrapositive {d : ℕ} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hdelta : C.delta = C.eps ^ 2 / 96)
    (h : MacroExp.Tr d) (Dom : Finset (Site d)) (o : Site d) (B T : Set (Site d))
    (lv : ℕ → TargetExt.LevelGeometry (zdGraph d) Dom o T)
    (hnest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D)
    (hgate : ∀ m, m + 1 < C.levels → ∀ x ∉ (lv m).D, ∀ y ∈ (lv m).D,
      (zdGraph d).Adj x y → y ∉ (lv (m + 1)).D)
    (hB : ∀ m < C.levels, B ⊆ ↑(lv m).D)
    (hfresh : ∀ m < C.levels, Disjoint (lv m).D h.inspected)
    (hsel : ∀ m < C.levels, ∀ K ⊆
      TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      C.contacts ≤ K.card → C.seedCount ≤ ((lv m).sel K).card)
    (hseed : ∀ m < C.levels, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      ((lv m).J x).card ≤ C.seedSize)
    (hreliable : ∀ m < C.levels, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
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
  have hq0 : 0 < (q : ℝ) := MacroExp.coe_pos_of_validAt2 hwf hv
  have hq1 : (q : ℝ) < 1 := MacroExp.coe_lt_one_of_validAt2 hwf hv
  rw [MacroExp.prob_eq_real_pinW h q hq0 hq1
    (measurableSet_connWithinSet (zdGraph d) Dom o B)] at hsrc
  have hdelta13 : C.delta ≤ 1 / 3 := by
    have heprod : 0 ≤ C.eps * (1 - C.eps) :=
      mul_nonneg hwf.eps_pos.le (sub_nonneg.2 hwf.eps_le_one)
    rw [hdelta]
    nlinarith
  have hout := TargetExt.targetExtension (zdGraph d) Dom o T
    (Δ := 2 * d) (by
      intro x
      rw [Finset.filter_congr_decidable]
      exact MacroExp.card_le_of_forall_adj fun y hy => (Finset.mem_filter.1 hy).2)
    hwf.levels_pos lv hnest hgate hB q hq1
    (pinW (fun _ : Site d => q) (↑h.inspected : Set (Site d))
      (↑h.openSites : Set (Site d))) (by
      intro m hm y hy
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
    exact hout
  have hnum := one_sub_eps_lt_extension_factor hwf.eps_pos hwf.eps_le_one hdelta
  exact (not_lt_of_ge htarget) (lt_of_lt_of_le hnum hout')

/-- Relative-gate form of `targetExtension_contrapositive`. -/
theorem targetExtension_contrapositive_rel {d : ℕ} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hdelta : C.delta = C.eps ^ 2 / 96)
    (h : MacroExp.Tr d) (Dom : Finset (Site d)) (o : Site d) (B T : Set (Site d))
    (lv : ℕ → TargetExt.LevelGeometry (zdGraph d) Dom o T)
    (hnest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D)
    (hgateRel : ∀ m, m + 1 < C.levels → ∀ x ∈ Dom, x ∉ (lv m).D →
      ∀ y ∈ (lv m).D, (zdGraph d).Adj x y → y ∉ (lv (m + 1)).D)
    (hB : ∀ m < C.levels, B ⊆ ↑(lv m).D)
    (hfresh : ∀ m < C.levels, Disjoint (lv m).D h.inspected)
    (hsel : ∀ m < C.levels, ∀ K ⊆
      TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      C.contacts ≤ K.card → C.seedCount ≤ ((lv m).sel K).card)
    (hseed : ∀ m < C.levels, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
      ((lv m).J x).card ≤ C.seedSize)
    (hreliable : ∀ m < C.levels, ∀ x ∈
      TargetExt.outerBoundary (zdGraph d) Dom (lv m).D,
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
  have hq0 : 0 < (q : ℝ) := MacroExp.coe_pos_of_validAt2 hwf hv
  have hq1 : (q : ℝ) < 1 := MacroExp.coe_lt_one_of_validAt2 hwf hv
  rw [MacroExp.prob_eq_real_pinW h q hq0 hq1
    (measurableSet_connWithinSet (zdGraph d) Dom o B)] at hsrc
  have hdelta13 : C.delta ≤ 1 / 3 := by
    have heprod : 0 ≤ C.eps * (1 - C.eps) :=
      mul_nonneg hwf.eps_pos.le (sub_nonneg.2 hwf.eps_le_one)
    rw [hdelta]
    nlinarith
  have hout := TargetExt.targetExtension_rel (zdGraph d) Dom o T
    (Δ := 2 * d) (by
      intro x
      rw [Finset.filter_congr_decidable]
      exact MacroExp.card_le_of_forall_adj fun y hy => (Finset.mem_filter.1 hy).2)
    hwf.levels_pos lv hnest hgateRel hB q hq1
    (pinW (fun _ : Site d => q) (↑h.inspected : Set (Site d))
      (↑h.openSites : Set (Site d))) (by
      intro m hm y hy
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
    exact hout
  have hnum := one_sub_eps_lt_extension_factor hwf.eps_pos hwf.eps_le_one hdelta
  exact (not_lt_of_ge htarget) (lt_of_lt_of_le hnum hout')

/-! ## The stopped-stub specialization -/

/-- The post-entry target is a whole finite set, not a designated open site.  In particular it is
nonempty: the axial site at longitudinal coordinate `20r` is in it. -/
theorem postTarget_nonempty {d r t : ℕ} (i : Fin d) {sigma : ℤ}
    (hsigma : sigma = 1 ∨ sigma = -1) (z : Site 2) :
    (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) :
      Set (Site d)).Nonempty := by
  obtain ⟨x, hx⟩ := Stopped.stubTarget_nonempty (MacroExp.ctr d r z) i hsigma
    (r := r) (t := t) (A := 17 * r) (by omega)
  exact ⟨x, Finset.mem_coe.2 hx⟩

/-- The level target event is contained in the reservation event because the whole far stub target
lies in `M y`. -/
theorem postTargetEvent_subset_reservation {d r t : ℕ} [NeZero d]
    (k : MacroExp.Tr d) {z y : Site 2} {i : Fin d} {sigma : ℤ}
    (hrt : 2 * r ≤ t)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    connWithinSet (zdGraph d)
        (↑(k.inspected ∪ MacroExp.E d r t z y) : Set (Site d)) (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
      ⊆ MacroExp.reservationEvent d r t k z y := by
  intro xi hxi
  rw [mem_connWithinSet_iff] at hxi
  rw [MacroExp.reservationEvent, mem_connWithinSet_iff]
  obtain ⟨a, ha, hconn⟩ := hxi
  exact ⟨a, Finset.mem_coe.2
    (Stopped.stubTarget_subset_M (d := d) (A := 17 * r) (by omega) hrt hsigma hemb
      (Finset.mem_coe.1 ha)), hconn⟩

/-- A crossing of the next face in the stopped stub is a source event in the post-entry domain.
The central box is already inspected, while the part beyond it lies in the outgoing edge region. -/
theorem crossEvent_subset_postSource {d r t s : ℕ} [NeZero d]
    {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : ℤ} {j : ℕ}
    (omega : SiteConfig (Site d)) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hnext : 10 * s * (j + 1) ≤ 17 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected) :
    Stopped.crossEvent d r t s h z i sigma j ⊆
      connWithinSet (zdGraph d)
        (↑((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
          MacroExp.E d r t z y) : Set (Site d))
        (MacroExp.emb 0)
        (↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1))) :
          Set (Site d)) := by
  apply connWithinSet_mono_set (zdGraph d) (x := MacroExp.emb 0)
  rw [Finset.coe_subset]
  have hbase : h.inspected ⊆
      (Stopped.levelTr d r t s h z i sigma j omega).inspected := by
    rw [Stopped.levelTr_inspected]
    exact Finset.subset_union_left
  have hstub0 := Stopped.stub_subset_Q_union_E (d := d) (t := t) hr hnext hrt hsigma hemb
  have hstub :
      Stopped.stub (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)) ⊆
        (Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
          MacroExp.E d r t z y := by
    intro x hx
    rcases Finset.mem_union.1 (hstub0 hx) with hxQ | hxE
    · exact Finset.mem_union_left _ (hbase (hQ hxQ))
    · exact Finset.mem_union_right _ hxE
  exact Finset.union_subset
    (hbase.trans Finset.subset_union_left)
    hstub

/-- One fixed stopped level.  This is (9.1a): if the current level is bad at output tolerance
`C.eps`, its probability of reaching the next whole cross-section is at most
`1 - C.delta`, where `C.delta = C.eps²/96`. -/
theorem prob_crossEvent_le_of_levelBad {d : ℕ} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : ℤ} {j : ℕ}
    (omega : SiteConfig (Site d)) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hnext : 10 * s * (j + 1) ≤ 17 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (lv : ℕ → TargetExt.LevelGeometry (zdGraph d)
      ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
      (MacroExp.emb 0)
      (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d)))
    (hnest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D)
    (hgate : ∀ m, m + 1 < C.levels → ∀ x ∉ (lv m).D, ∀ v ∈ (lv m).D,
      (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D)
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
      Stopped.levelBad d r t s h z y i sigma q C.eps j) :
    (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
      (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - C.delta := by
  let k := Stopped.levelTr d r t s h z i sigma j omega
  let Dom := k.inspected ∪ MacroExp.E d r t z y
  let B : Set (Site d) :=
    ↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)))
  let T : Set (Site d) :=
    ↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r))
  have hbad' : k.prob (fun _ : Site d => q) (MacroExp.reservationEvent d r t k z y) ≤
      1 - C.eps := by
    have hb := (Stopped.substitute_mem_levelBad_iff d r t s h z y i sigma q C.eps j omega).1 hbad
    simpa only [Stopped.levelBad, Set.mem_setOf_eq, k] using hb
  have htarget : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) T) ≤ 1 - C.eps := by
    calc
      k.prob (fun _ : Site d => q)
          (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) T)
        ≤ k.prob (fun _ : Site d => q) (MacroExp.reservationEvent d r t k z y) :=
          ProbInv.prob_mono k _ (by
            simpa only [Dom, T] using
              postTargetEvent_subset_reservation k hrt hsigma hemb)
      _ ≤ 1 - C.eps := hbad'
  have hsource : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) B) ≤
        1 - C.delta := by
    exact targetExtension_contrapositive hwf hv hdelta k Dom (MacroExp.emb 0) B T lv
      hnest hgate hface hfresh hsel hseed hreliable htarget
  calc
    k.prob (fun _ : Site d => q) (Stopped.crossEvent d r t s h z i sigma j)
      ≤ k.prob (fun _ : Site d => q)
          (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) B) :=
        ProbInv.prob_mono k _ (by
          simpa only [k, Dom, B] using
            crossEvent_subset_postSource omega hr hrt hnext hsigma hemb hQ)
    _ ≤ 1 - C.delta := hsource

/-- Relative-gate form of `prob_crossEvent_le_of_levelBad`. -/
theorem prob_crossEvent_le_of_levelBad_rel {d : ℕ} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : ℤ} {j : ℕ}
    (omega : SiteConfig (Site d)) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hnext : 10 * s * (j + 1) ≤ 17 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (lv : ℕ → TargetExt.LevelGeometry (zdGraph d)
      ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
      (MacroExp.emb 0)
      (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d)))
    (hnest : ∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D)
    (hgateRel : ∀ m, m + 1 < C.levels →
      ∀ x ∈ ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y),
      x ∉ (lv m).D → ∀ v ∈ (lv m).D,
      (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D)
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
      Stopped.levelBad d r t s h z y i sigma q C.eps j) :
    (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
      (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - C.delta := by
  let k := Stopped.levelTr d r t s h z i sigma j omega
  let Dom := k.inspected ∪ MacroExp.E d r t z y
  let B : Set (Site d) :=
    ↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)))
  let T : Set (Site d) :=
    ↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r))
  have hbad' : k.prob (fun _ : Site d => q) (MacroExp.reservationEvent d r t k z y) ≤
      1 - C.eps := by
    have hb := (Stopped.substitute_mem_levelBad_iff d r t s h z y i sigma q C.eps j omega).1
      hbad
    simpa only [Stopped.levelBad, Set.mem_setOf_eq, k] using hb
  have htarget : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) T) ≤ 1 - C.eps := by
    calc
      k.prob (fun _ : Site d => q)
          (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) T)
        ≤ k.prob (fun _ : Site d => q) (MacroExp.reservationEvent d r t k z y) :=
          ProbInv.prob_mono k _ (by
            simpa only [Dom, T] using postTargetEvent_subset_reservation k hrt hsigma hemb)
      _ ≤ 1 - C.eps := hbad'
  have hsource : k.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) B) ≤
        1 - C.delta := by
    exact targetExtension_contrapositive_rel hwf hv hdelta k Dom (MacroExp.emb 0) B T lv
      hnest (by simpa only [k, Dom] using hgateRel) hface hfresh hsel hseed hreliable htarget
  calc
    k.prob (fun _ : Site d => q) (Stopped.crossEvent d r t s h z i sigma j)
      ≤ k.prob (fun _ : Site d => q)
          (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) B) :=
        ProbInv.prob_mono k _ (by
          simpa only [k, Dom, B] using
            crossEvent_subset_postSource omega hr hrt hnext hsigma hemb hQ)
    _ ≤ 1 - C.delta := hsource

/-! ## The exact `hone`, first for a general transcript and then for `accepted` -/

/-- The post-entry finite-window clause needed by all levels, stated inline so it can be copied
verbatim into a later certificate interface.  Its conclusion is exactly the `hone` expected by
`Stopped.prob_directionEvent_compl_le_accepted`. -/
theorem hone_of_postEntry {d : ℕ} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s K : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : ℤ}
    (hr : 0 < r) (hrt : 2 * r ≤ t) (hfar : 10 * s * K ≤ 13 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (hpost : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      ∃ lv : ℕ → TargetExt.LevelGeometry (zdGraph d)
        ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d)),
        (∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D) ∧
        (∀ m, m + 1 < C.levels → ∀ x ∉ (lv m).D, ∀ v ∈ (lv m).D,
          (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D) ∧
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
          Stopped.levelBad d r t s h z y i sigma q C.eps j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob
          (fun _ : Site d => q) (Stopped.crossEvent d r t s h z i sigma j)
        ≤ 1 - C.delta := by
  intro j hj omega hbad
  obtain ⟨lv, hnest, hgate, hface, hfresh, hsel, hseed, hreliable⟩ := hpost j hj omega
  have hnext : 10 * s * (j + 1) ≤ 17 * r := by
    have hjK : j + 1 ≤ K := Nat.succ_le_iff.2 hj
    have hsK : 10 * s * (j + 1) ≤ 10 * s * K := Nat.mul_le_mul_left (10 * s) hjK
    omega
  exact prob_crossEvent_le_of_levelBad hwf hv hdelta omega hr hrt hnext hsigma hemb hQ lv
    hnest hgate hface hfresh hsel hseed hreliable hbad

/-- Relative-gate form of `hone_of_postEntry`. -/
theorem hone_of_postEntry_rel {d : ℕ} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s K : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : ℤ}
    (hr : 0 < r) (hrt : 2 * r ≤ t) (hfar : 10 * s * K ≤ 13 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (hpost : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      ∃ lv : ℕ → TargetExt.LevelGeometry (zdGraph d)
        ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d)),
        (∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D) ∧
        (∀ m, m + 1 < C.levels →
          ∀ x ∈ ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
            MacroExp.E d r t z y),
          x ∉ (lv m).D → ∀ v ∈ (lv m).D,
          (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D) ∧
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
          Stopped.levelBad d r t s h z y i sigma q C.eps j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob
          (fun _ : Site d => q) (Stopped.crossEvent d r t s h z i sigma j)
        ≤ 1 - C.delta := by
  intro j hj omega hbad
  obtain ⟨lv, hnest, hgateRel, hface, hfresh, hsel, hseed, hreliable⟩ := hpost j hj omega
  have hnext : 10 * s * (j + 1) ≤ 17 * r := by
    have hjK : j + 1 ≤ K := Nat.succ_le_iff.2 hj
    have hsK : 10 * s * (j + 1) ≤ 10 * s * K := Nat.mul_le_mul_left (10 * s) hjK
    omega
  exact prob_crossEvent_le_of_levelBad_rel hwf hv hdelta omega hr hrt hnext hsigma hemb hQ lv
    hnest hgateRel hface hfresh hsel hseed hreliable hbad

/-- The examined central box is already inspected in the accepted transcript, because it is
contained in the incoming edge region. -/
theorem Q_subset_accepted_inspected {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {r t n : ℕ} (hr : 0 < r) {h : MacroExp.Tr d}
    (hwspec : MacroExp.pendW d n h ∈ h.openV ∧
      (zdGraph 2).Adj (MacroExp.pendW d n h) (MacroExp.pendZ d n h))
    (omega0 : SiteConfig (Site d)) :
    MacroExp.Q d r t (MacroExp.pendZ d n h) ⊆
      (MacroExp.accepted d r t n h omega0).inspected := by
  intro x hxQ
  have hxE : x ∈ MacroExp.E d r t (MacroExp.pendW d n h) (MacroExp.pendZ d n h) :=
    Corridor.Q_subset_E hd r t hr hwspec.2.ne hxQ
  rw [MacroExp.accepted, FRDom.Transcript.step_inspected]
  by_cases hxI : x ∈ h.inspected
  · exact Finset.mem_union_left _ hxI
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hxE, hxI⟩)

/-- Accepted-transcript form, with the conclusion written exactly as the `hone` binder of
`Stopped.prob_directionEvent_compl_le_accepted`. -/
theorem hone_accepted {d : ℕ} [NeZero d]
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval} (hv : C.ValidAt2 q)
    (hdelta : C.delta = C.eps ^ 2 / 96)
    {r t s K n : ℕ} {h : MacroExp.Tr d} {y : Site 2} {i : Fin d} {sigma : ℤ}
    {omega0 : SiteConfig (Site d)}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t) (hfar : 10 * s * K ≤ 13 * r)
    (hwspec : MacroExp.pendW d n h ∈ h.openV ∧
      (zdGraph 2).Adj (MacroExp.pendW d n h) (MacroExp.pendZ d n h))
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - MacroExp.pendZ d n h) : Site d) = Pi.single i sigma)
    (hpost : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      ∃ lv : ℕ → TargetExt.LevelGeometry (zdGraph d)
        ((Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) i sigma j omega).inspected ∪
            MacroExp.E d r t (MacroExp.pendZ d n h) y)
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r (MacroExp.pendZ d n h)) i sigma r t (17 * r)) :
          Set (Site d)),
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
            (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x))) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      substitute (↑(MacroExp.accepted d r t n h omega0).inspected : Set (Site d))
          (MacroExp.accepted d r t n h omega0).state omega
        ∈ Stopped.levelBad d r t s (MacroExp.accepted d r t n h omega0)
          (MacroExp.pendZ d n h) y i sigma q C.eps j →
      (Stopped.levelTr d r t s (MacroExp.accepted d r t n h omega0)
        (MacroExp.pendZ d n h) i sigma j omega).prob
          (fun _ : Site d => q)
          (Stopped.crossEvent d r t s (MacroExp.accepted d r t n h omega0)
            (MacroExp.pendZ d n h) i sigma j)
        ≤ 1 - C.delta := by
  exact hone_of_postEntry_rel hwf hv hdelta hr hrt hfar hsigma hemb
    (Q_subset_accepted_inspected hd hr hwspec omega0) hpost

/-!
## Regression checks

1. **No designated open site.**  `crossEvent` reaches the whole `stubFace`; the post-entry target is
   the whole `stubTarget`.  No fixed unread site is required to be open.
2. **No empty target.**  `postTarget_nonempty` is proved from `Stopped.stubTarget_nonempty`, and
   `Stopped.stubTarget_subset_M` is used in `postTargetEvent_subset_reservation`.
3. **No stale conditional estimate.**  `targetExtension_contrapositive` is applied to the pinned
   law of the actual `levelTr` transcript.  Its `hfresh` hypothesis is about that transcript, after
   all earlier reads, so no estimate is carried across an overlapping read.
-/

#print axioms KNAll.Site.PerLevel.targetExtension_contrapositive
#print axioms KNAll.Site.PerLevel.prob_crossEvent_le_of_levelBad
#print axioms KNAll.Site.PerLevel.hone_of_postEntry
#print axioms KNAll.Site.PerLevel.hone_accepted

end KNAll.Site.PerLevel

end
