import Hypergraph.CoreAdaptiveSoundness
import Hypergraph.SiteLocalFromUniqueness

/-!
# A positive uniform benchmark for the bounded-damage exploration

`CoreAdaptiveSoundness` compares an accepted macro exploration with iid successful centres on
`Z^2`, where one failed centre may delete its closed nearest-neighbourhood.  `DamageBlocks` proves
that this damaged iid model percolates, but its original block tiling has the centre `(1,1)` over
the coarse origin.  The exploration starts at the actual origin.  This file translates the block
tiling before taking probabilities, so its distinguished fine vertex is exactly zero, and then
passes from an infinite safe path to every finite safe-target event used by the exploration.

There is no asymptotic input here.  The comparison parameter and the positive lower bound are
explicit finite/product-measure objects.
-/

noncomputable section

namespace KNAll.Site.CoreSafe

open MeasureTheory Set ProbabilityTheory
open Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

abbrev Plane := Site 2
abbrev Offset := DamageBlocks.Offset

/-- The success density corresponding to the worst permitted batch-failure density. -/
def successParam : unitInterval := unitInterval.symm DamageBlocks.etaMax

@[simp] theorem coe_successParam : (successParam : Real) = 1 - 9 / 2 ^ 37 := by
  rw [successParam, unitInterval.coe_symm_eq, DamageBlocks.coe_etaMax]

/-- Translate the `3 x 3` tiling so that the centre of its origin block is the lattice origin. -/
def originFine (zu : Plane × Offset) : Plane :=
  DamageBlocks.fineOfBlock zu - DamageBlocks.center 0

theorem originFine_injective : Function.Injective originFine := by
  intro x y hxy
  apply DamageBlocks.fineOfBlock_injective
  have := congrArg (fun z : Plane => z + DamageBlocks.center 0) hxy
  simpa [originFine] using this

/-- A coarse block is good when all nine translated fine sites are successful. -/
def originGoodBlocks (good : Set Plane) : Set Plane :=
  {z | forall u : Offset, originFine (z, u) ∈ good}

theorem measurable_originGoodBlocks : Measurable originGoodBlocks := by
  refine measurable_set_iff.2 fun z => ?_
  exact Measurable.forall fun u => measurable_set_mem (originFine (z, u))

/-- The probability that all nine coordinates are successful at density `1 - eta`. -/
theorem infinitePi_offset_all_true_symm (eta : unitInterval) :
    (Measure.infinitePi fun _ : Offset => Ber(True, False, unitInterval.symm eta))
        {q : Offset → Prop | forall u, q u}
      = ENNReal.ofReal ((1 - (eta : Real)) ^ 9) := by
  have hnonneg : (0 : Real) ≤ 1 - (eta : Real) := by linarith [eta.2.2]
  have hset : {q : Offset → Prop | forall u, q u}
      = Set.univ.pi (fun _ : Offset => ({True} : Set Prop)) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_singleton_iff, eq_iff_iff,
      iff_true]
  have hcard : Fintype.card Offset = 9 := by
    simp [Offset, DamageBlocks.Offset, Fintype.card_fun]
  rw [hset, Measure.infinitePi_eq_pi, Measure.pi_pi, Finset.prod_const,
    Finset.card_univ, hcard, bernoulliMeasure_prop_apply_true, unitInterval.coe_symm_eq,
    ENNReal.ofReal_pow hnonneg]

/-- The translated all-success block field is iid with density `(1-eta)^9`. -/
theorem prodBernoulli_map_originGoodBlocks (eta : unitInterval) :
    (prodBernoulli fun _ : Plane => unitInterval.symm eta).map originGoodBlocks
      = prodBernoulli fun _ : Plane => DamageBlocks.goodParam eta := by
  have hPhi : forall _z : Plane, Measurable fun q : Offset → Prop => forall u, q u :=
    fun _ => Measurable.forall fun u => measurable_pi_apply u
  exact prodBernoulli_map_grouped originFine_injective (unitInterval.symm eta)
    (fun _z q => forall u, q u) hPhi (fun _ => DamageBlocks.goodParam eta)
    (fun _ => infinitePi_offset_all_true_symm eta)

/-! ## Deterministic translation of the safe path -/

/-- Damage commutes with a lattice translation. -/
theorem damaged_siteShift (v : Plane) (failed : Set Plane) :
    DamageBlocks.damaged (siteShift v failed) = siteShift v (DamageBlocks.damaged failed) := by
  ext x
  simp only [DamageBlocks.damaged, Set.mem_setOf_eq, mem_siteShift]
  constructor
  · rintro ⟨f, hf, hfx⟩
    refine ⟨f + v, hf, ?_⟩
    rcases hfx with rfl | hfx
    · exact Or.inl rfl
    · exact Or.inr ((zdGraph_adj_shift_iff v f x).2 hfx)
  · rintro ⟨f, hf, hfx⟩
    refine ⟨f - v, ?_, ?_⟩
    · simpa using hf
    · rcases hfx with rfl | hfx
      · left; simp
      · right
        have := (zdGraph_adj_shift_iff v (f - v) x).1
        apply this
        simpa using hfx

/-- Consequently the complement of the damage set commutes with translation. -/
theorem safe_siteShift (v : Plane) (failed : Set Plane) :
    DamageBlocks.safe (siteShift v failed) = siteShift v (DamageBlocks.safe failed) := by
  rw [DamageBlocks.safe, DamageBlocks.safe, damaged_siteShift]
  ext x
  simp only [Set.mem_compl_iff, mem_siteShift]

/-- The translated block field is the old block field applied to a translated failure set. -/
theorem originGoodBlocks_eq (good : Set Plane) :
    originGoodBlocks good =
      DamageBlocks.goodBlocks (siteShift (-DamageBlocks.center 0) goodᶜ) := by
  ext z
  simp only [originGoodBlocks, Set.mem_setOf_eq, DamageBlocks.goodBlocks, mem_siteShift,
    Set.mem_compl_iff, originFine]
  simp only [sub_eq_add_neg, not_not]

/-- An infinite translated good-block cluster lifts to an infinite safe cluster at the actual
origin, not at a designated open tip. -/
theorem infinite_safeCluster_of_originGoodBlocks {good : Set Plane}
    (h : (siteCluster (zdGraph 2) (originGoodBlocks good) 0).Infinite) :
    (siteCluster (zdGraph 2) (DamageBlocks.safe goodᶜ) 0).Infinite := by
  let v : Plane := DamageBlocks.center 0
  let failed' : Set Plane := siteShift (-v) goodᶜ
  have hblocks : originGoodBlocks good = DamageBlocks.goodBlocks failed' := by
    simpa [v, failed'] using originGoodBlocks_eq good
  have hinf' : (siteCluster (zdGraph 2) (DamageBlocks.safe failed') (DamageBlocks.center 0)).Infinite :=
    DamageBlocks.infinite_safeCluster_of_goodBlocks (hblocks ▸ h)
  have hp' : DamageBlocks.safe failed' ∈ sitePerc (zdGraph 2) (DamageBlocks.center 0) :=
    (siteCluster_infinite_iff _ _ _).1 hinf'
  have hsafe : DamageBlocks.safe failed' = siteShift (-v) (DamageBlocks.safe goodᶜ) := by
    simpa [failed'] using safe_siteShift (-v) goodᶜ
  rw [hsafe] at hp'
  have hp0 : DamageBlocks.safe goodᶜ ∈
      sitePerc (zdGraph 2) (DamageBlocks.center 0 + (-v)) := by
    rw [← sitePerc_siteShift (-v) (DamageBlocks.center 0)]
    exact hp'
  have hv : DamageBlocks.center 0 + (-v) = (0 : Plane) := by simp [v]
  rw [hv] at hp0
  exact (siteCluster_infinite_iff _ _ _).2 hp0

/-! ## The positive uniform finite-volume lower bound -/

/-- Iid successful centres at `successParam` have a positive probability of an infinite safe
cluster through the origin. -/
theorem iid_safe_percolates_origin :
    0 < (prodBernoulli fun _ : Plane => successParam).real
      {good : Set Plane | (siteCluster (zdGraph 2)
        (DamageBlocks.safe goodᶜ) 0).Infinite} := by
  let EGood : Set (Set Plane) :=
    {omega | (siteCluster (zdGraph 2) omega 0).Infinite}
  let ESafe : Set (Set Plane) :=
    {good | (siteCluster (zdGraph 2) (DamageBlocks.safe goodᶜ) 0).Infinite}
  have hmGood : MeasurableSet EGood := measurableSet_siteInfinite _ _
  have hsub : originGoodBlocks ⁻¹' EGood ⊆ ESafe := by
    intro good hgood
    exact infinite_safeCluster_of_originGoodBlocks hgood
  have hmap := prodBernoulli_map_originGoodBlocks DamageBlocks.etaMax
  have hmap' :
      (prodBernoulli fun _ : Plane => successParam).map originGoodBlocks =
        prodBernoulli fun _ : Plane => DamageBlocks.goodParam DamageBlocks.etaMax := by
    simpa [successParam] using hmap
  calc
    (0 : Real) < thetaSite 2 (DamageBlocks.goodParam DamageBlocks.etaMax) :=
      DamageBlocks.thetaSite_goodParam_etaMax_pos
    _ = ((prodBernoulli fun _ : Plane => successParam).map originGoodBlocks).real EGood := by
      rw [hmap']
      rfl
    _ = (prodBernoulli fun _ : Plane => successParam).real
          (originGoodBlocks ⁻¹' EGood) := by
      rw [map_measureReal_apply measurable_originGoodBlocks hmGood]
    _ ≤ (prodBernoulli fun _ : Plane => successParam).real ESafe :=
      measureReal_mono hsub (measure_ne_top _ _)

/-- The fixed positive comparison constant. -/
def benchmark : Real :=
  (prodBernoulli fun _ : Plane => successParam).real
    {good : Set Plane | (siteCluster (zdGraph 2) (DamageBlocks.safe goodᶜ) 0).Infinite}

theorem benchmark_pos : 0 < benchmark := iid_safe_percolates_origin

/-- A globally safe vertex in the arena is safe for the arena-local bounded-damage definition. -/
theorem globalSafe_inter_subset_localSafe (A : Finset Plane) (good : Set Plane) :
    DamageBlocks.safe goodᶜ ∩ (↑A : Set Plane) ⊆
      BDDom.Safe.sites (zdGraph 2) A good := by
  rintro x ⟨hxsafe, hxA⟩
  refine ⟨Finset.mem_coe.1 hxA, fun z hzA hzx => ?_⟩
  by_contra hzgood
  exact hxsafe ⟨z, hzgood, hzx⟩

/-- An infinite globally safe path reaches the inner boundary of every finite arena through the
arena-local safe sites. -/
theorem localSafe_targetConn_of_infinite (A : Finset Plane) (h0A : (0 : Plane) ∈ A)
    (good : Set Plane)
    (hinf : (siteCluster (zdGraph 2) (DamageBlocks.safe goodᶜ) 0).Infinite) :
    good ∈ BDDom.Safe.targetConn (zdGraph 2) A 0
      (↑(innerBoundary (zdGraph 2) A) : Set Plane) := by
  have hglobal := FRDom.mem_targetConn_of_infinite (zdGraph 2) A h0A hinf
  rw [FRDom.mem_targetConn_iff] at hglobal
  rw [BDDom.Safe.mem_targetConn_iff, FRDom.mem_targetConn_iff]
  obtain ⟨t, ht, hconn⟩ := hglobal
  refine ⟨t, ht, ?_⟩
  rw [mem_connWithin_iff] at hconn ⊢
  have hsub := globalSafe_inter_subset_localSafe A good
  have hsub' : DamageBlocks.safe goodᶜ ∩ (↑A : Set Plane) ⊆
      BDDom.Safe.sites (zdGraph 2) A good ∩ (↑A : Set Plane) := by
    intro x hx
    exact ⟨hsub hx, Finset.mem_coe.2 (hsub hx).1⟩
  refine ⟨hsub' hconn.1, hconn.2.mono ?_⟩
  rw [SimpleGraph.le_iff_adj]
  intro x y hxy
  rw [openSiteGraph_adj_iff'] at hxy ⊢
  exact ⟨hxy.1, hsub' hxy.2.1, hsub' hxy.2.2⟩

/-- `benchmark` uniformly bounds every finite safe-target probability from below. -/
theorem benchmark_le_real_safeTargetConn (n : Nat) :
    benchmark ≤ (prodBernoulli fun _ : Plane => successParam).real
      (BDDom.Safe.targetConn (zdGraph 2) (box 2 n) 0
        (↑(innerBoundary (zdGraph 2) (box 2 n)) : Set Plane)) := by
  unfold benchmark
  refine measureReal_mono (fun good hinf => ?_) (measure_ne_top _ _)
  exact localSafe_targetConn_of_infinite (box 2 n) (zero_mem_box 2 n) good hinf

/-- The form consumed by `CoreAdaptiveSoundness`: pinning the initially accepted origin can only
increase the safe-target probability. -/
theorem benchmark_le_pinned_safeTargetConn (n : Nat) :
    benchmark ≤ pinnedProb (fun _ : Plane => successParam) {0} (fun _ => True)
      (BDDom.Safe.targetConn (zdGraph 2) (box 2 n) 0
        (↑(innerBoundary (zdGraph 2) (box 2 n)) : Set Plane)) :=
  (benchmark_le_real_safeTargetConn n).trans
    (FRDom.real_le_pinnedProb_of_isUpperSet _ _
      (BDDom.Safe.isUpperSet_targetConn (zdGraph 2) (box 2 n) 0 _))

/-- Any bounded-damage transcript whose base and failed-centre fields are the genuine macro start
state has the required uniform benchmark.  This removes the `hbern` premise from the eventual
certificate construction. -/
theorem benchmark_le_bern_of_start {d : Nat} [NeZero d] (r t n : Nat)
    (h0 : CoreAdaptSound.Tr (Site d) Plane)
    (hbase : h0.base = MacroExp.start d r t) (hfailed : h0.failed = ∅) :
    benchmark ≤ h0.bern successParam (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) := by
  unfold BDDom.Transcript.bern
  have hopen : h0.base.openV = {(0 : Plane)} := by
    rw [hbase]
    rfl
  rw [hopen, hfailed, Finset.union_empty, Finset.coe_singleton]
  calc
    benchmark ≤ pinnedProb (fun _ : Plane => successParam) {0} (fun _ => True)
        (BDDom.Safe.targetConn (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n)) :=
      benchmark_le_pinned_safeTargetConn n
    _ = pinnedProb (fun _ : Plane => successParam) {0} (fun v => v ∈ ({0} : Finset Plane))
        (BDDom.Safe.targetConn (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n)) := by
      symm
      apply pinnedProb_congr_val
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst v
      simp

/-- Slab soundness with the safe benchmark discharged once and for all.  The caller now supplies
only the physical accepted exploration and its history-uniform step estimate at `successParam`.
-/
theorem certificateSound2_of_adaptive_safe {d : Nat} [NeZero d] (hd : 3 ≤ d)
    (hs : forall (C : LeftImp2.Certificate2 d) (q : unitInterval),
      C.WellFormed → C.ValidAt2 q →
      exists (r t : Nat) (delta : Real)
        (h0 : CoreAdaptSound.Tr (Site d) Plane)
        (E : forall n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
          (box 2 n) 0 (MacroExp.tgt n)),
        0 < r ∧ 2 * t ≤ C.width ∧
        h0.base = MacroExp.start d r t ∧ h0.failed = ∅ ∧
        (forall n, (E n).density = fun _ : Site d => q) ∧
        (forall n, (E n).Admissible h0) ∧
        (forall n k, (E n).Admissible k → MacroExp.Good d r t k.base q delta) ∧
        (forall n h, (E n).Admissible h →
          ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
          (successParam : Real) ≤ h.prob (fun _ : Site d => q) ((E n).success h))) :
    LeftImp2.CertificateSound2 d := by
  apply CoreAdaptSound.certificateSound2_of_adaptive hd
  intro C q hwf hv
  obtain ⟨r, t, delta, h0, E, hr, ht, hbase, hfailed, hdensity, hstart,
    hadmGood, hstep⟩ := hs C q hwf hv
  exact ⟨r, t, successParam, benchmark, delta, h0, E, hr, ht, benchmark_pos,
    hbase, hfailed, hdensity, hstart, hadmGood,
    (fun n => benchmark_le_bern_of_start r t n h0 hbase hfailed), hstep⟩

#print axioms KNAll.Site.CoreSafe.iid_safe_percolates_origin
#print axioms KNAll.Site.CoreSafe.benchmark_le_pinned_safeTargetConn
#print axioms KNAll.Site.CoreSafe.benchmark_le_bern_of_start
#print axioms KNAll.Site.CoreSafe.certificateSound2_of_adaptive_safe

end KNAll.Site.CoreSafe

end
