import Hypergraph.PlanarComparison
import Percolation.Literature.SitePaths

/-!
# Three-by-three blocks for bounded-damage exploration

A failed macro trial at `z : ℤ²` is allowed to close vertices only in the closed
nearest-neighbourhood of `z`.  The deterministic repair groups possible failure centres into
disjoint `3 × 3` blocks.  If two adjacent coarse blocks contain no failed centre, the four-vertex
axis segment joining their centres avoids the closed neighbourhood of every failed centre.

The probabilistic part of this file is exact.  The map which declares a block good when all nine
of its failure bits are false sends iid Bernoulli(`η`) failure centres to iid site percolation with
parameter `(1-η)^9`.  At the value needed by the macro proof, `η = 9 / 2^37`, this density is above
the explicit percolating density obtained from incidence parameter `127/128`.

What is deliberately not asserted here is that the adaptive set of failed trial centres has the
iid Bernoulli law.  That is the separate bounded-damage domination theorem: it must couple the
history-uniform conditional failure bound to iid failure bits.  Once such a coupling supplies a
set contained in the iid failure set, the deterministic lemmas below apply directly.
-/

noncomputable section

namespace KNAll.Site.DamageBlocks

open MeasureTheory Set ProbabilityTheory
open Percolation.Literature Percolation.Literature.LatticeModels

abbrev Plane := Site 2
abbrev Offset := Fin 2 → Fin 3

/-- The fine-lattice vertex in coarse block `z` with coordinate offset `u ∈ {0,1,2}²`. -/
def fineOfBlock (zu : Plane × Offset) : Plane :=
  fun j => 3 * zu.1 j + (zu.2 j : ℕ)

/-- The `3 × 3` block indexed by `z`. -/
def block (z : Plane) : Set Plane :=
  fineOfBlock '' ({z} ×ˢ Set.univ)

/-- The central fine vertex of the block indexed by `z`. -/
def center (z : Plane) : Plane := fun j => 3 * z j + 1

/-- The `k`-th point of the positive coordinate segment starting at the centre of `z`. -/
def segmentPoint (z : Plane) (i : Fin 2) (k : ℤ) : Plane :=
  center z + Pi.single i k

@[simp] theorem fineOfBlock_apply (z : Plane) (u : Offset) (j : Fin 2) :
    fineOfBlock (z, u) j = 3 * z j + (u j : ℕ) := rfl

@[simp] theorem center_apply (z : Plane) (j : Fin 2) : center z j = 3 * z j + 1 := rfl

@[simp] theorem segmentPoint_apply (z : Plane) (i j : Fin 2) (k : ℤ) :
    segmentPoint z i k j = 3 * z j + 1 + if i = j then k else 0 := by
  simp only [segmentPoint, center, Pi.add_apply, Pi.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Euclidean division by three recovers both the block and offset coordinates. -/
theorem fineOfBlock_injective : Function.Injective fineOfBlock := by
  rintro ⟨z, u⟩ ⟨z', u'⟩ h
  have hz : z = z' := by
    funext j
    have hj := congrFun h j
    have hu0 : 0 ≤ (u j : ℕ) := Nat.zero_le _
    have hu2 : (u j : ℕ) ≤ 2 := Nat.le_pred_of_lt (u j).isLt
    have hu0' : 0 ≤ (u' j : ℕ) := Nat.zero_le _
    have hu2' : (u' j : ℕ) ≤ 2 := Nat.le_pred_of_lt (u' j).isLt
    simp only [fineOfBlock_apply] at hj
    omega
  subst z'
  have hu : u = u' := by
    funext j
    apply Fin.ext
    have hj := congrFun h j
    simp only [fineOfBlock_apply] at hj
    omega
  subst u'
  rfl

/-- Membership in a block is the coordinate box `3z_j ≤ x_j ≤ 3z_j+2`. -/
theorem mem_block_iff (z x : Plane) :
    x ∈ block z ↔ ∀ j, 3 * z j ≤ x j ∧ x j ≤ 3 * z j + 2 := by
  constructor
  · rintro ⟨⟨z', u⟩, ⟨rfl, -⟩, rfl⟩ j
    simp only [fineOfBlock_apply]
    have hu0 : 0 ≤ (u j : ℕ) := Nat.zero_le _
    have hu2 : (u j : ℕ) ≤ 2 := Nat.le_pred_of_lt (u j).isLt
    omega
  · intro h
    let u : Offset := fun j => ⟨Int.toNat (x j - 3 * z j), by
      have hj := h j
      omega⟩
    refine ⟨(z, u), ⟨rfl, Set.mem_univ u⟩, ?_⟩
    funext j
    simp only [fineOfBlock_apply, u]
    have hj := h j
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ x j - 3 * z j)]
    omega

@[simp] theorem center_mem_block (z : Plane) : center z ∈ block z := by
  rw [mem_block_iff]
  intro j
  simp [center]

/-- Distinct coarse indices give disjoint blocks. -/
theorem disjoint_block_of_ne {z z' : Plane} (hne : z ≠ z') : Disjoint (block z) (block z') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_block_iff] at hx hx'
  apply hne
  funext j
  have h1 := hx j
  have h2 := hx' j
  omega

/-- A configuration of failed fine vertices induces the configuration of blocks containing no
failed vertex. -/
def goodBlocks (failed : Set Plane) : Set Plane :=
  {z | ∀ u : Offset, fineOfBlock (z, u) ∉ failed}

theorem goodBlocks_eq_grouped (failed : Set Plane) :
    goodBlocks failed = {z | ∀ u : Offset, ¬ fineOfBlock (z, u) ∈ failed} := rfl

/-! ## Deterministic damage avoidance -/

/-- The sites spoiled by failed trial centres: a failed centre itself and all of its lattice
neighbours. -/
def damaged (failed : Set Plane) : Set Plane :=
  {x | ∃ f ∈ failed, f = x ∨ (zdGraph 2).Adj f x}

/-- The fine sites not spoiled by any failed trial centre. -/
def safe (failed : Set Plane) : Set Plane := (damaged failed)ᶜ

theorem not_failed_of_goodBlock {failed : Set Plane} {z x : Plane}
    (hz : z ∈ goodBlocks failed) (hx : x ∈ block z) : x ∉ failed := by
  obtain ⟨⟨z', u⟩, ⟨rfl, -⟩, rfl⟩ := hx
  exact hz u

/-- The closed nearest-neighbourhood of each point on the four-vertex centre-to-centre segment is
contained in the union of the two adjacent `3 × 3` blocks.  This is the reason for using side
length three. -/
theorem closedNeighbor_segmentPoint_mem_blocks (z : Plane) (i : Fin 2) {k : ℤ}
    (hk0 : 0 ≤ k) (hk3 : k ≤ 3) {x : Plane}
    (hx : x = segmentPoint z i k ∨ (zdGraph 2).Adj x (segmentPoint z i k)) :
    x ∈ block z ∪ block (z + Pi.single i 1) := by
  have hb : ∀ j : Fin 2,
      3 * z j ≤ x j ∧ x j ≤ 3 * z j + (if i = j then 5 else 2) := by
    rcases hx with rfl | hx
    · intro j
      rw [segmentPoint_apply]
      by_cases hij : i = j
      · simp [hij]
        omega
      · simp [hij]
    · obtain ⟨a, ha | ha⟩ := (zdGraph_adj_iff x (segmentPoint z i k)).1 hx
      · intro j
        have hj := congrFun ha j
        simp only [segmentPoint_apply, Pi.add_apply, Pi.single_apply] at hj
        by_cases hij : i = j <;> by_cases haj : a = j
        · simp [hij, haj] at hj ⊢
          omega
        · simp [hij, haj] at hj ⊢
          omega
        · simp [hij, haj] at hj ⊢
          omega
        · simp [hij, haj] at hj ⊢
          omega
      · intro j
        have hj := congrFun ha j
        simp only [segmentPoint_apply, Pi.add_apply, Pi.single_apply] at hj
        by_cases hij : i = j <;> by_cases haj : a = j
        · simp [hij, haj] at hj ⊢
          omega
        · simp [hij, haj] at hj ⊢
          omega
        · simp [hij, haj] at hj ⊢
          omega
        · simp [hij, haj] at hj ⊢
          omega
  by_cases hleft : x i ≤ 3 * z i + 2
  · left
    rw [mem_block_iff]
    intro j
    have hj := hb j
    by_cases hij : i = j
    · subst j
      exact ⟨hj.1, hleft⟩
    · simpa [hij] using hj
  · right
    rw [mem_block_iff]
    intro j
    have hj := hb j
    by_cases hij : i = j
    · subst j
      simp only [Pi.add_apply, Pi.single_eq_same]
      constructor <;> omega
    · have hji : j ≠ i := Ne.symm hij
      simp only [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero]
      simpa [hij] using hj

/-- The closed neighbourhood of a block centre is contained in that block. -/
theorem closedNeighbor_center_mem_block (z : Plane) {x : Plane}
    (hx : x = center z ∨ (zdGraph 2).Adj x (center z)) : x ∈ block z := by
  rw [mem_block_iff]
  rcases hx with rfl | hx
  · intro j
    simp [center]
  · obtain ⟨a, ha | ha⟩ := (zdGraph_adj_iff x (center z)).1 hx
    · intro j
      have hj := congrFun ha j
      simp only [center_apply, Pi.add_apply, Pi.single_apply] at hj
      by_cases haj : a = j
      · simp [haj] at hj ⊢
        omega
      · simp [Ne.symm haj] at hj
        omega
    · intro j
      have hj := congrFun ha j
      simp only [center_apply, Pi.add_apply, Pi.single_apply] at hj
      by_cases haj : a = j
      · simp [haj] at hj ⊢
        omega
      · simp [Ne.symm haj] at hj
        omega

/-- The centre of a good block is safe, without any assumption on neighbouring blocks. -/
theorem center_mem_safe_of_goodBlock {failed : Set Plane} {z : Plane}
    (hz : z ∈ goodBlocks failed) : center z ∈ safe failed := by
  intro hdamage
  obtain ⟨f, hf, hfc⟩ := hdamage
  exact (not_failed_of_goodBlock hz (closedNeighbor_center_mem_block z hfc)) hf

/-- Consecutive points of the centre-to-centre segment are nearest neighbours. -/
theorem segmentPoint_adj (z : Plane) (i : Fin 2) (k : ℤ) :
    (zdGraph 2).Adj (segmentPoint z i k) (segmentPoint z i (k + 1)) := by
  rw [zdGraph_adj_iff]
  refine ⟨i, Or.inl ?_⟩
  funext j
  by_cases hij : i = j
  · simp [segmentPoint, center, Pi.single_apply, hij]
    ring
  · simp [segmentPoint, center, Pi.single_apply, hij, Ne.symm hij]

theorem segmentPoint_zero (z : Plane) (i : Fin 2) : segmentPoint z i 0 = center z := by
  funext j
  simp [segmentPoint, center]

theorem segmentPoint_three (z : Plane) (i : Fin 2) :
    segmentPoint z i 3 = center (z + Pi.single i 1) := by
  funext j
  rw [segmentPoint_apply, center_apply]
  by_cases hij : i = j
  · subst j
    simp
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-- Every point of the centre segment is safe when both adjacent blocks are good. -/
theorem segmentPoint_mem_safe {failed : Set Plane} (z : Plane) (i : Fin 2)
    (hz : z ∈ goodBlocks failed) (hz' : z + Pi.single i 1 ∈ goodBlocks failed)
    {k : ℤ} (hk0 : 0 ≤ k) (hk3 : k ≤ 3) :
    segmentPoint z i k ∈ safe failed := by
  intro hdamage
  obtain ⟨f, hf, hfx⟩ := hdamage
  have hblocks := closedNeighbor_segmentPoint_mem_blocks z i hk0 hk3
    (show f = segmentPoint z i k ∨ (zdGraph 2).Adj f (segmentPoint z i k) from hfx)
  rcases hblocks with hfz | hfz'
  · exact (not_failed_of_goodBlock hz hfz) hf
  · exact (not_failed_of_goodBlock hz' hfz') hf

/-- **Positive-direction block bridge.**  The centres of two consecutive good blocks are joined by
a nearest-neighbour path entirely outside the damage set. -/
theorem pathIn_safe_center_add_single {failed : Set Plane} (z : Plane) (i : Fin 2)
    (hz : z ∈ goodBlocks failed) (hz' : z + Pi.single i 1 ∈ goodBlocks failed) :
    PathIn (zdGraph 2) (safe failed) (center z) (center (z + Pi.single i 1)) := by
  have h0 := segmentPoint_mem_safe z i hz hz' (k := (0 : ℤ)) (by omega) (by omega)
  have h1 := segmentPoint_mem_safe z i hz hz' (k := (1 : ℤ)) (by omega) (by omega)
  have h2 := segmentPoint_mem_safe z i hz hz' (k := (2 : ℤ)) (by omega) (by omega)
  have h3 := segmentPoint_mem_safe z i hz hz' (k := (3 : ℤ)) (by omega) (by omega)
  have hp : PathIn (zdGraph 2) (safe failed) (segmentPoint z i 0) (segmentPoint z i 3) :=
    (((PathIn.refl h0).tail (segmentPoint_adj z i 0) h1).tail
      (segmentPoint_adj z i 1) h2).tail (segmentPoint_adj z i 2) h3
  simpa [segmentPoint_zero, segmentPoint_three] using hp

/-- **Adjacent good-block bridge.**  For either orientation of a coarse lattice edge, the block
centres are connected through fine sites avoiding the closed neighbourhood of every failure
centre. -/
theorem pathIn_safe_centers_of_adj {failed : Set Plane} {z z' : Plane}
    (hzz' : (zdGraph 2).Adj z z')
    (hz : z ∈ goodBlocks failed) (hz' : z' ∈ goodBlocks failed) :
    PathIn (zdGraph 2) (safe failed) (center z) (center z') := by
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff z z').1 hzz'
  · subst z'
    exact pathIn_safe_center_add_single z i hz hz'
  · subst z
    exact (pathIn_safe_center_add_single z' i hz' hz).symm

/-- A path in the site graph is a reachability witness in the corresponding open-site graph. -/
theorem reachable_openSiteGraph_of_pathIn {V : Type*} {G : SimpleGraph V} {A : Set V} {x y : V}
    (h : PathIn G A x y) : (openSiteGraph G A).Reachable x y := by
  obtain ⟨hx, hxy⟩ := h
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hxb hbc ih =>
      have hb : b ∈ A := PathIn.right_mem ⟨hx, hxb⟩
      exact ih.tail ((openSiteGraph_adj_iff' G A b c).2 ⟨hbc.1, hb, hbc.2⟩)

/-- Multiplication by three followed by translation is injective. -/
theorem center_injective : Function.Injective center := by
  intro z z' h
  funext j
  have hj := congrFun h j
  simp only [center_apply] at hj
  omega

/-- Coarse good-site reachability lifts to safe fine-site reachability between block centres. -/
theorem reachable_safe_centers {failed : Set Plane} {z z' : Plane}
    (h : (openSiteGraph (zdGraph 2) (goodBlocks failed)).Reachable z z') :
    (openSiteGraph (zdGraph 2) (safe failed)).Reachable (center z) (center z') := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hzb hbc ih =>
      obtain ⟨hbcG, hb, hc⟩ := (openSiteGraph_adj_iff' (zdGraph 2)
        (goodBlocks failed) b c).1 hbc
      have hp := pathIn_safe_centers_of_adj hbcG hb hc
      have hr := reachable_openSiteGraph_of_pathIn hp
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      exact ih.trans hr

/-- An infinite good coarse cluster supplies infinitely many distinct safe fine-lattice centres. -/
theorem infinite_safeCluster_of_goodBlocks {failed : Set Plane}
    (h : (siteCluster (zdGraph 2) (goodBlocks failed) 0).Infinite) :
    (siteCluster (zdGraph 2) (safe failed) (center 0)).Infinite := by
  have himage : (center '' siteCluster (zdGraph 2) (goodBlocks failed) 0).Infinite :=
    h.image center_injective.injOn
  refine himage.mono ?_
  rintro x ⟨z, hz, rfl⟩
  exact ⟨center_mem_safe_of_goodBlock hz.1, reachable_safe_centers hz.2⟩

/-! ## Exact iid block map -/

/-- Probability that all nine coordinates in one block are false. -/
theorem infinitePi_offset_all_false (eta : unitInterval) :
    (Measure.infinitePi fun _ : Offset => Ber(True, False, eta))
        {q : Offset → Prop | ∀ u, ¬ q u}
      = ENNReal.ofReal ((1 - (eta : ℝ)) ^ 9) := by
  have hnonneg : (0 : ℝ) ≤ 1 - (eta : ℝ) := by linarith [eta.2.2]
  have hset : {q : Offset → Prop | ∀ u, ¬ q u}
      = Set.univ.pi (fun _ : Offset => ({False} : Set Prop)) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_singleton_iff, eq_iff_iff, iff_false]
  have hcard : Fintype.card Offset = 9 := by
    simp [Offset, Fintype.card_fun]
  rw [hset, Measure.infinitePi_eq_pi, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    hcard, bernoulliMeasure_prop_apply_false, ENNReal.ofReal_pow hnonneg]

/-- The iid density of good `3 × 3` blocks. -/
def goodParam (eta : unitInterval) : unitInterval :=
  ⟨(1 - (eta : ℝ)) ^ 9, by
    constructor
    · exact pow_nonneg (by linarith [eta.2.2]) _
    · exact pow_le_one₀ (by linarith [eta.2.2]) (by linarith [eta.2.1])⟩

@[simp] theorem coe_goodParam (eta : unitInterval) :
    ((goodParam eta : unitInterval) : ℝ) = (1 - (eta : ℝ)) ^ 9 := rfl

/-- **Disjoint blocks remain independent.**  Iid failure centres of density `eta` produce iid good
blocks of density `(1-eta)^9`. -/
theorem prodBernoulli_map_goodBlocks (eta : unitInterval) :
    (prodBernoulli fun _ : Plane => eta).map goodBlocks
      = prodBernoulli fun _ : Plane => goodParam eta := by
  have hPhi : ∀ _z : Plane, Measurable fun q : Offset → Prop => ∀ u, ¬ q u :=
    fun _ => Measurable.forall fun u => (measurable_pi_apply u).not
  exact prodBernoulli_map_grouped fineOfBlock_injective eta
    (fun _z q => ∀ u, ¬ q u) hPhi (fun _ => goodParam eta)
    (fun _ => infinitePi_offset_all_false eta)

theorem measurable_goodBlocks : Measurable goodBlocks := by
  refine measurable_set_iff.2 fun z => ?_
  exact Measurable.forall fun u => (measurable_set_mem (fineOfBlock (z, u))).not

theorem measurable_safe : Measurable safe := by
  refine measurable_set_iff.2 fun x => ?_
  exact (Measurable.exists fun f =>
    (measurable_set_mem f).and (measurable_const.or measurable_const)).not

/-! ## The explicit density comparison -/

/-- Incidence density `127/128`; its square is still at least the bond-Peierls threshold `63/64`.
It induces site density exactly `1-2^-28` in dimension two. -/
def blockIncParam : unitInterval := ⟨127 / 128, by norm_num, by norm_num⟩

@[simp] theorem coe_blockIncParam : ((blockIncParam : unitInterval) : ℝ) = 127 / 128 := rfl

theorem thetaSite_blockIncParam_pos : 0 < thetaSite 2 (siteParam 2 blockIncParam) := by
  have hq : 0 < theta (zdGraph 2) 0 (bondParam blockIncParam) :=
    theta_zd_pos_of_le le_rfl (bondParam blockIncParam)
      (by rw [coe_bondParam, coe_blockIncParam]; norm_num)
  have hbond := prodBernoulli_map_bondOfInc 2 blockIncParam
  have hsite := prodBernoulli_map_siteOfInc 2 blockIncParam
  have hmb := measurable_bondOfInc 2
  have hms := measurable_siteOfInc 2
  have hsub : bondOfInc 2 ⁻¹' (percolatesAt (0 : Plane))
      ⊆ siteOfInc 2 ⁻¹' {ω : SiteConfig Plane | (siteCluster (zdGraph 2) ω 0).Infinite} :=
    fun ω hω => infinite_siteCluster_of_percolatesAt 2 ω hω
  have hth : theta (zdGraph 2) 0 (bondParam blockIncParam)
      = ((prodBernoulli fun _ : Inc 2 => blockIncParam).map (bondOfInc 2)).real
          (percolatesAt (0 : Plane)) := by
    rw [hbond]
    rfl
  have hts : thetaSite 2 (siteParam 2 blockIncParam)
      = ((prodBernoulli fun _ : Inc 2 => blockIncParam).map (siteOfInc 2)).real
          {ω : SiteConfig Plane | (siteCluster (zdGraph 2) ω 0).Infinite} := by
    rw [hsite]
    rfl
  calc
    (0 : ℝ) < theta (zdGraph 2) 0 (bondParam blockIncParam) := hq
    _ = (prodBernoulli fun _ : Inc 2 => blockIncParam).real
          (bondOfInc 2 ⁻¹' percolatesAt (0 : Plane)) := by
        rw [hth, map_measureReal_apply hmb (measurableSet_percolatesAt_holds 0)]
    _ ≤ (prodBernoulli fun _ : Inc 2 => blockIncParam).real
          (siteOfInc 2 ⁻¹' {ω : SiteConfig Plane | (siteCluster (zdGraph 2) ω 0).Infinite}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = thetaSite 2 (siteParam 2 blockIncParam) := by
        rw [hts, map_measureReal_apply hms (measurableSet_siteInfinite _ _)]

theorem siteParam_blockIncParam_eq :
    ((siteParam 2 blockIncParam : unitInterval) : ℝ) = 1 - 1 / 2 ^ 28 := by
  rw [coe_siteParam, coe_blockIncParam]
  norm_num

/-- The worst batch-failure density from the macro proof: `rho=2^-32` and
`eta=9*rho/32=9*2^-37`. -/
def etaMax : unitInterval := ⟨9 / 2 ^ 37, by norm_num, by norm_num⟩

@[simp] theorem coe_etaMax : ((etaMax : unitInterval) : ℝ) = 9 / 2 ^ 37 := rfl

/-- The good-block density at the worst allowed failure rate exceeds `1-2^-28`. -/
theorem siteParam_blockIncParam_le_goodParam :
    siteParam 2 blockIncParam ≤ goodParam etaMax := by
  change (((siteParam 2 blockIncParam : unitInterval) : ℝ) ≤
    ((goodParam etaMax : unitInterval) : ℝ))
  rw [coe_goodParam, siteParam_blockIncParam_eq, coe_etaMax]
  norm_num

/-- Consequently iid good blocks percolate at the exact density produced by the worst failure
budget. -/
theorem thetaSite_goodParam_etaMax_pos : 0 < thetaSite 2 (goodParam etaMax) :=
  thetaSite_pos_of_le siteParam_blockIncParam_le_goodParam thetaSite_blockIncParam_pos

/-- **The complete iid block repair.**  If failure centres are iid at the worst density allowed by
the batch estimate, the complement of their closed graph-neighbourhood has an infinite cluster
through the centre of the origin block with positive probability. -/
theorem iid_safe_percolates_etaMax :
    0 < (prodBernoulli fun _ : Plane => etaMax).real
      {failed : Set Plane | (siteCluster (zdGraph 2) (safe failed) (center 0)).Infinite} := by
  let EGood : Set (Set Plane) :=
    {ω | (siteCluster (zdGraph 2) ω 0).Infinite}
  let ESafe : Set (Set Plane) :=
    {ω | (siteCluster (zdGraph 2) ω (center 0)).Infinite}
  have hmGood : MeasurableSet EGood := measurableSet_siteInfinite _ _
  have hmSafe : MeasurableSet ESafe := measurableSet_siteInfinite _ _
  have hsub : goodBlocks ⁻¹' EGood ⊆ safe ⁻¹' ESafe := by
    intro failed hf
    exact infinite_safeCluster_of_goodBlocks hf
  have hmap := prodBernoulli_map_goodBlocks etaMax
  calc
    (0 : ℝ) < thetaSite 2 (goodParam etaMax) := thetaSite_goodParam_etaMax_pos
    _ = ((prodBernoulli fun _ : Plane => etaMax).map goodBlocks).real EGood := by
        rw [hmap]
        rfl
    _ = (prodBernoulli fun _ : Plane => etaMax).real (goodBlocks ⁻¹' EGood) := by
        rw [map_measureReal_apply measurable_goodBlocks hmGood]
    _ ≤ (prodBernoulli fun _ : Plane => etaMax).real (safe ⁻¹' ESafe) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = (prodBernoulli fun _ : Plane => etaMax).real
          {failed : Set Plane |
            (siteCluster (zdGraph 2) (safe failed) (center 0)).Infinite} := rfl

end KNAll.Site.DamageBlocks

end
