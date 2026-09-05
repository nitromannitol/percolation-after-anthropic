import Hypergraph.SiteStatements

/-!
# Site percolation on `ℤ^d` percolates at a parameter below one

The development proves Peierls' estimate for **bond** percolation
(`Percolation.Literature.theta_zd_pos_of_le`: `θ(ℤ^d, p) > 0` for `d ≥ 2` and `p ≥ 63/64`).  This
file transfers it to **site** percolation, producing a parameter `a < 1` at which the origin of
`ℤ^d` percolates in the site model:

    `exists_thetaSite_pos : 2 ≤ d → ∃ a : unitInterval, (a : ℝ) < 1 ∧ 0 < thetaSite d a`.

The transfer is the half-edge coupling.  Index the incidences of the lattice by pairs
`(e, b) : Sym2 (Site d) × Bool`, an edge together with a label for one of its two ends, and give
every incidence an independent Bernoulli variable with parameter `r`.  Declare

* an **edge** open when both of its incidences are on: distinct edges use disjoint pairs of
  incidences, so the edge variables are independent with parameter `r²`
  (`prodBernoulli_map_bondOfInc`);
* a **vertex** open when at least one of the `2d` incidences at it is on: the incidence at `v` of
  the edge leaving `v` along the axis `j` in the direction `b` is `vertInc d (v, j, b)`, and
  `vertInc d` is injective (`vertInc_injective`), so distinct vertices use disjoint sets of
  incidences and the vertex variables are independent with parameter `1 - (1-r)^{2d}`
  (`prodBernoulli_map_siteOfInc`).

If an edge is open then both of its endpoints are open (`siteOfInc_of_mem_bondOfInc`), so an
infinite open bond cluster of the origin forces an infinite open site cluster of the origin
(`infinite_siteCluster_of_percolatesAt`).  With `r = 255/256` one has `r² ≥ 63/64`, and the
resulting site parameter `1 - (1/256)^{2d}` is below `1`.

Both pushforward computations go through the single lemma `prodBernoulli_map_blockMap`: a
configuration on a product index type `ι × κ` is read block by block, one block `{i} × κ` for each
`i`, and the resulting configuration on `ι` is again a product Bernoulli measure, with parameter the
probability that a block satisfies the reading rule.  This mirrors the technique of
`siteBernoulli_map_restrictSite` in `KN/SiteStatements.lean`: rewrite `prodBernoulli` through
`prodBernoulli_eq_map`, work with `MeasureTheory.Measure.infinitePi`, and identify the image measure
coordinatewise (`Measure.infinitePi_map_curry`, `Measure.infinitePi_map_pi`).
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set ProbabilityTheory
open Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Probability measures on `Prop` -/

/-- A probability measure on `Prop` is the Bernoulli law of the mass it gives to `True`. -/
theorem eq_bernoulliMeasure_of_apply_true {m : Measure Prop} [IsProbabilityMeasure m]
    (a : unitInterval) (h : m {True} = ENNReal.ofReal (a : ℝ)) :
    m = Ber(True, False, a) := by
  have hcompl : ({False} : Set Prop) = ({True} : Set Prop)ᶜ := by
    ext x
    by_cases hx : x
    · simp [hx]
    · simp [hx]
  refine Measure.ext_of_singleton fun p => ?_
  by_cases hp : p
  · rw [eq_true hp, h, bernoulliMeasure_prop_apply_true]
  · rw [eq_false hp, hcompl, prob_compl_eq_one_sub (measurableSet_singleton True),
      prob_compl_eq_one_sub (measurableSet_singleton True), h, bernoulliMeasure_prop_apply_true]

/-- `prodBernoulli` as a pushforward, with the one-coordinate factor named as Mathlib's Bernoulli
law on `Prop`. -/
theorem prodBernoulli_eq_map' {ι : Type*} (p : ι → unitInterval) :
    prodBernoulli p = Measure.map (fun q : ι → Prop => {i | q i})
      (Measure.infinitePi fun i : ι => Ber(True, False, p i)) :=
  prodBernoulli_eq_map p

/-- Two infinite products of probability measures with the same factors agree. -/
theorem infinitePi_congr {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {μ ν : (i : ι) → Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (h : μ = ν) :
    Measure.infinitePi μ = Measure.infinitePi ν := by
  subst h; rfl

/-! ## Reading a product configuration block by block -/

section Grouping

variable {ι κ : Type*}

/-- The block reading map: `i` is retained exactly when the block `{i} × κ` of the configuration
satisfies `Φ i`. -/
def blockMap (Φ : ι → (κ → Prop) → Prop) (ω : Set (ι × κ)) : Set ι :=
  {i | Φ i fun k => (i, k) ∈ ω}

theorem measurable_blockMap {Φ : ι → (κ → Prop) → Prop} (hΦ : ∀ i, Measurable (Φ i)) :
    Measurable (blockMap Φ) := by
  refine measurable_set_iff.2 fun i => ?_
  have h : Measurable fun ω : Set (ι × κ) => fun k : κ => (i, k) ∈ ω :=
    measurable_pi_lambda _ fun k => measurable_set_mem (i, k)
  exact (hΦ i).comp h

/-- **The block pushforward.**  Under `prodBernoulli` with constant parameter `r` on `ι × κ`, the
blocks `{i} × κ` are independent, so reading each block through `Φ i` gives back a product Bernoulli
measure on `ι`, whose parameter at `i` is the probability that a block satisfies `Φ i`. -/
theorem prodBernoulli_map_blockMap (r : unitInterval) (Φ : ι → (κ → Prop) → Prop)
    (hΦ : ∀ i, Measurable (Φ i)) (a : ι → unitInterval)
    (ha : ∀ i, (Measure.infinitePi fun _ : κ => Ber(True, False, r)) {q | Φ i q}
      = ENNReal.ofReal (a i : ℝ)) :
    (prodBernoulli fun _ : ι × κ => r).map (blockMap Φ) = prodBernoulli a := by
  have hmapΦ : ∀ i, (Measure.infinitePi fun _ : κ => Ber(True, False, r)).map (Φ i)
      = Ber(True, False, a i) := by
    intro i
    haveI : IsProbabilityMeasure
        ((Measure.infinitePi fun _ : κ => Ber(True, False, r)).map (Φ i)) :=
      Measure.isProbabilityMeasure_map (hΦ i).aemeasurable
    refine eq_bernoulliMeasure_of_apply_true (a i) ?_
    rw [Measure.map_apply (hΦ i) (measurableSet_singleton True), Set.preimage_singleton_true]
    exact ha i
  haveI hprob : ∀ i : ι, IsProbabilityMeasure
      ((Measure.infinitePi fun _ : κ => Ber(True, False, r)).map (Φ i)) := fun i =>
    Measure.isProbabilityMeasure_map (hΦ i).aemeasurable
  have hF2 : Measurable (fun g : ι → κ → Prop => fun i => Φ i (g i)) :=
    measurable_pi_lambda _ fun i => (hΦ i).comp (measurable_pi_apply i)
  have hcurry : Measurable ⇑(MeasurableEquiv.curry ι κ Prop) :=
    (MeasurableEquiv.curry ι κ Prop).measurable
  have h1 : (Measure.infinitePi fun _ : ι × κ => Ber(True, False, r)).map
      ⇑(MeasurableEquiv.curry ι κ Prop)
      = Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : κ => Ber(True, False, r) :=
    Measure.infinitePi_map_curry (fun _ _ => Ber(True, False, r))
  have h2 : (Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : κ =>
        Ber(True, False, r)).map (fun g : ι → κ → Prop => fun i => Φ i (g i))
      = Measure.infinitePi fun i : ι => Ber(True, False, a i) := by
    rw [Measure.infinitePi_map_pi
      (μ := fun _ : ι => Measure.infinitePi fun _ : κ => Ber(True, False, r)) hΦ]
    exact infinitePi_congr (funext hmapΦ)
  have hcomp : (blockMap Φ ∘ fun q : ι × κ → Prop => {p | q p})
      = ((fun q : ι → Prop => {i | q i}) ∘
          ((fun g : ι → κ → Prop => fun i => Φ i (g i)) ∘ ⇑(MeasurableEquiv.curry ι κ Prop))) :=
    rfl
  rw [prodBernoulli_eq_map' (fun _ : ι × κ => r),
    Measure.map_map (measurable_blockMap hΦ) measurable_setOf, hcomp,
    ← Measure.map_map measurable_setOf (hF2.comp hcurry),
    ← Measure.map_map hF2 hcurry, h1, h2]
  exact (prodBernoulli_eq_map' a).symm

/-- **The block pushforward through an injective indexing of the incidences.**  The blocks need not
exhaust the index type: it is enough that the incidences used by the different blocks are pairwise
distinct. -/
theorem prodBernoulli_map_grouped {I : Type*} {g : ι × κ → I} (hg : Function.Injective g)
    (r : unitInterval) (Φ : ι → (κ → Prop) → Prop) (hΦ : ∀ i, Measurable (Φ i))
    (a : ι → unitInterval)
    (ha : ∀ i, (Measure.infinitePi fun _ : κ => Ber(True, False, r)) {q | Φ i q}
      = ENNReal.ofReal (a i : ℝ)) :
    (prodBernoulli fun _ : I => r).map (fun ω : Set I => {i | Φ i fun k => g (i, k) ∈ ω})
      = prodBernoulli a := by
  have hstep : (prodBernoulli fun _ : I => r).map (restrictSite g)
      = prodBernoulli fun _ : ι × κ => r := siteBernoulli_map_restrictSite hg r
  have hcomp : (fun ω : Set I => {i | Φ i fun k => g (i, k) ∈ ω})
      = blockMap Φ ∘ restrictSite g := rfl
  rw [hcomp, ← Measure.map_map (measurable_blockMap hΦ) (measurable_restrictSite g), hstep]
  exact prodBernoulli_map_blockMap r Φ hΦ a ha

end Grouping

/-! ## The incidences of `ℤ^d` -/

/-- An incidence of the lattice: an edge together with a label for one of its two ends. -/
abbrev Inc (d : ℕ) : Type := Sym2 (Site d) × Bool

/-- The step from a vertex along the axis `j`, forwards when `b` is `true`. -/
def incStep (d : ℕ) (j : Fin d) (b : Bool) : Site d :=
  if b then Pi.single j 1 else -Pi.single j 1

@[simp] theorem incStep_true (d : ℕ) (j : Fin d) : incStep d j true = Pi.single j 1 := rfl

@[simp] theorem incStep_false (d : ℕ) (j : Fin d) : incStep d j false = -Pi.single j 1 := rfl

/-- The incidence at `v` of the edge leaving `v` along the axis `j` in the direction `b`.  The
label of the end is `b` itself: the end of an edge at its smaller vertex carries `true`, the end at
its larger vertex carries `false`. -/
def vertInc (d : ℕ) (x : Site d × Fin d × Bool) : Inc d :=
  (s(x.1, x.1 + incStep d x.2.1 x.2.2), x.2.2)

@[simp] theorem vertInc_apply (d : ℕ) (v : Site d) (j : Fin d) (b : Bool) :
    vertInc d (v, j, b) = (s(v, v + incStep d j b), b) := rfl

theorem single_add_single_ne_zero {d : ℕ} (j j' : Fin d) :
    (Pi.single j (1 : ℤ) : Site d) + Pi.single j' 1 ≠ 0 := by
  intro h
  have hj := congrFun h j
  rw [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at hj
  have hnn : (0 : ℤ) ≤ (Pi.single j' (1 : ℤ) : Site d) j := by
    rw [Pi.single_apply]
    split_ifs <;> norm_num
  omega

theorem single_inj_of_eq {d : ℕ} {j j' : Fin d}
    (h : (Pi.single j (1 : ℤ) : Site d) = Pi.single j' 1) : j = j' := by
  by_contra hne
  have hj := congrFun h j
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hj
  exact one_ne_zero hj

theorem incStep_add_ne_zero {d : ℕ} (j j' : Fin d) (b : Bool) :
    incStep d j' b + incStep d j b ≠ 0 := by
  cases b with
  | true => simpa using single_add_single_ne_zero j' j
  | false =>
    simp only [incStep_false]
    intro h
    refine single_add_single_ne_zero j' j ?_
    have hneg : -((Pi.single j' (1 : ℤ) : Site d) + Pi.single j 1) = 0 := by
      rw [neg_add]; exact h
    exact neg_eq_zero.mp hneg

theorem incStep_inj {d : ℕ} {j j' : Fin d} {b : Bool} (h : incStep d j b = incStep d j' b) :
    j = j' := by
  cases b with
  | true => exact single_inj_of_eq (by simpa using h)
  | false =>
    refine single_inj_of_eq ?_
    simp only [incStep_false] at h
    exact neg_injective h

/-- **Distinct vertices use distinct incidences.**  The two ends of an edge of `ℤ^d` carry different
labels, and from the label together with the edge the vertex and the axis can be recovered. -/
theorem vertInc_injective (d : ℕ) : Function.Injective (vertInc d) := by
  rintro ⟨v, j, b⟩ ⟨v', j', b'⟩ h
  rw [vertInc_apply, vertInc_apply, Prod.mk.injEq] at h
  obtain ⟨hsym, hb⟩ := h
  subst hb
  rw [Sym2.eq_iff] at hsym
  rcases hsym with ⟨rfl, h2⟩ | ⟨h1, h2⟩
  · rw [incStep_inj (add_left_cancel h2)]
  · exfalso
    rw [h1] at h2
    refine incStep_add_ne_zero j j' b ?_
    apply add_left_cancel (a := v')
    rw [← add_assoc, add_zero]
    exact h2

/-! ## The two configurations read off from the incidences -/

/-- The bond configuration read off from a configuration of incidences: an edge of `ℤ^d` is open
when both of its incidences are on. -/
def bondOfInc (d : ℕ) (ω : Set (Inc d)) : Set (Sym2 (Site d)) :=
  {e | e ∈ (zdGraph d).edgeSet ∧ (e, true) ∈ ω ∧ (e, false) ∈ ω}

/-- The site configuration read off from a configuration of incidences: a vertex is open when at
least one of its `2d` incidences is on. -/
def siteOfInc (d : ℕ) (ω : Set (Inc d)) : Set (Site d) :=
  {v | ∃ k : Fin d × Bool, vertInc d (v, k) ∈ ω}

theorem measurable_bondOfInc (d : ℕ) : Measurable (bondOfInc d) := by
  refine measurable_set_iff.2 fun e => ?_
  exact measurable_const.and ((measurable_set_mem (e, true)).and (measurable_set_mem (e, false)))

theorem measurable_siteOfInc (d : ℕ) : Measurable (siteOfInc d) := by
  refine measurable_set_iff.2 fun v => ?_
  exact Measurable.exists fun k => measurable_set_mem (vertInc d (v, k))

/-- **An open edge has two open endpoints.**  This is the whole content of the coupling: the
incidence `(e, true)` is the incidence at the smaller end of `e`, the incidence `(e, false)` the one
at its larger end, and the edge is open only when both are on. -/
theorem siteOfInc_of_mem_bondOfInc (d : ℕ) (ω : Set (Inc d)) {x y : Site d}
    (h : s(x, y) ∈ bondOfInc d ω) : x ∈ siteOfInc d ω ∧ y ∈ siteOfInc d ω := by
  obtain ⟨hmem, ht, hf⟩ := h
  have hadj : (zdGraph d).Adj x y := (SimpleGraph.mem_edgeSet _).1 hmem
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff x y).1 hadj
  · refine ⟨⟨(i, true), ?_⟩, ⟨(i, false), ?_⟩⟩
    · have hv : vertInc d (x, i, true) = (s(x, y), true) := by
        rw [vertInc_apply, incStep_true, hi]
      rw [hv]; exact ht
    · have hstep : y + incStep d i false = x := by rw [hi, incStep_false]; simp
      have hv : vertInc d (y, i, false) = (s(x, y), false) := by
        rw [vertInc_apply, hstep, Sym2.eq_swap]
      rw [hv]; exact hf
  · refine ⟨⟨(i, false), ?_⟩, ⟨(i, true), ?_⟩⟩
    · have hstep : x + incStep d i false = y := by rw [hi, incStep_false]; simp
      have hv : vertInc d (x, i, false) = (s(x, y), false) := by
        rw [vertInc_apply, hstep]
      rw [hv]; exact hf
    · have hstep : y + incStep d i true = x := by rw [hi, incStep_true]
      have hv : vertInc d (y, i, true) = (s(x, y), true) := by
        rw [vertInc_apply, hstep, Sym2.eq_swap]
      rw [hv]; exact ht

theorem openSite_adj_of_openBond_adj (d : ℕ) (ω : Set (Inc d)) {u v : Site d}
    (h : (openGraph (bondOfInc d ω)).Adj u v) :
    (openSiteGraph (zdGraph d) (siteOfInc d ω)).Adj u v := by
  rw [openGraph_adj] at h
  obtain ⟨hmem, -⟩ := h
  obtain ⟨hu, hv⟩ := siteOfInc_of_mem_bondOfInc d ω hmem
  exact (openSiteGraph_adj_iff' _ _ _ _).2 ⟨(SimpleGraph.mem_edgeSet _).1 hmem.1, hu, hv⟩

/-- **An infinite open bond cluster of the origin forces an infinite open site cluster of the
origin.**  Every vertex of an open bond path is open in the site configuration, and consecutive
vertices of the path are adjacent in `ℤ^d`. -/
theorem infinite_siteCluster_of_percolatesAt (d : ℕ) (ω : Set (Inc d))
    (h : ω ∈ bondOfInc d ⁻¹' (percolatesAt (0 : Site d))) :
    (siteCluster (zdGraph d) (siteOfInc d ω) 0).Infinite := by
  classical
  have hinf : (openCluster (bondOfInc d ω) (0 : Site d)).Infinite := h
  have hle : openGraph (bondOfInc d ω) ≤ openSiteGraph (zdGraph d) (siteOfInc d ω) := by
    intro u v huv
    exact openSite_adj_of_openBond_adj d ω huv
  have h0 : (0 : Site d) ∈ siteOfInc d ω := by
    obtain ⟨y, hy, hyF⟩ := hinf.exists_notMem_finset {(0 : Site d)}
    have hyne : y ≠ (0 : Site d) := by simpa using hyF
    have hy' : (openGraph (bondOfInc d ω)).Reachable 0 y := hy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hy'
    rcases hy'.cases_head with hcase | ⟨c, hac, -⟩
    · exact absurd hcase.symm hyne
    · exact ((openSiteGraph_adj_iff' _ _ _ _).1 (openSite_adj_of_openBond_adj d ω hac)).2.1
  refine hinf.mono ?_
  intro y hy
  exact ⟨h0, SimpleGraph.Reachable.mono hle hy⟩

/-! ## The two pushforward computations -/

theorem infinitePi_bool_both (r : unitInterval) :
    (Measure.infinitePi fun _ : Bool => Ber(True, False, r)) {q : Bool → Prop | q true ∧ q false}
      = ENNReal.ofReal ((r : ℝ) * r) := by
  have hset : {q : Bool → Prop | q true ∧ q false}
      = Set.univ.pi (fun _ : Bool => ({True} : Set Prop)) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_singleton_iff, eq_iff_iff, iff_true,
      Bool.forall_bool]
    tauto
  rw [hset, Measure.infinitePi_eq_pi, Measure.pi_pi, Fintype.prod_bool,
    bernoulliMeasure_prop_apply_true, ENNReal.ofReal_mul r.2.1]

theorem infinitePi_exists_of_fin (d : ℕ) (r : unitInterval) :
    (Measure.infinitePi fun _ : Fin d × Bool => Ber(True, False, r))
        {q : Fin d × Bool → Prop | ∃ k, q k}
      = ENNReal.ofReal (1 - (1 - (r : ℝ)) ^ (2 * d)) := by
  have hr : (0 : ℝ) ≤ 1 - (r : ℝ) := by have := r.2.2; linarith
  have hnone : {q : Fin d × Bool → Prop | ∀ k, ¬ q k}
      = Set.univ.pi (fun _ : Fin d × Bool => ({False} : Set Prop)) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_singleton_iff, eq_iff_iff, iff_false]
  have hmeas : MeasurableSet {q : Fin d × Bool → Prop | ∀ k, ¬ q k} :=
    (Measurable.forall fun k => (measurable_pi_apply k).not).setOf
  have hcompl : {q : Fin d × Bool → Prop | ∃ k, q k}
      = {q : Fin d × Bool → Prop | ∀ k, ¬ q k}ᶜ := by
    ext q
    constructor
    · rintro ⟨k, hk⟩ hall
      exact hall k hk
    · intro hq
      by_contra hcon
      exact hq fun k hk => hcon ⟨k, hk⟩
  have hcard : Fintype.card (Fin d × Bool) = 2 * d := by
    simp [Fintype.card_prod, mul_comm]
  have hval : (Measure.infinitePi fun _ : Fin d × Bool => Ber(True, False, r))
      {q : Fin d × Bool → Prop | ∀ k, ¬ q k} = ENNReal.ofReal ((1 - (r : ℝ)) ^ (2 * d)) := by
    rw [hnone, Measure.infinitePi_eq_pi, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
      hcard, bernoulliMeasure_prop_apply_false, ENNReal.ofReal_pow hr]
  rw [hcompl, prob_compl_eq_one_sub hmeas, hval, ENNReal.ofReal_sub _ (pow_nonneg hr _),
    ENNReal.ofReal_one]

/-- The parameter of the induced bond percolation: both incidences of an edge are on. -/
theorem bondParam_mem (r : unitInterval) : (r : ℝ) * r ∈ unitInterval := by
  have h0 := r.2.1
  have h1 := r.2.2
  exact ⟨by nlinarith, by nlinarith⟩

/-- The parameter of the induced bond percolation. -/
def bondParam (r : unitInterval) : unitInterval := ⟨_, bondParam_mem r⟩

@[simp] theorem coe_bondParam (r : unitInterval) : ((bondParam r : unitInterval) : ℝ) = (r : ℝ) * r :=
  rfl

/-- The parameter of the induced site percolation: at least one of the `2d` incidences at a vertex
is on. -/
theorem siteParam_mem (d : ℕ) (r : unitInterval) :
    1 - (1 - (r : ℝ)) ^ (2 * d) ∈ unitInterval := by
  have h0 : (0 : ℝ) ≤ 1 - (r : ℝ) := by have := r.2.2; linarith
  have h1 : (1 - (r : ℝ)) ≤ 1 := by have := r.2.1; linarith
  constructor
  · have := pow_le_one₀ h0 h1 (n := 2 * d)
    linarith
  · have := pow_nonneg h0 (2 * d)
    linarith

/-- The parameter of the induced site percolation. -/
def siteParam (d : ℕ) (r : unitInterval) : unitInterval := ⟨_, siteParam_mem d r⟩

@[simp] theorem coe_siteParam (d : ℕ) (r : unitInterval) :
    ((siteParam d r : unitInterval) : ℝ) = 1 - (1 - (r : ℝ)) ^ (2 * d) := rfl

/-- **The vertex variables are independent Bernoulli variables with parameter `1 - (1-r)^{2d}`.** -/
theorem prodBernoulli_map_siteOfInc (d : ℕ) (r : unitInterval) :
    (prodBernoulli fun _ : Inc d => r).map (siteOfInc d)
      = prodBernoulli fun _ : Site d => siteParam d r := by
  have hΦ : ∀ _v : Site d, Measurable fun q : Fin d × Bool → Prop => ∃ k, q k :=
    fun _ => Measurable.exists fun k => measurable_pi_apply k
  exact prodBernoulli_map_grouped (vertInc_injective d) r _ hΦ _
    (fun _ => infinitePi_exists_of_fin d r)

/-- **The edge variables are independent Bernoulli variables with parameter `r²`.** -/
theorem prodBernoulli_map_bondOfInc (d : ℕ) (r : unitInterval) :
    (prodBernoulli fun _ : Inc d => r).map (bondOfInc d)
      = bondPercolation (zdGraph d) (bondParam r) := by
  have hΦ : ∀ e : Sym2 (Site d),
      Measurable fun q : Bool → Prop => e ∈ (zdGraph d).edgeSet ∧ q true ∧ q false := fun e =>
    measurable_const.and ((measurable_pi_apply true).and (measurable_pi_apply false))
  have ha : ∀ e : Sym2 (Site d),
      (Measure.infinitePi fun _ : Bool => Ber(True, False, r))
          {q : Bool → Prop | e ∈ (zdGraph d).edgeSet ∧ q true ∧ q false}
        = ENNReal.ofReal
            (((if e ∈ (zdGraph d).edgeSet then bondParam r else 0 : unitInterval)) : ℝ) := by
    intro e
    by_cases he : e ∈ (zdGraph d).edgeSet
    · have hs : {q : Bool → Prop | e ∈ (zdGraph d).edgeSet ∧ q true ∧ q false}
          = {q : Bool → Prop | q true ∧ q false} := by ext q; simp [he]
      rw [if_pos he, hs, coe_bondParam]
      exact infinitePi_bool_both r
    · have hs : {q : Bool → Prop | e ∈ (zdGraph d).edgeSet ∧ q true ∧ q false}
          = (∅ : Set (Bool → Prop)) := by ext q; simp [he]
      rw [if_neg he, hs, measure_empty]
      simp
  have hmain := prodBernoulli_map_blockMap (ι := Sym2 (Site d)) (κ := Bool) r _ hΦ _ ha
  have hset : bondPercolation (zdGraph d) (bondParam r)
      = setBer((zdGraph d).edgeSet, bondParam r) := rfl
  have hind := prodBernoulli_indicator_holds (ι := Sym2 (Site d))
    ((zdGraph d).edgeSet) (bondParam r)
  rw [hset, ← hind]
  exact hmain

/-! ## The parameter `255/256` -/

/-- The parameter of the incidence variables: `255/256`, chosen so that its square is at least
`63/64`, the threshold of Peierls' estimate. -/
def incParam : unitInterval := ⟨255 / 256, by norm_num, by norm_num⟩

@[simp] theorem coe_incParam : ((incParam : unitInterval) : ℝ) = 255 / 256 := rfl

/-- **Site percolation on `ℤ^d`, `d ≥ 2`, percolates at some parameter strictly below `1`.**

The half-edge coupling turns Peierls' estimate for bond percolation
(`Percolation.Literature.theta_zd_pos_of_le`) into a site statement: with incidence parameter
`r = 255/256` the induced bond parameter is `r² ≥ 63/64`, so the origin has an infinite open bond
cluster with positive probability, and every such cluster is contained in the open site cluster of
the origin for the induced site configuration, whose law is site percolation at
`1 - (1/256)^{2d} < 1`. -/
theorem exists_thetaSite_pos (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ a : unitInterval, (a : ℝ) < 1 ∧ 0 < thetaSite d a := by
  refine ⟨siteParam d incParam, ?_, ?_⟩
  · rw [coe_siteParam]
    have h : (0 : ℝ) < (1 - (incParam : ℝ)) ^ (2 * d) := by
      apply pow_pos
      rw [coe_incParam]; norm_num
    linarith
  · have hq : 0 < theta (zdGraph d) 0 (bondParam incParam) :=
      theta_zd_pos_of_le hd (bondParam incParam) (by rw [coe_bondParam, coe_incParam]; norm_num)
    have hbond := prodBernoulli_map_bondOfInc d incParam
    have hsite := prodBernoulli_map_siteOfInc d incParam
    have hmb := measurable_bondOfInc d
    have hms := measurable_siteOfInc d
    have hsub : bondOfInc d ⁻¹' (percolatesAt (0 : Site d))
        ⊆ siteOfInc d ⁻¹' {ω : SiteConfig (Site d) | (siteCluster (zdGraph d) ω 0).Infinite} :=
      fun ω hω => infinite_siteCluster_of_percolatesAt d ω hω
    have hth : theta (zdGraph d) 0 (bondParam incParam)
        = ((prodBernoulli fun _ : Inc d => incParam).map (bondOfInc d)).real
            (percolatesAt (0 : Site d)) := by
      rw [hbond]; rfl
    have hts : thetaSite d (siteParam d incParam)
        = ((prodBernoulli fun _ : Inc d => incParam).map (siteOfInc d)).real
            {ω : SiteConfig (Site d) | (siteCluster (zdGraph d) ω 0).Infinite} := by
      rw [hsite]; rfl
    calc (0 : ℝ) < theta (zdGraph d) 0 (bondParam incParam) := hq
      _ = (prodBernoulli fun _ : Inc d => incParam).real
            (bondOfInc d ⁻¹' percolatesAt (0 : Site d)) := by
          rw [hth, map_measureReal_apply hmb (measurableSet_percolatesAt_holds 0)]
      _ ≤ (prodBernoulli fun _ : Inc d => incParam).real
            (siteOfInc d ⁻¹' {ω : SiteConfig (Site d) | (siteCluster (zdGraph d) ω 0).Infinite}) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ = thetaSite d (siteParam d incParam) := by
          rw [hts, map_measureReal_apply hms (measurableSet_siteInfinite _ _)]

end KNAll.Site

end
