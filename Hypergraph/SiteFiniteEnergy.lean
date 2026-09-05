import Hypergraph.PinnedProb
import Hypergraph.SiteSlabGeometry

/-!
# Finite energy for site percolation

The uniqueness of the infinite open cluster rests on a single local fact: changing the state of one
vertex changes the probability of an event by at most a bounded factor.  For bond percolation the
fact is `Percolation.Literature.bondPercolation_finiteEnergy` (closing edges) together with
`Percolation.Literature.bondPercolation_pow_mul_real_preimage_openEdges_le` (opening them).  This
module proves the site form, for a general vector `w` of vertex probabilities, and in the
denominator-free vocabulary of `KN.PinnedProb`: a pinning is substituted into the configuration and
the ordinary product probability is taken, so no conditioning event has to be shown to have positive
probability.

`KN.SiteSlabGeometry` already carries the map `openSite x ω = insert x ω`, its measurability
`measurable_openSite`, the two `DeterminedBy` facts `determinedBy_preimage_openSite` and
`determinedBy_setOf_mem`, and the one-site estimate
`siteBernoulli_mul_real_preimage_openSite_le` for a constant parameter.  Those are reused here
rather than repeated; what is added is the map `closeSite x ω = ω \ {x}` with the same three
facts, the passage to a general `w`, and the identification of the two pinnings of a single
coordinate with these two maps.

* `substitute_singleton_true`, `substitute_singleton_false` — pinning the single coordinate `x` to
  `True` is `openSite x`, and to `False` is `closeSite x`.  Hence `pinnedProb_open_eq` and
  `pinnedProb_closed_eq`, which turn every statement below into one about ordinary preimages.
* `siteBernoulli_real_eq_pinned` — **the splitting identity**
  `P(A) = w x · P_x^{open}(A) + (1 - w x) · P_x^{closed}(A)`.  Its proof is the independence of `{x is open}` from the events
  `openSite x ⁻¹' A` and `closeSite x ⁻¹' A`, which are determined by the coordinates other
  than `x`.
* `mul_pinnedProb_open_le`, `mul_pinnedProb_closed_le` — **finite energy**, each an immediate
  consequence of the splitting identity because the discarded summand is nonnegative:
  `w x · P_x^{open}(A) ≤ P(A)` and `(1 - w x) · P_x^{closed}(A) ≤ P(A)`.  Packaged as
  `siteFiniteEnergy` and, for a constant parameter strictly inside the unit interval, as
  `exists_pos_siteFiniteEnergy`.
* `pinnedProb_site_eq_of_notMem` — an event that does not see `x` does not feel the pinning.
* `prod_mul_real_preimage_openSites_le` — the same estimate for a finite set of vertices opened at
  once, which is the form the merging step of the uniqueness argument uses.

## References

* B. Bollobás, O. Riordan, *Percolation*, Cambridge Univ. Press (2006), Ch. 5, proof of Lemma 2
  (p. 106): opening every closed site of a box.
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §1.3 p. 10 (the product measure), §7.2
  (7.16) p. 151 (the local-modification mechanism), §8.2 p. 198 ("every configuration on `𝔼_B` has
  a strictly positive probability").
* R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V : Type*}

/-- Site percolation is the product Bernoulli measure on the set of open vertices. [folklore] -/
theorem siteBernoulli_eq_prodBernoulli (w : V → unitInterval) :
    siteBernoulli w = prodBernoulli w := rfl

/-! ## Closing one vertex

The counterpart of `openSite` of `KN.SiteSlabGeometry`, with the same three facts: measurability,
that the event `{ω | ω \ {x} ∈ E}` does not depend on the state of `x`, and that the event
`{x is closed}` depends on nothing else. -/

/-- The configuration `ω` with the vertex `x` closed.  The counterpart of
`KNAll.Site.openSite`. [cite: BollobasRiordanPercolation2006, Ch. 5 (proof of Lemma 2, p. 106)] -/
def closeSite (x : V) (ω : SiteConfig V) : SiteConfig V := ω \ {x}

/-- Membership in `closeSite x ω`. [folklore] -/
theorem mem_closeSite (x : V) (ω : SiteConfig V) (a : V) :
    a ∈ closeSite x ω ↔ a ∈ ω ∧ a ≠ x := by
  simp [closeSite]

/-- `x` is closed in `closeSite x ω`. [folklore] -/
theorem notMem_closeSite_self (x : V) (ω : SiteConfig V) : x ∉ closeSite x ω := by
  rw [mem_closeSite]
  rintro ⟨-, h⟩
  exact h rfl

/-- `closeSite x ω ⊆ ω`. [folklore] -/
theorem closeSite_subset (x : V) (ω : SiteConfig V) : closeSite x ω ⊆ ω := fun _ ha => ha.1

/-- Closing an already closed vertex changes nothing. [folklore] -/
theorem closeSite_eq_self {x : V} {ω : SiteConfig V} (hx : x ∉ ω) : closeSite x ω = ω := by
  ext a
  rw [mem_closeSite]
  exact ⟨fun h => h.1, fun h => ⟨h, fun hax => hx (hax ▸ h)⟩⟩

/-- `ω ↦ ω \ {x}` is measurable (coordinatewise it is `ω ↦ (a ∈ ω) ∧ (a ≠ x)`). [folklore] -/
theorem measurable_closeSite (x : V) : Measurable (closeSite (V := V) x) := by
  refine measurable_set_iff.2 fun a => ?_
  have hfun : (fun ω : SiteConfig V => a ∈ closeSite x ω) =
      fun ω : SiteConfig V => a ∈ ω ∧ a ≠ x :=
    funext fun ω => propext (mem_closeSite x ω a)
  rw [hfun]
  exact Measurable.and (measurable_set_mem a) measurable_const

/-- The event `{ω | ω \ {x} ∈ E}` does not depend on the state of `x`. [folklore] -/
theorem determinedBy_preimage_closeSite (x : V) (E : Set (SiteConfig V)) :
    DeterminedBy (closeSite x ⁻¹' E) ({x} : Set V)ᶜ := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  have hdel : closeSite x ω = closeSite x ω' := by
    ext a
    simp only [mem_closeSite]
    by_cases ha : a = x
    · simp [ha]
    · have hmem := Set.ext_iff.1 hagree a
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, ha,
        not_false_eq_true, and_true] at hmem
      rw [hmem]
  simp only [Set.mem_preimage, hdel]

/-- The event `{x is closed}` is determined by the state of `x`. [folklore] -/
theorem determinedBy_setOf_notMem (x : V) :
    DeterminedBy {ω : SiteConfig V | x ∉ ω} ({x} : Set V) := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  exact not_congr ((determinedBy_iff _ _).1 (determinedBy_setOf_mem x) ω ω' hagree)

/-! ## Pinning one vertex

`KN.PinnedProb` pins a set `R` of coordinates to prescribed values by substituting them into the
configuration.  For `R = {x}` the two available pinnings are exactly the two maps above. -/

/-- Pinning the single coordinate `x` to `True` is opening `x`. [folklore] -/
theorem substitute_singleton_true (x : V) (ω : SiteConfig V) :
    substitute ({x} : Set V) (fun _ => True) ω = openSite x ω := by
  ext a
  by_cases ha : a = x
  · subst ha
    rw [mem_substitute_of_mem _ (Set.mem_singleton a)]
    simp [openSite]
  · rw [mem_substitute_of_notMem _ (by simpa using ha)]
    simp [openSite, ha]

/-- Pinning the single coordinate `x` to `False` is closing `x`. [folklore] -/
theorem substitute_singleton_false (x : V) (ω : SiteConfig V) :
    substitute ({x} : Set V) (fun _ => False) ω = closeSite x ω := by
  ext a
  by_cases ha : a = x
  · subst ha
    rw [mem_substitute_of_mem _ (Set.mem_singleton a)]
    simp [closeSite]
  · rw [mem_substitute_of_notMem _ (by simpa using ha)]
    simp [mem_closeSite, ha]

/-- The probability of `A` with `x` pinned open is the probability of `{ω | ω ∪ {x} ∈ A}`.
[folklore] -/
theorem pinnedProb_open_eq (w : V → unitInterval) (x : V) (A : Set (SiteConfig V)) :
    pinnedProb w ({x} : Set V) (fun _ => True) A = (siteBernoulli w).real (openSite x ⁻¹' A) := by
  have hpre : substitute ({x} : Set V) (fun _ => True) ⁻¹' A = openSite (V := V) x ⁻¹' A := by
    rw [funext (substitute_singleton_true (V := V) x)]
  simp only [pinnedProb, hpre, siteBernoulli]

/-- The probability of `A` with `x` pinned closed is the probability of `{ω | ω \ {x} ∈ A}`.
[folklore] -/
theorem pinnedProb_closed_eq (w : V → unitInterval) (x : V) (A : Set (SiteConfig V)) :
    pinnedProb w ({x} : Set V) (fun _ => False) A = (siteBernoulli w).real (closeSite x ⁻¹' A) := by
  have hpre : substitute ({x} : Set V) (fun _ => False) ⁻¹' A = closeSite (V := V) x ⁻¹' A := by
    rw [funext (substitute_singleton_false (V := V) x)]
  simp only [pinnedProb, hpre, siteBernoulli]

/-- A pinned probability is a probability: it is nonnegative. [folklore] -/
theorem pinnedProb_nonneg (w : V → unitInterval) (R : Set V) (val : V → Prop)
    (A : Set (SiteConfig V)) : 0 ≤ pinnedProb w R val A := measureReal_nonneg

/-- A pinned probability is a probability: it is at most one. [folklore] -/
theorem pinnedProb_le_one (w : V → unitInterval) (R : Set V) (val : V → Prop)
    (A : Set (SiteConfig V)) : pinnedProb w R val A ≤ 1 := measureReal_le_one

/-! ## Factorisation at one vertex -/

/-- **An event that does not see `x` does not feel the pinning of `x`.**  A special case of
`KNAll.Site.pinnedProb_eq_of_determinedBy_compl`. [cite: GrimmettPercolation1999, §2.2] -/
theorem pinnedProb_site_eq_of_notMem (w : V → unitInterval) (x : V) (val : V → Prop)
    {A : Set (SiteConfig V)} (hA : DeterminedBy A ({x} : Set V)ᶜ) :
    pinnedProb w ({x} : Set V) val A = (siteBernoulli w).real A :=
  pinnedProb_eq_of_determinedBy_compl w ({x} : Set V) val hA

/-- **The splitting identity at one vertex.**  For every measurable event `A` and every vertex `x`,

`P(A) = w x · P(A with x pinned open) + (1 - w x) · P(A with x pinned closed)`.

Proof: `A ∩ {x is open} = {x is open} ∩ {ω | ω ∪ {x} ∈ A}` because opening an already open vertex
changes nothing, and the two factors are determined by `{x}` and by its complement, hence
independent; likewise for `A \ {x is open} = {x is closed} ∩ {ω | ω \ {x} ∈ A}`.  Adding the two
gives `P(A)`.  The Burton–Keane counting argument does not use this identity: it opens vertices
and never closes them, so the only probabilistic input it needs is the insertion bound
`prod_mul_real_preimage_openSites_le` below.
[cite: GrimmettPercolation1999, §2.2] -/
theorem siteBernoulli_real_eq_pinned (w : V → unitInterval) (x : V) {A : Set (SiteConfig V)}
    (hA : MeasurableSet A) :
    (siteBernoulli w).real A =
      (w x : ℝ) * pinnedProb w ({x} : Set V) (fun _ => True) A +
        (1 - (w x : ℝ)) * pinnedProb w ({x} : Set V) (fun _ => False) A := by
  classical
  have hCm : MeasurableSet {ω : SiteConfig V | x ∈ ω} := measurableSet_mem x
  have hC'm : MeasurableSet {ω : SiteConfig V | x ∉ ω} := measurableSet_notMem x
  have hOm : MeasurableSet (openSite x ⁻¹' A) := measurable_openSite x hA
  have hZm : MeasurableSet (closeSite x ⁻¹' A) := measurable_closeSite x hA
  have hCdet : DeterminedBy {ω : SiteConfig V | x ∈ ω} (↑({x} : Finset V) : Set V) := by
    rw [Finset.coe_singleton]; exact determinedBy_setOf_mem x
  have hC'det : DeterminedBy {ω : SiteConfig V | x ∉ ω} (↑({x} : Finset V) : Set V) := by
    rw [Finset.coe_singleton]; exact determinedBy_setOf_notMem x
  have hOdet : DeterminedBy (openSite x ⁻¹' A) ((↑({x} : Finset V) : Set V))ᶜ := by
    rw [Finset.coe_singleton]; exact determinedBy_preimage_openSite x A
  have hZdet : DeterminedBy (closeSite x ⁻¹' A) ((↑({x} : Finset V) : Set V))ᶜ := by
    rw [Finset.coe_singleton]; exact determinedBy_preimage_closeSite x A
  have hsplit1 : A ∩ {ω : SiteConfig V | x ∈ ω} =
      {ω : SiteConfig V | x ∈ ω} ∩ openSite x ⁻¹' A := by
    ext ω
    constructor
    · rintro ⟨hωA, hx⟩
      have hx' : x ∈ ω := hx
      refine ⟨hx, ?_⟩
      rw [Set.mem_preimage, openSite_eq_self hx']
      exact hωA
    · rintro ⟨hx, hωO⟩
      have hx' : x ∈ ω := hx
      rw [Set.mem_preimage, openSite_eq_self hx'] at hωO
      exact ⟨hωO, hx⟩
  have hsplit2 : A \ {ω : SiteConfig V | x ∈ ω} =
      {ω : SiteConfig V | x ∉ ω} ∩ closeSite x ⁻¹' A := by
    ext ω
    constructor
    · rintro ⟨hωA, hx⟩
      have hx' : x ∉ ω := hx
      refine ⟨hx, ?_⟩
      rw [Set.mem_preimage, closeSite_eq_self hx']
      exact hωA
    · rintro ⟨hx, hωZ⟩
      have hx' : x ∉ ω := hx
      rw [Set.mem_preimage, closeSite_eq_self hx'] at hωZ
      exact ⟨hωZ, hx⟩
  have h1 : (siteBernoulli w).real ({ω : SiteConfig V | x ∈ ω} ∩ openSite x ⁻¹' A) =
      (siteBernoulli w).real {ω : SiteConfig V | x ∈ ω} *
        (siteBernoulli w).real (openSite x ⁻¹' A) :=
    prodBernoulli_real_inter_of_determinedBy w {x} hCdet hOdet hCm hOm
  have h2 : (siteBernoulli w).real ({ω : SiteConfig V | x ∉ ω} ∩ closeSite x ⁻¹' A) =
      (siteBernoulli w).real {ω : SiteConfig V | x ∉ ω} *
        (siteBernoulli w).real (closeSite x ⁻¹' A) :=
    prodBernoulli_real_inter_of_determinedBy w {x} hC'det hZdet hC'm hZm
  have hCp : (siteBernoulli w).real {ω : SiteConfig V | x ∈ ω} = (w x : ℝ) :=
    prodBernoulli_real_setOf_mem w x
  have hC'p : (siteBernoulli w).real {ω : SiteConfig V | x ∉ ω} = 1 - (w x : ℝ) :=
    prodBernoulli_real_setOf_notMem w x
  have hkey : (siteBernoulli w).real (A ∩ {ω : SiteConfig V | x ∈ ω}) +
      (siteBernoulli w).real (A \ {ω : SiteConfig V | x ∈ ω}) = (siteBernoulli w).real A :=
    measureReal_inter_add_sdiff hCm (measure_ne_top _ _)
  rw [hsplit1, hsplit2] at hkey
  rw [pinnedProb_open_eq, pinnedProb_closed_eq, ← hkey, h1, h2, hCp, hC'p]

/-! ## Finite energy -/

/-- **Opening one vertex costs at most the factor `w x`**: `w x · P(A with x pinned open) ≤ P(A)`.
The splitting identity `siteBernoulli_real_eq_pinned` with the second summand, which is
nonnegative, discarded.  For a constant parameter and in the language of preimages this is
`KNAll.Site.siteBernoulli_mul_real_preimage_openSite_le` of `KN.SiteSlabGeometry`.
[cite: BollobasRiordanPercolation2006, Ch. 5 (proof of Lemma 2, p. 106)] -/
theorem mul_pinnedProb_open_le (w : V → unitInterval) (x : V) {A : Set (SiteConfig V)}
    (hA : MeasurableSet A) :
    (w x : ℝ) * pinnedProb w ({x} : Set V) (fun _ => True) A ≤ (siteBernoulli w).real A := by
  have hsplit := siteBernoulli_real_eq_pinned w x hA
  have hnn : 0 ≤ (1 - (w x : ℝ)) * pinnedProb w ({x} : Set V) (fun _ => False) A :=
    mul_nonneg (sub_nonneg.2 (w x).2.2) (pinnedProb_nonneg w _ _ A)
  linarith

/-- **Closing one vertex costs at most the factor `1 - w x`**:
`(1 - w x) · P(A with x pinned closed) ≤ P(A)`.  The splitting identity with the first summand
discarded.  The bond counterpart is `Percolation.Literature.bondPercolation_real_finiteEnergy`.
[cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
theorem mul_pinnedProb_closed_le (w : V → unitInterval) (x : V) {A : Set (SiteConfig V)}
    (hA : MeasurableSet A) :
    (1 - (w x : ℝ)) * pinnedProb w ({x} : Set V) (fun _ => False) A ≤
      (siteBernoulli w).real A := by
  have hsplit := siteBernoulli_real_eq_pinned w x hA
  have hnn : 0 ≤ (w x : ℝ) * pinnedProb w ({x} : Set V) (fun _ => True) A :=
    mul_nonneg (w x).2.1 (pinnedProb_nonneg w _ _ A)
  linarith

/-- **Finite energy at one vertex, in the two-sided form.**  If `δ` is below both `w x` and
`1 - w x`, then both pinnings of `x` cost at most the factor `δ`:

`δ · P(A with x pinned open) ≤ P(A)` and `δ · P(A with x pinned closed) ≤ P(A)`.

Equivalently, for `δ > 0`, forcing `x` open or closed multiplies the probability of `A` by at most
`1 / δ`. [cite: GrimmettPercolation1999, §8.2 p. 198] -/
theorem siteFiniteEnergy (w : V → unitInterval) (x : V) {δ : ℝ} (hδopen : δ ≤ (w x : ℝ))
    (hδclosed : δ ≤ 1 - (w x : ℝ)) {A : Set (SiteConfig V)} (hA : MeasurableSet A) :
    δ * pinnedProb w ({x} : Set V) (fun _ => True) A ≤ (siteBernoulli w).real A ∧
      δ * pinnedProb w ({x} : Set V) (fun _ => False) A ≤ (siteBernoulli w).real A := by
  constructor
  · refine le_trans ?_ (mul_pinnedProb_open_le w x hA)
    exact mul_le_mul_of_nonneg_right hδopen (pinnedProb_nonneg w _ _ A)
  · refine le_trans ?_ (mul_pinnedProb_closed_le w x hA)
    exact mul_le_mul_of_nonneg_right hδclosed (pinnedProb_nonneg w _ _ A)

/-- **Finite energy at a parameter strictly inside the unit interval.**  For `0 < p < 1` there is a
single positive `δ`, namely `min p (1 - p)`, such that at every vertex and for every measurable
event both pinnings cost at most the factor `δ`.  This is the two-sided hypothesis a classical
Burton–Keane argument is usually stated under; the proof of `SiteUniquenessInfiniteCluster_holds`
in `KN/SiteUniqueness.lean` does not use it, needing only the one-sided insertion bound
`prod_mul_real_preimage_openSites_le` below. [cite: BurtonKeane1989] -/
theorem exists_pos_siteFiniteEnergy (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ δ > 0, ∀ (x : V) (A : Set (SiteConfig V)), MeasurableSet A →
      δ * pinnedProb (fun _ : V => p) ({x} : Set V) (fun _ => True) A ≤
          (siteBernoulli fun _ : V => p).real A ∧
        δ * pinnedProb (fun _ : V => p) ({x} : Set V) (fun _ => False) A ≤
          (siteBernoulli fun _ : V => p).real A :=
  ⟨min (p : ℝ) (1 - (p : ℝ)), lt_min hp0 (by linarith), fun x A hA =>
    siteFiniteEnergy (fun _ : V => p) x (min_le_left _ _) (min_le_right _ _) hA⟩

/-! ## The same estimates as preimage inequalities -/

/-- Finite energy for opening one vertex, in the language of preimages:
`w x · P({ω | ω ∪ {x} ∈ E}) ≤ P(E)`.  This is
`KNAll.Site.siteBernoulli_mul_real_preimage_openSite_le` of `KN.SiteSlabGeometry` with the constant
parameter replaced by a general vector of vertex probabilities.
[cite: BollobasRiordanPercolation2006, Ch. 5 (proof of Lemma 2, p. 106)] -/
theorem mul_real_preimage_openSite_le (w : V → unitInterval) (x : V) {E : Set (SiteConfig V)}
    (hE : MeasurableSet E) :
    (w x : ℝ) * (siteBernoulli w).real (openSite x ⁻¹' E) ≤ (siteBernoulli w).real E := by
  rw [← pinnedProb_open_eq]
  exact mul_pinnedProb_open_le w x hE

/-- Finite energy for closing one vertex, in the language of preimages:
`(1 - w x) · P({ω | ω \ {x} ∈ E}) ≤ P(E)`. [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
theorem mul_real_preimage_closeSite_le (w : V → unitInterval) (x : V) {E : Set (SiteConfig V)}
    (hE : MeasurableSet E) :
    (1 - (w x : ℝ)) * (siteBernoulli w).real (closeSite x ⁻¹' E) ≤ (siteBernoulli w).real E := by
  rw [← pinnedProb_closed_eq]
  exact mul_pinnedProb_closed_le w x hE

/-- **Insertion tolerance at one vertex, qualitative form**: if `w x > 0`, the event `A` has
positive probability and opening `x` carries `A` into the measurable event `E`, then `E` has
positive probability.  The site analogue of
`Percolation.Literature.bondPercolation_real_pos_of_openEdges`.
[cite: BollobasRiordanPercolation2006, Ch. 5 (proof of Lemma 2, p. 106)] -/
theorem real_pos_of_openSite (w : V → unitInterval) (x : V) (hw : 0 < (w x : ℝ))
    {A E : Set (SiteConfig V)} (hE : MeasurableSet E) (hA : 0 < (siteBernoulli w).real A)
    (hAE : ∀ ω ∈ A, openSite x ω ∈ E) : 0 < (siteBernoulli w).real E := by
  have h1 : (siteBernoulli w).real A ≤ (siteBernoulli w).real (openSite x ⁻¹' E) :=
    measureReal_mono (fun ω hω => hAE ω hω) (measure_ne_top _ _)
  have h2 := mul_real_preimage_openSite_le w x hE
  nlinarith

/-! ## Opening a finite set of vertices at once

The merging step of the uniqueness argument opens every closed vertex of a box, so the one-vertex
estimate is needed with a finite set in place of a single vertex.  The proof is the one of
`Percolation.Literature.bondPercolation_pow_mul_real_preimage_openEdges_le`: the event that every
vertex of `F` is open and the event `{ω | ω ∪ F ∈ E}` are determined by `F` and by its complement,
so they are independent, and on their intersection `ω ∪ F = ω`. -/

/-- The configuration `ω` with every vertex of `F` opened.  The site form of
`Percolation.Literature.openEdges`. [cite: BollobasRiordanPercolation2006, Ch. 5 (proof of Lemma 2, p. 106)] -/
def openSites (F : Set V) (ω : SiteConfig V) : SiteConfig V := ω ∪ F

/-- Membership in `openSites F ω`. [folklore] -/
theorem mem_openSites (F : Set V) (ω : SiteConfig V) (a : V) :
    a ∈ openSites F ω ↔ a ∈ ω ∨ a ∈ F := Iff.rfl

/-- Opening a single vertex is opening the set `{x}`. [folklore] -/
theorem openSites_singleton (x : V) (ω : SiteConfig V) :
    openSites ({x} : Set V) ω = openSite x ω := by
  ext a
  rw [mem_openSites, mem_openSite]
  simp only [Set.mem_singleton_iff]
  exact or_comm

/-- If every vertex of `F` is already open then opening them changes nothing. [folklore] -/
theorem openSites_eq_self_of_subset {F : Set V} {ω : SiteConfig V} (h : F ⊆ ω) :
    openSites F ω = ω :=
  Set.union_eq_self_of_subset_right h

/-- `ω ↦ ω ∪ F` is measurable. [folklore] -/
theorem measurable_openSites (F : Set V) : Measurable (openSites (V := V) F) :=
  measurable_set_iff.2 fun a => (measurable_set_mem a).or measurable_const

/-- The event `{ω | ω ∪ F ∈ E}` is determined by the vertices off `F`. [folklore] -/
theorem determinedBy_preimage_openSites (F : Set V) (E : Set (SiteConfig V)) :
    DeterminedBy (openSites F ⁻¹' E) Fᶜ := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  have hun : openSites F ω = openSites F ω' := by
    ext a
    simp only [mem_openSites]
    by_cases ha : a ∈ F
    · simp [ha]
    · have hmem := Set.ext_iff.1 hagree a
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, ha, not_false_eq_true, and_true] at hmem
      rw [hmem]
  simp only [Set.mem_preimage, hun]

/-- The event that every vertex of `F` is open is determined by `F`. [folklore] -/
theorem determinedBy_allOpen (F : Set V) :
    DeterminedBy {ω : SiteConfig V | F ⊆ ω} F := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hs a ha
    exact ((Set.ext_iff.1 hagree a).1 ⟨hs ha, ha⟩).1
  · intro hs a ha
    exact ((Set.ext_iff.1 hagree a).2 ⟨hs ha, ha⟩).1

/-- **Insertion tolerance for a finite set of vertices**:
`(∏_{i ∈ F} w i) · P({ω | ω ∪ F ∈ E}) ≤ P(E)`.  The site analogue of
`Percolation.Literature.bondPercolation_pow_mul_real_preimage_openEdges_le`.
[cite: BollobasRiordanPercolation2006, Ch. 5 (proof of Lemma 2, p. 106)] -/
theorem prod_mul_real_preimage_openSites_le (w : V → unitInterval) (F : Finset V)
    {E : Set (SiteConfig V)} (hE : MeasurableSet E) :
    (∏ i ∈ F, (w i : ℝ)) * (siteBernoulli w).real (openSites (↑F : Set V) ⁻¹' E) ≤
      (siteBernoulli w).real E := by
  classical
  have hDm : MeasurableSet (openSites (↑F : Set V) ⁻¹' E) := measurable_openSites _ hE
  have hCdet : DeterminedBy {ω : SiteConfig V | (↑F : Set V) ⊆ ω} (↑F : Set V) :=
    determinedBy_allOpen (↑F : Set V)
  have hCm : MeasurableSet {ω : SiteConfig V | (↑F : Set V) ⊆ ω} :=
    hCdet.measurableSet_of_finset
  have hind : (siteBernoulli w).real ({ω : SiteConfig V | (↑F : Set V) ⊆ ω} ∩
        openSites (↑F : Set V) ⁻¹' E) =
      (siteBernoulli w).real {ω : SiteConfig V | (↑F : Set V) ⊆ ω} *
        (siteBernoulli w).real (openSites (↑F : Set V) ⁻¹' E) :=
    prodBernoulli_real_inter_of_determinedBy w F hCdet
      (determinedBy_preimage_openSites (↑F : Set V) E) hCm hDm
  have hC : (siteBernoulli w).real {ω : SiteConfig V | (↑F : Set V) ⊆ ω} = ∏ i ∈ F, (w i : ℝ) :=
    prodBernoulli_real_subset w F
  have hsub : {ω : SiteConfig V | (↑F : Set V) ⊆ ω} ∩ openSites (↑F : Set V) ⁻¹' E ⊆ E := by
    rintro ω ⟨hωC, hωD⟩
    rw [Set.mem_preimage, openSites_eq_self_of_subset hωC] at hωD
    exact hωD
  calc (∏ i ∈ F, (w i : ℝ)) * (siteBernoulli w).real (openSites (↑F : Set V) ⁻¹' E)
      = (siteBernoulli w).real ({ω : SiteConfig V | (↑F : Set V) ⊆ ω} ∩
          openSites (↑F : Set V) ⁻¹' E) := by rw [hind, hC]
    _ ≤ (siteBernoulli w).real E := measureReal_mono hsub (measure_ne_top _ _)

/-! ## The site uniqueness statement

Finite energy is the first ingredient of the Burton–Keane argument; the argument itself is not
attempted here.  The statement below records its conclusion in the shape of the bond statement
`Percolation.Literature.Grimmett1999_numInfiniteClusters_le_one`, so that the port of
`Percolation/Literature/UniquenessInfiniteCluster.lean` has a fixed target.  It is a `def ... : Prop`,
proved unconditionally as `SiteUniquenessInfiniteCluster_holds` in `KN/SiteUniqueness.lean` and
consumed by `KN/SiteLocalFromUniqueness.lean`. -/

/-- The number of infinite open clusters of a site configuration, as an extended natural number.
A closed vertex is isolated in `openSiteGraph G ω`, so its component is a singleton and only
genuine open clusters can be infinite.  The bond form is
`Percolation.Literature.numInfiniteClusters`. [cite: GrimmettPercolation1999, §8.2 p. 198] -/
def numInfiniteSiteClusters (G : SimpleGraph V) (ω : SiteConfig V) : ℕ∞ :=
  {C : (openSiteGraph G ω).ConnectedComponent | C.supp.Infinite}.encard

/-- **Uniqueness of the infinite open cluster for site percolation on `ℤ^d`.**  Proved as
`SiteUniquenessInfiniteCluster_holds` in `KN/SiteUniqueness.lean`.  For
every `d` and every `p`, almost surely at most one open cluster is infinite.  The bond statement,
proved in `Percolation/Literature/UniquenessInfiniteCluster.lean`, is
`Percolation.Literature.Grimmett1999_numInfiniteClusters_le_one`; this is the same assertion for
sites, and it is the infinite-volume input that the coalescence field of
`KNAll.Site.SiteLocalInputs` currently carries as a hypothesis.  Its proof is Burton–Keane, whose
first ingredient is the finite energy proved above. [cite: BurtonKeane1989] -/
def SiteUniquenessInfiniteCluster : Prop :=
  ∀ (d : ℕ) (p : unitInterval),
    ∀ᵐ ω ∂(siteBernoulli fun _ : Site d => p),
      numInfiniteSiteClusters (zdGraph d) ω ≤ 1

end KNAll.Site

end
