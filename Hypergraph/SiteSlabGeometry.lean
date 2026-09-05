import Hypergraph.SiteThetaMono

/-!
# The lattice symmetries of the site slab reduction

The site analogues of the three geometric facts that carry the bond slab reduction
(`Percolation.Literature.KozmaNitzanTheorem6OfSlab`, "Proof of the first step") from the slab that
the manuscript produces to the slab family `slabGraph d k = {x | 0 ≤ x 0 ≤ k}` that
`KNAll.Site.SiteSlabReduction` speaks about.

* `thetaSiteOn_iso` — the percolation probability of a rooted graph is an isomorphism invariant.
  The bond statement is `Percolation.Literature.theta_iso`, and the proof is the same: the coupling
  inequality `thetaSiteOn_comap_le` applied through the isomorphism and through its inverse.
* `thetaSiteOn_pos_of_adj` — positivity of the percolation probability passes between adjacent
  roots (Grimmett 1999, §2.2 p. 35).  In the site model the vertex `x` must itself be open, which
  costs a factor `p`: the event `{x open}` is determined by the single coordinate `x`, the event
  `{ω | ω ∪ {x} percolates from x}` is determined by all the others, and the two are therefore
  independent (`siteBernoulli_mul_real_preimage_openSite_le`, the site form of the insertion
  tolerance `Percolation.Literature.bondPercolation_pow_mul_real_preimage_openEdges_le`).
* `exists_slab_pos_of_thin` — percolation in the slab `{x | |x j| ≤ r for j ≠ 0, 1}`, which is thin
  in `d - 2` coordinates, forces percolation in one of the slabs `slab d k`, which is thin in the
  coordinate `0` alone.  For `d ≥ 3` there is a coordinate `i ∉ {0, 1}`; translating by `r e_i` puts
  the `i`-th coordinate of the thin slab into `[0, 2r]`, and exchanging the coordinates `0` and `i`
  turns that into `slab d (2r)`.  Both maps are automorphisms of `zdGraph d`
  (`zdGraph_adj_shiftPermSite_iff`), so `thetaSiteOn_iso` moves the percolation probability;
  enlarging the vertex set is `thetaSiteOn_induce_mono`; and the root, which the translation has
  moved to `r e_0`, returns to the origin of the slab along the axis by `thetaSiteOn_pos_of_adj`
  (`thetaSiteOn_slabOrigin_pos_of_axis`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer (1999): §1.6 p. 16 (invariance of `P_p` under the
  symmetries of the lattice), §2.2 p. 35 (positivity of `θ` at adjacent roots).
* B. Bollobás, O. Riordan, *Percolation*, CUP (2006), Ch. 5 (opening a site of positive cost).
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

/-! ## The percolation probability is an isomorphism invariant -/

/-- **`θ` is invariant under isomorphisms of rooted graphs** for site percolation:
`θ_{G'}(φ x, p) = θ_G(x, p)`.  The bond statement is `Percolation.Literature.theta_iso`, proved the
same way: `thetaSiteOn_comap_le` gives one inequality through `φ` and the other through `φ.symm`.
[cite: GrimmettPercolation1999, §1.6 p. 16] -/
theorem thetaSiteOn_iso {V W : Type*} [Countable V] [Countable W] {G : SimpleGraph V}
    {G' : SimpleGraph W} (φ : G ≃g G') (x : V) (p : unitInterval) :
    thetaSiteOn G' (φ x) p = thetaSiteOn G x p := by
  have h1 : G = G'.comap φ := by
    ext a b; exact (φ.map_rel_iff).symm
  have h2 : G' = G.comap φ.symm := by
    ext a b; exact (φ.symm.map_rel_iff).symm
  refine le_antisymm ?_ ?_
  · have hle := thetaSiteOn_comap_le G (f := φ.symm) φ.symm.injective (φ x) p
    rw [← h2, φ.symm_apply_apply] at hle
    exact hle
  · have hle := thetaSiteOn_comap_le G' (f := φ) φ.injective x p
    rwa [← h1] at hle

/-! ## Opening one site: the insertion tolerance of site percolation -/

section Insertion

variable {V : Type*}

/-- The configuration `ω` with the vertex `x` opened.  The site form of
`Percolation.Literature.openEdges`. [cite: BollobasRiordanPercolation2006, Ch. 5 (proof of Lemma 2, p. 106)] -/
def openSite (x : V) (ω : SiteConfig V) : SiteConfig V := insert x ω

/-- Membership in `openSite x ω`. [folklore] -/
theorem mem_openSite (x : V) (ω : SiteConfig V) (a : V) :
    a ∈ openSite x ω ↔ a = x ∨ a ∈ ω := Set.mem_insert_iff

/-- `ω ⊆ openSite x ω`. [folklore] -/
theorem subset_openSite (x : V) (ω : SiteConfig V) : ω ⊆ openSite x ω := Set.subset_insert x ω

/-- `x` is open in `openSite x ω`. [folklore] -/
theorem mem_openSite_self (x : V) (ω : SiteConfig V) : x ∈ openSite x ω := Set.mem_insert x ω

/-- Opening an already open vertex changes nothing. [folklore] -/
theorem openSite_eq_self {x : V} {ω : SiteConfig V} (hx : x ∈ ω) : openSite x ω = ω :=
  Set.insert_eq_self.2 hx

/-- `ω ↦ ω ∪ {x}` is measurable. [folklore] -/
theorem measurable_openSite (x : V) : Measurable (openSite (V := V) x) := by
  refine measurable_set_iff.2 fun a => ?_
  have hfun : (fun ω : SiteConfig V => a ∈ openSite x ω) = fun ω : SiteConfig V => a = x ∨ a ∈ ω :=
    funext fun ω => propext (mem_openSite x ω a)
  rw [hfun]
  exact Measurable.or measurable_const (measurable_set_mem a)

/-- The event `{ω | ω ∪ {x} ∈ E}` does not depend on the state of `x`. [folklore] -/
theorem determinedBy_preimage_openSite (x : V) (E : Set (SiteConfig V)) :
    DeterminedBy (openSite x ⁻¹' E) ({x} : Set V)ᶜ := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  have hins : openSite x ω = openSite x ω' := by
    ext a
    simp only [mem_openSite]
    by_cases ha : a = x
    · simp [ha]
    · have hmem := Set.ext_iff.1 hagree a
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff, ha,
        not_false_eq_true, and_true] at hmem
      rw [hmem]
  simp only [Set.mem_preimage, hins]

/-- The event `{x is open}` is determined by the state of `x`. [folklore] -/
theorem determinedBy_setOf_mem (x : V) :
    DeterminedBy {ω : SiteConfig V | x ∈ ω} ({x} : Set V) := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  constructor
  · intro hx; exact ((Set.ext_iff.1 hagree x).1 ⟨hx, rfl⟩).1
  · intro hx; exact ((Set.ext_iff.1 hagree x).2 ⟨hx, rfl⟩).1

/-- **Insertion tolerance for one site**: `p · P({ω | ω ∪ {x} ∈ E}) ≤ P(E)`.  The event
`{x open}` is determined by the coordinate `x` and `{ω | ω ∪ {x} ∈ E}` by all the others, so the
two are independent, their intersection has probability `p · P({ω | ω ∪ {x} ∈ E})`, and on that
intersection `ω ∪ {x} = ω`, so it is contained in `E`.  The bond statement is
`Percolation.Literature.bondPercolation_pow_mul_real_preimage_openEdges_le`.
[cite: BollobasRiordanPercolation2006, Ch. 5 (proof of Lemma 2, p. 106)] -/
theorem siteBernoulli_mul_real_preimage_openSite_le (p : unitInterval) (x : V)
    {E : Set (SiteConfig V)} (hE : MeasurableSet E) :
    (p : ℝ) * (siteBernoulli fun _ : V => p).real (openSite x ⁻¹' E) ≤
      (siteBernoulli fun _ : V => p).real E := by
  classical
  have hDm : MeasurableSet (openSite x ⁻¹' E) := measurable_openSite x hE
  have hCm : MeasurableSet {ω : SiteConfig V | x ∈ ω} := measurableSet_mem x
  have hA : DeterminedBy {ω : SiteConfig V | x ∈ ω} (↑({x} : Finset V) : Set V) := by
    rw [Finset.coe_singleton]; exact determinedBy_setOf_mem x
  have hB : DeterminedBy (openSite x ⁻¹' E) ((↑({x} : Finset V) : Set V))ᶜ := by
    rw [Finset.coe_singleton]; exact determinedBy_preimage_openSite x E
  have hind : (siteBernoulli fun _ : V => p).real
        ({ω : SiteConfig V | x ∈ ω} ∩ openSite x ⁻¹' E) =
      (siteBernoulli fun _ : V => p).real {ω : SiteConfig V | x ∈ ω} *
        (siteBernoulli fun _ : V => p).real (openSite x ⁻¹' E) :=
    prodBernoulli_real_inter_of_determinedBy (fun _ : V => p) {x} hA hB hCm hDm
  have hC : (siteBernoulli fun _ : V => p).real {ω : SiteConfig V | x ∈ ω} = (p : ℝ) :=
    prodBernoulli_real_setOf_mem (fun _ : V => p) x
  have hsub : {ω : SiteConfig V | x ∈ ω} ∩ openSite x ⁻¹' E ⊆ E := by
    rintro ω ⟨hωC, hωD⟩
    have hins : openSite x ω = ω := openSite_eq_self hωC
    rw [Set.mem_preimage, hins] at hωD
    exact hωD
  calc (p : ℝ) * (siteBernoulli fun _ : V => p).real (openSite x ⁻¹' E)
      = (siteBernoulli fun _ : V => p).real
          ({ω : SiteConfig V | x ∈ ω} ∩ openSite x ⁻¹' E) := by rw [hind, hC]
    _ ≤ (siteBernoulli fun _ : V => p).real E := measureReal_mono hsub (measure_ne_top _ _)

end Insertion

/-! ## Positivity of the percolation probability at adjacent roots -/

/-- The percolation probability is at most the probability that the root is open: an infinite open
cluster at `x` is in particular nonempty, and every vertex of it, `x` included, is open. [folklore] -/
theorem thetaSiteOn_le_coe {V : Type*} (G : SimpleGraph V) (y : V) (p : unitInterval) :
    thetaSiteOn G y p ≤ (p : ℝ) := by
  have hsub : {ω : SiteConfig V | (siteCluster G ω y).Infinite} ⊆ {ω : SiteConfig V | y ∈ ω} := by
    intro ω hω
    obtain ⟨z, hz⟩ := hω.nonempty
    exact hz.1
  calc thetaSiteOn G y p ≤ (siteBernoulli fun _ : V => p).real {ω : SiteConfig V | y ∈ ω} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = (p : ℝ) := prodBernoulli_real_setOf_mem (fun _ : V => p) y

/-- **Positivity of `θ` passes between adjacent roots** in the site model: if `x ∼ y` and the open
cluster of `y` is infinite with positive probability, so is that of `x`.  Grimmett 1999, §2.2 p. 35
for the bond model (`Percolation.Literature.theta_pos_of_adj`); the site model pays the extra
factor `p` for opening `x`, supplied by `siteBernoulli_mul_real_preimage_openSite_le`, and `p > 0`
because `θ ≤ p`. [cite: GrimmettPercolation1999, §2.2 p. 35 (before Thm. (2.8))] -/
theorem thetaSiteOn_pos_of_adj {V : Type*} [Countable V] (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (p : unitInterval) (h : 0 < thetaSiteOn G y p) :
    0 < thetaSiteOn G x p := by
  have hp : 0 < (p : ℝ) := lt_of_lt_of_le h (thetaSiteOn_le_coe G y p)
  have hAE : {ω : SiteConfig V | (siteCluster G ω y).Infinite} ⊆
      openSite x ⁻¹' {ω : SiteConfig V | (siteCluster G ω x).Infinite} := by
    intro ω hω
    obtain ⟨z, hz⟩ := hω.nonempty
    have hy : y ∈ ω := hz.1
    have hsub : siteCluster G ω y ⊆ siteCluster G (openSite x ω) x := by
      rintro w ⟨-, hreach⟩
      refine ⟨mem_openSite_self x ω, ?_⟩
      have hadj : (openSiteGraph G (openSite x ω)).Adj x y :=
        (openSiteGraph_adj_iff' G _ x y).2
          ⟨hxy, mem_openSite_self x ω, subset_openSite x ω hy⟩
      exact hadj.reachable.trans (hreach.mono (openSiteGraph_mono G (subset_openSite x ω)))
    exact hω.mono hsub
  have h1 : thetaSiteOn G y p ≤ (siteBernoulli fun _ : V => p).real
      (openSite x ⁻¹' {ω : SiteConfig V | (siteCluster G ω x).Infinite}) :=
    measureReal_mono hAE (measure_ne_top _ _)
  have h2 := siteBernoulli_mul_real_preimage_openSite_le p x (measurableSet_siteInfinite G x)
  calc (0 : ℝ) < (p : ℝ) * thetaSiteOn G y p := mul_pos hp h
    _ ≤ (p : ℝ) * (siteBernoulli fun _ : V => p).real
          (openSite x ⁻¹' {ω : SiteConfig V | (siteCluster G ω x).Infinite}) :=
        mul_le_mul_of_nonneg_left h1 hp.le
    _ ≤ thetaSiteOn G x p := h2

/-! ## Translations and coordinate permutations of `ℤ^d` -/

section Geometry

variable {d : ℕ}

/-- A permutation of the coordinates of `ℤ^d`, as a bijection of the sites. [folklore] -/
def permSite (e : Fin d ≃ Fin d) : Site d ≃ Site d where
  toFun x := fun j => x (e j)
  invFun x := fun j => x (e.symm j)
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

@[simp] theorem permSite_apply (e : Fin d ≃ Fin d) (x : Site d) (j : Fin d) :
    permSite e x j = x (e j) := rfl

/-- Translation by `v` followed by the coordinate permutation `e`, as a bijection of the sites.
[folklore] -/
def shiftPermSite (v : Site d) (e : Fin d ≃ Fin d) : Site d ≃ Site d :=
  (Site.shift v).trans (permSite e)

@[simp] theorem shiftPermSite_apply (v : Site d) (e : Fin d ≃ Fin d) (x : Site d) (j : Fin d) :
    shiftPermSite v e x j = (x + v) (e j) := rfl

/-- A permutation of the coordinates of `ℤ^d` preserves adjacency: it carries the step `e_i` to the
step `e_{e⁻¹ i}`. (Grimmett 1999, §1.6 p. 16.) [cite: GrimmettPercolation1999, §1.6 p. 16] -/
theorem zdGraph_adj_permSite (e : Fin d ≃ Fin d) {x y : Site d} (h : (zdGraph d).Adj x y) :
    (zdGraph d).Adj (permSite e x) (permSite e y) := by
  have hsingle : ∀ i j : Fin d,
      (Pi.single i (1 : ℤ) : Site d) (e j) = (Pi.single (e.symm i) (1 : ℤ) : Site d) j := by
    intro i j
    by_cases hji : j = e.symm i
    · subst hji
      simp
    · have hne : e j ≠ i := fun hc => hji (by rw [← hc, Equiv.symm_apply_apply])
      simp only [Pi.single_apply, if_neg hne, if_neg hji]
  rw [zdGraph_adj_iff] at h ⊢
  obtain ⟨i, hi | hi⟩ := h
  · refine ⟨e.symm i, Or.inl ?_⟩
    funext j
    show y (e j) = x (e j) + (Pi.single (e.symm i) (1 : ℤ) : Site d) j
    rw [← hsingle i j]
    exact congrFun hi (e j)
  · refine ⟨e.symm i, Or.inr ?_⟩
    funext j
    show x (e j) = y (e j) + (Pi.single (e.symm i) (1 : ℤ) : Site d) j
    rw [← hsingle i j]
    exact congrFun hi (e j)

/-- A permutation of the coordinates of `ℤ^d` is an automorphism of the nearest-neighbour graph.
[cite: GrimmettPercolation1999, §1.6 p. 16] -/
theorem zdGraph_adj_permSite_iff (e : Fin d ≃ Fin d) (x y : Site d) :
    (zdGraph d).Adj (permSite e x) (permSite e y) ↔ (zdGraph d).Adj x y := by
  refine ⟨fun h => ?_, zdGraph_adj_permSite e⟩
  have hback := zdGraph_adj_permSite e.symm h
  have hx : permSite e.symm (permSite e x) = x := by funext j; simp
  have hy : permSite e.symm (permSite e y) = y := by funext j; simp
  rwa [hx, hy] at hback

/-- A translation followed by a coordinate permutation is an automorphism of `ℤ^d`.
[cite: GrimmettPercolation1999, §1.6 p. 16] -/
theorem zdGraph_adj_shiftPermSite_iff (v : Site d) (e : Fin d ≃ Fin d) (x y : Site d) :
    (zdGraph d).Adj (shiftPermSite v e x) (shiftPermSite v e y) ↔ (zdGraph d).Adj x y := by
  have hx : shiftPermSite v e x = permSite e (x + v) := rfl
  have hy : shiftPermSite v e y = permSite e (y + v) := rfl
  rw [hx, hy, zdGraph_adj_permSite_iff]
  simpa using zdGraph_adj_shift_iff v x y

/-- A translation followed by a coordinate permutation, as an isomorphism between induced subgraphs
of `ℤ^d` whose vertex sets correspond under it.  The site analogue of
`Percolation.Literature.induceShiftIso`. [cite: GrimmettPercolation1999, §1.6 p. 16] -/
def induceShiftPermIso (v : Site d) (e : Fin d ≃ Fin d) {S T : Set (Site d)}
    (h : ∀ x : Site d, x ∈ T ↔ shiftPermSite v e x ∈ S) :
    (zdGraph d).induce T ≃g (zdGraph d).induce S where
  toEquiv := (shiftPermSite v e).subtypeEquiv h
  map_rel_iff' {a b} := zdGraph_adj_shiftPermSite_iff v e a.1 b.1

/-- The underlying map of `induceShiftPermIso`. [folklore] -/
@[simp] theorem coe_induceShiftPermIso_apply (v : Site d) (e : Fin d ≃ Fin d) {S T : Set (Site d)}
    (h : ∀ x : Site d, x ∈ T ↔ shiftPermSite v e x ∈ S) (a : T) :
    ((induceShiftPermIso v e h a : S) : Site d) = shiftPermSite v e a := rfl

end Geometry

/-! ## From a slab thin in `d - 2` coordinates to the slabs `slab d k` -/

/-- Consecutive points of a coordinate axis of `ℤ^d` are adjacent. [folklore] -/
theorem zdGraph_adj_single_succ' (d : ℕ) (i : Fin d) (n : ℤ) :
    (zdGraph d).Adj (Pi.single i n) (Pi.single i (n + 1)) := by
  rw [zdGraph_adj_iff]
  refine ⟨i, Or.inl ?_⟩
  rw [← Pi.single_add]

/-- The axis point `n e₀`, `n ≤ k`, lies in the slab `{x | 0 ≤ x 0 ≤ k}`. [folklore] -/
theorem siteSingle_mem_slab (d : ℕ) [NeZero d] {k n : ℕ} (hn : n ≤ k) :
    (Pi.single (0 : Fin d) (n : ℤ) : Site d) ∈ slab d k :=
  ⟨by simp, by simpa using hn⟩

/-- **Positivity of `θ` in a slab passes from the axis to the origin**: `n` applications of
`thetaSiteOn_pos_of_adj` along the path `n e₀, (n-1) e₀, …, 0`, which stays inside the slab.
[cite: GrimmettPercolation1999, §2.2 p. 35 (before Thm. (2.8))] -/
theorem thetaSiteOn_slabOrigin_pos_of_axis (d : ℕ) [NeZero d] {k : ℕ} (p : unitInterval) :
    ∀ n : ℕ, ∀ hn : n ≤ k,
      0 < thetaSiteOn (slabGraph d k) ⟨Pi.single 0 (n : ℤ), siteSingle_mem_slab d hn⟩ p →
        0 < thetaSiteOn (slabGraph d k) (slabOrigin d k) p
  | 0, _, h => by
    have h0 : (⟨Pi.single 0 ((0 : ℕ) : ℤ), siteSingle_mem_slab d (Nat.zero_le k)⟩ : slab d k) =
        slabOrigin d k :=
      Subtype.ext (by simp [slabOrigin])
    rwa [h0] at h
  | n + 1, hn, h => by
    refine thetaSiteOn_slabOrigin_pos_of_axis d p n (Nat.le_of_succ_le hn) ?_
    refine thetaSiteOn_pos_of_adj (slabGraph d k) ?_ p h
    change (zdGraph d).Adj (Pi.single 0 (n : ℤ)) (Pi.single 0 ((n + 1 : ℕ) : ℤ))
    push_cast
    exact zdGraph_adj_single_succ' d 0 n

/-- **The slab family bridge.**  For `d ≥ 3`, percolation at `p` in the slab
`{x | |x j| ≤ r for every j ≠ 0, 1}`, which is thin in the `d - 2` coordinates other than `0` and
`1`, forces percolation at the same `p` in one of the slabs `slab d k = {x | 0 ≤ x 0 ≤ k}`, which
are thin in the coordinate `0` alone.  Pick a coordinate `i ∉ {0, 1}`, translate by `r e_i` so that
the `i`-th coordinate of the thin slab lies in `[0, 2r]`, and exchange the coordinates `0` and `i`:
the composite is an automorphism of `ℤ^d` (`zdGraph_adj_shiftPermSite_iff`) carrying the thin slab
inside `slab d (2r)` and the origin to `r e₀`.  `thetaSiteOn_iso` moves the percolation probability,
`thetaSiteOn_induce_mono` enlarges the vertex set, and
`thetaSiteOn_slabOrigin_pos_of_axis` returns the root to the origin of the slab.
[cite: GrimmettPercolation1999, §1.6 p. 16 and §2.2 p. 35] -/
theorem exists_slab_pos_of_thin (d : ℕ) [NeZero d] (hd : 3 ≤ d) (r : ℕ) (p : unitInterval)
    (h : 0 < thetaSiteOn ((zdGraph d).induce {x : Site d | ∀ j, j ≠ 0 → j ≠ 1 → |x j| ≤ (r : ℤ)})
          ⟨0, by simp⟩ p) :
    ∃ k : ℕ, 0 < thetaSiteOn (slabGraph d k) (slabOrigin d k) p := by
  classical
  -- a coordinate in which the given slab is thin
  obtain ⟨i, hi0, hi1⟩ : ∃ i : Fin d, i ≠ 0 ∧ i ≠ 1 := by
    refine ⟨⟨2, by omega⟩, ?_, ?_⟩
    · simp
    · refine Fin.ne_of_val_ne ?_
      rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < d by omega)]
      simp
  set Th : Set (Site d) := {x : Site d | ∀ j, j ≠ 0 → j ≠ 1 → |x j| ≤ (r : ℤ)} with hThdef
  have h0Th : (0 : Site d) ∈ Th := by
    rw [hThdef]
    intro j _ _
    simp
  set v : Site d := Pi.single i (r : ℤ) with hvdef
  set e : Fin d ≃ Fin d := Equiv.swap 0 i with hedef
  set S : Set (Site d) := {z : Site d | (shiftPermSite v e).symm z ∈ Th} with hSdef
  have hmem : ∀ x : Site d, x ∈ Th ↔ shiftPermSite v e x ∈ S := by
    intro x
    rw [hSdef]
    show x ∈ Th ↔ (shiftPermSite v e).symm (shiftPermSite v e x) ∈ Th
    rw [Equiv.symm_apply_apply]
  -- the exchange of the coordinates `0` and `i`
  have he0 : e 0 = i := by rw [hedef]; exact Equiv.swap_apply_left 0 i
  have hei0 : e i = 0 := by rw [hedef]; exact Equiv.swap_apply_right 0 i
  have hei : ∀ j : Fin d, e j = i ↔ j = 0 := by
    intro j
    refine ⟨fun hj => ?_, fun hj => by rw [hj]; exact he0⟩
    have hswap : e (e j) = 0 := by rw [hj]; exact hei0
    rw [hedef, Equiv.swap_apply_self] at hswap
    exact hswap
  -- the image of the origin is `r e₀`
  have hΦ0 : shiftPermSite v e (0 : Site d) = Pi.single (0 : Fin d) (r : ℤ) := by
    funext j
    show ((0 : Site d) + v) (e j) = (Pi.single (0 : Fin d) (r : ℤ) : Site d) j
    rw [zero_add, hvdef]
    simp only [Pi.single_apply]
    by_cases hj : j = 0
    · rw [if_pos ((hei j).2 hj), if_pos hj]
    · rw [if_neg fun hc => hj ((hei j).1 hc), if_neg hj]
  -- the image of the thin slab lies in `slab d (2r)`
  have hSslab : S ⊆ slab d (2 * r) := by
    intro z hz
    have hx : (shiftPermSite v e).symm z ∈ Th := hz
    rw [hThdef] at hx
    have habs : |(shiftPermSite v e).symm z i| ≤ (r : ℤ) := hx i hi0 hi1
    have hz0 : z 0 = (shiftPermSite v e).symm z i + (r : ℤ) := by
      conv_lhs => rw [← (shiftPermSite v e).apply_symm_apply z]
      show ((shiftPermSite v e).symm z + v) (e 0) = (shiftPermSite v e).symm z i + (r : ℤ)
      rw [he0]
      show (shiftPermSite v e).symm z i + v i = (shiftPermSite v e).symm z i + (r : ℤ)
      rw [hvdef]
      simp
    rw [abs_le] at habs
    simp only [slab, Set.mem_setOf_eq]
    constructor
    · rw [hz0]; linarith [habs.1]
    · rw [hz0]; push_cast; linarith [habs.2]
  -- transport the percolation probability
  have hsingleS : (Pi.single (0 : Fin d) (r : ℤ) : Site d) ∈ S := by
    rw [← hΦ0]
    exact (hmem 0).1 h0Th
  have hiso := thetaSiteOn_iso (induceShiftPermIso v e hmem) ⟨(0 : Site d), h0Th⟩ p
  have hroot : (induceShiftPermIso v e hmem ⟨(0 : Site d), h0Th⟩) =
      (⟨Pi.single (0 : Fin d) (r : ℤ), hsingleS⟩ : S) := Subtype.ext hΦ0
  rw [hroot] at hiso
  have hposS : 0 < thetaSiteOn ((zdGraph d).induce S)
      ⟨Pi.single (0 : Fin d) (r : ℤ), hsingleS⟩ p := by
    rw [hiso]
    exact h
  have hmono := thetaSiteOn_induce_mono (zdGraph d) hSslab
    (Pi.single (0 : Fin d) (r : ℤ)) hsingleS p
  refine ⟨2 * r, ?_⟩
  refine thetaSiteOn_slabOrigin_pos_of_axis d p r (by omega) ?_
  exact lt_of_lt_of_le hposS hmono

end KNAll.Site

end
