import Hypergraph.SiteFiniteEnergy
import Hypergraph.SiteLocalInputs
import Hypergraph.SiteUniqueness
import Percolation.Literature.ZeroOneLaw

/-!
# The local inputs from supercriticality and uniqueness

`SiteLocalInputs d p` of `KN/SiteLocalInputs.lean` is the pair of local facts that the
renormalization argument consumes, and that module leaves both of them unproved.  This module
proves the structure from two named hypotheses: `0 < thetaSite d p`, and the almost sure uniqueness
of the infinite open cluster, `SiteUniquenessInfiniteCluster` of `KN/SiteFiniteEnergy.lean`.

The two fields are proved separately, and both rest on the same three tools.

* **Ergodicity of the lattice translations.**  `ergodic_siteShift` transports
  `Percolation.Literature.ergodic_coordShift_infinitePi` of `ZeroOneLaw.lean` from the product
  measure on `Site d → Prop` to `siteBernoulli` on `Set (Site d)` along the coordinate encoding
  `q ↦ {i | q i}`, exactly as `ergodic_relabel_shift_bondPercolation` does for bond percolation.
  The consequence used below is `siteBernoulli_zero_one_of_shift`.
* **First exit.**  An open walk that starts inside `box d L` and ends outside it meets the sphere
  `boxSphere d L` (`exists_boxSphere_reachable`).  This makes the arm events decrease in the radius
  and makes an infinite cluster reach every sphere.
* **A discrete intermediate value theorem along a walk**, `exists_reachable_coord_eq_zero`: an open
  walk from a site with `i`-th coordinate `≤ 0` to a site with `i`-th coordinate `≥ 0` passes
  through the hyperplane `{y | y i = 0}`.

The coalescence field is the continuity from above of the arm events, which decrease in the radius
by the first-exit lemma and whose intersection is the event that `x` and `y` lie in two distinct
infinite clusters; uniqueness makes that null.

The face-hitting field needs more than one arm estimate.  It asks for a single cluster meeting all
`2d` faces of `box d m`, and uniqueness is what merges `2d` separate hits into one cluster; so the
field reduces, by a union bound over the faces, to the statement that one face meets an infinite
cluster with probability close to one.  A face of `box d m` is a translate of the box of side
`2m + 1` of the hyperplane `{y | y i = 0}`, and those boxes exhaust the hyperplane, so the reduction
is again a continuity from above, this time to the event that the whole hyperplane misses every
infinite cluster.  That event is null for two reasons together: an infinite cluster exists almost
surely, since its existence is translation invariant and hence trivial by the zero–one law; and an
infinite cluster missing the hyperplane is connected, so by the discrete intermediate value theorem
it lies in one of the two half spaces `{y | 1 ≤ ±y i}`, and the event that every infinite cluster
lies in `{y | k ≤ ±y i}` has a probability independent of `k` by translation invariance while the
intersection over `k` is empty.

The conclusions are `siteLocalInputs_of_uniqueness`, which carries uniqueness as a hypothesis, and
`siteLocalInputs_of_thetaSite_pos`, which discharges it with
`SiteUniquenessInfiniteCluster_holds` of `KN/SiteUniqueness.lean` and so assumes only
`0 < thetaSite d p`.  In dimension zero the face-hitting field is vacuous, there being no faces, and
the coalescence field needs no dimension hypothesis at all.

## References

* R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
* G. R. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

open scoped ENNReal

/-! ## Geometry of boxes, spheres and open walks -/

section Geometry

variable {d : ℕ}

/-- **Adjacency in `ℤ^d` moves one coordinate by one.**  The unpacking of `zdGraph_adj_iff` used
throughout: adjacent sites agree off a coordinate `i`, and differ there by `±1`. -/
theorem exists_coord_of_zdGraph_adj {x y : Site d} (h : (zdGraph d).Adj x y) :
    ∃ i, (∀ j, j ≠ i → y j = x j) ∧ (y i = x i + 1 ∨ y i = x i - 1) := by
  obtain ⟨i, h | h⟩ := (zdGraph_adj_iff x y).1 h
  · exact ⟨i, fun j hj => by simp [h, hj], Or.inl (by simp [h])⟩
  · exact ⟨i, fun j hj => by simp [h, hj], Or.inr (by simp [h])⟩

/-- **A site of `box d L` adjacent to a site outside it lies on the sphere.**  Its coordinate in the
direction of the step is `L` or `-L`, since one more step leaves the cube. -/
theorem mem_boxSphere_of_adj_notMem {L : ℕ} {x y : Site d} (h : (zdGraph d).Adj x y)
    (hx : x ∈ box d L) (hy : y ∉ box d L) : x ∈ boxSphere d L := by
  rw [mem_box] at hx
  obtain ⟨i, hoff, hi⟩ := exists_coord_of_zdGraph_adj h
  refine ⟨hx, i, ?_⟩
  by_contra hcon
  push Not at hcon
  refine hy (mem_box.2 fun j => ?_)
  by_cases hj : j = i
  · subst hj
    obtain ⟨h1, h2⟩ := hx j
    obtain ⟨hne1, hne2⟩ := hcon
    rcases hi with h | h <;> omega
  · rw [hoff j hj]
    exact hx j

/-- **The radius is read off from a point of the sphere.**  A site cannot lie on two spheres. -/
theorem boxSphere_radius_unique {M M' : ℕ} {a : Site d} (h : a ∈ boxSphere d M)
    (h' : a ∈ boxSphere d M') : M = M' := by
  obtain ⟨hb, i, hi⟩ := h
  obtain ⟨hb', i', hi'⟩ := h'
  have h1 := hb' i
  have h2 := hb i'
  have hle : (M : ℤ) ≤ M' := by rcases hi with h | h <;> omega
  have hge : (M' : ℤ) ≤ M := by rcases hi' with h | h <;> omega
  omega

/-- **First exit.**  An open walk from a site of `box d L` to a site outside `box d L` reaches the
sphere of radius `L` before leaving the cube: the first step out of the cube is taken from a site
whose coordinate in that direction is `±L`. -/
theorem exists_boxSphere_reachable {L : ℕ} {ω : SiteConfig (Site d)} :
    ∀ {u w : Site d}, (openSiteGraph (zdGraph d) ω).Walk u w → u ∈ box d L → w ∉ box d L →
      ∃ a ∈ boxSphere d L, (openSiteGraph (zdGraph d) ω).Reachable u a := by
  intro u w p
  induction p with
  | nil => intro hu hw; exact absurd hu hw
  | @cons u b w hadj q ih =>
    intro hu hw
    by_cases hb : b ∈ box d L
    · obtain ⟨a, ha, hra⟩ := ih hb hw
      exact ⟨a, ha, (SimpleGraph.Adj.reachable hadj).trans hra⟩
    · exact ⟨u, mem_boxSphere_of_adj_notMem ((openSiteGraph_adj_iff' _ ω u b).1 hadj).1 hu hb,
        SimpleGraph.Reachable.refl u⟩

/-- **Reaching outside the cube is reaching its sphere.** -/
theorem siteConnSet_boxSphere_of_reach {L : ℕ} {ω : SiteConfig (Site d)} {x w : Site d}
    (hx : x ∈ box d L) (hw : w ∉ box d L) (h : ω ∈ siteConn (zdGraph d) x w) :
    ω ∈ siteConnSet (zdGraph d) x (boxSphere d L) := by
  obtain ⟨hxo, hr⟩ := h
  obtain ⟨p⟩ := hr
  obtain ⟨a, ha, hra⟩ := exists_boxSphere_reachable p hx hw
  exact Set.mem_biUnion ha ⟨hxo, hra⟩

/-- **The arm events decrease in the radius.**  A cluster reaching the sphere of radius `M` reaches
every smaller sphere around a site of the smaller cube. -/
theorem siteConnSet_boxSphere_antitone {M' M : ℕ} {x : Site d} (hx : x ∈ box d M')
    (hMM : M' ≤ M) :
    siteConnSet (zdGraph d) x (boxSphere d M) ⊆ siteConnSet (zdGraph d) x (boxSphere d M') := by
  intro ω hω
  simp only [siteConnSet, Set.mem_iUnion, exists_prop] at hω
  obtain ⟨a, ha, hxa⟩ := hω
  by_cases hab : a ∈ box d M'
  · have hMM' : M = M' := by
      obtain ⟨hb, i, hi⟩ := ha
      have hbi := (mem_box.1 hab) i
      rcases hi with h | h <;> omega
    subst hMM'
    exact Set.mem_biUnion ha hxa
  · exact siteConnSet_boxSphere_of_reach hx hab hxa

/-- **A discrete intermediate value theorem along an open walk.**  A walk from a site with `i`-th
coordinate at most `0` to a site with `i`-th coordinate at least `0` meets the hyperplane
`{y | y i = 0}`, because each step changes a coordinate by at most one. -/
theorem exists_reachable_coord_eq_zero {ω : SiteConfig (Site d)} (i : Fin d) :
    ∀ {u w : Site d}, (openSiteGraph (zdGraph d) ω).Walk u w → u i ≤ 0 → 0 ≤ w i →
      ∃ t, (openSiteGraph (zdGraph d) ω).Reachable u t ∧ t i = 0 := by
  intro u w p
  induction p with
  | nil => intro h1 h2; exact ⟨_, SimpleGraph.Reachable.refl _, le_antisymm h1 h2⟩
  | @cons u b w hadj q ih =>
    intro h1 h2
    rcases eq_or_lt_of_le h1 with heq | hlt
    · exact ⟨u, SimpleGraph.Reachable.refl u, heq⟩
    · have hb : b i ≤ 0 := by
        obtain ⟨j, hoff, hj⟩ :=
          exists_coord_of_zdGraph_adj ((openSiteGraph_adj_iff' _ ω u b).1 hadj).1
        by_cases hji : i = j
        · subst hji
          rcases hj with h | h <;> omega
        · rw [hoff i hji]
          exact h1
      obtain ⟨t, hrt, ht⟩ := ih hb h2
      exact ⟨t, (SimpleGraph.Adj.reachable hadj).trans hrt, ht⟩

end Geometry

/-! ## Percolation events and the lattice translations -/

section Events

variable {V : Type*}

/-- **A percolating site is open.**  An infinite component contains a site other than its base, and
a non-trivial open walk opens its first site. -/
theorem mem_of_mem_sitePerc {G : SimpleGraph V} {ω : SiteConfig V} {x : V}
    (h : ω ∈ sitePerc G x) : x ∈ ω := by
  rw [mem_sitePerc_iff] at h
  obtain ⟨y, hy, hyx⟩ := h.exists_notMem_finset {x}
  have hne : x ≠ y := fun hc => hyx (by rw [← hc]; exact Finset.mem_singleton_self x)
  have hconn : ω ∈ siteConn G x y := by
    rw [← siteReach_eq_of_ne G hne]
    exact hy
  exact hconn.1

/-- **The infinite-cluster event of `KN/SiteStatements.lean` is `sitePerc`.**  The two sets differ
only in whether the openness of the base site is demanded, and an infinite component demands it. -/
theorem siteCluster_infinite_iff (G : SimpleGraph V) (ω : SiteConfig V) (x : V) :
    (siteCluster G ω x).Infinite ↔ ω ∈ sitePerc G x := by
  rw [mem_sitePerc_iff]
  refine ⟨Set.Infinite.mono fun y hy => hy.2, fun h => ?_⟩
  have hx : x ∈ ω := mem_of_mem_sitePerc ((mem_sitePerc_iff G ω x).2 h)
  exact Set.Infinite.mono (fun y hy => ⟨hx, hy⟩) h

/-- The event that `x` is joined to some site of `A` is measurable on a countable graph. -/
theorem measurableSet_siteConnSet_countable [Countable V] (G : SimpleGraph V) (x : V) (A : Set V) :
    MeasurableSet (siteConnSet G x A) :=
  MeasurableSet.biUnion (Set.to_countable A) fun a _ => measurableSet_siteConn G x a

end Events

section Shift

variable {d : ℕ}

/-- **Translation of configurations.**  The site `x` is open in `siteShift v ω` exactly when `x + v`
is open in `ω`; so `siteShift v ω` is `ω` moved by `-v`. -/
def siteShift (v : Site d) : SiteConfig (Site d) → SiteConfig (Site d) :=
  restrictSite (fun x => x + v)

@[simp] theorem mem_siteShift (v : Site d) (ω : SiteConfig (Site d)) (x : Site d) :
    x ∈ siteShift v ω ↔ x + v ∈ ω := Iff.rfl

/-- Translation of configurations is measurable. -/
theorem measurable_siteShift (v : Site d) : Measurable (siteShift (d := d) v) :=
  measurable_restrictSite _

/-- **Translation invariance of the site measure**, from `siteBernoulli_map_restrictSite`. -/
theorem measurePreserving_siteShift (p : unitInterval) (v : Site d) :
    MeasurePreserving (siteShift (d := d) v) (siteBernoulli fun _ : Site d => p)
      (siteBernoulli fun _ : Site d => p) :=
  ⟨measurable_siteShift v, siteBernoulli_map_restrictSite (add_left_injective v) p⟩

/-- Translation carries the open site graph of the translated configuration into that of `ω`. -/
def siteShiftHom (v : Site d) (ω : SiteConfig (Site d)) :
    openSiteGraph (zdGraph d) (siteShift v ω) →g openSiteGraph (zdGraph d) ω where
  toFun x := x + v
  map_rel' := by
    intro a b h
    rw [openSiteGraph_adj_iff'] at h ⊢
    exact ⟨by simpa using (zdGraph_adj_shift_iff v a b).2 h.1, h.2.1, h.2.2⟩

/-- The inverse translation, in the other direction. -/
def siteShiftHom' (v : Site d) (ω : SiteConfig (Site d)) :
    openSiteGraph (zdGraph d) ω →g openSiteGraph (zdGraph d) (siteShift v ω) where
  toFun x := x - v
  map_rel' := by
    intro a b h
    rw [openSiteGraph_adj_iff'] at h ⊢
    refine ⟨?_, by simpa using h.2.1, by simpa using h.2.2⟩
    have := (zdGraph_adj_shift_iff v (a - v) (b - v)).1
    simpa using this (by simpa using h.1)

/-- **Open connections translate.** -/
theorem reachable_siteShift_iff (v : Site d) (ω : SiteConfig (Site d)) (a b : Site d) :
    (openSiteGraph (zdGraph d) (siteShift v ω)).Reachable a b ↔
      (openSiteGraph (zdGraph d) ω).Reachable (a + v) (b + v) := by
  refine ⟨fun h => h.map (siteShiftHom v ω), fun h => ?_⟩
  simpa [siteShiftHom'] using h.map (siteShiftHom' v ω)

/-- Translating a set does not change whether it is infinite. -/
theorem infinite_preimage_add_iff (v : Site d) (s : Set (Site d)) :
    ((fun x : Site d => x + v) ⁻¹' s).Infinite ↔ s.Infinite := by
  have h : (fun x : Site d => x + v) ⁻¹' s = (fun y : Site d => y - v) '' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨fun hx => ⟨x + v, hx, by simp⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    simpa using hy
  rw [h]
  exact Set.infinite_image_iff fun a _ b _ hab => by simpa using hab

/-- **The percolation event translates.** -/
theorem sitePerc_siteShift (v z : Site d) :
    siteShift v ⁻¹' sitePerc (zdGraph d) z = sitePerc (zdGraph d) (z + v) := by
  ext ω
  simp only [Set.mem_preimage, mem_sitePerc_iff]
  have hset : {y : Site d | (openSiteGraph (zdGraph d) (siteShift v ω)).Reachable z y} =
      (fun x : Site d => x + v) ⁻¹'
        {u : Site d | (openSiteGraph (zdGraph d) ω).Reachable (z + v) u} := by
    ext y
    exact reachable_siteShift_iff v ω z y
  rw [hset, infinite_preimage_add_iff]

/-! ### Ergodicity of a translation -/

/-- **A non-zero translation moves every finite set of sites off itself**, after enough iterations:
the linear form `x ↦ x k` is bounded on a finite set and is shifted by `n * v k`. -/
theorem exists_iterate_add_notMem {v : Site d} (hv : v ≠ 0) (s : Finset (Site d)) :
    ∃ n : ℕ, ∀ x ∈ s, (fun y : Site d => y + v)^[n] x ∉ s := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hiter : ∀ (n : ℕ) (x : Site d), (fun y : Site d => y + v)^[n] x = x + n • v := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, succ_nsmul]
      abel
  set M : ℕ := s.sup fun x => (x k).natAbs with hMdef
  have hM : ∀ x ∈ s, |x k| ≤ (M : ℤ) := by
    intro x hx
    have h : (x k).natAbs ≤ M := Finset.le_sup (f := fun x : Site d => (x k).natAbs) hx
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  refine ⟨2 * M + 1, fun x hx hx' => ?_⟩
  rw [hiter] at hx'
  have h1 := hM x hx
  have h2 := hM _ hx'
  have hcoord : (x + (2 * M + 1 : ℕ) • v) k = x k + ((2 * M + 1 : ℕ) : ℤ) * v k := by
    simp [nsmul_eq_mul]
  rw [hcoord] at h2
  have hbig : |((2 * M + 1 : ℕ) : ℤ) * v k| ≤ 2 * (M : ℤ) := by
    calc |((2 * M + 1 : ℕ) : ℤ) * v k|
        = |(x k + ((2 * M + 1 : ℕ) : ℤ) * v k) - x k| := by ring_nf
      _ ≤ |x k + ((2 * M + 1 : ℕ) : ℤ) * v k| + |x k| := abs_sub _ _
      _ ≤ (M : ℤ) + (M : ℤ) := add_le_add h2 h1
      _ = 2 * (M : ℤ) := by ring
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((2 * M + 1 : ℕ) : ℤ))] at hbig
  have hvk : 1 ≤ |v k| := Int.one_le_abs hk
  have hcast : ((2 * M + 1 : ℕ) : ℤ) = 2 * (M : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hbig
  nlinarith [hbig, hvk]

/-- **A translation acts ergodically on the site measure.**  This is
`ergodic_coordShift_infinitePi` of `ZeroOneLaw.lean`, carried along the coordinate encoding
`q ↦ {i | q i}` exactly as `ergodic_relabel_shift_bondPercolation` carries it for bonds. -/
theorem ergodic_siteShift (p : unitInterval) {v : Site d} (hv : v ≠ 0) :
    Ergodic (siteShift v) (siteBernoulli fun _ : Site d => p) := by
  classical
  have herg : Ergodic (coordShift (X := Prop) (fun x : Site d => x + v))
      (Measure.infinitePi fun _ : Site d =>
        unitInterval.toNNReal p • Measure.dirac True +
          unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False) :=
    ergodic_coordShift_infinitePi _ (add_left_injective v) (fun _ => rfl)
      fun s => exists_iterate_add_notMem hv s
  have hmp : MeasurePreserving (fun q : Site d → Prop => {i | q i})
      (Measure.infinitePi fun _ : Site d =>
        unitInterval.toNNReal p • Measure.dirac True +
          unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False)
      (siteBernoulli fun _ : Site d => p) :=
    ⟨measurable_setOf, (prodBernoulli_eq_map _).symm⟩
  exact hmp.ergodic_of_ergodic_semiconj herg (measurable_siteShift v) fun q => rfl

/-- **Zero–one law for translation-invariant events of the site measure.** -/
theorem siteBernoulli_zero_one_of_shift (p : unitInterval) {v : Site d} (hv : v ≠ 0)
    {A : Set (SiteConfig (Site d))} (hA : MeasurableSet A) (hinv : siteShift v ⁻¹' A = A) :
    (siteBernoulli fun _ : Site d => p) A = 0 ∨ (siteBernoulli fun _ : Site d => p) A = 1 :=
  (ergodic_siteShift p hv).toPreErgodic.prob_eq_zero_or_one hA hinv

end Shift

/-! ## Uniqueness, in the form used below -/

section Uniqueness

variable {d : ℕ}

/-- The event that at most one open cluster is infinite. -/
def uniqueEvent (d : ℕ) : Set (SiteConfig (Site d)) :=
  {ω | numInfiniteSiteClusters (zdGraph d) ω ≤ 1}

/-- On the uniqueness event, two percolating sites are joined. -/
theorem reachable_of_uniqueEvent {ω : SiteConfig (Site d)} (hω : ω ∈ uniqueEvent d) {x y : Site d}
    (hx : ω ∈ sitePerc (zdGraph d) x) (hy : ω ∈ sitePerc (zdGraph d) y) :
    (openSiteGraph (zdGraph d) ω).Reachable x y :=
  (numInfiniteSiteClusters_le_one_iff _ ω).1 hω x y hx hy

/-- The uniqueness hypothesis, read as the nullity of the complement of `uniqueEvent`. -/
theorem measure_compl_uniqueEvent (huniq : SiteUniquenessInfiniteCluster) (d : ℕ)
    (p : unitInterval) :
    (siteBernoulli fun _ : Site d => p) (uniqueEvent d)ᶜ = 0 := by
  have h := huniq d p
  rw [ae_iff] at h
  exact h

end Uniqueness

/-! ## The coalescence field -/

section Coalescence

variable {d : ℕ}

/-- **The two-arm failure event.**  The clusters of `x` and of `y` both reach the sphere of radius
`M`, and yet `x` and `y` are not joined. -/
def armsFail (d M : ℕ) (x y : Site d) : Set (SiteConfig (Site d)) :=
  (siteConnSet (zdGraph d) x (boxSphere d M) ∩ siteConnSet (zdGraph d) y (boxSphere d M)) \
    siteConn (zdGraph d) x y

/-- The two-arm failure event is measurable. -/
theorem measurableSet_armsFail (d M : ℕ) (x y : Site d) : MeasurableSet (armsFail d M x y) :=
  ((measurableSet_siteConnSet_countable _ x _).inter
    (measurableSet_siteConnSet_countable _ y _)).diff (measurableSet_siteConn _ x y)

/-- **The two-arm failure events decrease in the radius**, for sites of the inner box: this is the
first-exit lemma applied to both arms. -/
theorem armsFail_antitone {m : ℕ} {x y : Site d} (hx : x ∈ box d m) (hy : y ∈ box d m) :
    Antitone fun k : ℕ => armsFail d (m + k) x y := by
  intro k k' hkk ω hω
  refine ⟨⟨?_, ?_⟩, hω.2⟩
  · exact siteConnSet_boxSphere_antitone (box_mono d (Nat.le_add_right m k) hx)
      (Nat.add_le_add_left hkk m) hω.1.1
  · exact siteConnSet_boxSphere_antitone (box_mono d (Nat.le_add_right m k) hy)
      (Nat.add_le_add_left hkk m) hω.1.2

/-- **An arm to every sphere is an infinite cluster.**  The sphere of radius `M` determines `M`, so
the sites the arms reach are pairwise distinct. -/
theorem sitePerc_of_forall_siteConnSet {m : ℕ} {ω : SiteConfig (Site d)} {z : Site d}
    (hz : ∀ k : ℕ, ω ∈ siteConnSet (zdGraph d) z (boxSphere d (m + k))) :
    ω ∈ sitePerc (zdGraph d) z := by
  choose a ha hza using fun k : ℕ => (by
    simpa only [siteConnSet, Set.mem_iUnion, exists_prop] using hz k :
    ∃ a, a ∈ boxSphere d (m + k) ∧ ω ∈ siteConn (zdGraph d) z a)
  rw [mem_sitePerc_iff]
  refine Set.infinite_of_injective_forall_mem (f := a) (fun k k' hkk => ?_) fun k => (hza k).2
  have h2 : a k ∈ boxSphere d (m + k') := by rw [hkk]; exact ha k'
  have h3 := boxSphere_radius_unique (ha k) h2
  omega

/-- **The two-arm failure events intersect in a two-cluster event.** -/
theorem iInter_armsFail_subset {m : ℕ} {x y : Site d} :
    (⋂ k : ℕ, armsFail d (m + k) x y) ⊆
      (sitePerc (zdGraph d) x ∩ sitePerc (zdGraph d) y) \ siteConn (zdGraph d) x y := by
  intro ω hω
  simp only [Set.mem_iInter] at hω
  exact ⟨⟨sitePerc_of_forall_siteConnSet fun k => (hω k).1.1,
    sitePerc_of_forall_siteConnSet fun k => (hω k).1.2⟩, (hω 0).2⟩

/-- **Two unjoined infinite clusters form a null event**, by uniqueness. -/
theorem measure_twoCluster_eq_zero (huniq : SiteUniquenessInfiniteCluster) (d : ℕ)
    (p : unitInterval) (x y : Site d) :
    (siteBernoulli fun _ : Site d => p)
      ((sitePerc (zdGraph d) x ∩ sitePerc (zdGraph d) y) \ siteConn (zdGraph d) x y) = 0 := by
  refine measure_mono_null ?_ (measure_compl_uniqueEvent huniq d p)
  intro ω hω hu
  exact hω.2 ⟨mem_of_mem_sitePerc hω.1.1, reachable_of_uniqueEvent hu hω.1.1 hω.1.2⟩

/-- **The coalescence field.**  For every inner scale and every error there is one annulus radius
that works for all pairs of sites of the inner box. -/
theorem exists_radius_armsFail_le (huniq : SiteUniquenessInfiniteCluster) (d : ℕ)
    (p : unitInterval) (m : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ M > m, ∀ x ∈ box d m, ∀ y ∈ box d m,
      (siteBernoulli fun _ : Site d => p).real (armsFail d M x y) ≤ η := by
  classical
  have key : ∀ᶠ k : ℕ in Filter.atTop, ∀ q ∈ (box d m) ×ˢ (box d m),
      (siteBernoulli fun _ : Site d => p).real (armsFail d (m + k) q.1 q.2) ≤ η := by
    rw [Filter.eventually_all_finset]
    intro q hq
    rw [Finset.mem_product] at hq
    have htend : Filter.Tendsto
        (fun k : ℕ => (siteBernoulli fun _ : Site d => p) (armsFail d (m + k) q.1 q.2))
        Filter.atTop
        (nhds ((siteBernoulli fun _ : Site d => p) (⋂ k : ℕ, armsFail d (m + k) q.1 q.2))) :=
      tendsto_measure_iInter_atTop
        (fun k => (measurableSet_armsFail d (m + k) q.1 q.2).nullMeasurableSet)
        (armsFail_antitone hq.1 hq.2) ⟨0, measure_ne_top _ _⟩
    rw [measure_mono_null iInter_armsFail_subset
      (measure_twoCluster_eq_zero huniq d p q.1 q.2)] at htend
    have htend' : Filter.Tendsto
        (fun k : ℕ => (siteBernoulli fun _ : Site d => p).real (armsFail d (m + k) q.1 q.2))
        Filter.atTop (nhds (ENNReal.toReal 0)) :=
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
    rw [ENNReal.toReal_zero] at htend'
    exact (htend'.eventually_lt_const hη).mono fun k hk => hk.le
  obtain ⟨k, hk, hk0⟩ := (key.and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨m + k, by omega, fun x hx y hy => hk (x, y) (Finset.mem_product.2 ⟨hx, hy⟩)⟩

end Coalescence

/-! ## The face-hitting field -/

section FaceHit

variable {d : ℕ}

/-- The event that some open cluster is infinite. -/
def percSomewhere (d : ℕ) : Set (SiteConfig (Site d)) :=
  ⋃ z : Site d, sitePerc (zdGraph d) z

theorem measurableSet_percSomewhere (d : ℕ) : MeasurableSet (percSomewhere d) :=
  MeasurableSet.iUnion fun z => measurableSet_sitePerc _ z

/-- The percolation event of `x` under a translated configuration. -/
theorem mem_sitePerc_siteShift (v z : Site d) (ω : SiteConfig (Site d)) :
    siteShift v ω ∈ sitePerc (zdGraph d) z ↔ ω ∈ sitePerc (zdGraph d) (z + v) := by
  rw [← sitePerc_siteShift v z]
  exact Iff.rfl

/-- **The existence of an infinite cluster is translation invariant.** -/
theorem preimage_siteShift_percSomewhere (v : Site d) :
    siteShift v ⁻¹' percSomewhere d = percSomewhere d := by
  ext ω
  simp only [percSomewhere, Set.mem_preimage, Set.mem_iUnion, mem_sitePerc_siteShift]
  exact ⟨fun ⟨z, hz⟩ => ⟨z + v, hz⟩, fun ⟨u, hu⟩ => ⟨u - v, by simpa using hu⟩⟩

/-- **Almost surely there is an infinite cluster**, at a parameter where the origin percolates: the
event is translation invariant, hence trivial by the zero–one law, and it is not null. -/
theorem measure_percSomewhere_eq_one (hd : 0 < d) (p : unitInterval) (hp : 0 < thetaSite d p) :
    (siteBernoulli fun _ : Site d => p) (percSomewhere d) = 1 := by
  have hv : (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℤ) : Site d) ≠ 0 := by
    intro h
    have h2 := congrFun h (⟨0, hd⟩ : Fin d)
    simp at h2
  have hne : (siteBernoulli fun _ : Site d => p) (percSomewhere d) ≠ 0 := by
    intro h0
    have h1 : (siteBernoulli fun _ : Site d => p) (sitePerc (zdGraph d) (0 : Site d)) = 0 :=
      measure_mono_null (Set.subset_iUnion (fun z => sitePerc (zdGraph d) z) 0) h0
    have hset : {ω : SiteConfig (Site d) | (siteCluster (zdGraph d) ω 0).Infinite}
        = sitePerc (zdGraph d) (0 : Site d) := Set.ext fun ω => siteCluster_infinite_iff _ ω 0
    have h2 : thetaSite d p = 0 := by
      rw [thetaSite, thetaSiteOn, hset, measureReal_def, h1, ENNReal.toReal_zero]
    exact hp.ne' h2
  rcases siteBernoulli_zero_one_of_shift p hv (measurableSet_percSomewhere d)
    (preimage_siteShift_percSomewhere _) with h | h
  · exact absurd h hne
  · exact h

/-! ### The half-space events -/

/-- **Every infinite cluster lies in the half space `{y | k ≤ ε * y i}`.**  Only `ε = ±1` is used;
the sign is carried as a parameter so that both half spaces are one family. -/
def halfEvent (d : ℕ) (i : Fin d) (ε k : ℤ) : Set (SiteConfig (Site d)) :=
  {ω | (∃ z, ω ∈ sitePerc (zdGraph d) z) ∧
    ∀ z, ω ∈ sitePerc (zdGraph d) z →
      ∀ y, (openSiteGraph (zdGraph d) ω).Reachable z y → k ≤ ε * y i}

theorem measurableSet_halfEvent (i : Fin d) (ε k : ℤ) : MeasurableSet (halfEvent d i ε k) := by
  have hset : halfEvent d i ε k = percSomewhere d ∩
      ⋂ z : Site d, ⋂ y ∈ {y : Site d | ¬ (k ≤ ε * y i)},
        (sitePerc (zdGraph d) z ∩ siteReach (zdGraph d) z y)ᶜ := by
    ext ω
    simp only [halfEvent, percSomewhere, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion,
      Set.mem_iInter, Set.mem_compl_iff, siteReach]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun z y hy hmem => hy (h2 z hmem.1 y hmem.2)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun z hz y hyr => ?_⟩
      by_contra hcon
      exact h2 z y hcon ⟨hz, hyr⟩
  rw [hset]
  exact (measurableSet_percSomewhere d).inter
    (MeasurableSet.iInter fun z => MeasurableSet.biInter (Set.to_countable _)
      fun y _ => ((measurableSet_sitePerc _ z).inter (measurableSet_siteReach _ z y)).compl)

/-- **The half-space events translate.** -/
theorem preimage_siteShift_halfEvent (i : Fin d) (ε k : ℤ) (v : Site d) :
    siteShift v ⁻¹' halfEvent d i ε k = halfEvent d i ε (k + ε * v i) := by
  ext ω
  simp only [halfEvent, Set.mem_preimage, Set.mem_setOf_eq, mem_sitePerc_siteShift,
    reachable_siteShift_iff]
  constructor
  · rintro ⟨⟨z, hz⟩, h2⟩
    refine ⟨⟨z + v, hz⟩, fun z' hz' y hy => ?_⟩
    have h3 := h2 (z' - v) (by simpa using hz') (y - v) (by simpa using hy)
    have h4 : ε * ((y - v) i) = ε * y i - ε * v i := by rw [Pi.sub_apply, mul_sub]
    rw [h4] at h3
    linarith
  · rintro ⟨⟨z, hz⟩, h2⟩
    refine ⟨⟨z - v, by simpa using hz⟩, fun z' hz' y hy => ?_⟩
    have h3 := h2 (z' + v) hz' (y + v) hy
    have h4 : ε * ((y + v) i) = ε * y i + ε * v i := by rw [Pi.add_apply, mul_add]
    rw [h4] at h3
    linarith

theorem halfEvent_antitone (i : Fin d) (ε : ℤ) :
    Antitone fun n : ℕ => halfEvent d i ε (n : ℤ) := by
  intro n n' hnn ω hω
  refine ⟨hω.1, fun z hz y hy => le_trans ?_ (hω.2 z hz y hy)⟩
  exact_mod_cast hnn

/-- **No infinite cluster lies in every half space.**  An infinite cluster has a site, and that site
has a fixed coordinate. -/
theorem iInter_halfEvent_eq_empty (i : Fin d) (ε : ℤ) :
    (⋂ n : ℕ, halfEvent d i ε (n : ℤ)) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨z, hz⟩ := (h 0).1
  have hbound := (h ((ε * z i).toNat + 1)).2 z hz z (SimpleGraph.Reachable.refl z)
  push_cast at hbound
  omega

/-- **The half-space events are null.**  Their probability does not depend on the half space, by
translation invariance, while the intersection over the half spaces is empty. -/
theorem measure_halfEvent_one_eq_zero (p : unitInterval) (i : Fin d) (ε : ℤ) (hε : ε * ε = 1) :
    (siteBernoulli fun _ : Site d => p) (halfEvent d i ε 1) = 0 := by
  have hshift : ∀ k : ℤ, (siteBernoulli fun _ : Site d => p) (halfEvent d i ε (k + 1))
      = (siteBernoulli fun _ : Site d => p) (halfEvent d i ε k) := by
    intro k
    have h := (measurePreserving_siteShift p (Pi.single i ε)).measure_preimage
      (measurableSet_halfEvent i ε k).nullMeasurableSet
    rw [preimage_siteShift_halfEvent i ε k (Pi.single i ε)] at h
    simpa only [Pi.single_eq_same, hε] using h
  have hconst : ∀ n : ℕ, (siteBernoulli fun _ : Site d => p) (halfEvent d i ε (n : ℤ))
      = (siteBernoulli fun _ : Site d => p) (halfEvent d i ε 0) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, hshift, ih]
  have htend := tendsto_measure_iInter_atTop
    (μ := siteBernoulli fun _ : Site d => p)
    (s := fun n : ℕ => halfEvent d i ε (n : ℤ))
    (fun n => (measurableSet_halfEvent i ε (n : ℤ)).nullMeasurableSet)
    (halfEvent_antitone i ε) ⟨0, measure_ne_top _ _⟩
  rw [iInter_halfEvent_eq_empty i ε, measure_empty] at htend
  have htend2 : Filter.Tendsto
      (fun n : ℕ => (siteBernoulli fun _ : Site d => p) (halfEvent d i ε (n : ℤ)))
      Filter.atTop (nhds 0) := htend
  simp only [hconst] at htend2
  have h0 : (siteBernoulli fun _ : Site d => p) (halfEvent d i ε 0) = 0 :=
    tendsto_const_nhds_iff.1 htend2
  have h1 := hshift 0
  norm_num at h1
  rw [h1, h0]

/-! ### The hyperplane and its exhausting boxes -/

/-- The hyperplane `{y | y i = 0}`. -/
def hyperplane (d : ℕ) (i : Fin d) : Set (Site d) := {y | y i = 0}

/-- The centred box of side `2m+1` inside the hyperplane `{y | y i = 0}`. -/
def hyperBox (d : ℕ) (i : Fin d) (m : ℕ) : Set (Site d) :=
  {y | y i = 0 ∧ ∀ j, j ≠ i → -(m : ℤ) ≤ y j ∧ y j ≤ m}

theorem hyperBox_subset {i : Fin d} {m m' : ℕ} (h : m ≤ m') :
    hyperBox d i m ⊆ hyperBox d i m' := by
  rintro y ⟨hy, hb⟩
  refine ⟨hy, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := hb j hj
  constructor <;> omega

theorem iUnion_hyperBox (i : Fin d) : (⋃ m : ℕ, hyperBox d i m) = hyperplane d i := by
  ext y
  simp only [Set.mem_iUnion, hyperBox, hyperplane, Set.mem_setOf_eq]
  refine ⟨fun ⟨_, hm, _⟩ => hm, fun hy => ⟨Finset.univ.sup fun j => (y j).natAbs, hy, ?_⟩⟩
  intro j _
  have h : (y j).natAbs ≤ Finset.univ.sup fun j => (y j).natAbs :=
    Finset.le_sup (f := fun j : Fin d => (y j).natAbs) (Finset.mem_univ j)
  have h2 : |y j| ≤ ((Finset.univ.sup fun j => (y j).natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  exact abs_le.1 h2

/-- The event that no site of `S` lies in an infinite cluster. -/
def missEvent (d : ℕ) (S : Set (Site d)) : Set (SiteConfig (Site d)) :=
  {ω | ∀ z ∈ S, ω ∉ sitePerc (zdGraph d) z}

theorem measurableSet_missEvent (S : Set (Site d)) : MeasurableSet (missEvent d S) := by
  have hset : missEvent d S = ⋂ z ∈ S, (sitePerc (zdGraph d) z)ᶜ := by
    ext ω
    simp only [missEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
  rw [hset]
  exact MeasurableSet.biInter (Set.to_countable S) fun z _ => (measurableSet_sitePerc _ z).compl

theorem missEvent_antitone (i : Fin d) : Antitone fun m : ℕ => missEvent d (hyperBox d i m) :=
  fun _ _ h _ hω z hz => hω z (hyperBox_subset h hz)

theorem iInter_missEvent_hyperBox (i : Fin d) :
    (⋂ m : ℕ, missEvent d (hyperBox d i m)) = missEvent d (hyperplane d i) := by
  ext ω
  simp only [Set.mem_iInter, missEvent, Set.mem_setOf_eq]
  constructor
  · intro h z hz
    rw [← iUnion_hyperBox i] at hz
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hz
    exact h m z hm
  · intro h m z hz
    exact h z (by rw [← iUnion_hyperBox i]; exact Set.mem_iUnion.2 ⟨m, hz⟩)

/-- **The hyperplane is met by an infinite cluster, almost surely.**  On the uniqueness event, an
infinite cluster missing the hyperplane is connected and so lies in one of the two half spaces, and
those events are null. -/
theorem missEvent_hyperplane_subset (i : Fin d) :
    missEvent d (hyperplane d i) ⊆
      ((percSomewhere d)ᶜ ∪ (uniqueEvent d)ᶜ) ∪ (halfEvent d i 1 1 ∪ halfEvent d i (-1) 1) := by
  intro ω hω
  by_cases hperc : ω ∈ percSomewhere d
  · by_cases hu : ω ∈ uniqueEvent d
    · obtain ⟨z₀, hz₀⟩ := Set.mem_iUnion.1 hperc
      have hperc_of_reach : ∀ y : Site d, (openSiteGraph (zdGraph d) ω).Reachable z₀ y →
          ω ∈ sitePerc (zdGraph d) y := by
        intro y hy
        rw [mem_sitePerc_iff] at hz₀ ⊢
        have hset : {u : Site d | (openSiteGraph (zdGraph d) ω).Reachable z₀ u}
            = {u : Site d | (openSiteGraph (zdGraph d) ω).Reachable y u} :=
          Set.ext fun u => ⟨fun h => hy.symm.trans h, fun h => hy.trans h⟩
        rwa [hset] at hz₀
      have hA : ∀ y : Site d, (openSiteGraph (zdGraph d) ω).Reachable z₀ y → y i ≠ 0 := by
        intro y hy hyi
        exact hω y hyi (hperc_of_reach y hy)
      have hivt : ∀ y y' : Site d, (openSiteGraph (zdGraph d) ω).Reachable z₀ y →
          (openSiteGraph (zdGraph d) ω).Reachable z₀ y' → y i ≤ 0 → 0 ≤ y' i → False := by
        intro y y' hy hy' h1 h2
        obtain ⟨q⟩ := hy.symm.trans hy'
        obtain ⟨t, hrt, ht⟩ := exists_reachable_coord_eq_zero i q h1 h2
        exact hA t (hy.trans hrt) ht
      have hreach : ∀ z : Site d, ω ∈ sitePerc (zdGraph d) z →
          ∀ y : Site d, (openSiteGraph (zdGraph d) ω).Reachable z y →
            (openSiteGraph (zdGraph d) ω).Reachable z₀ y := by
        intro z hz y hy
        exact (reachable_of_uniqueEvent hu hz₀ hz).trans hy
      right
      rcases lt_or_gt_of_ne (hA z₀ (SimpleGraph.Reachable.refl z₀)) with hneg | hpos
      · right
        refine ⟨⟨z₀, hz₀⟩, fun z hz y hy => ?_⟩
        by_contra hcon
        push Not at hcon
        exact hivt z₀ y (SimpleGraph.Reachable.refl z₀) (hreach z hz y hy) (by omega) (by omega)
      · left
        refine ⟨⟨z₀, hz₀⟩, fun z hz y hy => ?_⟩
        by_contra hcon
        push Not at hcon
        exact hivt y z₀ (hreach z hz y hy) (SimpleGraph.Reachable.refl z₀) (by omega) (by omega)
    · exact Or.inl (Or.inr hu)
  · exact Or.inl (Or.inl hperc)

theorem measure_missEvent_hyperplane_eq_zero (huniq : SiteUniquenessInfiniteCluster) (hd : 0 < d)
    (p : unitInterval) (hp : 0 < thetaSite d p) (i : Fin d) :
    (siteBernoulli fun _ : Site d => p) (missEvent d (hyperplane d i)) = 0 := by
  refine measure_mono_null (missEvent_hyperplane_subset i) (measure_union_null
    (measure_union_null ?_ (measure_compl_uniqueEvent huniq d p))
    (measure_union_null (measure_halfEvent_one_eq_zero p i 1 (by ring))
      (measure_halfEvent_one_eq_zero p i (-1) (by ring))))
  rw [measure_compl (measurableSet_percSomewhere d) (measure_ne_top _ _),
    measure_percSomewhere_eq_one hd p hp, measure_univ, tsub_self]

/-! ### From the hyperplane to the faces of a box -/

/-- **The missing event translates.** -/
theorem preimage_siteShift_missEvent (v : Site d) (S : Set (Site d)) :
    siteShift v ⁻¹' missEvent d S = missEvent d {u : Site d | u - v ∈ S} := by
  ext ω
  simp only [missEvent, Set.mem_preimage, Set.mem_setOf_eq, mem_sitePerc_siteShift]
  constructor
  · intro h u hu
    simpa using h (u - v) hu
  · intro h z hz
    exact h (z + v) (by simpa using hz)

/-- **A face of `box d m` is a translate of the hyperplane box of side `2m+1`.** -/
theorem boxFace_eq_preimage (d m : ℕ) (i : Fin d) (b : Bool) :
    boxFace d m i b =
      {u : Site d | u - Pi.single i (if b then (m : ℤ) else -(m : ℤ)) ∈ hyperBox d i m} := by
  ext u
  simp only [boxFace, hyperBox, Set.mem_setOf_eq, Pi.sub_apply, Pi.single_eq_same, sub_eq_zero]
  constructor
  · rintro ⟨hb, hi⟩
    refine ⟨hi, fun j hj => ?_⟩
    rw [Pi.single_apply, if_neg hj, sub_zero]
    exact hb j
  · rintro ⟨hi, hj⟩
    refine ⟨fun j => ?_, hi⟩
    by_cases hji : j = i
    · subst hji
      rw [hi]
      cases b <;> simp
    · have h := hj j hji
      rwa [Pi.single_apply, if_neg hji, sub_zero] at h

theorem measureReal_missEvent_boxFace (p : unitInterval) (d m : ℕ) (i : Fin d) (b : Bool) :
    (siteBernoulli fun _ : Site d => p).real (missEvent d (boxFace d m i b))
      = (siteBernoulli fun _ : Site d => p).real (missEvent d (hyperBox d i m)) := by
  have h := MeasurePreserving.measure_preimage
    (measurePreserving_siteShift p (Pi.single i (if b then (m : ℤ) else -(m : ℤ))))
    (measurableSet_missEvent (hyperBox d i m)).nullMeasurableSet
  rw [preimage_siteShift_missEvent, ← boxFace_eq_preimage] at h
  rw [measureReal_def, measureReal_def, h]

/-! ### The face-hitting event -/

/-- The event that some open cluster meets all `2d` faces of `box d m`. -/
def faceEvent (d m : ℕ) : Set (SiteConfig (Site d)) :=
  {ω | ∃ x : Site d, ∀ (i : Fin d) (b : Bool),
    (siteCluster (zdGraph d) ω x ∩ boxFace d m i b).Nonempty}

theorem measurableSet_faceEvent (d m : ℕ) : MeasurableSet (faceEvent d m) := by
  have hset : faceEvent d m =
      ⋃ x : Site d, ⋂ q : Fin d × Bool, siteConnSet (zdGraph d) x (boxFace d m q.1 q.2) := by
    ext ω
    simp only [faceEvent, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.inter_nonempty,
      siteConnSet, exists_prop]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, fun q => by obtain ⟨y, hy1, hy2⟩ := hx q.1 q.2; exact ⟨y, hy2, hy1⟩⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, fun i b => by obtain ⟨y, hy1, hy2⟩ := hx (i, b); exact ⟨y, hy2, hy1⟩⟩
  rw [hset]
  exact MeasurableSet.iUnion fun x =>
    MeasurableSet.iInter fun q => measurableSet_siteConnSet_countable _ x _

/-- **Faces met by infinite clusters give one cluster meeting all of them**, by uniqueness. -/
theorem faceEvent_superset (d m : ℕ) (hd : 0 < d) :
    uniqueEvent d ∩ (⋂ q : Fin d × Bool, (missEvent d (boxFace d m q.1 q.2))ᶜ) ⊆ faceEvent d m := by
  rintro ω ⟨hu, hmiss⟩
  have hmiss' : ∀ q : Fin d × Bool, ∃ z ∈ boxFace d m q.1 q.2, ω ∈ sitePerc (zdGraph d) z := by
    intro q
    by_contra hcon
    push Not at hcon
    exact (Set.mem_iInter.1 hmiss q) fun z hz => hcon z hz
  choose z hz hzperc using hmiss'
  refine ⟨z (⟨0, hd⟩, true), fun i b => ⟨z (i, b), ⟨?_, ?_⟩, hz (i, b)⟩⟩
  · exact mem_of_mem_sitePerc (hzperc (⟨0, hd⟩, true))
  · exact reachable_of_uniqueEvent hu (hzperc (⟨0, hd⟩, true)) (hzperc (i, b))

/-- **The face-hitting field.**  Beyond a scale that depends only on the error, every box has, with
high probability, an open cluster meeting all `2d` of its faces. -/
theorem exists_scale_faceEvent_ge (huniq : SiteUniquenessInfiniteCluster) (hd : 0 < d)
    (p : unitInterval) (hp : 0 < thetaSite d p) (η : ℝ) (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      1 - η ≤ (siteBernoulli fun _ : Site d => p).real (faceEvent d m) := by
  classical
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : 0 < η / (2 * (d : ℝ)) := by positivity
  have hlim : ∀ i : Fin d, Filter.Tendsto
      (fun m : ℕ => (siteBernoulli fun _ : Site d => p).real (missEvent d (hyperBox d i m)))
      Filter.atTop (nhds 0) := by
    intro i
    have h := tendsto_measure_iInter_atTop
      (μ := siteBernoulli fun _ : Site d => p)
      (s := fun m : ℕ => missEvent d (hyperBox d i m))
      (fun m => (measurableSet_missEvent (hyperBox d i m)).nullMeasurableSet)
      (missEvent_antitone i) ⟨0, measure_ne_top _ _⟩
    rw [iInter_missEvent_hyperBox i, measure_missEvent_hyperplane_eq_zero huniq hd p hp i] at h
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rwa [ENNReal.toReal_zero] at h'
  have hev : ∀ᶠ m : ℕ in Filter.atTop, ∀ i : Fin d,
      (siteBernoulli fun _ : Site d => p).real (missEvent d (hyperBox d i m))
        < η / (2 * (d : ℝ)) := by
    rw [Filter.eventually_all]
    exact fun i => (hlim i).eventually_lt_const hc
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨m₀, fun m hm => ?_⟩
  have hfaces : ∀ q : Fin d × Bool,
      (siteBernoulli fun _ : Site d => p).real (missEvent d (boxFace d m q.1 q.2))
        ≤ η / (2 * (d : ℝ)) := by
    intro q
    rw [measureReal_missEvent_boxFace p d m q.1 q.2]
    exact (hm₀ m hm q.1).le
  have hsub : (faceEvent d m)ᶜ ⊆ (uniqueEvent d)ᶜ ∪
      ⋃ q ∈ (Finset.univ : Finset (Fin d × Bool)), missEvent d (boxFace d m q.1 q.2) := by
    intro ω hω
    by_cases hu : ω ∈ uniqueEvent d
    · refine Or.inr ?_
      simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and]
      by_contra hcon
      push Not at hcon
      exact hω (faceEvent_superset d m hd ⟨hu, Set.mem_iInter.2 fun q => hcon q⟩)
    · exact Or.inl hu
  have hzero : (siteBernoulli fun _ : Site d => p).real (uniqueEvent d)ᶜ = 0 := by
    rw [measureReal_def, measure_compl_uniqueEvent huniq d p, ENNReal.toReal_zero]
  have hcard : (Finset.univ : Finset (Fin d × Bool)).card = 2 * d := by
    simp [Finset.card_univ, Fintype.card_prod, mul_comm]
  have hsumconst : ∑ _q : Fin d × Bool, (η / (2 * (d : ℝ))) = η := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    field_simp
  have hbound : (siteBernoulli fun _ : Site d => p).real (faceEvent d m)ᶜ ≤ η := by
    calc (siteBernoulli fun _ : Site d => p).real (faceEvent d m)ᶜ
        ≤ (siteBernoulli fun _ : Site d => p).real ((uniqueEvent d)ᶜ ∪
            ⋃ q ∈ (Finset.univ : Finset (Fin d × Bool)), missEvent d (boxFace d m q.1 q.2)) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (siteBernoulli fun _ : Site d => p).real (uniqueEvent d)ᶜ +
            (siteBernoulli fun _ : Site d => p).real
              (⋃ q ∈ (Finset.univ : Finset (Fin d × Bool)), missEvent d (boxFace d m q.1 q.2)) :=
          measureReal_union_le _ _
      _ ≤ ∑ q ∈ (Finset.univ : Finset (Fin d × Bool)),
            (siteBernoulli fun _ : Site d => p).real (missEvent d (boxFace d m q.1 q.2)) := by
          rw [hzero, zero_add]
          exact measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _q : Fin d × Bool, (η / (2 * (d : ℝ))) :=
          Finset.sum_le_sum fun q _ => hfaces q
      _ = η := hsumconst
  have hcompl : (siteBernoulli fun _ : Site d => p).real (faceEvent d m)ᶜ
      = 1 - (siteBernoulli fun _ : Site d => p).real (faceEvent d m) := by
    rw [measureReal_compl (measurableSet_faceEvent d m), probReal_univ]
  rw [hcompl] at hbound
  linarith

end FaceHit

/-! ## The structure -/

section Assemble

/-- **The local inputs of the geometric construction, from supercriticality and uniqueness.**  The
coalescence field needs uniqueness only; the face-hitting field needs both, and in dimension zero it
holds vacuously, there being no faces to meet. -/
theorem siteLocalInputs_of_uniqueness (huniq : SiteUniquenessInfiniteCluster) (d : ℕ)
    (p : unitInterval) (hp : 0 < thetaSite d p) : SiteLocalInputs d p where
  coalescence m η hη := exists_radius_armsFail_le huniq d p m η hη
  faceHit η hη := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      refine ⟨0, fun m _ => ?_⟩
      have hset : {ω : SiteConfig (Site 0) | ∃ x : Site 0, ∀ (i : Fin 0) (b : Bool),
          (siteCluster (zdGraph 0) ω x ∩ boxFace 0 m i b).Nonempty} = Set.univ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact ⟨0, fun i => i.elim0⟩
      rw [hset, probReal_univ]
      linarith
    · exact exists_scale_faceEvent_ge huniq hd p hp η hη

/-- **The local inputs at a supercritical parameter.**  Uniqueness is discharged by
`SiteUniquenessInfiniteCluster_holds` of `KN/SiteUniqueness.lean`, so nothing is assumed beyond
`0 < thetaSite d p`. -/
theorem siteLocalInputs_of_thetaSite_pos (d : ℕ) (p : unitInterval) (hp : 0 < thetaSite d p) :
    SiteLocalInputs d p :=
  siteLocalInputs_of_uniqueness SiteUniquenessInfiniteCluster_holds d p hp

end Assemble

#print axioms siteLocalInputs_of_uniqueness
#print axioms siteLocalInputs_of_thetaSite_pos
#check @siteLocalInputs_of_uniqueness
#check @siteLocalInputs_of_thetaSite_pos





end KNAll.Site

end
