import Hypergraph.SiteOneArm

/-!
# The local inputs of the geometric construction

The geometric construction consumes a handful of *local* consequences of supercriticality: that a
large box contains a big cluster, that two long arms belong to the same cluster, that a big cluster
reaches every face of a large box.  Only the first of these follows from `θ(p) > 0` alone; the other
two are the local face of the uniqueness of the infinite cluster, whose proof is Burton–Keane
together with the ergodicity of the site measure under the lattice translations.  That is a separate
development, and this module does not attempt it.

What is proved here:

* `thetaSiteOn_le_clusterAtLeast` — the probability that the open cluster of `x` has at least `n`
  vertices is at least `θ(p)`, for every `n`.  The infinite-cluster event is contained in each
  one-arm event, which is `siteInfinite_eq_iInter_clusterAtLeast` read in one direction.
* `exists_pos_forall_clusterAtLeast` — the same bound in the form the construction asks for: a
  single positive constant below every one-arm probability.
* `thetaSiteOn_pos_iff` — with `thetaSiteOn_pos_of_forall_le` of `KN.SiteOneArm`, which is the
  converse, a uniform positive one-arm bound is *equivalent* to a positive percolation probability.
  Neither direction needs anything beyond continuity from above.

What is only *stated* here: `SiteLocalInputs d p`, a structure whose two fields are the local facts
the construction needs and that are not available in the development.  Carrying them as an explicit
hypothesis is what keeps the chain honest: every theorem that uses them displays them.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V : Type*}

/-! ## What supercriticality gives for free -/

/-- **Every one-arm probability is at least `θ(p)`.**  A configuration whose open cluster at `x` is
infinite has, for each `n`, a set of `n` vertices in that cluster, so the infinite-cluster event is
contained in `clusterAtLeast G x n`. -/
theorem thetaSiteOn_le_clusterAtLeast [Countable V] (G : SimpleGraph V) (x : V)
    (p : unitInterval) (n : ℕ) :
    thetaSiteOn G x p ≤ (siteBernoulli (fun _ : V => p)).real (clusterAtLeast G x n) := by
  have hsub : {ω : SiteConfig V | (siteCluster G ω x).Infinite} ⊆ clusterAtLeast G x n := by
    rw [siteInfinite_eq_iInter_clusterAtLeast]
    exact Set.iInter_subset _ n
  rw [thetaSiteOn]
  exact measureReal_mono hsub (measure_ne_top _ _)

/-- **A uniform positive one-arm bound**, in the form the geometric construction wants: at a
parameter where the origin percolates, one constant lies below every one-arm probability.  The
constant is `θ(p)` itself. -/
theorem exists_pos_forall_clusterAtLeast [Countable V] (G : SimpleGraph V)
    (x : V) (p : unitInterval) (h : 0 < thetaSiteOn G x p) :
    ∃ c > 0, ∀ n, c ≤ (siteBernoulli (fun _ : V => p)).real (clusterAtLeast G x n) :=
  ⟨thetaSiteOn G x p, h, fun n => thetaSiteOn_le_clusterAtLeast G x p n⟩

/-- **Percolation is exactly a uniform one-arm bound.**  The forward direction is
`exists_pos_forall_clusterAtLeast`, the backward one `thetaSiteOn_pos_of_forall_le` of
`KN.SiteOneArm`; the second is continuity from above, and the first is the containment of the
infinite-cluster event in each one-arm event. -/
theorem thetaSiteOn_pos_iff [Countable V] (G : SimpleGraph V) (x : V) (p : unitInterval) :
    0 < thetaSiteOn G x p ↔
      ∃ c > 0, ∀ n, c ≤ (siteBernoulli (fun _ : V => p)).real (clusterAtLeast G x n) :=
  ⟨exists_pos_forall_clusterAtLeast G x p,
    fun ⟨c, hc, h⟩ => thetaSiteOn_pos_of_forall_le G x p c hc h⟩

/-! ## The regions the local inputs speak about

Two subsets of the centred cube `box d M`, written directly as sets of sites so that the statements
below can be read off without further vocabulary: its sup-norm sphere, and one of its `2d` faces. -/

/-- The sup-norm sphere of radius `M`: the sites of `box d M` having a coordinate equal to `M` or to
`-M`.  A path leaving `box d M` from inside meets it, so `siteConnSet G x (boxSphere d M)` is the
event that the open cluster of `x` reaches distance `M`, an event of the finite region `box d M`. -/
def boxSphere (d M : ℕ) : Set (Site d) :=
  {x | (∀ j, -(M : ℤ) ≤ x j ∧ x j ≤ M) ∧ ∃ j, x j = (M : ℤ) ∨ x j = -(M : ℤ)}

/-- The face of `box d M` in the coordinate `i`, on the upper side when `b = true` and on the lower
side when `b = false`. -/
def boxFace (d M : ℕ) (i : Fin d) (b : Bool) : Set (Site d) :=
  {x | (∀ j, -(M : ℤ) ≤ x j ∧ x j ≤ M) ∧ x i = if b then (M : ℤ) else -(M : ℤ)}

/-- Each face lies on the sphere, so a cluster meeting a face reaches distance `M`. -/
theorem boxFace_subset_boxSphere (d M : ℕ) (i : Fin d) (b : Bool) :
    boxFace d M i b ⊆ boxSphere d M := by
  rintro x ⟨hx, hi⟩
  refine ⟨hx, i, ?_⟩
  cases b
  · exact Or.inr (by simpa using hi)
  · exact Or.inl (by simpa using hi)

/-! ## The interface -/

/-- **The local inputs of the geometric construction, as a hypothesis.**  Neither field is proved in
this development: both are local forms of the uniqueness of the infinite cluster, and uniqueness is
Burton–Keane together with ergodicity, which is out of scope here.  Everything downstream that uses
them carries `SiteLocalInputs d p` and so displays its dependence on them.

Both statements speak about finite regions only: no infinite-cluster event appears in either.

## References

* R. M. Burton, M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
* G. R. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2 (uniqueness) and §7.4, §8.3 (block
  arguments in the supercritical phase). -/
structure SiteLocalInputs (d : ℕ) (p : unitInterval) : Prop where
  /-- **Two long arms belong to one cluster.**  Fix an inner box `box d m`.  For every `η > 0` there
  is a radius `M > m` such that, for any two sites `x, y` of the inner box, the probability that the
  open clusters of `x` and of `y` both reach the sphere of radius `M`, and yet `x` and `y` are not
  connected to one another, is at most `η`.  Two clusters crossing the annulus between `box d m` and
  `box d M` therefore coalesce with probability at least `1 - η`.

  In the supercritical phase this is uniqueness read at finite volume: the events `{x reaches the
  sphere of radius M}` decrease, as `M` grows, to `{the cluster of x is infinite}`, and the limiting
  event `{|C x| = ∞, |C y| = ∞, x ↮ y}` is null exactly because the infinite cluster is unique. -/
  coalescence : ∀ m : ℕ, ∀ η : ℝ, 0 < η → ∃ M > m, ∀ x ∈ box d m, ∀ y ∈ box d m,
    (siteBernoulli (fun _ : Site d => p)).real
        ((siteConnSet (zdGraph d) x (boxSphere d M) ∩
            siteConnSet (zdGraph d) y (boxSphere d M)) \ siteConn (zdGraph d) x y) ≤ η
  /-- **A cluster reaching every face of a large box.**  For every `η > 0` there is a scale `m₀`
  such that for every `m ≥ m₀` the probability that some open cluster meets all `2d` faces of
  `box d m` is at least `1 - η`.  In particular each single face is met with probability at least
  `1 - η`.

  The cluster is the ambient one: the connections witnessing it are not required to stay inside
  `box d m`, so this is implied by, and weaker than, the usual statement that `box d m` contains an
  open crossing cluster. -/
  faceHit : ∀ η : ℝ, 0 < η → ∃ m₀ : ℕ, ∀ m ≥ m₀,
    1 - η ≤ (siteBernoulli (fun _ : Site d => p)).real
      {ω | ∃ x : Site d, ∀ (i : Fin d) (b : Bool),
        (siteCluster (zdGraph d) ω x ∩ boxFace d m i b).Nonempty}

end KNAll.Site

end
