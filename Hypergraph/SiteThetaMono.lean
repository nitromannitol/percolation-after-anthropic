import Hypergraph.SiteStatements

/-!
# Monotonicity of the site percolation probability

Two facts about `KNAll.Site.thetaSiteOn` that the definition of the critical parameter is set up to
supply.

* `thetaSite_eq_zero_of_lt_criticalProbSite`: below the critical parameter the origin does not
  percolate.  This is immediate from `criticalProbSite_le_of_pos`, which says that every parameter
  at which the origin percolates is at least the critical one.
* `thetaSiteOn_mono`: the percolation probability is a non-decreasing function of the parameter.
  The proof is Grimmett's monotone coupling (1999, §1.4 p. 13; Thm. (2.1) p. 32, (2.3)), carried out
  on the vertices rather than the edges: attach independent uniform `[0, 1]` labels to the vertices
  and call a vertex open when its label is at most `p`.  The configuration at `p₁` is then contained
  in the configuration at `p₂` whenever `p₁ ≤ p₂`, and the event that the open cluster of `x` is
  infinite is increasing.  The coupling itself is already available for an arbitrary index type as
  `Percolation.Literature.LatticeModels.prodBernoulli_real_mono_of_isUpperSet`, so only the two
  properties of the event are proved here: it is increasing (`isUpperSet_siteInfinite`) and it is
  measurable (`KNAll.Site.measurableSet_siteInfinite`).

`Percolation.Literature.theta_mono_holds` is the same statement for bond percolation.

## References

* G. R. Grimmett, *Percolation*, 2nd ed., Springer (1999), §1.4 (p. 13) and Thm. (2.1) (pp. 32–33).
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Below the critical parameter there is no percolation -/

/-- **No percolation strictly below the critical parameter.**  A positive percolation probability at
`p` would place the critical parameter at or below `p` by `criticalProbSite_le_of_pos`. -/
theorem thetaSite_eq_zero_of_lt_criticalProbSite (d : ℕ) (p : unitInterval)
    (hp : (p : ℝ) < criticalProbSite d) : thetaSite d p = 0 := by
  by_contra hne
  have hpos : 0 < thetaSite d p :=
    lt_of_le_of_ne (thetaSiteOn_nonneg (zdGraph d) (0 : Site d) p) (Ne.symm hne)
  exact absurd (criticalProbSite_le_of_pos d p hpos) (not_le.2 hp)

/-! ## The percolation probability is non-decreasing in the parameter -/

section Mono

variable {V : Type*}

/-- Opening more vertices opens more edges. -/
theorem openSiteGraph_mono (G : SimpleGraph V) {ω ω' : SiteConfig V} (h : ω ⊆ ω') :
    openSiteGraph G ω ≤ openSiteGraph G ω' := by
  refine SimpleGraph.le_iff_adj.2 fun a b hab => ?_
  rw [openSiteGraph_adj_iff'] at hab ⊢
  exact ⟨hab.1, h hab.2.1, h hab.2.2⟩

/-- Opening more vertices enlarges the open cluster of `x`. -/
theorem siteCluster_mono (G : SimpleGraph V) {ω ω' : SiteConfig V} (h : ω ⊆ ω') (x : V) :
    siteCluster G ω x ⊆ siteCluster G ω' x := by
  rintro y ⟨hx, hr⟩
  exact ⟨h hx, hr.mono (openSiteGraph_mono G h)⟩

/-- **The infinite-cluster event is increasing**: it is preserved by opening further vertices. -/
theorem isUpperSet_siteInfinite (G : SimpleGraph V) (x : V) :
    IsUpperSet {ω : SiteConfig V | (siteCluster G ω x).Infinite} :=
  fun _ _ h hω => hω.mono (siteCluster_mono G h x)

/-- **The percolation probability is non-decreasing in the parameter.**  Grimmett's monotone
coupling on the vertices: the event that the open cluster of `x` is infinite is increasing and
measurable, and `prodBernoulli` is monotone in its parameters on such events.
[cite: GrimmettPercolation1999, §1.4 p. 13; Thm. (2.1) (2.3) pp. 32–33] -/
theorem thetaSiteOn_mono [Countable V] (G : SimpleGraph V) (x : V) :
    Monotone (thetaSiteOn G x) := by
  intro p q hpq
  simp only [thetaSiteOn, siteBernoulli]
  exact prodBernoulli_real_mono_of_isUpperSet (fun _ : V => hpq) (isUpperSet_siteInfinite G x)
    (measurableSet_siteInfinite G x)

end Mono

/-- The percolation probability of site percolation on `ℤ^d` is non-decreasing in `p`. -/
theorem thetaSite_mono (d : ℕ) : Monotone (thetaSite d) :=
  thetaSiteOn_mono (zdGraph d) (0 : Site d)

end KNAll.Site

end
