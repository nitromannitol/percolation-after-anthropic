import Hypergraph.SitePlanarInput
import Hypergraph.SiteThetaMono

/-!
# The planar input to the renormalization comparison

The renormalization argument compares a coarse lattice with ordinary site percolation on the plane
at a density close to one.  It uses one fact about the plane, that site percolation there percolates
at *some* density below one, and it uses neither the value of the planar critical parameter nor any
statement about percolation at a critical point.  This file isolates that fact and the two
consequences the comparison consumes.

* `HighDensityPlanarSite` names the fact, and `highDensityPlanarSite_holds` proves it by reading
  `KNAll.Site.exists_thetaSite_pos` at `d = 2`.
* `thetaSite_pos_of_le` upgrades it from one density to every larger one, using the monotone
  coupling packaged as `KNAll.Site.thetaSite_mono` in `KN/SiteThetaMono.lean`.
* `exists_planar_threshold` and `exists_ambient_threshold` combine the two into the form the
  geometry quotes: a density below one above which every density percolates, on the plane and on
  `ℤ^d` respectively.

The bound `criticalProbSite d ≤ p` for a density `p` at which the origin percolates is
`KNAll.Site.criticalProbSite_le_of_pos` in `KN/SiteStatements.lean`; it is not restated here.
-/

noncomputable section

namespace KNAll.Site

/-! ## The planar input -/

/-- **Site percolation on the plane percolates at some density below one.**  This is the only fact
about `ℤ^2` that the renormalization comparison needs. -/
def HighDensityPlanarSite : Prop :=
  ∃ a : unitInterval, (a : ℝ) < 1 ∧ 0 < thetaSite 2 a

/-- The planar input holds: it is `exists_thetaSite_pos` at `d = 2`. -/
theorem highDensityPlanarSite_holds : HighDensityPlanarSite :=
  exists_thetaSite_pos 2 le_rfl

/-! ## Upward closure -/

/-- **Percolation at a density persists at every larger density.**  The percolation probability is
non-decreasing in the parameter by the monotone coupling `thetaSite_mono`. -/
theorem thetaSite_pos_of_le {d : ℕ} {a b : unitInterval} (hab : a ≤ b)
    (ha : 0 < thetaSite d a) : 0 < thetaSite d b :=
  lt_of_lt_of_le ha (thetaSite_mono d hab)

/-! ## The threshold form -/

/-- **A planar threshold.**  There is a density below one above which the plane percolates at every
density.  The comparison shows that the coarse lattice dominates site percolation at some density,
and needs only that the density may be taken above a fixed threshold below one. -/
theorem exists_planar_threshold :
    ∃ a : unitInterval, (a : ℝ) < 1 ∧ ∀ b : unitInterval, a ≤ b → 0 < thetaSite 2 b := by
  obtain ⟨a, ha1, hapos⟩ := highDensityPlanarSite_holds
  exact ⟨a, ha1, fun _ hab => thetaSite_pos_of_le hab hapos⟩

/-- **A threshold for the ambient lattice.**  The comparison is planar, while the conclusion is
about `ℤ^d`, so the same packaging is recorded for every `d ≥ 2`. -/
theorem exists_ambient_threshold (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ a : unitInterval, (a : ℝ) < 1 ∧ ∀ b : unitInterval, a ≤ b → 0 < thetaSite d b := by
  obtain ⟨a, ha1, hapos⟩ := exists_thetaSite_pos d hd
  exact ⟨a, ha1, fun _ hab => thetaSite_pos_of_le hab hapos⟩

end KNAll.Site

end
