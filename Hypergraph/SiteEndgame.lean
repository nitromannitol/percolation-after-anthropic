import Hypergraph.SitePlanarInput
import Hypergraph.SiteCriticalBounds

/-!
# The critical parameter of site percolation is nondegenerate, and the endgame is unconditional

`criticalProbSite_pos` (`KN/SiteCriticalBounds.lean`) and `exists_thetaSite_pos`
(`KN/SitePlanarInput.lean`) together place the critical parameter strictly inside the unit interval.
That removes both side hypotheses from `siteCriticality_of_slabReductionBelow`, so the
below-parameter route to `SiteCriticality` rests on the reduction alone: no theorem about
percolation at a critical point, and no imported half-space or slab statement.
-/

noncomputable section

namespace KNAll.Site

open Percolation.Literature

/-- **`p_c < 1` for site percolation on `ℤ^d`, `d ≥ 2`.**  Site percolation occurs at some parameter
below one, by the half-edge comparison with bond percolation, and the critical parameter is at most
any such parameter. -/
theorem criticalProbSite_lt_one (d : ℕ) [NeZero d] (hd : 2 ≤ d) : criticalProbSite d < 1 := by
  obtain ⟨a, ha1, hapos⟩ := exists_thetaSite_pos d hd
  exact lt_of_le_of_lt (criticalProbSite_le_of_pos d a hapos) ha1

/-- The critical parameter lies strictly inside the unit interval. -/
theorem criticalProbSite_mem_Ioo (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    criticalProbSite d ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨criticalProbSite_pos d, criticalProbSite_lt_one d hd⟩

/-- **The below-parameter endgame, with no side hypotheses.**  If percolation at a parameter strictly
inside the unit interval forces percolation in a slab at some strictly smaller parameter, then there
is no percolation at the critical parameter.  Nothing else is assumed: in particular no half-space
theorem and no statement about percolation at a critical point. -/
theorem siteCriticality_of_slabReductionBelow' (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hred : SiteSlabReductionBelow d) : SiteCriticality d :=
  siteCriticality_of_slabReductionBelow d (criticalProbSite_pos d) (criticalProbSite_lt_one d hd)
    hred

end KNAll.Site

end
