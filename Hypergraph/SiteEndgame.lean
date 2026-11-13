import Hypergraph.SitePlanarInput
import Hypergraph.SiteCriticalBounds

/-!
# The critical parameter of site percolation is nondegenerate

`criticalProbSite_pos` (`KN/SiteCriticalBounds.lean`) and `exists_thetaSite_pos`
(`KN/SitePlanarInput.lean`) together place the critical parameter strictly inside the unit interval.
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

end KNAll.Site

end
