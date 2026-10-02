import Mathlib
import Hypergraph.FinalCriticality
import PercolationAudit.SiteCriticality.SolutionBasic
import PercolationAudit.Support.SiteCriticalityBridge

/-!
# Solution: `SiteCriticality` (site percolation at criticality)

The challenge module `PercolationAudit/SiteCriticality/Challenge.lean` imports only Mathlib and
states `site_no_percolation_at_critical` with one intentional `sorry`.  This solution imports the
repository `Hypergraph` together with `PercolationAudit.SiteCriticality.SolutionBasic` — a
verbatim copy of the challenge's statement vocabulary — and proves the byte-identical statement
from `KNAll.Site.site_no_percolation_at_critical` (`Hypergraph/FinalCriticality.lean`) through
the identifications recorded in `PercolationAudit/Support/SiteCriticalityBridge.lean`.

The transport is definitional.  The audit vocabulary (`Site`, `zdGraph`, `prodBernoulli`,
`siteCluster`, `thetaSite`, `criticalProbSiteI`, …) is a token-for-token copy of the repository's
and of its `PercolationContinuity` dependency's, so the library theorem's type is definitionally
equal to the goal.  The vocabulary has no structure-typed hypothesis, so no conversion
lemma is needed.
-/

open MeasureTheory Set

namespace KNAll
namespace StatementAudit
namespace SiteCriticality

/-- **No site percolation at the critical parameter, in every dimension at least three**
(`KNAll.Site.site_no_percolation_at_critical`, `Hypergraph/FinalCriticality.lean`): for
nearest-neighbour Bernoulli site percolation on `ℤ^d` with `d ≥ 3`, the probability that the open
cluster of the origin is infinite vanishes at the critical parameter. -/
theorem site_no_percolation_at_critical (d : ℕ) (hd : 3 ≤ d) :
    thetaSite d (criticalProbSiteI d) = 0 := by
  exact KNAll.Site.site_no_percolation_at_critical d hd

end SiteCriticality
end StatementAudit
end KNAll
