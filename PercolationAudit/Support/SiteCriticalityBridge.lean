import Mathlib
import Hypergraph.FinalCriticality
import PercolationAudit.SiteCriticality.SolutionBasic

/-!
# Comparator bridge: `PercolationAudit.SiteCriticality` vocabulary → repository

This file connects the statement-audit vocabulary of
`PercolationAudit/SiteCriticality/Challenge.lean` (copied verbatim into
`PercolationAudit/SiteCriticality/SolutionBasic.lean`, which imports only Mathlib) to the objects
of the repository `Hypergraph` and of its dependency `PercolationContinuity`, so that
`PercolationAudit/SiteCriticality/Solution.lean` is literal gluing.

**It is imported by the `Solution` file only.**  The `Challenge` and `SolutionBasic` files
must stay Mathlib-only: a repository import inside the vocabulary changes instance
elaboration there and breaks the comparator's constant-by-constant closure check.

The audit vocabulary is a token-for-token copy of the repository's, so every bridge here is
`rfl`.  There is no `structure` or `inductive` in the vocabulary, hence no field-by-field
conversion.
-/

namespace PercolationAudit
namespace Support
namespace SiteCriticalityBridge

open MeasureTheory

/-- The audit vocabulary agrees with the repository definitionally.  These `rfl` lemmas
record the identifications the solution relies on. -/
theorem site_eq (d : ℕ) :
    KNAll.StatementAudit.SiteCriticality.Site d =
      Percolation.Literature.LatticeModels.Site d := rfl

theorem zdGraph_eq (d : ℕ) :
    KNAll.StatementAudit.SiteCriticality.zdGraph d =
      Percolation.Literature.LatticeModels.zdGraph d := rfl

theorem prodBernoulli_eq {ι : Type*} (p : ι → unitInterval) :
    KNAll.StatementAudit.SiteCriticality.prodBernoulli p =
      Percolation.Literature.LatticeModels.prodBernoulli p := rfl

theorem openSiteGraph_eq {V : Type*} (G : SimpleGraph V) (ω : Set V) :
    KNAll.StatementAudit.SiteCriticality.openSiteGraph G ω = KNAll.Site.openSiteGraph G ω := rfl

theorem siteCluster_eq {V : Type*} (G : SimpleGraph V) (ω : Set V) (x : V) :
    KNAll.StatementAudit.SiteCriticality.siteCluster G ω x = KNAll.Site.siteCluster G ω x := rfl

theorem siteBernoulli_eq {V : Type*} (w : V → unitInterval) :
    KNAll.StatementAudit.SiteCriticality.siteBernoulli w = KNAll.Site.siteBernoulli w := rfl

theorem thetaSiteOn_eq {V : Type*} (G : SimpleGraph V) (x : V) (p : unitInterval) :
    KNAll.StatementAudit.SiteCriticality.thetaSiteOn G x p = KNAll.Site.thetaSiteOn G x p := rfl

theorem thetaSite_eq (d : ℕ) (p : unitInterval) :
    KNAll.StatementAudit.SiteCriticality.thetaSite d p = KNAll.Site.thetaSite d p := rfl

theorem criticalProbSite_eq (d : ℕ) :
    KNAll.StatementAudit.SiteCriticality.criticalProbSite d = KNAll.Site.criticalProbSite d := rfl

theorem criticalProbSiteI_eq (d : ℕ) :
    KNAll.StatementAudit.SiteCriticality.criticalProbSiteI d = KNAll.Site.criticalProbSiteI d :=
  rfl

end SiteCriticalityBridge
end Support
end PercolationAudit
