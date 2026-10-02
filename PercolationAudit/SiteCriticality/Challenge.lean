import Mathlib

/-!
# Site percolation at criticality — comparator challenge

Mathlib-only comparator challenge for the headline theorem of the formalization
*Percolation after Anthropic* (Ahmed Bou-Rabee and Justin Leder): nearest-neighbour Bernoulli
**site** percolation on `ℤ^d`, `d ≥ 3`, has no infinite open cluster at its critical parameter,
`θ(p_c) = 0`.  The library's statement is `KNAll.Site.site_no_percolation_at_critical` in
`Hypergraph/FinalCriticality.lean`.

This file imports only `Mathlib` — no repository module — and rebuilds from Mathlib primitives
every definition needed to read the theorem: the lattice `Site d = Fin d → ℤ` with its
nearest-neighbour graph `zdGraph`, the product Bernoulli measure `prodBernoulli`, site
configurations and open clusters (`SiteConfig`, `openSiteGraph`, `siteCluster`), the site
percolation measure `siteBernoulli`, the percolation probability `thetaSite`, and the critical
parameter `criticalProbSite`, regarded as a point `criticalProbSiteI d` of the unit interval.  The
definitions are statement-level copies of the repository's, token for token.  The sole
intentional `sorry` is the proof of the final theorem.

The vocabulary between `VOCABULARY-BEGIN` and `VOCABULARY-END` is copied verbatim into
`SolutionBasic.lean`; the two must stay byte-identical so that the comparator's
constant-by-constant closure check passes.
-/

open MeasureTheory Set

namespace KNAll
namespace StatementAudit
namespace SiteCriticality

-- VOCABULARY-BEGIN
/-! ## The lattice `ℤ^d` (`LatticeGraph.lean` of the `PercolationContinuity` dependency) -/

/-- A site of the hypercubic lattice `ℤ^d`: a function `Fin d → ℤ`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The nearest-neighbour graph on `ℤ^d`, Mathlib's Hasse diagram of the product order. -/
noncomputable abbrev zdGraph (d : ℕ) : SimpleGraph (Site d) := SimpleGraph.hasse (Site d)

/-! ## The product Bernoulli measure (`ProdBernoulli.lean` of the `PercolationContinuity`
dependency) -/

section ProdBernoulli

variable {ι : Type*}

/-- The product of Bernoulli measures with parameters `p i` on `Set ι`: each `i` belongs to the
random set independently with probability `p i`. -/
noncomputable def prodBernoulli (p : ι → unitInterval) : Measure (Set ι) :=
  .comap (fun s i => i ∈ s) <| Measure.infinitePi fun i : ι =>
    unitInterval.toNNReal (p i) • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm (p i)) • Measure.dirac False

end ProdBernoulli

/-! ## Site percolation on a graph (`Hypergraph/SiteStatements.lean`) -/

/-- A site configuration: the set of open vertices. -/
abbrev SiteConfig (V : Type*) : Type _ := Set V

variable {V : Type*}

/-- The graph of open vertices: an edge of `G` survives when both of its endpoints are open. -/
def openSiteGraph (G : SimpleGraph V) (ω : SiteConfig V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => G.Adj x y ∧ x ∈ ω ∧ y ∈ ω

/-- The open cluster of `x`: empty when `x` is closed, and otherwise the set of vertices joined to
`x` by a path of open vertices. -/
def siteCluster (G : SimpleGraph V) (ω : SiteConfig V) (x : V) : Set V :=
  {y | x ∈ ω ∧ (openSiteGraph G ω).Reachable x y}

/-- Site percolation with vertex probabilities `w`: each vertex is open independently. -/
noncomputable def siteBernoulli (w : V → unitInterval) : Measure (SiteConfig V) := prodBernoulli w

/-- Site percolation on an arbitrary graph: the probability that the open cluster of `x` is
infinite when every vertex is open with probability `p`. -/
noncomputable def thetaSiteOn (G : SimpleGraph V) (x : V) (p : unitInterval) : ℝ :=
  (siteBernoulli (fun _ : V => p)).real {ω | (siteCluster G ω x).Infinite}

/-- The percolation probability of site percolation on `ℤ^d` at parameter `p`: the probability that
the open cluster of the origin is infinite. -/
noncomputable def thetaSite (d : ℕ) (p : unitInterval) : ℝ :=
  thetaSiteOn (zdGraph d) (0 : Site d) p

/-- The critical parameter of site percolation on `ℤ^d`: the infimum of the parameters at which the
origin percolates, together with `1`. -/
noncomputable def criticalProbSite (d : ℕ) : ℝ :=
  sInf ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSite d ⟨p, h⟩} ∪ {1})

/-- The set whose infimum defines the critical parameter consists of nonnegative numbers. -/
theorem criticalProbSite_nonneg_mem (d : ℕ) :
    ∀ p ∈ ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSite d ⟨p, h⟩} ∪ {1}), 0 ≤ p := by
  rintro p (⟨h, -⟩ | h)
  · exact h.1
  · rw [Set.mem_singleton_iff] at h
    rw [h]; exact zero_le_one

/-- The critical parameter lies in the unit interval. -/
theorem criticalProbSite_mem_Icc (d : ℕ) : criticalProbSite d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_csInf ⟨1, Or.inr rfl⟩ (criticalProbSite_nonneg_mem d),
    csInf_le ⟨0, criticalProbSite_nonneg_mem d⟩ (Or.inr rfl)⟩

/-- The critical parameter as a point of the unit interval, so that it can be fed to `thetaSite`. -/
noncomputable def criticalProbSiteI (d : ℕ) : unitInterval :=
  ⟨criticalProbSite d, criticalProbSite_mem_Icc d⟩
-- VOCABULARY-END

/-! ## The theorem -/

/-- **No site percolation at the critical parameter, in every dimension at least three**
(`KNAll.Site.site_no_percolation_at_critical`, `Hypergraph/FinalCriticality.lean`): for
nearest-neighbour Bernoulli site percolation on `ℤ^d` with `d ≥ 3`, the probability that the open
cluster of the origin is infinite vanishes at the critical parameter. -/
theorem site_no_percolation_at_critical (d : ℕ) (hd : 3 ≤ d) :
    thetaSite d (criticalProbSiteI d) = 0 := by
  sorry

end SiteCriticality
end StatementAudit
end KNAll
