import Mathlib

/-!
# Statement-level audit vocabulary for the `SiteCriticality` comparator

Verbatim copy of the vocabulary block of
`PercolationAudit/SiteCriticality/Challenge.lean` (between `VOCABULARY-BEGIN` and
`VOCABULARY-END`), Mathlib-only; a mechanical copy, not hand-edited.  The two
blocks must stay byte-identical so that the comparator's constant-by-constant
closure check passes.
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
end SiteCriticality
end StatementAudit
end KNAll
