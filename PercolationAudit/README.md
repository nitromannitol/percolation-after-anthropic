# PercolationAudit Comparator Surface

This directory contains a Mathlib-only comparator challenge for the headline theorem of the
formalization *Percolation after Anthropic* (Ahmed Bou-Rabee and Justin Leder): nearest-neighbour
Bernoulli site percolation on `ℤ^d`, `d ≥ 3`, has no infinite open cluster at its critical
parameter, `θ(p_c) = 0`.

| Directory | Checked theorem |
| --- | --- |
| `SiteCriticality/` | `KNAll.StatementAudit.SiteCriticality.site_no_percolation_at_critical` |

`SiteCriticality/Challenge.lean` imports only `Mathlib`, rebuilds from scratch every definition
needed to read the theorem — the lattice `Site d = Fin d → ℤ` and its nearest-neighbour graph
`zdGraph`, the product Bernoulli measure `prodBernoulli`, site configurations and open clusters
(`SiteConfig`, `openSiteGraph`, `siteCluster`), the site percolation measure `siteBernoulli`, the
percolation probability `thetaSite`, and the critical parameter `criticalProbSite` as a point
`criticalProbSiteI` of the unit interval — states the theorem, and ends with one `sorry`, the
proof being checked.

## What Is Checked

The theorem states that for every `d ≥ 3`, `thetaSite d (criticalProbSiteI d) = 0`:

- **Model.** A site configuration is the set `ω` of open vertices of `ℤ^d`; each vertex is open
  independently with probability `p`, under `prodBernoulli (fun _ => p)`.  Two vertices are joined
  when a nearest-neighbour path of open vertices connects them; a closed vertex has an empty open
  cluster.
- **Percolation probability.** `θ(p) = thetaSite d p` is the probability that the open cluster of
  the origin is infinite.
- **Critical parameter.** `p_c = criticalProbSite d` is the infimum of
  `{p ∈ [0, 1] | θ(p) > 0} ∪ {1}`; `criticalProbSiteI d` is the same number as a point of the unit
  interval, built from the proof `criticalProbSite_mem_Icc` that it lies in `[0, 1]`.
- **Conclusion.** `θ(p_c) = 0`.

The statement has no hypothesis other than the dimension `d` and `3 ≤ d`.  The library's
certified statement is `KNAll.Site.site_no_percolation_at_critical`
(`Hypergraph/FinalCriticality.lean`); the challenge states the same theorem over the copied
vocabulary.  The two small theorems `criticalProbSite_nonneg_mem` and `criticalProbSite_mem_Icc`
belong to the vocabulary, because the proof term of `criticalProbSiteI` mentions them; they are
copied with their proofs.

## Definition Provenance

The challenge definitions are statement-level copies of the repository definitions needed to
state the theorem surface.  The first three come from the `PercolationContinuity` dependency
(`anthropics/formal-math`, commit `795efb86f191735c5481675763537cfb4ff37e55`, subdirectory
`percolation`); the rest are in `Hypergraph/SiteStatements.lean`.

| Challenge declaration | Repository source |
| --- | --- |
| `Site` | `percolation/Percolation/Literature/LatticeModels/LatticeGraph.lean:48` (dependency) |
| `zdGraph` | `percolation/Percolation/Literature/LatticeModels/LatticeGraph.lean:93` (dependency) |
| `prodBernoulli` | `percolation/Percolation/Literature/LatticeModels/ProdBernoulli.lean:46` (dependency) |
| `SiteConfig` | `Hypergraph/SiteStatements.lean:33` |
| `openSiteGraph` | `Hypergraph/SiteStatements.lean:38` |
| `siteCluster` | `Hypergraph/SiteStatements.lean:43` |
| `siteBernoulli` | `Hypergraph/SiteStatements.lean:55` |
| `thetaSiteOn` | `Hypergraph/SiteStatements.lean:63` |
| `thetaSite` | `Hypergraph/SiteStatements.lean:123` |
| `criticalProbSite` | `Hypergraph/SiteStatements.lean:129` |
| `criticalProbSite_nonneg_mem` | `Hypergraph/SiteStatements.lean:134` |
| `criticalProbSite_mem_Icc` | `Hypergraph/SiteStatements.lean:141` |
| `criticalProbSiteI` | `Hypergraph/SiteStatements.lean:153` |
| `site_no_percolation_at_critical` | `Hypergraph/FinalCriticality.lean` (`KNAll.Site.site_no_percolation_at_critical`) |

## Reproducing The Checks

The comparator configuration permits only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enables the nanoda replay.  The challenge elaborates standalone against this repository's
Mathlib toolchain:

```bash
bash PercolationAudit/check_standalone.sh PercolationAudit/SiteCriticality/Challenge.lean
bash PercolationAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'` warning.  The solution
builds with `lake build PercolationAudit`.  Then, with `leanprover/comparator`, `lean4export` (at
the toolchain's tag) and `landrun` built at the pins below, from the repository root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator PercolationAudit/SiteCriticality/comparator.json
```

expecting `Your solution is okay!`.

**Status.**  The challenge elaborates on Mathlib alone with one intentional `sorry`; the
solution builds and proves the byte-identical statement from
`KNAll.Site.site_no_percolation_at_critical` through the definitional identifications in
`PercolationAudit/Support/SiteCriticalityBridge.lean`; `leanprover/comparator` at commit
`575674928e239f5bc452aab72d1dd7b0f1326494`, with nanoda at `6ae1f0cd962f081f6c423454c5da729d841236a7`
and landrun at `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, printed `Your solution is okay!`
with the nanoda kernel enabled.
