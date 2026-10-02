# Percolation after Anthropic

A machine-checked **Lean 4** development of the Kozma–Nitzan connection inequalities for Bernoulli percolation and of their extension to independent hyperedges and site percolation. Its headline theorem is that nearest-neighbour Bernoulli site percolation on `ℤ^d`, `d ≥ 3`, has no infinite open cluster at its critical parameter, `θ_site(p_c) = 0`.

The development builds on [Anthropic's bond-percolation proof](https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation), a pinned git dependency, and on [mathlib](https://github.com/leanprover-community/mathlib4). The results on the Kozma–Nitzan conjectures are stated precisely in the accompanying manuscript, [`docs/kn-results.pdf`](docs/kn-results.pdf) ([LaTeX](docs/kn-results.tex)), which follows the numbering of [Kozma and Nitzan's paper](https://arxiv.org/abs/2401.12397). [`VERIFICATION.md`](VERIFICATION.md) records the review and the reproducible checks.

## What is proved

**The headline theorem.** [`Hypergraph/FinalCriticality.lean`](Hypergraph/FinalCriticality.lean) proves

```lean
KNAll.Site.site_no_percolation_at_critical (d : ℕ) (hd : 3 ≤ d) :
  thetaSite d (criticalProbSiteI d) = 0
```

where `thetaSite d p` is the probability that the open cluster of the origin is infinite for site percolation on `ℤ^d` in which every vertex is open independently with probability `p`, and `criticalProbSite d` is the infimum of `{p ∈ [0,1] | θ(p) > 0} ∪ {1}`, regarded as a point `criticalProbSiteI d` of the unit interval. The theorem has no argument other than the dimension and `3 ≤ d`. The same file states the conclusion with the cluster and measure definitions unfolded (`site_no_percolation_at_critical_expanded` and `site_no_percolation_at_critical_primitive`), proves that the critical parameter lies strictly between zero and one (`criticalProbSite_mem_Ioo_of_three_le`), and bundles the phase transition in `site_phase_transition`. The planar site result is outside this declaration's scope.

**The Kozma–Nitzan inequalities.** [`KNConjectures/`](KNConjectures/) contains the finite bond results, with the numbering of Kozma and Nitzan (there is no Conjecture 5 and no Question 6). Here `o ↔ A` means that `o` is connected to some vertex of `A` in a finite weighted graph with independent edges.

| Paper | Lean statement | File |
| --- | --- | --- |
| Conjecture 1, `P(o ↔ b) ≥ P(o ↔ A) min_{x∈A} P(x ↔ b)` | `KNAll.conjecture1_holds` | [`Conjectures.lean`](KNConjectures/Conjectures.lean) |
| Conjecture 1, derived directly from the bond-percolation proof of the dependency | `KN1Corollary.kozmaNitzan_conjecture1` | [`KozmaNitzanConjecture1.lean`](KNConjectures/KozmaNitzanConjecture1.lean) |
| Conjecture 2 and its strong form (display (3)) | `KNAll.conjecture2_holds`, `KNAll.conjecture2Strong_holds` | [`Conjectures.lean`](KNConjectures/Conjectures.lean) |
| Conjecture 3 | `KNAll.conjecture3_holds` | [`Conjectures.lean`](KNConjectures/Conjectures.lean) |
| Conjecture 4, with the minimizer fixed before conditioning, and for monotone cluster properties | `KNAll.conjecture4_holds`, `KNAll.conjecture4Fixed_holds`, `KNAll.conjecture4_clusterProperty_holds` | [`Conjectures.lean`](KNConjectures/Conjectures.lean), [`ClusterProperty.lean`](KNConjectures/ClusterProperty.lean) |
| Conjecture 6, and its strong form without the endpoint hypotheses of display (39) | `KNAll.Guarded.conjecture6_holds`, `KNAll.Guarded.conjecture6Strong_holds` | [`Conjecture6Proof.lean`](KNConjectures/Conjecture6Proof.lean) |
| Question 5 | `KNAll.question5_holds` | [`Question5.lean`](KNConjectures/Question5.lean) |
| Question 7 | `KNAll.question7_holds` | [`Conjectures.lean`](KNConjectures/Conjectures.lean) |
| Question 8, every-minimizer reading: a counterexample | `KNAll.not_question8EveryMin` | [`Question8Counterexample.lean`](KNConjectures/Question8Counterexample.lean) |
| Question 9 | `KNAll.question9_holds`, from `KNAll.setSourceFixedMin_holds` | [`Question9.lean`](KNConjectures/Question9.lean), [`Question9Reduction.lean`](KNConjectures/Question9Reduction.lean) |
| The comparison principle for increasing functions of a cluster conditioned to avoid a set | `KNAll.genY_all` | [`Conjectures.lean`](KNConjectures/Conjectures.lean) |

These are affirmative answers to Questions 5, 7 and 9 and a counterexample to the **every-minimizer** reading of Question 8: the inequality fails for a vertex that minimizes the avoidance-conditioned score `P(a ↔ b, o ↮ A)` on a four-vertex graph in which `P(o ↮ A) = 0` and both vertices of `A` minimize. The distinction matters when minimizers tie, and the counterexample does not refute an existential choice among tied minimizers. Conjecture 1 follows from the strong form of Conjecture 2 by Harris's inequality, and Conjecture 3 from Conjecture 1.

**Hypergraphs and site percolation.** [`Hypergraph/`](Hypergraph/) proves the finite connection inequality for independent labelled hyperedges, represents site percolation by incidence hyperedges, and carries out the lattice exploration and the parameter descent that give the headline theorem.

- `KNAll.Site.FiniteHyperGluingClosed.hyperedgeGluing` ([`FiniteHyperGluingClosed.lean`](Hypergraph/FiniteHyperGluingClosed.lean)): in every finite model of independent hyperedges, `P(o ↔ b, o ↔ A) ≥ P(o ↔ A) min_{a∈A} P(a ↔ b)`; for edges of size two this is the finite inequality of Conjecture 1.
- `KNAll.Site.FiniteHyperGluingClosed.pinnedSiteGluing`: the same inequality for site percolation on a finite graph when the observer, the target and the vertices of `A` are open with probability one. `KNAll.Site.siteGluingUnpinned_of_hyperedgeGluing` ([`SiteRepresentation.lean`](Hypergraph/SiteRepresentation.lean)) removes the pinning when the observer and the target are distinct and lie outside `A`.
- [`ExactReachableMacroInterpreter.lean`](Hypergraph/ExactReachableMacroInterpreter.lean) and [`CoreSafeBenchmark.lean`](Hypergraph/CoreSafeBenchmark.lean) carry out the exploration and its comparison process, and [`ExactCommonQAssembly.lean`](Hypergraph/ExactCommonQAssembly.lean) assembles the common smaller parameter.

**What is conditional.** Nothing is. Every statement above is a proved theorem; none carries a hypothesis on a cited result, and the headline theorem has no hypothesis other than `d` and `3 ≤ d`. The development depends on the proved bond-percolation library, whose theorems `Percolation.Continuity.CSH.cshHolds` and `Percolation.Continuity.CSH.percolationContinuity_allDimensions` (`θ(p_c) = 0` for bond percolation, `d ≥ 2`) belong to that dependency and not to this repository.

**Correspondence with the sources.** The Kozma–Nitzan statements are closed propositions in [`Statements.lean`](KNConjectures/Statements.lean), [`Statements6.lean`](KNConjectures/Statements6.lean), [`Statements9.lean`](KNConjectures/Statements9.lean) and [`Question8Defs.lean`](KNConjectures/Question8Defs.lean), whose docstrings give the page or display of Kozma and Nitzan; Conjecture 3 is the dependency's `Percolation.Literature.KozmaNitzan2024_conjecture3`, and Question 5 is stated by its theorem. The section "Lean Verification" of the [manuscript](docs/kn-results.tex) lists the correspondences that are not literal: `KNAll.genY_all` yields the manuscript's comparison theorem after an order-equivalent rank replaces the real-valued order; `KNAll.setSourceFixedMin_holds` also covers the empty source; and the formal Conjecture 3 quantifies over the empty set `A` as well, and the formal Conjecture 6 also covers the degenerate pair `v = w`. Two results of the manuscript are not part of the Lean certificate: the sharper right-hand side `P(o ↔ b, o ↔ A)` in its theorem on Question 5 (the Lean theorem has the right-hand side `P(o ↔ b)` printed by Kozma and Nitzan), and its positive result for Question 8 when `|A| ≤ 2` (a unique minimizer works, and every minimizer works if `P(o ↮ A) > 0`); the reading with a unique minimizer is left open for `|A| ≥ 3`. The statement of the headline theorem is read against the comparator challenge, whose [README](PercolationAudit/README.md) maps each vocabulary declaration to its source in this repository or in the dependency.

## Guarantees

- **No `sorry`** in the library. The comparator challenge [`PercolationAudit/SiteCriticality/Challenge.lean`](PercolationAudit/SiteCriticality/Challenge.lean) contains one intentional statement-level `sorry`, which its solution file proves.
- **No custom axiom.** The principal declarations depend only on mathlib's standard axioms `propext`, `Classical.choice` and `Quot.sound`. [`scripts/Audit.lean`](scripts/Audit.lean) prints their axiom dependencies, and [`scripts/acceptance.py`](scripts/acceptance.py) inspects Lean's elaborated declarations, including implicit and instance binders: it permits natural-number parameters and numeric lower bounds and rejects every other assumption and every nonstandard axiom. The CI workflow [`build.yml`](.github/workflows/build.yml) runs both. The checker tests that narrow property, not whether a mathematical definition expresses the intended model.
- **Independent check of the statement.** The headline theorem is restated, with the model rebuilt from mathlib primitives alone, in [`PercolationAudit/SiteCriticality/Challenge.lean`](PercolationAudit/SiteCriticality/Challenge.lean). The CI workflow [`comparator.yml`](.github/workflows/comparator.yml) submits the challenge and its solution to [leanprover/comparator](https://github.com/leanprover/comparator), which checks that the restatement is proved from the library through an independent implementation of the Lean kernel. See [`PercolationAudit/README.md`](PercolationAudit/README.md) and [`PercolationAudit/DESIGN.md`](PercolationAudit/DESIGN.md).
- **Pinned toolchain.** Lean `v4.32.0`, mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, and the git dependencies below, recorded in [`lake-manifest.json`](lake-manifest.json) and required by [`lakefile.toml`](lakefile.toml).

  | Package | Revision |
  | --- | --- |
  | `PercolationContinuity` ([`anthropics/formal-math`](https://github.com/anthropics/formal-math), subdirectory `percolation`) | `795efb86f191735c5481675763537cfb4ff37e55` |
  | `plausible` | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
  | `LeanSearchClient` | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
  | `importGraph` | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
  | `proofwidgets` | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
  | `aesop` | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
  | `Qq` | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
  | `batteries` | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
  | `Cli` | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

## Size

About 100,800 lines of Lean in 226 modules (`KNConjectures/`: 40 modules and its root; `Hypergraph/`: 184 modules and its root), of which about 78,500 lines are code once comments and blank lines are removed, on top of the Anthropic bond-percolation library (247 modules). The comparator surface under `PercolationAudit/` is not counted.

## Building

Install Git, Python 3 and [elan](https://github.com/leanprover/elan). The toolchain is pinned in [`lean-toolchain`](lean-toolchain) and selects Lean **4.32.0**. Allow substantial disk space for mathlib and the bond development. From a clone:

```sh
git clone https://github.com/nitromannitol/percolation-after-anthropic.git
cd percolation-after-anthropic
bash scripts/bootstrap.sh
```

The bootstrap explicitly fetches the pinned upstream commit, which need not be reachable from the upstream default branch, downloads the mathlib cache, and runs the normal Lake build. Later builds use

```sh
lake exe cache get          # prebuilt mathlib
lake build                  # the default targets KNConjectures and Hypergraph
lake build PercolationAudit # the Mathlib-only comparator surface, not a default target
```

Both `autoImplicit` and `relaxedAutoImplicit` are disabled. The two default targets cover every module of the library. The bond library is fetched as a dependency rather than duplicated here, and `lake-manifest.json` pins mathlib and all transitive packages. `import KNConjectures` and `import Hypergraph` load the two parts of the development.

The checks recorded in [`VERIFICATION.md`](VERIFICATION.md) are reproduced by

```sh
lake env lean scripts/Audit.lean
python3 scripts/acceptance.py . \
  Hypergraph.FinalCriticality:KNAll.Site.site_no_percolation_at_critical \
  Hypergraph.FinalCriticality:KNAll.Site.site_no_percolation_at_critical_primitive
python3 -m unittest discover -s tests -v
python3 tests/exact_hypergraph_checks.py
python3 Hypergraph/boolean-tutte/verify.py
```

`scripts/Audit.lean` prints the principal statements and their axioms; `scripts/acceptance.py` is the structural checker described under Guarantees; `tests/test_acceptance.py` is its regression suite, which compiles Lean fixtures with hidden hypotheses and a custom axiom; `tests/exact_hypergraph_checks.py` and `Hypergraph/boolean-tutte/verify.py` are exact finite enumerations. The exact enumerations are additional finite checks, not proofs of the general results. Selected output of these commands is in [`verification/`](verification/).

The comparator challenge elaborates on mathlib alone, and the comparator replays the solution, from the repository root:

```sh
bash PercolationAudit/check_standalone.sh PercolationAudit/SiteCriticality/Challenge.lean
bash PercolationAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic
lake build PercolationAudit
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator PercolationAudit/SiteCriticality/comparator.json
```

The first command is expected to finish with `rc=0` and exactly one `declaration uses 'sorry'` warning, and the comparator with `Your solution is okay!`. The tools are built at the pins `leanprover/comparator` commit `575674928e239f5bc452aab72d1dd7b0f1326494`, `lean4export` at the tag of the toolchain (`v4.32.0`), nanoda at `6ae1f0cd962f081f6c423454c5da729d841236a7` and landrun at `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`; the [audit README](PercolationAudit/README.md) gives the details. [`CONTRIBUTING.md`](CONTRIBUTING.md) collects further build notes.

## Repository layout

```
KNConjectures/        the finite bond results: Conjectures 1-4 and 6, Questions 5, 7 and 9,
                      and the Question 8 counterexample (Statements*.lean state them)
KNConjectures.lean    the root module of that library
Hypergraph/           the finite hyperedge inequality, site percolation, the lattice
                      exploration and parameter descent; FinalCriticality.lean is the
                      headline theorem
Hypergraph/boolean-tutte/
                      the Boolean-Tutte completion: a manuscript on an exact finite linear
                      program on Boolean gate signatures and its exact-arithmetic regression
                      (verify.py); separate from the lattice criticality proof and not part
                      of the Lean development
Hypergraph.lean       the root module of that library
PercolationAudit/     the Mathlib-only comparator surface
  SiteCriticality/      Challenge.lean, SolutionBasic.lean, Solution.lean, comparator.json
  Support/              SiteCriticalityBridge.lean, the bridge used by the solution
  check_standalone.sh   standalone elaboration and vocabulary check
  README.md, DESIGN.md  what is checked and how the surface is built
docs/                 the KN manuscript, kn-results.tex and kn-results.pdf
scripts/              bootstrap.sh, Audit.lean, acceptance.py
tests/                test_acceptance.py, exact_hypergraph_checks.py
verification/         selected output of the verification commands
source-layout.json    maps the module names used in the manuscript (KN.*) to the paths here
VERIFICATION.md       the review and the reproducible checks
lakefile.toml, lake-manifest.json, lean-toolchain
                      the build configuration and its pins
.github/workflows/    build.yml and comparator.yml
CONTRIBUTING.md, CITATION.cff, formalization.yaml, LICENSE, NOTICE
```

Theorem namespaces follow the numbering of the sources (`KNAll`, `KNAll.Guarded`, `KNAll.Site`).

## How this was built

The Lean code of this repository was written by ChatGPT and Claude under the close
supervision of Ahmed Bou-Rabee; models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml), following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors, citation, acknowledgements

The Lean development is by **Ahmed Bou-Rabee** and **Justin Leder**; Justin Leder is the responsible maintainer. To cite it, use [`CITATION.cff`](CITATION.cff). The conjectures and questions are those of [Kozma and Nitzan, *A reduction of the θ(p_c)=0 problem to a conjectured inequality*, arXiv:2401.12397](https://arxiv.org/abs/2401.12397). Built on Lean 4, mathlib and Lake, and on the Anthropic bond-percolation proof and its literature library; thanks to the Anthropic formal-math team.

## License

Apache License 2.0; see [`LICENSE`](LICENSE). The upstream attribution of the bond-percolation dependency is in [`NOTICE`](NOTICE).
