# Percolation after Anthropic

A machine-checked **Lean 4** development of the Kozma–Nitzan connection inequalities for
Bernoulli percolation and of their extension to independent hyperedges and site percolation.
It formalizes the conjectures and questions of

> Gady Kozma and Shahaf Nitzan,
> *A reduction of the θ(p_c)=0 problem to a conjectured inequality*,
> [arXiv:2401.12397](https://arxiv.org/abs/2401.12397).

Its headline theorem is that nearest-neighbour Bernoulli site percolation on `ℤ^d`, `d ≥ 3`,
has no infinite open cluster at its critical parameter, `θ_site(p_c) = 0`. The results on the
Kozma–Nitzan conjectures are stated precisely in the accompanying manuscript,
[`docs/kn-results.pdf`](docs/kn-results.pdf) ([LaTeX](docs/kn-results.tex)), which follows the
numbering of the paper above. [`VERIFICATION.md`](VERIFICATION.md) records the review and the
reproducible checks. Every theorem stated below is proved, and none takes a result cited from
the literature as a hypothesis; see
[Standing assumptions and scope](#standing-assumptions-and-scope).

The development extends [Anthropic's formalization of `θ(p_c) = 0` for bond percolation](https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation),
a git dependency pinned to one commit, and is built on
[mathlib](https://github.com/leanprover-community/mathlib4). The dependency proves the bond
result; this repository adds the Kozma–Nitzan inequalities, their extension to independent
hyperedges and the site percolation theorem. The upstream notice of the dependency is retained
in [`NOTICE`](NOTICE).

[![CI](https://github.com/nitromannitol/percolation-after-anthropic/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/percolation-after-anthropic/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/percolation-after-anthropic/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/percolation-after-anthropic/actions/workflows/comparator.yml)

## What is proved

The finite results concern a finite weighted graph with independent edges, in which `o ↔ A`
means that `o` is connected to some vertex of `A`. The development proves the connection
inequalities of Kozma and Nitzan (Conjectures 1–4 and 6, numbered as in their paper; there is
no Conjecture 5 and no Question 6), answers their Questions 5, 7 and 9, and refutes the
every-minimizer reading of Question 8. It then proves the finite connection inequality for
independent labelled hyperedges, represents site percolation by incidence hyperedges, and
carries out the lattice exploration and the parameter descent that give the headline theorem.
The setting is stated precisely in
[Standing assumptions and scope](#standing-assumptions-and-scope).

The headline theorem is in [`Hypergraph/FinalCriticality.lean`](Hypergraph/FinalCriticality.lean),
the Kozma–Nitzan results are in [`KNConjectures/`](KNConjectures/), and the hyperedge
inequality is in [`Hypergraph/FiniteHyperGluingClosed.lean`](Hypergraph/FiniteHyperGluingClosed.lean).

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Headline theorem | `KNAll.Site.site_no_percolation_at_critical` | `θ_site(p_c) = 0` for site percolation on `ℤ^d`, `d ≥ 3` ([`FinalCriticality.lean`](Hypergraph/FinalCriticality.lean)) |
| Hyperedge gluing | `KNAll.Site.FiniteHyperGluingClosed.hyperedgeGluing` | the finite connection inequality for independent labelled hyperedges ([`FiniteHyperGluingClosed.lean`](Hypergraph/FiniteHyperGluingClosed.lean)) |
| Conjecture 1 | `KNAll.conjecture1_holds` | `P(o ↔ b) ≥ P(o ↔ A) min_{x∈A} P(x ↔ b)` ([`Conjectures.lean`](KNConjectures/Conjectures.lean)) |
| Conjecture 1, second proof | `KN1Corollary.kozmaNitzan_conjecture1` | derived directly from the bond-percolation proof of the dependency ([`KozmaNitzanConjecture1.lean`](KNConjectures/KozmaNitzanConjecture1.lean)) |
| Conjecture 2 and its strong form (display (3)) | `KNAll.conjecture2_holds`, `KNAll.conjecture2Strong_holds` | `P(o ↔ b) ≥ min_{x∈A} P(o ↔ A, x ↔ b)`, and `P(o ↔ b, o ↔ A) ≥ min_{x∈A} P(x ↔ b, o ↔ A)` ([`Conjectures.lean`](KNConjectures/Conjectures.lean)) |
| Conjecture 3 | `KNAll.conjecture3_holds` | derived from Conjecture 1 ([`Conjectures.lean`](KNConjectures/Conjectures.lean)) |
| Conjecture 4 | `KNAll.conjecture4_holds`, `KNAll.conjecture4Fixed_holds`, `KNAll.conjecture4_clusterProperty_holds` | `E[F(C_o); o ↔ A] ≥ min_{x∈A} E[F(C_x); o ↔ A]` for every increasing `F`, with the minimizer fixed before conditioning, and for monotone cluster properties ([`Conjectures.lean`](KNConjectures/Conjectures.lean), [`ClusterProperty.lean`](KNConjectures/ClusterProperty.lean)) |
| Conjecture 6 | `KNAll.Guarded.conjecture6_holds`, `KNAll.Guarded.conjecture6Strong_holds` | the inequality of Conjecture 6 and its strong form without the endpoint hypotheses of display (39) ([`Conjecture6Proof.lean`](KNConjectures/Conjecture6Proof.lean)) |
| Question 5 | `KNAll.question5_holds` | one probability distribution on the relay set `A`, independent of `b`, whose weighted row of joint connection probabilities is bounded coordinatewise by the connection probabilities from `o` ([`Question5.lean`](KNConjectures/Question5.lean)) |
| Question 7 (display (41)) | `KNAll.question7_holds` | if `a ∈ A` minimises `P(a ↔ b)` over `A`, then `P(o ↔ A, a ↔ b) ≤ P(o ↔ b, o ↔ A)` ([`Conjectures.lean`](KNConjectures/Conjectures.lean)) |
| Question 8 | `KNAll.not_question8EveryMin` | a counterexample to the every-minimizer reading ([`Question8Counterexample.lean`](KNConjectures/Question8Counterexample.lean)) |
| Question 9 | `KNAll.question9_holds`, from `KNAll.setSourceFixedMin_holds` | if `a` minimises `P_H(x ↔ b)` over `A`, where `H` is `G` minus the edges at `o`, then display (41) holds ([`Question9.lean`](KNConjectures/Question9.lean), [`Question9Reduction.lean`](KNConjectures/Question9Reduction.lean)) |
| Comparison theorem of the manuscript | `KNAll.genY_all` | the comparison principle for increasing functions of a cluster conditioned to avoid a set ([`Conjectures.lean`](KNConjectures/Conjectures.lean)) |

**The headline theorem.** [`Hypergraph/FinalCriticality.lean`](Hypergraph/FinalCriticality.lean)
proves

```lean
KNAll.Site.site_no_percolation_at_critical (d : ℕ) (hd : 3 ≤ d) :
  thetaSite d (criticalProbSiteI d) = 0
```

where `thetaSite d p` is the probability that the open cluster of the origin is infinite for
site percolation on `ℤ^d` in which every vertex is open independently with probability `p`,
and `criticalProbSite d` is the infimum of `{p ∈ [0,1] | θ(p) > 0} ∪ {1}`, regarded as a point
`criticalProbSiteI d` of the unit interval. The theorem has no argument other than the
dimension and `3 ≤ d`. The same file states the conclusion with the cluster and measure
definitions unfolded (`site_no_percolation_at_critical_expanded` and
`site_no_percolation_at_critical_primitive`), proves that the critical parameter lies strictly
between zero and one (`criticalProbSite_mem_Ioo_of_three_le`), and bundles the phase transition
in `site_phase_transition`. The planar site result is outside this declaration's scope.

**The Kozma–Nitzan inequalities.** [`KNConjectures/`](KNConjectures/) contains the finite bond
results, with the numbering of Kozma and Nitzan. These are affirmative answers to Questions 5,
7 and 9 and a counterexample to the **every-minimizer** reading of Question 8: the inequality
fails for a vertex that minimizes the avoidance-conditioned score `P(a ↔ b, o ↮ A)` on a
four-vertex graph in which `P(o ↮ A) = 0` and both vertices of `A` minimize. The distinction
matters when minimizers tie, and the counterexample does not refute an existential choice among
tied minimizers. Conjecture 1 follows from the strong form of Conjecture 2 by Harris's
inequality, and Conjecture 3 from Conjecture 1.

**Hypergraphs and site percolation.** [`Hypergraph/`](Hypergraph/) proves the finite connection
inequality for independent labelled hyperedges, represents site percolation by incidence
hyperedges, and carries out the lattice exploration and the parameter descent that give the
headline theorem.

- `KNAll.Site.FiniteHyperGluingClosed.hyperedgeGluing`
  ([`FiniteHyperGluingClosed.lean`](Hypergraph/FiniteHyperGluingClosed.lean)): in every finite
  model of independent hyperedges, `P(o ↔ b, o ↔ A) ≥ P(o ↔ A) min_{a∈A} P(a ↔ b)`; for edges
  of size two this is the finite inequality of Conjecture 1.
- `KNAll.Site.FiniteHyperGluingClosed.pinnedSiteGluing`: the same inequality for site
  percolation on a finite graph when the observer, the target and the vertices of `A` are open
  with probability one. `KNAll.Site.siteGluingUnpinned_of_hyperedgeGluing`
  ([`SiteRepresentation.lean`](Hypergraph/SiteRepresentation.lean)) removes the pinning when
  the observer and the target are distinct and lie outside `A`.
- [`ExactReachableMacroInterpreter.lean`](Hypergraph/ExactReachableMacroInterpreter.lean) and
  [`CoreSafeBenchmark.lean`](Hypergraph/CoreSafeBenchmark.lean) carry out the exploration and
  its comparison process, and
  [`ExactCommonQAssembly.lean`](Hypergraph/ExactCommonQAssembly.lean) assembles the common
  smaller parameter.

## Standing assumptions and scope

1. **Every theorem is about every instance of its model.** The finite results hold for every
   finite weighted graph with independent edges, and the hyperedge inequality for every finite
   model of independent labelled hyperedges. The headline theorem holds for every dimension
   `d ≥ 3`; its only arguments are `d` and `3 ≤ d`.
2. **Axioms and incomplete proofs.** The library (`KNConjectures/` and `Hypergraph/`) contains
   no `sorry`, no `admit`, no `native_decide` and no new `axiom`. The axiom report of each
   main theorem consists of exactly `propext`, `Classical.choice` and `Quot.sound`. The main
   theorems rely on no unproved result: nothing is conditional, and none carries a hypothesis
   on a cited result. Everything they use is available in mathlib, is proved in this repository
   or belongs to the proved bond-percolation library of the dependency, whose theorems
   `Percolation.Continuity.CSH.cshHolds` and
   `Percolation.Continuity.CSH.percolationContinuity_allDimensions` (`θ(p_c) = 0` for bond
   percolation, `d ≥ 2`) belong to that dependency and not to this repository.
3. **Two results of the manuscript are not part of the Lean certificate.** These are the
   sharper right-hand side `P(o ↔ b, o ↔ A)` in its theorem on Question 5 (the Lean theorem has
   the right-hand side `P(o ↔ b)` printed by Kozma and Nitzan), and its positive result for
   Question 8 when `|A| ≤ 2` (a unique minimizer works, and every minimizer works if
   `P(o ↮ A) > 0`); the reading with a unique minimizer is left open for `|A| ≥ 3`. The planar
   site result is outside the scope of the headline declaration.
4. **Correspondence with the sources.** The Kozma–Nitzan statements are closed propositions in
   [`Statements.lean`](KNConjectures/Statements.lean),
   [`Statements6.lean`](KNConjectures/Statements6.lean),
   [`Statements9.lean`](KNConjectures/Statements9.lean) and
   [`Question8Defs.lean`](KNConjectures/Question8Defs.lean), whose docstrings give the page or
   display of Kozma and Nitzan; Conjecture 3 is the dependency's
   `Percolation.Literature.KozmaNitzan2024_conjecture3`, and Question 5 is stated by its
   theorem. The section "Lean Verification" of the [manuscript](docs/kn-results.tex) lists the
   correspondences that are not literal: `KNAll.genY_all` yields the manuscript's comparison
   theorem after an order-equivalent rank replaces the real-valued order;
   `KNAll.setSourceFixedMin_holds` also covers the empty source; and the formal Conjecture 3
   quantifies over the empty set `A` as well, and the formal Conjecture 6 also covers the
   degenerate pair `v = w`. The statement of the headline theorem is read against the
   comparator challenge, whose [README](PercolationAudit/README.md) maps each vocabulary
   declaration to its source in this repository or in the dependency.

## Guarantees

- **No `sorry`.** The library has none. The comparator challenge
  [`PercolationAudit/SiteCriticality/Challenge.lean`](PercolationAudit/SiteCriticality/Challenge.lean)
  contains one intentional statement-level `sorry`, which its solution file proves.
- **Standard axioms only.** The axiom report of each of the 14 declarations printed by
  [`scripts/Audit.lean`](scripts/Audit.lean) lists exactly `propext`, `Classical.choice` and
  `Quot.sound`. They are the headline theorem, `site_phase_transition`, the finite results of
  Conjectures 1, 2 (strong form), 3, 4 (fixed minimizer) and 6 and of Questions 5, 7 and 9, the
  counterexample to the every-minimizer reading of Question 8, the two hyperedge and site
  gluing inequalities, and the dependency's `percolationContinuity_allDimensions`. The CI
  workflow [`build.yml`](.github/workflows/build.yml) fails if the audit log contains `sorryAx`,
  a report with any other axiom, or no report.
- **Structural check of the headline statement.** [`scripts/acceptance.py`](scripts/acceptance.py)
  inspects Lean's elaborated declarations, including implicit and instance binders: it permits
  natural-number parameters and numeric lower bounds and rejects every other assumption and
  every nonstandard axiom. The CI workflow runs it on the headline theorem and on
  `site_no_percolation_at_critical_primitive`. The checker tests that narrow property, not
  whether a mathematical definition expresses the intended model.
- **Independent check of the statement.** The headline theorem is restated, with the model
  rebuilt from mathlib primitives alone, in
  [`PercolationAudit/SiteCriticality/Challenge.lean`](PercolationAudit/SiteCriticality/Challenge.lean).
  The solution file proves the restatement from the library, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the
  restatement is proved, with only the three standard axioms, through independent
  implementations of the Lean kernel. The Kozma–Nitzan inequalities and the hyperedge
  theorems have no comparator pair. See [`PercolationAudit/README.md`](PercolationAudit/README.md)
  and [`PercolationAudit/DESIGN.md`](PercolationAudit/DESIGN.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0`, mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`, and the bond-percolation library at one exact
  commit, as recorded in [`lake-manifest.json`](lake-manifest.json) (see
  [Building](#building)). [`lakefile.toml`](lakefile.toml) requires only the bond-percolation
  library; mathlib and the other packages are resolved through it and pinned by the manifest.

## Size

The library contains 226 Lean files with 99,466 physical lines (`KNConjectures`: 41 files and
14,389 lines; `Hypergraph`: 185 files and 85,077 lines), on top of mathlib and the
bond-percolation library of the dependency. The comparator sources under `PercolationAudit/`
are counted separately.

## Building

Install Git, Python 3 and [elan](https://github.com/leanprover/elan). The toolchain is pinned
in [`lean-toolchain`](lean-toolchain) and selects Lean **4.32.0**, and Lake fetches the
dependencies. Allow substantial disk space for mathlib and the bond development. From a clone:

```sh
git clone https://github.com/nitromannitol/percolation-after-anthropic.git
cd percolation-after-anthropic
bash scripts/bootstrap.sh
```

The bootstrap explicitly fetches the pinned upstream commit, which is on no branch of
`anthropics/formal-math` (its default branch no longer contains `percolation/`), downloads the
mathlib cache, and runs the normal Lake build. Later builds use

```sh
lake exe cache get          # prebuilt mathlib
lake build                  # the default targets KNConjectures and Hypergraph
lake build PercolationAudit # the Mathlib-only comparator surface, not a default target
```

The bond-percolation library has no prebuilt cache, so the first build compiles it as well as
the library. Both `autoImplicit` and `relaxedAutoImplicit` are disabled. The two default
targets cover every module of the library. The bond library is fetched as a dependency rather
than duplicated here, and `lake-manifest.json` pins mathlib and all transitive packages.
`import KNConjectures` and `import Hypergraph` load the two parts of the development.

The dependencies, at the exact revisions of `lake-manifest.json`:

| Package | Revision |
| --- | --- |
| `PercolationContinuity` ([`anthropics/formal-math`](https://github.com/anthropics/formal-math), subdirectory `percolation`) | `795efb86f191735c5481675763537cfb4ff37e55` |
| `mathlib` | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| `plausible` | `e12c1910fe855cbfc38803cd4e55543906d5fa62` |
| `LeanSearchClient` | `c5d5b8fe6e5158def25cd28eb94e4141ad97c843` |
| `importGraph` | `7e9612bf0b9ee66db3cb5b9988a35afc706f5a12` |
| `proofwidgets` | `6e311e2a844da9b2cc3971187df2fe0066947b93` |
| `aesop` | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` |
| `Qq` | `38d591e778f100aec9762bb582f9c7f55f50e9dc` |
| `batteries` | `023ce7d62a0531e22a5331e20b587817a80d49ff` |
| `Cli` | `88679d088c9720c27ebdf2ba4dafe17341747f94` |

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

`scripts/Audit.lean` prints the principal statements and their axioms; `scripts/acceptance.py`
is the structural checker described under Guarantees; `tests/test_acceptance.py` is its
regression suite, which compiles Lean fixtures with hidden hypotheses and a custom axiom;
`tests/exact_hypergraph_checks.py` and `Hypergraph/boolean-tutte/verify.py` are exact finite
enumerations. The exact enumerations are additional finite checks, not proofs of the general
results. Selected output of these commands is in [`verification/`](verification/).

## Running the comparator

The configuration
[`PercolationAudit/SiteCriticality/comparator.json`](PercolationAudit/SiteCriticality/comparator.json)
permits exactly `propext`, `Classical.choice` and `Quot.sound`. The comparator checks that the
solution proves the challenge statement, compares their dependency closures, and replays the
proof with the Lean kernel and the nanoda kernel.

The challenge elaborates on mathlib alone, and the comparator replays the solution, from the
repository root:

```sh
bash PercolationAudit/check_standalone.sh PercolationAudit/SiteCriticality/Challenge.lean
bash PercolationAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic
lake build PercolationAudit
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator PercolationAudit/SiteCriticality/comparator.json
```

The first command is expected to finish with `rc=0` and exactly one `declaration uses 'sorry'`
warning, and the comparator with `Your solution is okay!`. The tools are built at the pins
`leanprover/comparator` commit `575674928e239f5bc452aab72d1dd7b0f1326494`, `lean4export` at
the tag of the toolchain (`v4.32.0`), nanoda at `6ae1f0cd962f081f6c423454c5da729d841236a7` and
landrun at `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`; the
[audit README](PercolationAudit/README.md) gives the details.

There are two continuous-integration workflows: **CI** builds the library, rejects any
`declaration uses 'sorry'`, checks the axiom reports and runs the structural checker and the
exact finite checks; **Comparator audit** checks the challenge/solution pair. Both run on
pushes to `main` and can be started manually from the
[Actions page](https://github.com/nitromannitol/percolation-after-anthropic/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
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

Theorem namespaces follow the numbering of the sources (`KNAll`, `KNAll.Guarded`,
`KNAll.Site`).

## How this was built

The Lean code of this repository was written by ChatGPT and Claude under the close
supervision of Ahmed Bou-Rabee; models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml), following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The Lean development in this repository is by **Ahmed Bou-Rabee**. It builds on Anthropic's separate bond-percolation proof as a pinned dependency; the authorship of that upstream work is distinct from the authorship of this repository. To cite this development, use [`CITATION.cff`](CITATION.cff). The conjectures and questions are those of [Kozma and Nitzan, *A reduction of the θ(p_c)=0 problem to a conjectured inequality*, arXiv:2401.12397](https://arxiv.org/abs/2401.12397). Built on Lean 4, mathlib and Lake; thanks to the Anthropic formal-math team for the upstream library.

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE). The
upstream attribution of the bond-percolation dependency is in [`NOTICE`](NOTICE).
