# Percolation after Anthropic

Lean proofs of the Kozma–Nitzan connection inequalities and their extension to independent hyperedges and site percolation. The development builds on [Anthropic's bond-percolation proof](https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation), pinned as a dependency.

[VERIFICATION.md](VERIFICATION.md) records the review, corrections, and reproducible checks.

## KN-Conjectures: proofs and counterexamples

[`KNConjectures/`](KNConjectures/) contains the finite bond results, using the numbering of [Kozma and Nitzan's paper](https://arxiv.org/abs/2401.12397):

- Conjectures 1–4 and 6, including the strong joint-event and fixed-minimizer forms.
- Affirmative answers to Questions 5, 7, and 9.
- A counterexample to the **every-minimizer** reading of Question 8. This distinction matters when minimizers tie.

The [KN manuscript](docs/kn-results.pdf) ([LaTeX](docs/kn-results.tex)) states these results precisely. Main entry points are [`Conjectures.lean`](KNConjectures/Conjectures.lean), [`Conjecture6Proof.lean`](KNConjectures/Conjecture6Proof.lean), and [`Question8Counterexample.lean`](KNConjectures/Question8Counterexample.lean). The separate derivation of Conjecture 1 directly from the original bond proof is [`KozmaNitzanConjecture1.lean`](KNConjectures/KozmaNitzanConjecture1.lean).

## Hypergraphs and site percolation

[`Hypergraph/`](Hypergraph/) proves the finite connection inequality for independent labelled hyperedges, represents site percolation by incidence hyperedges, and carries out the lattice exploration and parameter descent.

The final theorem is in [`FinalCriticality.lean`](Hypergraph/FinalCriticality.lean):

```lean
KNAll.Site.site_no_percolation_at_critical (d : ℕ) (hd : 3 ≤ d) :
  thetaSite d (criticalProbSiteI d) = 0
```

Its only arguments are the dimension and `3 ≤ d`. The same file gives the statement with the cluster and measure definitions unfolded, and proves that the critical parameter lies strictly between zero and one. The planar site result is outside this declaration's scope.

Read [`FiniteHyperGluingClosed.lean`](Hypergraph/FiniteHyperGluingClosed.lean) for the finite inequality, [`ExactReachableMacroInterpreter.lean`](Hypergraph/ExactReachableMacroInterpreter.lean) and [`CoreSafeBenchmark.lean`](Hypergraph/CoreSafeBenchmark.lean) for the exploration and its comparison process, and [`ExactCommonQAssembly.lean`](Hypergraph/ExactCommonQAssembly.lean) for the common smaller parameter.

## Build and verify

Install Git, Python 3, and [elan](https://github.com/leanprover/elan). The toolchain file selects Lean **4.32.0**. Allow substantial disk space for Mathlib and the bond development. From a clone:

```sh
git clone https://github.com/nitromannitol/percolation-after-anthropic.git
cd percolation-after-anthropic
bash scripts/bootstrap.sh
```

The bootstrap explicitly fetches the pinned upstream commit, downloads the Mathlib cache, and runs the normal Lake build. Later builds use `lake build`; both `autoImplicit` and `relaxedAutoImplicit` are disabled. The two default targets cover every retained proof module. The original bond library is fetched as a dependency, rather than duplicated here. `lake-manifest.json` pins Mathlib and all transitive packages.

```sh
lake env lean scripts/Audit.lean
python3 scripts/acceptance.py . \
  Hypergraph.FinalCriticality:KNAll.Site.site_no_percolation_at_critical \
  Hypergraph.FinalCriticality:KNAll.Site.site_no_percolation_at_critical_primitive
python3 -m unittest discover -s tests -v
python3 tests/exact_hypergraph_checks.py
python3 Hypergraph/boolean-tutte/verify.py
```

`Audit.lean` prints the principal statements and their axioms. The acceptance checker inspects Lean's elaborated declarations, including implicit and instance binders; it permits natural-number parameters and numeric lower bounds, and rejects other assumptions or nonstandard axioms. It checks that narrow property, not whether a mathematical definition expresses the intended model. The exact enumerations are additional finite checks, not proofs of the general results.

## Source and attribution

The original bond proof and its literature library were produced by Claude under Justin Leder's direction at Anthropic. The subsequent KN, hypergraph, and site development was produced with ChatGPT and Claude, prompted by Ahmed Bou-Rabee. Original theorem namespaces are retained; `source-layout.json` maps the previous module paths to the current organization. Obsolete scaffolding and superseded experiments have been removed.

Licensed under [Apache 2.0](LICENSE); see [NOTICE](NOTICE) for upstream attribution.
