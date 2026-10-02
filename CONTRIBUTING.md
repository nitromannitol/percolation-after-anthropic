# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively solicited collaborative
project, but issues and pull requests are welcome.

The bond-percolation library comes from
[`anthropics/formal-math`](https://github.com/anthropics/formal-math) (subdirectory `percolation`),
which `lakefile.toml` requires as a `git` dependency pinned to an exact commit; Lake materializes
it under `.lake/packages/PercolationContinuity`. The commit need not be reachable from the upstream
default branch, so `scripts/bootstrap.sh` fetches it explicitly before Lake resolves the package.
The dependency is read-only for this project: extensions belong under `KNConjectures/` and
`Hypergraph/`, and contributors must not edit the dependency's sources.

## Building locally

```bash
bash scripts/bootstrap.sh   # first build: pinned dependency, mathlib cache, lake build
lake exe cache get          # prebuilt mathlib oleans
lake build                  # the default targets KNConjectures and Hypergraph
lake build PercolationAudit # the Mathlib-only comparator surface
```

The bond library has no olean cache and is compiled from source on the first build, as is the
project itself. The comparator challenge `PercolationAudit/SiteCriticality/Challenge.lean` contains
one documented statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`; it elaborates with exactly one `declaration uses 'sorry'` warning.

A few practical notes for working with a development of this size:

- **Never run `lake clean`.** It wipes the `mathlib` and `PercolationContinuity` oleans and forces
  a long rebuild from source. To force a project-only rebuild, remove the project build artifacts
  under `.lake/build/lib/lean/KNConjectures` and `.lake/build/lib/lean/Hypergraph` (and the
  corresponding `.lake/build/ir/` directories) and re-run `lake build`.
- **Per-file rebuilds.** Lake invalidates by content hash, not mtime, so `touch` does nothing;
  delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the module.
- **The main results** are in `Hypergraph/FinalCriticality.lean` and `KNConjectures/Conjectures.lean`.
  The axiom report is `lake env lean scripts/Audit.lean`, and `scripts/acceptance.py` checks that a
  declaration is closed; both are described in the README.
- **The comparator surface** under `PercolationAudit/` is deliberately not a default target. Run
  `bash PercolationAudit/check_standalone.sh --vocabulary` after editing a challenge or its
  `SolutionBasic.lean`; the two vocabulary blocks must stay byte-identical.
- **The Python checks** are `python3 -m unittest discover -s tests -v` (the acceptance checker's
  regression suite, which compiles Lean fixtures) and `python3 tests/exact_hypergraph_checks.py`.

## Elaboration policy for new files

These rules apply to new files; each addresses a recurring elaboration cost.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with `nlinarith`. When a
  nonlinear fact is needed, hoist it into a small `private` lemma over abstract real variables so
  that `Real.rpow` and `Real.exp` terms never enter a numeric tactic.
- Prefer the explicit `mul_le_mul_of_nonneg_*` / `add_le_add_*` lemmas to `gcongr` on goals over
  `ℝ`.
- Use `positivity` for sign goals only.
- Before `ring` or `field_simp` on an expression built with `set`, run `clear_value` on the bound
  names; otherwise the let-bodies are unfolded inside the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for performance" without a
  warm profile before and after (`lake env lean --profile <file>`). The profiler's default 100 ms
  floor hides diffuse costs; use `-D profiler.threshold=1` when hunting them.
- Keep Lean files under 1500 lines.
- Never run `lake clean`.
