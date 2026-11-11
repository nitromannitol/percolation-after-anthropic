# Contributing and building

This repository is mainly a finished artifact, a Lean development of the Kozma–Nitzan
connection inequalities and of site percolation at criticality, but issues and pull requests
are welcome.

The bond-percolation library comes from
[`anthropics/formal-math`](https://github.com/anthropics/formal-math) (subdirectory `percolation`),
which `lakefile.toml` requires as a `git` dependency pinned to an exact commit; Lake materializes
it under `.lake/packages/PercolationContinuity`. The commit is on no branch of
`anthropics/formal-math` (its default branch no longer contains `percolation/`), so
`scripts/bootstrap.sh` fetches it explicitly before Lake resolves the package.
The dependency is read-only for this project: extensions belong under `KNConjectures/` and
`Hypergraph/`, and contributors must not edit the dependency's sources.

## Building locally

```bash
bash scripts/bootstrap.sh   # first build: pinned dependency, mathlib cache, lake build
lake exe cache get          # prebuilt mathlib oleans
lake build                  # the default targets KNConjectures and Hypergraph
lake build PercolationAudit # the Mathlib-only comparator surface
```

The toolchain is pinned in `lean-toolchain`. The bond library has no olean cache and is compiled
from source on the first build, as is the project itself. The only intentional `sorry` is in the
comparator challenge `PercolationAudit/SiteCriticality/Challenge.lean`, which contains one
documented statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`; it elaborates with exactly one `declaration uses 'sorry'` warning.

The Python checks are `python3 -m unittest discover -s tests -v` (the acceptance checker's
regression suite, which compiles Lean fixtures) and `python3 tests/exact_hypergraph_checks.py`.

## The main results and the axiom audit

The main results are in `Hypergraph/FinalCriticality.lean` and `KNConjectures/Conjectures.lean`.
To reproduce the axiom reports:

```bash
lake env lean scripts/Audit.lean
python3 scripts/acceptance.py . \
  Hypergraph.FinalCriticality:KNAll.Site.site_no_percolation_at_critical \
  Hypergraph.FinalCriticality:KNAll.Site.site_no_percolation_at_critical_primitive
```

`scripts/Audit.lean` prints the axiom dependencies of the principal declarations; it is a script
and not a module of the libraries, so no `#print axioms` command runs again when a library
module is rebuilt. `scripts/acceptance.py` checks that a declaration is closed: it permits
natural-number parameters and numeric lower bounds and rejects every other assumption and every
nonstandard axiom. Both are described in the README, and the CI workflow `build.yml` runs both;
it rejects `sorryAx`, any axiom other than `propext`, `Classical.choice` and `Quot.sound`, and an
audit log without a report.

## Conventions for Lean files

- **Never run `lake clean`.** It wipes the `mathlib` and `PercolationContinuity` oleans and forces
  a long rebuild from source. To force a project-only rebuild, remove the project build artifacts
  under `.lake/build/lib/lean/KNConjectures` and `.lake/build/lib/lean/Hypergraph` (and the
  corresponding `.lake/build/ir/` directories) and re-run `lake build`.
- **Per-file rebuilds.** Lake invalidates by content hash, not mtime, so `touch` does nothing;
  delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the module.
- **Dependencies are read-only.** Packages under `.lake/packages/` are not edited.
- Keep Lean files under 1500 lines.

### Elaboration policy for new files

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

## Comparators

The comparator surface under `PercolationAudit/` is deliberately not a default target. Each pair
is a directory `PercolationAudit/<Pair>/` with `Challenge.lean`, `Solution.lean` and
`comparator.json`, which permits exactly `propext`, `Classical.choice` and `Quot.sound`. Run
`bash PercolationAudit/check_standalone.sh --vocabulary` after editing a challenge or its
`SolutionBasic.lean`; the two vocabulary blocks must stay byte-identical. Do not change a
challenge without checking it against the statement of the headline theorem. The README
explains how to run the comparator.

## Continuous integration

- **CI** (`.github/workflows/build.yml`) builds the library and the comparator surface, rejects
  any `declaration uses 'sorry'` in the library build, checks the axiom reports and the
  structural acceptance check, and runs the regression tests and the exact finite checks.
- **Comparator audit** (`.github/workflows/comparator.yml`) builds the pinned comparator tools
  and checks every challenge/solution pair under `PercolationAudit/`.

Both run on pushes to `main` and can be started manually from the Actions page.
