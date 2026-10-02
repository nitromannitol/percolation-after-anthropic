# Design of the comparator surface

Each headline theorem has a directory here with the same four files.

- `Challenge.lean` imports `Mathlib` and nothing else. It rebuilds from Mathlib primitives
  every object the theorem mentions: the lattice and its nearest-neighbour graph, the product
  Bernoulli measure, site configurations and open clusters, the percolation probability and the
  critical parameter. It states the theorem and ends in a single `sorry`. This file is the
  object of trust: a reader checks what it says, not how it is proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean` (between `VOCABULARY-BEGIN` and `VOCABULARY-END`). It imports only
  `Mathlib`, so the vocabulary elaborates in the solution exactly as in the challenge.
- `Solution.lean` imports the library together with `SolutionBasic` and the bridges in
  `Support/`, restates the challenge theorem byte-for-byte, and proves it from the library's
  verified statement.
- `comparator.json` names the challenge module, the solution module, the theorem and the
  permitted axioms (`propext`, `Classical.choice`, `Quot.sound`).

The files under `Support/` are part of the solutions. `SiteCriticalityBridge.lean` identifies
the challenge's definitions with the library's: the vocabulary is definitionally equal, so the
`*_eq` lemmas are `rfl`. The vocabulary has no `structure` or `inductive`, so no field-by-field
`Iff` is needed.

The vocabulary contains two theorems, `criticalProbSite_nonneg_mem` and
`criticalProbSite_mem_Icc`, because the definition `criticalProbSiteI` carries the second as the
membership proof of its subtype value. The comparator checks every constant reachable from the
statement, proofs of definitions included, so these two theorems are copied with their proofs.

The public workflow feeds the pair to
[leanprover/comparator](https://github.com/leanprover/comparator), which elaborates both
statements and requires them to coincide, replays the solution's proof through an independent
implementation of the Lean kernel, and rejects any axiom outside the permitted three. Nothing
a solution imports can change the statement the reader saw in the challenge; it can only
supply a kernel-checked proof of it.

`check_standalone.sh` elaborates a challenge on its own, with the library's build options, to
confirm that it depends on Mathlib alone, and with `--vocabulary` checks that the vocabulary
block is byte-identical in `Challenge.lean` and `SolutionBasic.lean`.
