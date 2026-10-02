# Verification

The development builds with Lean 4.32.0 and Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`. The principal bond and site declarations carry their intended dimension restrictions and use only `propext`, `Classical.choice`, and `Quot.sound`. Apart from those restrictions, the review found no mathematical assumption and no proof hole in either final theorem.

## Properties of the statements and the tooling

1. **The acceptance checker inspects elaborated binders.** [`scripts/acceptance.py`](scripts/acceptance.py) inspects Lean's elaborated binders and axiom dependencies rather than a shortened printed type, so a theorem carrying a hidden `Fact False` instance is rejected. It rejects substantive explicit, implicit, instance, and data arguments, and exits unsuccessfully when the declaration is conditional or the audit cannot complete. Its acceptance criterion allows natural-number parameters with numeric lower bounds; it is deliberately narrower than a general-purpose theorem validator.

2. **The direct-file build and the Lake configuration agree.** Both `autoImplicit` and `relaxedAutoImplicit` are disabled. Six modules declare their variables explicitly, so that they elaborate without inferred variables and with their conclusions unchanged:

   | Module in `Hypergraph/` | Variables declared explicitly |
   | --- | --- |
   | `BoundedDamageDomination.lean` | graph, source, target, finite set |
   | `StoppedLevel.lean` | integer sign parameter |
   | `CoreTaggedCoverUpdate.lean` | scales, probability, tolerance, history |
   | `TargetAwareLattice.lean` | probability and tolerance |
   | `CoreFaceTargetPackaging.lean` | probabilities and tolerances |
   | `ExactQuarterPlanExtraction.lean` | probability and tolerance |

   The default targets cover all modules of the library.

3. **Boundary exposure.** The map from an edge to its outside reached set is not injective for ordinary graphs. With exposed set `{z₁,z₂}`, the edges `{z₁,u}` and `{z₂,u}` have the same outside reached set, yet their singleton label sets have empty intersection. The argument therefore applies the four-functions theorem to sets of independent labels and uses reached vertex sets as additional information. The Lean proof retains the necessary labels.

4. **The exploration.** The proof maintains actual open-path witnesses, assigns one responsible predecessor to each pending destination, and protects its unread support. Failed examinations can disable nearby moves. The comparison uses a high-density independent field with bounded local deletions, justified by an independent block construction, and a reduction to finitely many prototypes yields one common smaller parameter.

5. **The covariance argument.** Exposing a cluster does not by itself turn covariance into an average of covariances. The argument includes the covariance of conditional means (the total-covariance term) and the resampling/telescoping argument that handles it.

6. **Question 8.** The [KN manuscript](docs/kn-results.pdf) uses the avoidance-conditioned score and states the counterexample to the every-minimizer interpretation. [`Question8Counterexample.lean`](KNConjectures/Question8Counterexample.lean) proves that refutation. It does not refute an existential choice among tied minimizers and should not be summarized as doing so.

7. **The source tree.** Every Lean file under `KNConjectures/` and `Hypergraph/` is in the import closure of the two default targets, so a build of the default targets builds the whole tree. The import closures contain all public results and their dependencies.

## Checks performed

- All **224 extension modules** (40 in `KNConjectures/`, 184 in `Hypergraph/`), the two root modules, and the **247 upstream bond-library modules** compile from source. Both default Lake targets pass. `bash scripts/bootstrap.sh` also completes successfully, including its pinned dependency setup and the normal build.
- [`scripts/Audit.lean`](scripts/Audit.lean) prints the principal declarations and axiom lists and checks concrete three-dimensional instances. The final site statement and its fully expanded form separately pass the structural acceptance checker.
- Six acceptance regression tests pass. They compile eleven Lean fixtures, including false instance/implicit/explicit hypotheses, an impossible data certificate, an assumption hidden behind an abbreviation, an impossible dimension bound, and a custom axiom. An additional test exercises the real command path and temporary-file cleanup.
- Exact independent enumeration checks all 2,048 four-vertex hypergraphs with distinct edges of size at least two at probability one half: 177,147 configurations and 491,520 strong gluing inequalities. Another 100 nonuniform five-vertex labelled models check strong gluing, first-contact, and selected increasing-function fixed-minimizer inequalities, including repeated/empty labels and endpoint probabilities.
- The separate Boolean–Tutte regression passes 22,297 exact-arithmetic checks. Its manuscript and the KN manuscript compile without unresolved references or overfull boxes.

The mathematical review checked the meanings of the model definitions and final statements, the covariance and first-contact mechanisms, endpoint probabilities, label identity under deletion, actual path witnesses, exploration freshness, failure damage, and the common smaller-parameter argument. This is a semantic and structural review supported by compilation of the full source chain, not a handwritten re-derivation of every Lean proof term. Finite enumeration and PDF compilation are supporting checks, not proofs of the general statements.

## Source correspondence and reproduction

The 247 bond-library modules match the pinned [Anthropic commit](https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation). A byte-for-byte comparison of the public site snapshot, commit `0baf9224c8d2590dc55c7ee6ec1af380bf82f852` with tree `8bd5200a06d0b7dc47d3584c96e75e64c77a36cc`, with the corresponding sources of this repository found 192 of its 193 site modules identical, the remaining difference being in comments; the 37 KN companion modules also matched. [`source-layout.json`](source-layout.json) maps the module names used by that snapshot and by the manuscript to the current paths.

The [README](README.md#building) gives all reproduction commands. Selected command output is in [`verification/`](verification/). The `.lake` build directory is not part of the repository.
