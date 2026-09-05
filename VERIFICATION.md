# Verification and corrections — 5 September 2026

The cleaned development builds successfully with Lean 4.32.0 and Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`. The principal bond and site declarations have their intended dimension restrictions and use only `propext`, `Classical.choice`, and `Quot.sound`. The review found no additional mathematical assumption or proof hole in either final theorem.

## Issues found and addressed

1. **The previous acceptance checker could miss an impossible hypothesis.** It parsed a shortened printed type and accepted a theorem carrying a hidden `Fact False` instance. The replacement in [`scripts/acceptance.py`](scripts/acceptance.py) inspects Lean's elaborated binders and axiom dependencies. It rejects substantive explicit, implicit, instance, and data arguments, and exits unsuccessfully when the declaration is conditional or the audit cannot complete. Its acceptance criterion allows natural-number parameters with numeric lower bounds; it is deliberately narrower than a general-purpose theorem validator.

2. **The old direct-file build and Lake configuration disagreed.** Six retained modules depended on inferred variables despite the Lake configuration disabling that inference. Explicit declarations repair the following modules without weakening their conclusions:

   | Module in `Hypergraph/` | Variables made explicit |
   | --- | --- |
   | `BoundedDamageDomination.lean` | graph, source, target, finite set |
   | `StoppedLevel.lean` | integer sign parameter |
   | `CoreTaggedCoverUpdate.lean` | scales, probability, tolerance, history |
   | `TargetAwareLattice.lean` | probability and tolerance |
   | `CoreFaceTargetPackaging.lean` | probabilities and tolerances |
   | `ExactQuarterPlanExtraction.lean` | probability and tolerance |

   Both `autoImplicit` and `relaxedAutoImplicit` remain disabled. The default targets now cover all retained proof modules.

3. **The public boundary-exposure explanation incorrectly asserted injectivity for ordinary graphs.** With exposed set `{z₁,z₂}`, the edges `{z₁,u}` and `{z₂,u}` have the same outside reached set. Their singleton label sets nevertheless have empty intersection. The corrected explanation applies the four-functions theorem to sets of independent labels and uses reached vertex sets as additional information. The final Lean proof already retains the necessary labels.

4. **The public exploration sketch omitted the damage caused by failed examinations.** The current proof maintains actual open-path witnesses, assigns one responsible predecessor to each pending destination, and protects its unread support. Failures can disable nearby moves. The comparison uses a high-density independent field with bounded local deletions, justified by an independent block construction. The public description now includes these steps and the reduction to finitely many prototypes needed for one common smaller parameter.

5. **The public covariance explanation skipped the covariance of conditional means.** Exposing a cluster does not by itself turn covariance into an average of covariances. The corrected account includes the total-covariance term and the resampling/telescoping argument that handles it.

6. **An older all-conjectures draft misstated Question 8.** The retained [KN manuscript](docs/kn-results.pdf) uses the avoidance-conditioned score and states the counterexample to the every-minimizer interpretation. [`Question8Counterexample.lean`](KNConjectures/Question8Counterexample.lean) proves that refutation. It should not be summarized as refuting an existential choice among tied minimizers.

7. **Obsolete source files prevented a whole-tree build.** Forty-two unused KN modules, including seven broken or blocked modules, and three surgical fragments were removed from the working source tree. The retained import closures contain all current public results and their dependencies. Superseded scaffolding and the experiment with missing Python helper modules are excluded. The superseded public site manuscript, which described earlier exploration interfaces, was removed from the website; the current formal proof is linked directly.

## Checks performed

- The initial inventory covered 520 Lean sources outside the dependency cache, including the original library, extensions, scripts, and incomplete fragments. A fresh dependency-ordered rebuild tested all 516 ordinary modules: 509 passed, four failed, and three were blocked by those failures. All 440 modules in the final site import closure passed that initial rebuild. Strict Lake builds then identified and repaired the six implicit-variable discrepancies above.
- In this reorganized repository, all **224 retained extension modules** (40 in `KNConjectures/`, 184 in `Hypergraph/`) and the **247 upstream bond-library modules** were compiled from source. Both default Lake targets pass. `bash scripts/bootstrap.sh` also completes successfully, including its pinned dependency setup and the normal build.
- [`scripts/Audit.lean`](scripts/Audit.lean) prints the principal declarations and axiom lists and checks concrete three-dimensional instances. The final site statement and its fully expanded form separately pass the structural acceptance checker.
- Six acceptance regression tests pass. They compile eleven Lean fixtures, including false instance/implicit/explicit hypotheses, an impossible data certificate, an assumption hidden behind an abbreviation, an impossible dimension bound, and a custom axiom. An additional test exercises the real command path and temporary-file cleanup.
- Exact independent enumeration checks all 2,048 four-vertex hypergraphs with distinct edges of size at least two at probability one half: 177,147 configurations and 491,520 strong gluing inequalities. Another 100 nonuniform five-vertex labelled models check strong gluing, first-contact, and selected increasing-function fixed-minimizer inequalities, including repeated/empty labels and endpoint probabilities.
- The separate Boolean–Tutte regression passes 22,297 exact-arithmetic checks. Its manuscript and the KN manuscript compile without unresolved references or overfull boxes.

The mathematical review checked the meanings of the model definitions and final statements, the covariance and first-contact mechanisms, endpoint probabilities, label identity under deletion, actual path witnesses, exploration freshness, failure damage, and the common smaller-parameter argument. This is a semantic and structural review supported by compilation of the full source chain, not a handwritten re-derivation of every Lean proof term. Finite enumeration and PDF compilation are supporting checks, not proofs of the general statements.

## Source correspondence and reproduction

The original 247 bond modules match the pinned [Anthropic commit](https://github.com/anthropics/formal-math/tree/795efb86f191735c5481675763537cfb4ff37e55/percolation). The website snapshot compared in the initial review was commit `0baf9224c8d2590dc55c7ee6ec1af380bf82f852`, whose tree is `8bd5200a06d0b7dc47d3584c96e75e64c77a36cc`. Of its 193 site modules, 192 matched the original local files byte for byte; the remaining difference was comments. The 37 KN companion modules also matched. Module imports have now been reorganized; [`source-layout.json`](source-layout.json) maps their former names to the current paths.

The [README](README.md#build-and-verify) gives all reproduction commands. Selected command output is in [`verification/`](verification/). The `.lake` cache and private reading notes are excluded from the repository.
