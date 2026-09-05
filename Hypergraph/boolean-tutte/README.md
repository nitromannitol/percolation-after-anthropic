# Boolean–Tutte completion: status

The manuscript `completion.tex` replaces the proposed
Christoffel/Gram relaxation by the exact finite linear program on Boolean gate
signatures.

Main gains:

- it is the strongest lower bound determined by the selected intersection moments
  for arbitrary finite event systems;
- it dominates every Rayleigh/Gram bound built from the same moments;
- its capped form also uses the exact gate-signature probabilities when the
  observable lies in `[0,1]`;
- its gate-count quotient gives the sharp Dawson–Sankoff formula at order two;
- for two gates, the order-two formula is exact using the same data for which the
  Gram formula can have a positive deficit;
- in a finite random-cluster model it yields coefficientwise nonnegative
  component-partition/Tutte polynomial certificates, simultaneously for all
  `q > 0`.

Verification performed:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  completion.tex
python3 verify.py
```

The PDF builds in two passes with no unresolved references, overfull boxes, or
mathematical compilation warnings. The exact-arithmetic regression performs 22,297
checks of the Dawson–Sankoff formula, its comparison with Cauchy–Schwarz, the
two-gate deficit identity, Möbius completion, and the full-level dual identity.
The regression is not a substitute for the proofs.

These finite random-cluster results are separate from the lattice criticality proof.
