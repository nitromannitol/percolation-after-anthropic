#!/usr/bin/env python3
"""Exact-arithmetic checks for random_cluster_boolean_tutte_completion.tex.

These checks are regressions, not substitutes for the proofs in the manuscript.
"""

from fractions import Fraction
from itertools import combinations, product


def choose(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    out = 1
    for j in range(1, k + 1):
        out = out * (n - j + 1) // j
    return out


def check_dawson_sankoff() -> int:
    checks = 0
    for n in range(2, 8):
        for raw in product(range(4), repeat=n):
            u = [Fraction(0)] + [Fraction(v) for v in raw]
            alpha = sum(u)
            s1 = sum(Fraction(k) * u[k] for k in range(1, n + 1))
            if s1 == 0:
                assert alpha == 0
                checks += 1
                continue
            s2 = sum(Fraction(choose(k, 2)) * u[k] for k in range(1, n + 1))
            x = 1 + 2 * s2 / s1
            r = x.numerator // x.denominator
            assert 1 <= r <= n
            ds = 2 * s1 / (r + 1) - 2 * s2 / (r * (r + 1))
            pz = s1 * s1 / (s1 + 2 * s2)
            assert pz <= ds <= alpha
            predicted_gap = (
                s1 * (x - r) * (r + 1 - x) / (x * r * (r + 1))
            )
            assert ds - pz == predicted_gap
            for k in range(1, n + 1):
                rhs = (
                    2 * Fraction(k, r + 1)
                    - 2 * Fraction(choose(k, 2), r * (r + 1))
                )
                assert rhs <= 1
            checks += 1
    return checks


def check_two_gate_deficit() -> int:
    checks = 0
    for z1, z2, z12 in product(range(7), repeat=3):
        a = Fraction(z1 + z12)
        d = Fraction(z2 + z12)
        c = Fraction(z12)
        alpha = Fraction(z1 + z2 + z12)
        assert a + d - c == alpha
        det = a * d - c * c
        if det > 0:
            gram = a * d * (a + d - 2 * c) / det
            deficit = c * (a - c) * (d - c) / det
            assert gram <= alpha
            assert alpha - gram == deficit
        checks += 1
    return checks


def all_nonempty_subsets(n: int):
    base = tuple(range(n))
    for size in range(1, n + 1):
        yield from combinations(base, size)


def check_mobius_completion() -> int:
    checks = 0
    for n in range(1, 6):
        subsets = list(all_nonempty_subsets(n))
        # Deterministic positive signature masses keep this exhaustive check small.
        z = {s: Fraction(1 + sum(1 << i for i in s)) for s in subsets}
        moments = {
            t: sum(value for s, value in z.items() if set(t).issubset(s))
            for t in subsets
        }
        alpha = sum(z.values())
        recovered = sum(
            ((-1) ** (len(t) + 1)) * moments[t]
            for t in subsets
        )
        assert recovered == alpha
        checks += len(subsets)
    return checks


def check_dual_atom_identity() -> int:
    checks = 0
    for n in range(1, 6):
        subsets = list(all_nonempty_subsets(n))
        # Inclusion-exclusion is a feasible full-level dual certificate.
        coeff = {s: Fraction((-1) ** (len(s) + 1)) for s in subsets}
        for sigma in subsets:
            atom_coefficient = sum(
                coeff[s] for s in subsets if set(s).issubset(sigma)
            )
            assert atom_coefficient == 1
            checks += 1
    return checks


def main() -> None:
    counts = {
        "Dawson-Sankoff instances": check_dawson_sankoff(),
        "two-gate instances": check_two_gate_deficit(),
        "Mobius moment entries": check_mobius_completion(),
        "dual atom identities": check_dual_atom_identity(),
    }
    for label, count in counts.items():
        print(f"{label}: {count}")
    print(f"total exact checks: {sum(counts.values())}")


if __name__ == "__main__":
    main()
