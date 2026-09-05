import Hypergraph.StubBudget

/-!
# A simultaneous scale choice for the stopped core construction

The number of stopped levels has to be chosen before the corridor radius.  This small numerical
lemma records that order explicitly.  Besides the geometric-series bound, it supplies all of the
elementary inequalities used by the core stopped tower, the next-head freshness lemma, and the
post-entry family.  In particular, the stronger recursive budget `10 * s * K ≤ 10 * r` is built
in; the older `13 * r` bound then follows for free.
-/

noncomputable section

namespace KNAll.Site.CoreStopBudget

open KNAll.Site

/-- Choose the stopped depth `K`, then the shell stride `s`, then a corridor radius `r`, and only
then the transverse half-width `t`.  The statement is deliberately independent of a certificate
structure so it can be reused during extraction and after parameter descent. -/
theorem exists_scales (d L F R : Nat) {rho delta2 : Real}
    (hrho : 0 < rho) (hdelta0 : 0 < delta2) (hdelta1 : delta2 ≤ 1) :
    ∃ K s r t : Nat,
      (1 - delta2) ^ K ≤ rho / 32 ∧
      0 < s ∧ 0 < r ∧
      10 * s * K ≤ 10 * r ∧
      10 * s * K ≤ 13 * r ∧
      L + 1 ≤ 10 * s ∧
      L + 1 ≤ 3 * r ∧
      5 * s * K + L + F + 2 ≤ 8 * r ∧
      F + 1 ≤ 2 * r ∧
      F + 1 ≤ t ∧
      5 * r ≤ t ∧
      44 ≤ r ∧
      100 * (d + 1) * (R + 1) < r := by
  obtain ⟨K, hK⟩ := Budget.exists_levelCount rho delta2 hrho hdelta0 hdelta1
  let s : Nat := L + 1
  let r : Nat :=
    max 44
      (max (100 * (d + 1) * (R + 1) + 1)
        (max (s * K) (5 * s * K + L + F + 2)))
  let t : Nat := 5 * r + F + 1
  refine ⟨K, s, r, t, hK.le, ?_⟩
  have hs : 0 < s := by simp [s]
  have hr44 : 44 ≤ r := by simp [r]
  have hrpos : 0 < r := lt_of_lt_of_le (by decide : 0 < 44) hr44
  have hscale_le : 100 * (d + 1) * (R + 1) + 1 ≤ r := by
    simp [r]
  have hsK : s * K ≤ r := by simp [r]
  have hlong0 : 5 * s * K + L + F + 2 ≤ r := by simp [r]
  constructor
  · exact hs
  constructor
  · exact hrpos
  constructor
  · simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hsK
  constructor
  · have h10 : 10 * s * K ≤ 10 * r := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hsK
    have h1013 : 10 * r ≤ 13 * r := by omega
    exact h10.trans h1013
  constructor
  · simp [s]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · dsimp [t]
    omega
  constructor
  · dsimp [t]
    omega
  constructor
  · exact hr44
  · omega

/-- The same choice with a strict geometric-series estimate, useful when a downstream theorem
preserves strict inequalities rather than weakening them to `≤`. -/
theorem exists_scales_strict (d L F R : Nat) {rho delta2 : Real}
    (hrho : 0 < rho) (hdelta0 : 0 < delta2) (hdelta1 : delta2 ≤ 1) :
    ∃ K s r t : Nat,
      (1 - delta2) ^ K < rho / 32 ∧
      0 < s ∧ 0 < r ∧
      10 * s * K ≤ 10 * r ∧
      10 * s * K ≤ 13 * r ∧
      L + 1 ≤ 10 * s ∧
      L + 1 ≤ 3 * r ∧
      5 * s * K + L + F + 2 ≤ 8 * r ∧
      F + 1 ≤ 2 * r ∧
      F + 1 ≤ t ∧
      5 * r ≤ t ∧
      44 ≤ r ∧
      100 * (d + 1) * (R + 1) < r := by
  obtain ⟨K, hK⟩ := Budget.exists_levelCount rho delta2 hrho hdelta0 hdelta1
  let s : Nat := L + 1
  let r : Nat :=
    max 44
      (max (100 * (d + 1) * (R + 1) + 1)
        (max (s * K) (5 * s * K + L + F + 2)))
  let t : Nat := 5 * r + F + 1
  refine ⟨K, s, r, t, hK, ?_⟩
  have hs : 0 < s := by simp [s]
  have hr44 : 44 ≤ r := by simp [r]
  have hrpos : 0 < r := lt_of_lt_of_le (by decide : 0 < 44) hr44
  have hscale_le : 100 * (d + 1) * (R + 1) + 1 ≤ r := by
    simp [r]
  have hsK : s * K ≤ r := by simp [r]
  have hlong0 : 5 * s * K + L + F + 2 ≤ r := by simp [r]
  constructor
  · exact hs
  constructor
  · exact hrpos
  constructor
  · simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hsK
  constructor
  · have h10 : 10 * s * K ≤ 10 * r := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hsK
    have h1013 : 10 * r ≤ 13 * r := by omega
    exact h10.trans h1013
  constructor
  · simp [s]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · dsimp [t]
    omega
  constructor
  · dsimp [t]
    omega
  constructor
  · exact hr44
  · omega

#print axioms KNAll.Site.CoreStopBudget.exists_scales
#print axioms KNAll.Site.CoreStopBudget.exists_scales_strict

end KNAll.Site.CoreStopBudget

end
