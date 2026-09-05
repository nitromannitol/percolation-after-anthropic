import Hypergraph.ExactTargetPlan
import Mathlib.Probability.Distributions.Binomial

/-!
# Arithmetic choices for exact target schemes

This file isolates the two Archimedean choices in the target-scheme extraction: the least
number of independent seed trials and the number of shell levels.  In particular, the useful
bound `k * a <= delta⁻¹` is proved for the least successful seed count rather than inserted as
an assumption.
-/

noncomputable section

namespace KNAll.Site.ExactTargetArithmetic

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory unitInterval

def deltaCOf (epsilon : Real) : Real := epsilon / 4
def deltaOf (epsilon : Real) : Real := epsilon ^ 2 / 64
def etaOf (epsilon : Real) : Real := deltaOf epsilon ^ 2 * deltaCOf epsilon
def seedCardOf (d m : Nat) : Nat := (2 * m + 2) * (4 * m + 1) ^ (d - 1)

/-- The probability of exactly one success in `k` Bernoulli trials is at most one.  Written in
the form needed for the least-seed-count estimate. -/
private theorem cast_mul_mul_pow_pred_le_one {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    {k : Nat} (hk : 0 < k) :
    (k : Real) * a * (1 - a) ^ (k - 1) ≤ 1 := by
  let p : unitInterval := ⟨a, ha0, ha1⟩
  have hprob : Bin(k, p).real ({1} : Set Nat) ≤ 1 := measureReal_le_one
  rw [binomial_real_singleton] at hprob
  simpa [p, Nat.choose_one_right, pow_one, mul_assoc, mul_left_comm, mul_comm] using hprob

/-- Choose the least number of seed blocks whose joint failure is below `delta`.  Minimality and
the binomial one-success term give the additional budget `k*a ≤ delta⁻¹`. -/
theorem exists_seed_count {a delta : Real}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ k : Nat, 0 < k ∧ (1 - a) ^ k < delta ∧ (k : Real) * a ≤ delta⁻¹ := by
  have hbase0 : 0 ≤ 1 - a := by linarith
  have hbase1 : 1 - a < 1 := by linarith
  let hex : ∃ k : Nat, (1 - a) ^ k < delta :=
    exists_pow_lt_of_lt_one hdelta0 hbase1
  let k : Nat := Nat.find hex
  have hkfail : (1 - a) ^ k < delta := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    rw [hk0, pow_zero] at hkfail
    exact (not_lt_of_ge hdelta1) hkfail
  have hprev : delta ≤ (1 - a) ^ (k - 1) := by
    apply le_of_not_gt
    intro hlt
    exact Nat.find_min hex (Nat.sub_one_lt hkpos.ne') hlt
  have hterm : (k : Real) * a * delta ≤ 1 := by
    calc
      (k : Real) * a * delta ≤ (k : Real) * a * (1 - a) ^ (k - 1) := by
        gcongr
      _ ≤ 1 := cast_mul_mul_pow_pred_le_one ha0.le ha1 hkpos
  have hkbudget : (k : Real) * a ≤ delta⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hdelta0]
    simpa [mul_assoc] using hterm
  exact ⟨k, hkpos, hkfail, hkbudget⟩

/-- For positive target error and positive barrier probability, finitely many shell levels make
the deterministic averaging coefficient exceed one. -/
theorem exists_level_count {delta b : Real} (hdelta : 0 < delta) (hb : 0 < b) :
    ∃ L : Nat, 0 < L ∧ 1 < (L : Real) * delta * b := by
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / (delta * b))
  have hprod : 0 < delta * b := mul_pos hdelta hb
  have hmain : 1 < (L : Real) * (delta * b) := by
    rw [div_lt_iff₀ hprod] at hL
    simpa [mul_comm] using hL
  have hLpos : 0 < L := by
    by_contra hzero
    have : L = 0 := Nat.eq_zero_of_not_pos hzero
    rw [this] at hmain
    norm_num at hmain
  exact ⟨L, hLpos, by simpa [mul_assoc] using hmain⟩

end KNAll.Site.ExactTargetArithmetic

end

#print axioms KNAll.Site.ExactTargetArithmetic.exists_seed_count
#print axioms KNAll.Site.ExactTargetArithmetic.exists_level_count
