import Hypergraph.ExactTargetArithmetic

/-!
# Numerical data for an exact target scheme

Starting from an interior extraction parameter, an output tolerance, and a positive source
scale, this module makes all remaining choices in (T2), (T3), and (T6).  The construction is
purely numerical and therefore reusable by every concrete quarter-face or long-box geometry.
-/

noncomputable section

namespace KNAll.Site.ExactTargetSchemeNumbers

open Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site ExactTargetArithmetic

variable {d : Nat} [NeZero d]

/-- The numerical part of a target scheme, including every inequality later copied into a
`Plan.WellFormed` proof. -/
structure Numbers (d : Nat) (p0 : unitInterval) (epsilon : Real) (m : Nat) where
  k : Nat
  N : Nat
  L : Nat
  R0 : Nat
  barrierLower : Real
  k_pos : 0 < k
  N_pos : 0 < N
  L_pos : 0 < L
  radius_budget : 2 * m + L + 2 ≤ R0
  packing : k * (siteBox d (8 * m)).card ≤ N
  seed_failure : (1 - (p0 : Real) ^ seedCardOf d m) ^ k < deltaOf epsilon
  seed_budget : (k : Real) * (p0 : Real) ^ seedCardOf d m ≤ (deltaOf epsilon)⁻¹
  barrier_pos : 0 < barrierLower
  barrier_lt_one : barrierLower < 1
  barrier_leaf : barrierLower < (1 - (p0 : Real)) ^ (2 * d * N)
  level_budget : 1 < (L : Real) * deltaOf epsilon * barrierLower

/-- All numerical target-scheme data exist.  No asymptotic rate or percolation input is used. -/
theorem exists_numbers (p0 : unitInterval)
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (epsilon : Real) (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (m : Nat) (hm : 0 < m) :
    Nonempty (Numbers d p0 epsilon m) := by
  let delta := deltaOf epsilon
  have hdelta0 : 0 < delta := by
    dsimp [delta, deltaOf]
    positivity
  have hdelta1 : delta ≤ 1 := by
    dsimp [delta, deltaOf]
    nlinarith [sq_nonneg epsilon]
  let s := seedCardOf d m
  have hs : 0 < s := by
    dsimp [s, seedCardOf]
    positivity
  let a : Real := (p0 : Real) ^ s
  have ha0 : 0 < a := pow_pos hp0 s
  have ha1 : a ≤ 1 := pow_le_one₀ p0.2.1 p0.2.2
  obtain ⟨k, hk0, hkfail, hkbudget⟩ :=
    ExactTargetArithmetic.exists_seed_count ha0 ha1 hdelta0 hdelta1
  let N := k * (siteBox d (8 * m)).card
  have hbox : 0 < (siteBox d (8 * m)).card :=
    Finset.card_pos.2 (siteBox_nonempty d (8 * m))
  have hN : 0 < N := Nat.mul_pos hk0 hbox
  let rawBarrier : Real := (1 - (p0 : Real)) ^ (2 * d * N)
  have hraw0 : 0 < rawBarrier := by
    dsimp [rawBarrier]
    exact pow_pos (sub_pos.2 hp1) _
  have hraw1 : rawBarrier ≤ 1 := by
    dsimp [rawBarrier]
    exact pow_le_one₀ (by linarith [p0.2.1]) (by linarith [p0.2.1])
  let b := rawBarrier / 2
  have hb0 : 0 < b := div_pos hraw0 (by norm_num)
  have hb1 : b < 1 := lt_of_lt_of_le (half_lt_self hraw0) hraw1
  have hbraw : b < rawBarrier := half_lt_self hraw0
  obtain ⟨L, hL0, hLbudget⟩ := ExactTargetArithmetic.exists_level_count hdelta0 hb0
  exact ⟨{
    k := k
    N := N
    L := L
    R0 := 2 * m + L + 2
    barrierLower := b
    k_pos := hk0
    N_pos := hN
    L_pos := hL0
    radius_budget := le_rfl
    packing := le_rfl
    seed_failure := by simpa [a, s, delta] using hkfail
    seed_budget := by simpa [a, s, delta] using hkbudget
    barrier_pos := hb0
    barrier_lt_one := hb1
    barrier_leaf := by simpa [b, rawBarrier] using hbraw
    level_budget := by simpa [delta] using hLbudget }⟩

end KNAll.Site.ExactTargetSchemeNumbers

end

#print axioms KNAll.Site.ExactTargetSchemeNumbers.exists_numbers
