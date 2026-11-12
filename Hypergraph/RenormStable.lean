import Hypergraph.RenormData

/-!
# Stability of a certificate

A certificate is a finite list of cylinder events, each holding at the parameter `p` with strict
slack.  Two facts are proved about it.

* `CylinderExperiment.abs_prob_sub_le` — the probability of one cylinder event moves by at most
  `card support` times the parameter shift.  This is `prodBernoulli_real_lipschitz` read at the
  constant parameter families, where the sum of a constant over the support is the cardinality
  times the constant.
* `RenormData.exists_valid_nhds` — a certificate valid at `p` is valid at every parameter close
  enough to `p`.  There are finitely many bounds, the `i`-th one holds with margin
  `(bound i).prob p - threshold i > 0`, and moving the parameter by less than
  `margin / (card support + 1)` moves the `i`-th probability by less than its own margin.  The
  `+ 1` in the denominator keeps the quotient meaningful when the support is empty, and the
  minimum over the bounds is taken with `Finset.inf'`, whose nonemptiness hypothesis is why the
  case of no bounds, where the conclusion is vacuous, is treated separately.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {d : ℕ}

/-! ## The Lipschitz estimate for a single cylinder event -/

/-- **A cylinder event is Lipschitz in the parameter.**  Changing the constant parameter from `p`
to `q` moves the probability by at most the number of sites the event depends on times the shift:
the general Lipschitz estimate for product measures, with the sum of a constant over the support
evaluated as a cardinality. -/
theorem CylinderExperiment.abs_prob_sub_le (E : CylinderExperiment d) (p q : unitInterval) :
    |E.prob p - E.prob q| ≤ (E.support.card : ℝ) * |(p : ℝ) - (q : ℝ)| := by
  have h := prodBernoulli_real_lipschitz (fun _ : Site d => p) (fun _ : Site d => q)
    E.support E.determined E.measurable'
  simpa [CylinderExperiment.prob, siteBernoulli, Finset.sum_const, nsmul_eq_mul] using h

/-! ## Stability of a certificate -/

/-- **A certificate valid at `p` is valid near `p`.**  Each of the finitely many bounds holds at `p`
with a strictly positive margin; a parameter shift smaller than the margin divided by one more than
the size of the support moves that probability by less than the margin, so the strict inequality
survives.  Taking the smallest of these radii over the finitely many bounds gives one radius that
works for all of them. -/
theorem RenormData.exists_valid_nhds (C : RenormData d) {p : unitInterval} (h : C.ValidAt p) :
    ∃ ε > 0, ∀ q : unitInterval, |(q : ℝ) - (p : ℝ)| < ε → C.ValidAt q := by
  classical
  rcases eq_or_ne C.numBounds 0 with h0 | h0
  · -- No bounds: validity is vacuous, so any radius works.
    refine ⟨1, one_pos, fun q _ i => ?_⟩
    exact absurd i.isLt (by omega)
  · -- At least one bound: take the smallest of the individual radii.
    have hne : (Finset.univ : Finset (Fin C.numBounds)).Nonempty :=
      ⟨⟨0, Nat.pos_of_ne_zero h0⟩, Finset.mem_univ _⟩
    obtain ⟨f, hf⟩ : ∃ f : Fin C.numBounds → ℝ, ∀ i,
        f i = ((C.bound i).prob p - C.threshold i) / (((C.bound i).support.card : ℝ) + 1) :=
      ⟨_, fun _ => rfl⟩
    have hfpos : ∀ i, 0 < f i := by
      intro i
      rw [hf]
      exact div_pos (sub_pos.2 (h i)) (by positivity)
    refine ⟨Finset.univ.inf' hne f, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff hne).2 fun i _ => hfpos i
    · intro q hq i
      have hle : Finset.univ.inf' hne f ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
      have hcard : (0 : ℝ) < ((C.bound i).support.card : ℝ) + 1 := by positivity
      have hlip := (C.bound i).abs_prob_sub_le p q
      have key : (C.bound i).prob p - (C.bound i).prob q
          < f i * (((C.bound i).support.card : ℝ) + 1) := by
        calc (C.bound i).prob p - (C.bound i).prob q
            ≤ |(C.bound i).prob p - (C.bound i).prob q| := le_abs_self _
          _ ≤ ((C.bound i).support.card : ℝ) * |(p : ℝ) - (q : ℝ)| := hlip
          _ ≤ (((C.bound i).support.card : ℝ) + 1) * |(q : ℝ) - (p : ℝ)| := by
              rw [abs_sub_comm]
              exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ < (((C.bound i).support.card : ℝ) + 1) * Finset.univ.inf' hne f :=
              mul_lt_mul_of_pos_left hq hcard
          _ ≤ (((C.bound i).support.card : ℝ) + 1) * f i :=
              mul_le_mul_of_nonneg_left hle (le_of_lt hcard)
          _ = f i * (((C.bound i).support.card : ℝ) + 1) := mul_comm _ _
      have hval : f i * (((C.bound i).support.card : ℝ) + 1)
          = (C.bound i).prob p - C.threshold i := by
        rw [hf]
        field_simp
      rw [hval] at key
      linarith

end KNAll.Site

end
