import Hypergraph.RenormData

/-!
# Certificates are stable, and that is the whole below-parameter route

A certificate is a finite list of cylinder events, each holding at the parameter `p` with strict
slack.  Three steps carry that to a statement about the critical parameter.

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
* `siteSlabReductionBelow_of_certificate` — given percolation at `p`, extract a certificate, take
  the radius `ε` on which it stays valid, and evaluate at `q = p - min (ε/2) (p/2)`, which is both
  a point of the unit interval and strictly below `p`.  Soundness of the certificate turns validity
  at `q` into percolation in a slab at `q`, which is exactly `SiteSlabReductionBelow`.

`siteCriticality_of_slabReductionBelow'` then closes the argument, so `SiteCriticality d` follows
from the two geometric propositions `CertificateExtraction d` and `CertificateSoundness d` alone.
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

/-! ## The assembly -/

/-- **The below-parameter reduction from the two geometric inputs.**  Percolation at `p` yields a
certificate valid at `p`; the certificate stays valid on a neighbourhood of `p`, which contains
parameters strictly below `p`; and a valid certificate forces percolation in its slab. -/
theorem siteSlabReductionBelow_of_certificate (d : ℕ) [NeZero d]
    (hex : CertificateExtraction d) (hsound : CertificateSoundness d) :
    SiteSlabReductionBelow d := by
  intro p hp0 hp1 hpos
  obtain ⟨C, hC⟩ := hex p hp0 hp1 hpos
  obtain ⟨ε, hε, hnhds⟩ := C.exists_valid_nhds hC
  obtain ⟨t, ht0, htε, htp⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ε / 2 ∧ t ≤ (p : ℝ) / 2 :=
    ⟨min (ε / 2) ((p : ℝ) / 2), lt_min (by linarith) (by linarith),
      min_le_left _ _, min_le_right _ _⟩
  have hp1' : (p : ℝ) ≤ 1 := p.2.2
  have hq0 : (0 : ℝ) ≤ (p : ℝ) - t := by linarith
  have hq1 : (p : ℝ) - t ≤ 1 := by linarith
  refine ⟨C.slabWidth, ⟨(p : ℝ) - t, Set.mem_Icc.2 ⟨hq0, hq1⟩⟩, ?_, ?_⟩
  · show (p : ℝ) - t < (p : ℝ)
    linarith
  · refine hsound C _ ?_
    refine hnhds _ ?_
    show |((p : ℝ) - t) - (p : ℝ)| < ε
    have hrw : ((p : ℝ) - t) - (p : ℝ) = -t := by ring
    rw [hrw, abs_neg, abs_of_pos ht0]
    linarith

/-- **The capstone.**  From the two geometric propositions of `KN/RenormData.lean` alone, site
percolation on `ℤ^d` has no infinite cluster at its critical parameter.  No theorem about
percolation at a critical point, and no half-space or slab criticality statement, is used. -/
theorem siteCriticality_of_certificate (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hex : CertificateExtraction d) (hsound : CertificateSoundness d) : SiteCriticality d :=
  siteCriticality_of_slabReductionBelow' d hd (siteSlabReductionBelow_of_certificate d hex hsound)

end KNAll.Site

end
