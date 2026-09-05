import Hypergraph.HyperUpper
import Percolation.Literature.ConditionalPositiveAssociationProofs

/-!
# Harris' inequality for increasing functions of a product Bernoulli configuration

`KN/HyperUpper.lean` carries the event form of positive association, `prodBernoulli_harris_upper`:
two increasing measurable events are positively correlated.  The covariance hierarchy of the later
phases is stated for increasing real *functions* of the configuration, which is what this module
supplies:

* `prodBernoulli_integral_mul_le_of_nonneg` — for nonnegative increasing `f, g : Set ι → ℝ` over a
  finite index type, `(∫ f)(∫ g) ≤ ∫ f g` under `prodBernoulli p`;
* `prodBernoulli_integral_mul_le` — the same without the sign hypothesis.

Over a finite index type an integral against `prodBernoulli p` is the finite weighted sum
`∑ ω : Set ι, weight p ω * f ω` (`Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum`),
so no integrability side condition arises anywhere and the inequality is
`Percolation.Literature.BHK2006.harris`, i.e. Mathlib's `fkg` for the product weight.  The sign
hypothesis is removed by subtracting `f ∅` and `g ∅`: on a finite index type an increasing function
attains its minimum at `∅`, and shifting each of `f` and `g` by a constant leaves both sides of the
inequality changed by the same amount because `prodBernoulli p` is a probability measure.

The specialisation of this file to `ι = Sym2 V` is
`Percolation.Continuity.HullPort.integral_harris`, which also assumes nonnegativity; the general
index type and the removal of the sign hypothesis are what is new here.

## References

* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
* G. R. Grimmett, *Percolation*, 2nd ed., Springer (1999), Thm. (2.4) p. 34.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Literature.BHK2006 (weight harris integral_prodBernoulli_eq_sum)
open scoped Classical

variable {ι : Type*}

/-! ## The product weights sum to one -/

/-- The product weights of `prodBernoulli p` sum to `1`, since `prodBernoulli p` is a probability
measure and its integral of `1` is the sum of the weights. [folklore] -/
theorem sum_weight_prodBernoulli [Fintype ι] (p : ι → unitInterval) :
    ∑ ω : Set ι, weight (fun e => (p e : ℝ)) ω = 1 := by
  have h1 := integral_prodBernoulli_eq_sum p fun _ => (1 : ℝ)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  exact h1.symm

/-- Shifting a function by a constant shifts its weighted sum by that constant, since the weights
sum to one. [folklore] -/
theorem sum_weight_sub [Fintype ι] (p : ι → unitInterval) (h : Set ι → ℝ) (c : ℝ) :
    ∑ ω : Set ι, weight (fun e => (p e : ℝ)) ω * (h ω - c)
      = (∑ ω : Set ι, weight (fun e => (p e : ℝ)) ω * h ω) - c := by
  have hstep : ∀ ω : Set ι, weight (fun e => (p e : ℝ)) ω * (h ω - c)
      = weight (fun e => (p e : ℝ)) ω * h ω - weight (fun e => (p e : ℝ)) ω * c :=
    fun ω => by ring
  simp_rw [hstep]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_weight_prodBernoulli p, one_mul]

/-- Expansion of the weighted sum of the product of two shifted functions. [folklore] -/
theorem sum_weight_sub_mul_sub [Fintype ι] (p : ι → unitInterval) (f g : Set ι → ℝ) (a b : ℝ) :
    ∑ ω : Set ι, weight (fun e => (p e : ℝ)) ω * ((f ω - a) * (g ω - b))
      = (∑ ω : Set ι, weight (fun e => (p e : ℝ)) ω * (f ω * g ω))
        - (∑ ω : Set ι, weight (fun e => (p e : ℝ)) ω * f ω) * b
        - (∑ ω : Set ι, weight (fun e => (p e : ℝ)) ω * g ω) * a + a * b := by
  have hstep : ∀ ω : Set ι, weight (fun e => (p e : ℝ)) ω * ((f ω - a) * (g ω - b))
      = weight (fun e => (p e : ℝ)) ω * (f ω * g ω)
        - weight (fun e => (p e : ℝ)) ω * f ω * b
        - weight (fun e => (p e : ℝ)) ω * g ω * a
        + weight (fun e => (p e : ℝ)) ω * (a * b) := fun ω => by ring
  simp_rw [hstep]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, ← Finset.sum_mul, sum_weight_prodBernoulli p, one_mul]

/-! ## Harris' inequality in functional form -/

/-- **Harris' inequality for two increasing nonnegative functions** of a product Bernoulli
configuration over a finite index type: `(∫ f)(∫ g) ≤ ∫ f g`.  Over a finite index type each
integral is the finite weighted sum `∑ ω, weight p ω * f ω`, so this is the product-weight form
`Percolation.Literature.BHK2006.harris` (Mathlib's `fkg` for the product weight).
[cite: HarrisPCPS1960, Lemma 4.1] [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem prodBernoulli_integral_mul_le_of_nonneg [Fintype ι] (p : ι → unitInterval)
    {f g : Set ι → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f ω ∂(prodBernoulli p)) * (∫ ω, g ω ∂(prodBernoulli p))
      ≤ ∫ ω, f ω * g ω ∂(prodBernoulli p) := by
  have hw0 : ∀ e, 0 ≤ (p e : ℝ) := fun e => (p e).2.1
  have hw1 : ∀ e, (p e : ℝ) ≤ 1 := fun e => (p e).2.2
  have key := harris (w := fun e => (p e : ℝ)) hw0 hw1 hf0 hg0 hf hg
  rw [sum_weight_prodBernoulli p, one_mul] at key
  rw [integral_prodBernoulli_eq_sum, integral_prodBernoulli_eq_sum, integral_prodBernoulli_eq_sum]
  exact key

/-- **Harris' inequality for two increasing functions** of a product Bernoulli configuration over a
finite index type, with no sign hypothesis: `(∫ f)(∫ g) ≤ ∫ f g`.  Reduction to
`prodBernoulli_integral_mul_le_of_nonneg` by subtracting `f ∅` and `g ∅`, which are the minima of
`f` and `g`; the covariance is unchanged by such a shift because `prodBernoulli p` is a probability
measure.  [cite: HarrisPCPS1960, Lemma 4.1] [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem prodBernoulli_integral_mul_le [Fintype ι] (p : ι → unitInterval)
    {f g : Set ι → ℝ} (hf : Monotone f) (hg : Monotone g) :
    (∫ ω, f ω ∂(prodBernoulli p)) * (∫ ω, g ω ∂(prodBernoulli p))
      ≤ ∫ ω, f ω * g ω ∂(prodBernoulli p) := by
  have key := prodBernoulli_integral_mul_le_of_nonneg p
    (f := fun ω => f ω - f ∅) (g := fun ω => g ω - g ∅)
    (fun _ _ h => sub_le_sub_right (hf h) (f ∅))
    (fun _ _ h => sub_le_sub_right (hg h) (g ∅))
    (fun ω => sub_nonneg.2 (hf (Set.empty_subset ω)))
    (fun ω => sub_nonneg.2 (hg (Set.empty_subset ω)))
  simp only [integral_prodBernoulli_eq_sum] at key ⊢
  rw [sum_weight_sub p f (f ∅), sum_weight_sub p g (g ∅),
    sum_weight_sub_mul_sub p f g (f ∅) (g ∅)] at key
  nlinarith [key]

end KNAll.Site

end
