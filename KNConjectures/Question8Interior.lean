import KNConjectures.Question8Defs
import Percolation.Literature.LatticeModels.ProdBernoulliWeightContinuity

/-!
# Question 8: closure of the strict-minimiser form from interior weights

The strict inequalities selecting a relay persist on an open neighbourhood of the
weight vector.  Interior weight vectors are dense, while the desired probability
inequality is closed.  This proves the boundary-closure proposition without making
any assertion about the open core itself.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open _root_.Topology
open scoped Classical

/-- **Boundary closure for a strict minimizer.**  To prove `Question8Strict`, it is
enough to prove it for weight functions all of whose coordinates lie strictly
between zero and one. -/
theorem q8Strict_of_interior
    (hInterior :
      ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
        (o b a : Fin n),
        (∀ e, 0 < w e ∧ w e < 1) →
          IsQ8StrictMin w A o b a → q8L w A o b a ≤ q8R w A o b) :
    Question8Strict := by
  intro n w A o b a hmin
  let I : Set (Sym2 (Fin n) → unitInterval) :=
    {p | ∀ e, 0 < p e ∧ p e < 1}
  let N : Set (Sym2 (Fin n) → unitInterval) :=
    ⋂ x ∈ A.erase a,
      {p | q8Score p A o b a < q8Score p A o b x}
  let C : Set (Sym2 (Fin n) → unitInterval) :=
    {p | q8L p A o b a ≤ q8R p A o b}
  have hNopen : IsOpen N := by
    dsimp only [N]
    refine isOpen_biInter_finset fun x hx ↦ ?_
    exact isOpen_lt
      (prodBernoulli_real_continuous
        (openConn a b ∩ (U A o)ᶜ))
      (prodBernoulli_real_continuous
        (openConn x b ∩ (U A o)ᶜ))
  have hwN : w ∈ N := by
    simp only [N, mem_iInter]
    intro x hx
    exact hmin.2 x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
  have hNstrict : ∀ {p}, p ∈ N → IsQ8StrictMin p A o b a := by
    intro p hp
    refine ⟨hmin.1, ?_⟩
    intro x hx hxa
    have hxerase : x ∈ A.erase a := Finset.mem_erase.2 ⟨hxa, hx⟩
    have hp' : ∀ x ∈ A.erase a,
        q8Score p A o b a < q8Score p A o b x := by
      simpa only [N, mem_iInter, mem_setOf_eq] using hp
    exact hp' x hxerase
  have hIdense : Dense I := by
    exact dense_setOf_weights_pos_lt_one
  have hCclosed : IsClosed C := by
    exact isClosed_le
      (prodBernoulli_real_continuous
        (openConn a b ∩ U A o))
      (prodBernoulli_real_continuous
        (openConn o b ∩ U A o))
  have hsub : N ∩ I ⊆ C := by
    intro p hp
    exact hInterior n p A o b a hp.2 (hNstrict hp.1)
  have hwClosure : w ∈ closure (N ∩ I) :=
    hIdense.open_subset_closure_inter hNopen hwN
  exact (closure_minimal hsub hCclosed) hwClosure

end KNAll

end

#print axioms KNAll.q8Strict_of_interior
