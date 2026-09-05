import Hypergraph.ExactTargetProductSound

/-!
# Pinned-law soundness of exact target plans

Finite pinning is itself a product law: overwrite the named finite coordinates, or equivalently
replace their Bernoulli weights by zero and one.  Applying the product-law target theorem to those
weights gives the transcript-uniform and overlap-compatible target implications below.
-/

noncomputable section

namespace KNAll.Site.ExactTargetPinnedSound

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {ι : Type*}

/-- **Finite pinning is exactly the zero-one product law.**  Unlike the ratio form of
conditioning, this identity needs no positivity assumption on the pinned pattern. -/
theorem pinnedProb_eq_prodBernoulli_pinW (p : ι → unitInterval) (R : Finset ι)
    (val : ι → Prop) {A : Set (Set ι)} (hA : MeasurableSet A) :
    pinnedProb p (↑R : Set ι) val A =
      (prodBernoulli
        (pinW p (↑R : Set ι) {x | val x})).real A := by
  let xi : Set ι := {x | val x}
  have hpreM : MeasurableSet (overwrite (↑R : Set ι) xi ⁻¹' A) :=
    measurable_overwrite _ _ hA
  have hpreD : DeterminedBy (overwrite (↑R : Set ι) xi ⁻¹' A)
      (↑R : Set ι)ᶜ :=
    determinedBy_preimage_overwrite _ _ _
  have hweights :
      (prodBernoulli p).real (overwrite (↑R : Set ι) xi ⁻¹' A) =
        (prodBernoulli (pinW p (↑R : Set ι) xi)).real
          (overwrite (↑R : Set ι) xi ⁻¹' A) :=
    prodBernoulli_real_eq_of_determinedBy p (pinW p (↑R : Set ι) xi)
      (fun x hx => (pinW_apply_of_not_mem p xi hx).symm) hpreD hpreM
  rw [pinnedProb]
  change (prodBernoulli p).real
      (substitute (↑R : Set ι) (fun x => x ∈ xi) ⁻¹' A) =
    (prodBernoulli (pinW p (↑R : Set ι) xi)).real A
  rw [TargetExt.substitute_eq_overwrite]
  rw [hweights]
  rw [← prodBernoulli_pinW_real_inter_localCylinder p R.finite_toSet.countable xi A,
    inter_localCylinder_eq_preimage_overwrite_inter,
    prodBernoulli_pinW_real_inter_localCylinder p R.finite_toSet.countable xi
      (overwrite (↑R : Set ι) xi ⁻¹' A)]

end KNAll.Site.ExactTargetPinnedSound

namespace KNAll.Site.ExactTargetPlan.Plan

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

/-- Exact target soundness under an arbitrary finite pinned transcript exterior to the active
box.  The named source is among the pins and is pinned open. -/
theorem soundPinned (C : ExactTargetPlan.Plan d) (hC : C.WellFormed)
    {q : unitInterval} (hvalid : C.ValidAt q)
    {Dom R : Finset (Site d)} (hactiveDom : C.active ⊆ Dom)
    (hRactive : Disjoint R C.active)
    (val : Site d → Prop) (o : Site d) (hoDom : o ∈ Dom)
    (hoR : o ∈ R) (hvalo : val o)
    (hsrc : 1 - C.delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o
          (↑C.source : Set (Site d)))) :
    1 - C.epsilon <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o
          (↑C.target : Set (Site d))) := by
  let xi : Set (Site d) := {x | val x}
  let wp : Site d → unitInterval :=
    pinW (fun _ : Site d => q) (↑R : Set (Site d)) xi
  have hwactive : ∀ x ∈ C.active, wp x = q := by
    intro x hx
    apply pinW_apply_of_not_mem
    intro hxR
    exact Finset.disjoint_left.1 hRactive (Finset.mem_coe.1 hxR) hx
  have hwo : wp o = 1 := by
    exact pinW_apply_of_mem_of_mem (fun _ : Site d => q)
      (Finset.mem_coe.2 hoR) hvalo
  have hoActive : o ∉ C.active := by
    intro hoA
    exact Finset.disjoint_left.1 hRactive hoR hoA
  have hmSource : MeasurableSet
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o
        (↑C.source : Set (Site d))) :=
    measurableSet_connWithinSet (zdGraph d) Dom o (↑C.source : Set (Site d))
  have hmTarget : MeasurableSet
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o
        (↑C.target : Set (Site d))) :=
    measurableSet_connWithinSet (zdGraph d) Dom o (↑C.target : Set (Site d))
  have hsourceEq := ExactTargetPinnedSound.pinnedProb_eq_prodBernoulli_pinW
    (fun _ : Site d => q) R val hmSource
  have htargetEq := ExactTargetPinnedSound.pinnedProb_eq_prodBernoulli_pinW
    (fun _ : Site d => q) R val hmTarget
  have hsrcProduct : 1 - C.delta <
      (prodBernoulli wp).real
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o
          (↑C.source : Set (Site d))) := by
    simpa only [wp, xi] using hsourceEq ▸ hsrc
  have htargetProduct := C.soundProduct hC hvalid wp hactiveDom hwactive o
    (Finset.mem_sdiff.2 ⟨hoDom, hoActive⟩) hwo hsrcProduct
  rw [htargetEq]
  simpa only [wp, xi] using htargetProduct

/-- Overlap-compatible exterior wrapper.  Only `P \ active` is pinned; the unpinned overlap
between `P` and the active box remains part of the fresh product domain `P ∪ active`. -/
theorem soundPinnedExterior (C : ExactTargetPlan.Plan d) (hC : C.WellFormed)
    {q : unitInterval} (hvalid : C.ValidAt q)
    (P R : Finset (Site d))
    (hRext : R ⊆ ExactTargetPlan.exterior P C.active)
    (val : Site d → Prop) (o : Site d) (hoR : o ∈ R) (hvalo : val o)
    (hsrc : 1 - C.delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(P ∪ C.active) : Set (Site d)) o
          (↑C.source : Set (Site d)))) :
    1 - C.epsilon <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(P ∪ C.active) : Set (Site d)) o
          (↑C.target : Set (Site d))) := by
  have hRactive : Disjoint R C.active :=
    ExactTargetPlan.ExteriorSupported.disjoint_active hRext
  have hoP : o ∈ P :=
    ExactTargetPlan.ExteriorSupported.subset_ambient hRext hoR
  exact C.soundPinned hC hvalid (fun x hx => Finset.mem_union_right P hx)
    hRactive val o (Finset.mem_union_left C.active hoP) hoR hvalo hsrc

#print axioms KNAll.Site.ExactTargetPinnedSound.pinnedProb_eq_prodBernoulli_pinW
#print axioms KNAll.Site.ExactTargetPlan.Plan.soundPinned
#print axioms KNAll.Site.ExactTargetPlan.Plan.soundPinnedExterior

end KNAll.Site.ExactTargetPlan.Plan

end
