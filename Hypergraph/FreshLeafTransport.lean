import Hypergraph.ExactTargetPlan

/-!
# Transport of fresh finite site leaves

An i.i.d. site cylinder may be moved to any explicitly bijective copy of its finite
coordinates without changing its probability.  If the copy is disjoint from a pinned set, the
same equality holds in the residual product law.  The final section records the exact laws of the
canonical seed and barrier leaves used by `ExactTargetPlan`.
-/

noncomputable section

namespace KNAll.Site.FreshLeafTransport

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {ι α β κ : Type*}

/-! ## Explicit finite-coordinate transport -/

/-- Realize an event on abstract coordinates `α` on an explicitly embedded copy in `ι`. -/
def realizeEvent (f : α ↪ ι) (A : Set (SiteConfig α)) : Set (SiteConfig ι) :=
  restrictSite f ⁻¹' A

theorem measurableSet_realizeEvent (f : α ↪ ι) {A : Set (SiteConfig α)}
    (hA : MeasurableSet A) : MeasurableSet (realizeEvent f A) :=
  hA.preimage (measurable_restrictSite f)

/-- A realized event reads only the range of its coordinate embedding. -/
theorem determinedBy_realizeEvent (f : α ↪ ι) (A : Set (SiteConfig α)) :
    DeterminedBy (realizeEvent f A) (Set.range f) := by
  rw [determinedBy_iff]
  intro omega omega' hagree
  have hr : restrictSite f omega = restrictSite f omega' := by
    ext a
    have ha := Set.ext_iff.1 hagree (f a)
    simpa [mem_restrictSite] using ha
  change restrictSite f omega ∈ A ↔ restrictSite f omega' ∈ A
  rw [hr]

/-- Homogeneous product probability of a realized event is independent of the embedding. -/
theorem real_realizeEvent_eq (q : unitInterval) (f : α ↪ ι)
    {A : Set (SiteConfig α)} (hA : MeasurableSet A) :
    (siteBernoulli (fun _ : ι => q)).real (realizeEvent f A) =
      (siteBernoulli (fun _ : α => q)).real A := by
  exact siteBernoulli_real_preimage_restrictSite (fun _ : ι => q) f.injective hA

/-- Transport an event along an explicit bijection of its coordinate types. -/
def transportEvent (e : α ≃ β) (A : Set (SiteConfig α)) : Set (SiteConfig β) :=
  realizeEvent e.toEmbedding A

/-- **Fresh-leaf transport.**  Relabelling finitely many homogeneous coordinates along an
explicit equivalence preserves the real probability of every measurable leaf event. -/
theorem real_transportEvent_eq [Finite α] [Finite β] (q : unitInterval) (e : α ≃ β)
    {A : Set (SiteConfig α)} (hA : MeasurableSet A) :
    (siteBernoulli (fun _ : β => q)).real (transportEvent e A) =
      (siteBernoulli (fun _ : α => q)).real A :=
  real_realizeEvent_eq q e.toEmbedding hA

/-- The inclusion of a finite set into its ambient coordinate type. -/
def finsetInclusion (S : Finset ι) : S ↪ ι where
  toFun := Subtype.val
  inj' := Subtype.val_injective

/-- Embed the coordinates of `S` into `β` using an explicit bijection with `T`. -/
def finsetTransportEmbedding {S : Finset ι} {T : Finset β} (e : S ≃ T) : S ↪ β where
  toFun x := (e x).1
  inj' := fun _ _ h => e.injective (Subtype.ext h)

/-- An event on the finite coordinate type `S`, transported to the copy `T` in another ambient
space. -/
def transportFinsetEvent {S : Finset ι} {T : Finset β} (e : S ≃ T)
    (A : Set (SiteConfig S)) : Set (SiteConfig β) :=
  realizeEvent (finsetTransportEmbedding e) A

/-- Ambient form of fresh-leaf transport: the copy on `T` and the original copy on `S` have the
same homogeneous site probability. -/
theorem real_transportFinsetEvent_eq {S : Finset ι} {T : Finset β} (q : unitInterval)
    (e : S ≃ T) {A : Set (SiteConfig S)} (hA : MeasurableSet A) :
    (siteBernoulli (fun _ : β => q)).real (transportFinsetEvent e A) =
      (siteBernoulli (fun _ : ι => q)).real (realizeEvent (finsetInclusion S) A) := by
  change (siteBernoulli (fun _ : β => q)).real
      (realizeEvent (finsetTransportEmbedding e) A) = _
  rw [real_realizeEvent_eq q (finsetTransportEmbedding e) hA,
    real_realizeEvent_eq q (finsetInclusion S) hA]

/-! ## Freshness with respect to a pinned transcript -/

/-- A leaf realized on coordinates disjoint from the pins retains its unconditional law. -/
theorem pinnedProb_realizeEvent_eq (q : unitInterval) (f : α ↪ ι)
    {A : Set (SiteConfig α)} (hA : MeasurableSet A) (R : Set ι) (val : ι → Prop)
    (hfresh : Disjoint R (Set.range f)) :
    pinnedProb (fun _ : ι => q) R val (realizeEvent f A) =
      (siteBernoulli (fun _ : α => q)).real A := by
  have hrange : Set.range f ⊆ Rᶜ := by
    intro x hx hR
    exact Set.disjoint_left.1 hfresh hR hx
  rw [pinnedProb_eq_of_determinedBy_compl _ _ _
      ((determinedBy_realizeEvent f A).mono hrange)]
  change (siteBernoulli (fun _ : ι => q)).real (realizeEvent f A) = _
  exact real_realizeEvent_eq q f hA

/-- Residual fresh-leaf transport between two ambient finite copies. -/
theorem pinnedProb_transportFinsetEvent_eq {S : Finset ι} {T : Finset β}
    (q : unitInterval) (e : S ≃ T) {A : Set (SiteConfig S)} (hA : MeasurableSet A)
    (R : Set β) (val : β → Prop)
    (hfresh : Disjoint R (↑T : Set β)) :
    pinnedProb (fun _ : β => q) R val (transportFinsetEvent e A) =
      (siteBernoulli (fun _ : ι => q)).real (realizeEvent (finsetInclusion S) A) := by
  have hrange : Set.range (finsetTransportEmbedding e) = (↑T : Set β) := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (e s).2
    · intro hx
      let t : T := ⟨x, hx⟩
      exact ⟨e.symm t, by simp [finsetTransportEmbedding, t]⟩
  rw [← hrange] at hfresh
  change pinnedProb (fun _ : β => q) R val
      (realizeEvent (finsetTransportEmbedding e) A) = _
  rw [pinnedProb_realizeEvent_eq q (finsetTransportEmbedding e) hA R val hfresh,
    real_realizeEvent_eq q (finsetInclusion S) hA]

/-! ## Exact canonical seed and barrier laws -/

/-- The event that every coordinate of `F` is open. -/
def allOpenEvent [DecidableEq ι] (F : Finset ι) : Set (SiteConfig ι) :=
  {omega | (↑F : Set ι) ⊆ omega}

theorem determinedBy_allOpenEvent [DecidableEq ι] (F : Finset ι) :
    DeterminedBy (allOpenEvent F) (↑F : Set ι) :=
  determinedBy_allOpen (↑F : Set ι)

theorem measurableSet_allOpenEvent [DecidableEq ι] (F : Finset ι) :
    MeasurableSet (allOpenEvent F) :=
  (determinedBy_allOpenEvent F).measurableSet_of_finset

theorem real_allOpenEvent [DecidableEq ι] (q : unitInterval) (F : Finset ι) :
    (siteBernoulli (fun _ : ι => q)).real (allOpenEvent F) = (q : Real) ^ F.card := by
  rw [siteBernoulli, allOpenEvent, prodBernoulli_real_subset, Finset.prod_const]

/-- Exact finite-product formula for the event that some one of a pairwise-disjoint family of
equal-cardinality blocks is entirely open. -/
theorem real_exists_allOpen_eq [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (q : unitInterval) (block : κ → Finset ι) (s : Nat)
    (hdisj : (Set.univ : Set κ).PairwiseDisjoint block)
    (hcard : ∀ i, (block i).card = s) :
    (siteBernoulli (fun _ : ι => q)).real
        {omega | ∃ i, (↑(block i) : Set ι) ⊆ omega} =
      1 - (1 - (q : Real) ^ s) ^ Fintype.card κ := by
  classical
  change (prodBernoulli (fun _ : ι => q)).real
      {omega | ∃ i, (↑(block i) : Set ι) ⊆ omega} = _
  let I : Finset κ := Finset.univ
  have hevent : {omega : SiteConfig ι | ∃ i, (↑(block i) : Set ι) ⊆ omega} =
      ⋃ i ∈ I, allOpenEvent (block i) := by
    ext omega
    simp [I, allOpenEvent]
  have hmeas : MeasurableSet (⋃ i ∈ I, allOpenEvent (block i)) :=
    Finset.measurableSet_biUnion I fun i _ => measurableSet_allOpenEvent (block i)
  have hcompl : (⋃ i ∈ I, allOpenEvent (block i))ᶜ =
      ⋂ i ∈ I, (allOpenEvent (block i))ᶜ := by
    rw [Set.compl_iUnion₂]
  have hpair : (↑I : Set κ).PairwiseDisjoint block := by
    simpa [I] using hdisj
  have hprod :
      (prodBernoulli (fun _ : ι => q)).real
          (⋂ i ∈ I, (allOpenEvent (block i))ᶜ) =
        ∏ i ∈ I,
          (prodBernoulli (fun _ : ι => q)).real (allOpenEvent (block i))ᶜ := by
    have huniv : DeterminedBy (Set.univ : Set (SiteConfig ι))
        (⋃ i ∈ I, (↑(block i) : Set ι))ᶜ := by
      rw [determinedBy_iff]
      intro _ _ _
      exact Iff.rfl
    have h := prodBernoulli_real_inter_biInter_of_determinedBy
      (fun _ : ι => q) I block hpair
      (fun i _ => (determinedBy_allOpenEvent (block i)).compl)
      (fun i _ => (measurableSet_allOpenEvent (block i)).compl)
      huniv MeasurableSet.univ
    simpa only [Set.univ_inter, probReal_univ, one_mul] using h
  have hfactor : ∀ i,
      (prodBernoulli (fun _ : ι => q)).real (allOpenEvent (block i))ᶜ =
        1 - (q : Real) ^ s := by
    intro i
    rw [measureReal_compl (measurableSet_allOpenEvent (block i)), probReal_univ]
    change 1 - (siteBernoulli (fun _ : ι => q)).real (allOpenEvent (block i)) = _
    rw [real_allOpenEvent, hcard i]
  have hfail :
      (prodBernoulli (fun _ : ι => q)).real
          (⋃ i ∈ I, allOpenEvent (block i))ᶜ =
        (1 - (q : Real) ^ s) ^ Fintype.card κ := by
    rw [hcompl, hprod]
    simp_rw [hfactor]
    simp [I]
  rw [hevent]
  have hc :
      (prodBernoulli (fun _ : ι => q)).real
          (⋃ i ∈ I, allOpenEvent (block i))ᶜ =
        (prodBernoulli (fun _ : ι => q)).real Set.univ -
          (prodBernoulli (fun _ : ι => q)).real
            (⋃ i ∈ I, allOpenEvent (block i)) :=
    measureReal_compl hmeas
  rw [probReal_univ, hfail] at hc
  linarith

variable {d : Nat}

theorem determinedBy_seedEvent {k : Nat} (block : Fin k → Finset (Site d)) :
    DeterminedBy (ExactTargetPlan.seedEvent block)
      (↑(ExactTargetPlan.seedSupport block) : Set (Site d)) := by
  rw [determinedBy_iff]
  intro omega omega' hagree
  have hagree' := TargetExt.forall_iff_of_inter_eq hagree
  simp only [ExactTargetPlan.seedEvent, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun x hx => ?_⟩
    apply (hagree' x ?_).1 (hi hx)
    apply Finset.mem_coe.2
    unfold ExactTargetPlan.seedSupport
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, Finset.mem_coe.1 hx⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, fun x hx => ?_⟩
    apply (hagree' x ?_).2 (hi hx)
    apply Finset.mem_coe.2
    unfold ExactTargetPlan.seedSupport
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, Finset.mem_coe.1 hx⟩

theorem measurableSet_seedEvent {k : Nat} (block : Fin k → Finset (Site d)) :
    MeasurableSet (ExactTargetPlan.seedEvent block) :=
  (determinedBy_seedEvent block).measurableSet_of_finset

/-- Exact law of the T5 seed leaf. -/
theorem real_seedEvent_eq {k : Nat} (q : unitInterval)
    (block : Fin k → Finset (Site d)) (s : Nat)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hcard : ∀ i, (block i).card = s) :
    (siteBernoulli (fun _ : Site d => q)).real (ExactTargetPlan.seedEvent block) =
      1 - (1 - (q : Real) ^ s) ^ k := by
  simpa only [ExactTargetPlan.seedEvent, Fintype.card_fin] using
    (real_exists_allOpen_eq q block s
      (by
        intro i _ j _ hij
        exact hdisj i j hij)
      hcard)

/-- Exact residual law of a T5 seed leaf whose whole support is fresh. -/
theorem pinnedProb_seedEvent_eq {k : Nat} (q : unitInterval)
    (block : Fin k → Finset (Site d)) (s : Nat)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hcard : ∀ i, (block i).card = s)
    (R : Set (Site d)) (val : Site d → Prop)
    (hfresh : Disjoint R (↑(ExactTargetPlan.seedSupport block) : Set (Site d))) :
    pinnedProb (fun _ : Site d => q) R val (ExactTargetPlan.seedEvent block) =
      1 - (1 - (q : Real) ^ s) ^ k := by
  rw [pinnedProb_eq_of_determinedBy_compl _ _ _
      ((determinedBy_seedEvent block).mono
        (fun x hxS hxR => Set.disjoint_left.1 hfresh hxR hxS))]
  change (siteBernoulli (fun _ : Site d => q)).real
      (ExactTargetPlan.seedEvent block) = _
  exact real_seedEvent_eq q block s hdisj hcard

theorem determinedBy_barrierEvent (support : Finset (Site d)) :
    DeterminedBy (ExactTargetPlan.barrierEvent support) (↑support : Set (Site d)) := by
  rw [determinedBy_iff]
  intro omega omega' hagree
  have h := TargetExt.forall_iff_of_inter_eq hagree
  simp only [ExactTargetPlan.barrierEvent, Set.mem_setOf_eq]
  exact forall_congr' fun x => forall_congr' fun hx => not_congr (h x (Finset.mem_coe.2 hx))

theorem measurableSet_barrierEvent (support : Finset (Site d)) :
    MeasurableSet (ExactTargetPlan.barrierEvent support) :=
  (determinedBy_barrierEvent support).measurableSet_of_finset

/-- Exact law of an all-closed barrier support. -/
theorem real_barrierEvent_eq (q : unitInterval) (support : Finset (Site d)) :
    (siteBernoulli (fun _ : Site d => q)).real (ExactTargetPlan.barrierEvent support) =
      (1 - (q : Real)) ^ support.card := by
  rw [siteBernoulli, ExactTargetPlan.barrierEvent,
    prodBernoulli_real_forall_notMem, Finset.prod_const]

/-- Cardinality-indexed form used by the T6 barrier leaf. -/
theorem real_barrierEvent_eq_of_card (q : unitInterval) (support : Finset (Site d))
    (n : Nat) (hcard : support.card = n) :
    (siteBernoulli (fun _ : Site d => q)).real (ExactTargetPlan.barrierEvent support) =
      (1 - (q : Real)) ^ n := by
  rw [real_barrierEvent_eq, hcard]

/-- Exact residual law of a T6 barrier whose support is fresh. -/
theorem pinnedProb_barrierEvent_eq (q : unitInterval) (support : Finset (Site d))
    (R : Set (Site d)) (val : Site d → Prop)
    (hfresh : Disjoint R (↑support : Set (Site d))) :
    pinnedProb (fun _ : Site d => q) R val (ExactTargetPlan.barrierEvent support) =
      (1 - (q : Real)) ^ support.card := by
  rw [pinnedProb_eq_of_determinedBy_compl _ _ _
      ((determinedBy_barrierEvent support).mono
        (fun x hxS hxR => Set.disjoint_left.1 hfresh hxR hxS))]
  change (siteBernoulli (fun _ : Site d => q)).real
      (ExactTargetPlan.barrierEvent support) = _
  exact real_barrierEvent_eq q support

/-! ### Direct T5/T6 leaf-table consequences -/

/-- A well-formed exact target plan's named T5 leaf has the canonical seed probability. -/
theorem plan_seedLeaf_prob_eq (q : unitInterval) {C : ExactTargetPlan.Plan d}
    (hC : C.WellFormed) :
    (C.leaf C.seedLeaf).experiment.prob q =
      1 - (1 - (q : Real) ^ C.seedCard) ^ C.k := by
  have h5 := hC.2.2.2.2.1
  rw [CylinderExperiment.prob, h5.2.2.2.1]
  exact real_seedEvent_eq q C.seedBlock C.seedCard h5.2.1 h5.1

/-- A well-formed exact target plan's named T6 leaf has the canonical all-closed probability. -/
theorem plan_barrierLeaf_prob_eq (q : unitInterval) {C : ExactTargetPlan.Plan d}
    (hC : C.WellFormed) :
    (C.leaf C.barrierLeaf).experiment.prob q =
      (1 - (q : Real)) ^ (2 * d * C.N) := by
  have h6 := hC.2.2.2.2.2
  rw [CylinderExperiment.prob, h6.2.2.1, real_barrierEvent_eq, h6.1]

#print axioms KNAll.Site.FreshLeafTransport.real_transportFinsetEvent_eq
#print axioms KNAll.Site.FreshLeafTransport.pinnedProb_transportFinsetEvent_eq
#print axioms KNAll.Site.FreshLeafTransport.real_seedEvent_eq
#print axioms KNAll.Site.FreshLeafTransport.pinnedProb_seedEvent_eq
#print axioms KNAll.Site.FreshLeafTransport.real_barrierEvent_eq_of_card
#print axioms KNAll.Site.FreshLeafTransport.pinnedProb_barrierEvent_eq
#print axioms KNAll.Site.FreshLeafTransport.plan_seedLeaf_prob_eq
#print axioms KNAll.Site.FreshLeafTransport.plan_barrierLeaf_prob_eq

end KNAll.Site.FreshLeafTransport

end
