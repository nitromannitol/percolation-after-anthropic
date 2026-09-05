import Hypergraph.HyperCore

/-!
# Phase 1, targets 3 and 4

* `measurableSet_clusterEvent` — over a finite label type every event is measurable: it is
  determined by the finite set of all labels, hence a finite union of cylinders
  (`DeterminedBy.measurableSet_of_finset`).
* `prodBernoulli_deleteHyper_real_eq` — closing the labels that meet `K` does not change the
  probability of an event determined by the labels avoiding `K`.

The second statement carries no measurability hypothesis on the event and no finiteness hypothesis
on the label type, so `prodBernoulli_real_eq_of_determinedBy` (which needs the event to be
measurable) does not apply.  What replaces it is the gluing map
`glue(x, y)_i = x_i` for `i ∈ F`, `= y_i` for `i ∉ F` on `(ι → Prop) × (ι → Prop)`: gluing two
independent samples of the two product measures along `F` produces a sample of the product measure
with the parameters of the first family on `F` and of the second family off `F`
(`map_gluePi_bern`, the two-family form of `infinitePi_prod_map_piecewise`).  An event determined
by `F` has `glue ⁻¹' B = B ×ˢ univ`, whose product measure is the measure of `B` for *any* `B`
(`Measure.prod_prod` needs no measurability), and `μ (f ⁻¹' B) ≤ (map f μ) B` always
(`MeasureTheory.le_map_apply`).  This gives one inequality between the two probabilities; exchanging
the roles of the two parameter families gives the other.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open ProbabilityTheory

/-! ## Target 3: measurability over a finite label type -/

/-- **Target 3.**  Over a finite label type every event is measurable. -/
theorem measurableSet_clusterEvent {V E : Type*} [Fintype E] (H : Hypergraph V E)
    (S K : Set V) : MeasurableSet (clusterEvent H S K) := by
  classical
  have h : DeterminedBy (clusterEvent H S K) (↑(Finset.univ : Finset E)) := by
    rw [determinedBy_iff]
    intro ω ω' hω
    have hωω : ω = ω' := by simpa using hω
    rw [hωω]
  exact h.measurableSet_of_finset

/-! ## The gluing map -/

section Glue

variable {ι : Type*}

open Classical in
/-- The gluing map on `ι → Prop`: the coordinates in `F` are read off the first argument, the
others off the second. -/
private def gluePi (F : Set ι) (z : (ι → Prop) × (ι → Prop)) (i : ι) : Prop :=
  if i ∈ F then z.1 i else z.2 i

private theorem gluePi_of_mem (F : Set ι) (z : (ι → Prop) × (ι → Prop)) {i : ι} (hi : i ∈ F) :
    gluePi F z i = z.1 i := by
  simp [gluePi, hi]

private theorem gluePi_of_notMem (F : Set ι) (z : (ι → Prop) × (ι → Prop)) {i : ι} (hi : i ∉ F) :
    gluePi F z i = z.2 i := by
  simp [gluePi, hi]

private theorem measurable_gluePi (F : Set ι) : Measurable (gluePi F) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : i ∈ F
  · have h : (fun z : (ι → Prop) × (ι → Prop) => gluePi F z i) = fun z => z.1 i :=
      funext fun z => gluePi_of_mem F z hi
    rw [h]
    exact (measurable_pi_apply i).comp measurable_fst
  · have h : (fun z : (ι → Prop) × (ι → Prop) => gluePi F z i) = fun z => z.2 i :=
      funext fun z => gluePi_of_notMem F z hi
    rw [h]
    exact (measurable_pi_apply i).comp measurable_snd

/-- **Gluing two independent product samples along `F`.**  Reading the coordinates in `F` off a
sample of the Bernoulli product with parameters `p` and the coordinates off `F` off an independent
sample of the Bernoulli product with parameters `q` gives a sample of the Bernoulli product with
parameters `p` on `F` and `q` off `F`.  Two-family form of `infinitePi_prod_map_piecewise`. -/
private theorem map_gluePi_bern (p q r : ι → unitInterval) {F : Set ι}
    (hp : ∀ i ∈ F, r i = p i) (hq : ∀ i ∉ F, r i = q i) :
    ((Measure.infinitePi fun i => Ber(True, False, p i)).prod
        (Measure.infinitePi fun i => Ber(True, False, q i))).map (gluePi F)
      = Measure.infinitePi fun i => Ber(True, False, r i) := by
  classical
  refine Measure.eq_infinitePi _ fun I t ht => ?_
  have hmeas : MeasurableSet (Set.pi (↑I : Set ι) t) :=
    MeasurableSet.pi I.countable_toSet fun j _ => ht j
  rw [Measure.map_apply (measurable_gluePi F) hmeas]
  have hpre : gluePi F ⁻¹' Set.pi (↑I : Set ι) t
      = Set.pi (↑I : Set ι) (fun i => if i ∈ F then t i else Set.univ) ×ˢ
        Set.pi (↑I : Set ι) (fun i => if i ∈ F then Set.univ else t i) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · by_cases hjF : j ∈ F
        · rw [if_pos hjF, ← gluePi_of_mem F z hjF]
          exact h j hj
        · rw [if_neg hjF]
          exact Set.mem_univ _
      · by_cases hjF : j ∈ F
        · rw [if_pos hjF]
          exact Set.mem_univ _
        · rw [if_neg hjF, ← gluePi_of_notMem F z hjF]
          exact h j hj
    · rintro ⟨h1, h2⟩ j hj
      by_cases hjF : j ∈ F
      · rw [gluePi_of_mem F z hjF]
        have h := h1 j hj
        rwa [if_pos hjF] at h
      · rw [gluePi_of_notMem F z hjF]
        have h := h2 j hj
        rwa [if_neg hjF] at h
  rw [hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun j _ => MeasurableSet.of_discrete),
    Measure.infinitePi_pi _ (fun j _ => MeasurableSet.of_discrete),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hjF : j ∈ F
  · rw [if_pos hjF, if_pos hjF, hp j hjF, measure_univ, mul_one]
  · rw [if_neg hjF, if_neg hjF, hq j hjF, measure_univ, one_mul]

/-- **One inequality between two parameter families agreeing on `F`, with no measurability
hypothesis.**  If `B` depends only on the coordinates in `F`, and `r` agrees with `p` on `F` and
with `q` off `F`, then `B` is at least as likely under `r` as under `p`. -/
private theorem infinitePi_bern_le_of_saturated (p q r : ι → unitInterval) {F : Set ι}
    (hp : ∀ i ∈ F, r i = p i) (hq : ∀ i ∉ F, r i = q i) {B : Set (ι → Prop)}
    (hB : ∀ x y : ι → Prop, (∀ i ∈ F, x i = y i) → (x ∈ B ↔ y ∈ B)) :
    (Measure.infinitePi fun i => Ber(True, False, p i)) B
      ≤ (Measure.infinitePi fun i => Ber(True, False, r i)) B := by
  have hpre : gluePi F ⁻¹' B = B ×ˢ (Set.univ : Set (ι → Prop)) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact hB (gluePi F z) z.1 fun i hi => gluePi_of_mem F z hi
  calc (Measure.infinitePi fun i => Ber(True, False, p i)) B
      = (Measure.infinitePi fun i => Ber(True, False, p i)) B * 1 := (mul_one _).symm
    _ = ((Measure.infinitePi fun i => Ber(True, False, p i)).prod
          (Measure.infinitePi fun i => Ber(True, False, q i)))
            (B ×ˢ (Set.univ : Set (ι → Prop))) := by
        rw [Measure.prod_prod, measure_univ]
    _ = ((Measure.infinitePi fun i => Ber(True, False, p i)).prod
          (Measure.infinitePi fun i => Ber(True, False, q i))) (gluePi F ⁻¹' B) := by
        rw [hpre]
    _ ≤ (((Measure.infinitePi fun i => Ber(True, False, p i)).prod
          (Measure.infinitePi fun i => Ber(True, False, q i))).map (gluePi F)) B :=
        Measure.le_map_apply (measurable_gluePi F).aemeasurable B
    _ = (Measure.infinitePi fun i => Ber(True, False, r i)) B := by
        rw [map_gluePi_bern p q r hp hq]

/-- **Two parameter families agreeing on `F` give the same probability to every event determined
by `F`**, with no measurability hypothesis on the event (compare
`prodBernoulli_real_eq_of_determinedBy`, which assumes it). -/
private theorem prodBernoulli_apply_eq_of_determinedBy' (p q : ι → unitInterval) {F : Set ι}
    (hpq : ∀ i ∈ F, p i = q i) {A : Set (Set ι)} (hA : DeterminedBy A F) :
    prodBernoulli p A = prodBernoulli q A := by
  have hsat : ∀ x y : ι → Prop, (∀ i ∈ F, x i = y i) →
      (x ∈ (fun χ : ι → Prop => {i | χ i}) ⁻¹' A ↔
        y ∈ (fun χ : ι → Prop => {i | χ i}) ⁻¹' A) := by
    intro x y hxy
    simp only [Set.mem_preimage]
    refine (determinedBy_iff A F).1 hA _ _ ?_
    ext i
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hi⟩; exact ⟨(hxy i hi) ▸ h, hi⟩
    · rintro ⟨h, hi⟩; exact ⟨(hxy i hi) ▸ h, hi⟩
  rw [prodBernoulli_apply_eq_infinitePi, prodBernoulli_apply_eq_infinitePi]
  refine le_antisymm ?_ ?_
  · exact infinitePi_bern_le_of_saturated p q q (fun i hi => (hpq i hi).symm) (fun _ _ => rfl) hsat
  · exact infinitePi_bern_le_of_saturated q p p (fun i hi => hpq i hi) (fun _ _ => rfl) hsat

end Glue

/-! ## Target 4: closing the labels that meet `K` -/

/-- **Target 4.**  Closing the labels that meet `K` does not change the probability of an event
determined by the labels avoiding `K`. -/
theorem prodBernoulli_deleteHyper_real_eq {V E : Type*} (H : Hypergraph V E) (K : Set V)
    {A : Set (Set E)} (hA : DeterminedBy A (labelsMeeting H K)ᶜ) :
    (prodBernoulli (deleteHyper H K).prob).real A = (prodBernoulli H.prob).real A := by
  classical
  have hpq : ∀ e ∈ (labelsMeeting H K)ᶜ, (deleteHyper H K).prob e = H.prob e := by
    intro e he
    have he' : e ∉ labelsMeeting H K := he
    simp only [deleteHyper, if_neg he']
  simp only [measureReal_def,
    prodBernoulli_apply_eq_of_determinedBy' (deleteHyper H K).prob H.prob hpq hA]

end KNAll.Site

end
