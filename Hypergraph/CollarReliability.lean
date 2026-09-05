import Hypergraph.TargetExtension

/-!
# Reliability after exposing a finite collar

This file isolates the finite disintegration estimate used by the reinforced-window target
argument.  If `B` is a collar event and, after the collar is pinned, the residual probability of
`A` is at most `1 - δ`, then the mass of such bad collar patterns is charged to `B ∩ Aᶜ` with
factor `δ`.  The statement is entirely finite-coordinate and transports no conditional estimate
between parameters.
-/

noncomputable section

namespace KNAll.Site.TargetExt

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {ι : Type*}

open Classical in
/-- **Restricted finite-pattern Markov inequality.**  The usual pinned-probability Markov
estimate remains valid after intersecting with any event determined by the pinned coordinates.

In the target construction `B` is the event that one reinforced window is entirely open.  The
right-hand side can then be bounded by Harris and a named finite hitting leaf, retaining the small
factor `P(B)` rather than paying for the whole collar. -/
theorem mul_real_inter_setOf_pinnedProb_le_le
    (w : ι → unitInterval) (S : Finset ι) {A B : Set (Set ι)}
    (hA : MeasurableSet A) (hB : DeterminedBy B (↑S : Set ι)) (δ : ℝ) :
    δ * (prodBernoulli w).real
        (B ∩ { ω : Set ι |
          pinnedProb w (↑S : Set ι) (fun i => i ∈ ω) A ≤ 1 - δ }) ≤
      (prodBernoulli w).real (B ∩ Aᶜ) := by
  classical
  let Low : Set (Set ι) :=
    { ω : Set ι | pinnedProb w (↑S : Set ι) (fun i => i ∈ ω) A ≤ 1 - δ }
  have hLow : DeterminedBy Low (↑S : Set ι) :=
    determinedBy_setOf_pinnedProb_le w (↑S : Set ι) A (1 - δ)
  have hLow' : Low =
      { ω : Set ι | pinnedProb w (↑S : Set ι) (fun i => i ∈ ω) A ≤ 1 - δ } := by
    rfl
  have hBL : DeterminedBy (B ∩ Low) (↑S : Set ι) := hB.inter hLow
  have hBm : MeasurableSet B := hB.measurableSet_of_finset
  have hBLm : MeasurableSet (B ∩ Low) := hBL.measurableSet_of_finset
  rw [← hLow', real_eq_sum_inter_localCylinder w S hBLm,
    real_eq_sum_inter_localCylinder w S (hBm.inter hA.compl), Finset.mul_sum]
  refine Finset.sum_le_sum fun T hT => ?_
  have hTS : T ⊆ S := Finset.mem_powerset.1 hT
  rw [inter_localCylinder_of_determinedBy hBL hTS]
  by_cases hTBL : (↑T : Set ι) ∈ B ∩ Low
  · rw [if_pos hTBL]
    have hTB : (↑T : Set ι) ∈ B := hTBL.1
    have hTL : pinnedProb w (↑S : Set ι) (fun i => i ∈ (↑T : Set ι)) A ≤
        1 - δ := hTBL.2
    have hBcyl : B ∩ localCylinder (↑S : Set ι) (↑T : Set ι) =
        localCylinder (↑S : Set ι) (↑T : Set ι) := by
      simpa [inter_localCylinder_of_determinedBy hB hTS, hTB]
    have heq : (B ∩ Aᶜ) ∩ localCylinder (↑S : Set ι) (↑T : Set ι) =
        Aᶜ ∩ localCylinder (↑S : Set ι) (↑T : Set ι) := by
      calc
        (B ∩ Aᶜ) ∩ localCylinder (↑S : Set ι) (↑T : Set ι) =
            Aᶜ ∩ (B ∩ localCylinder (↑S : Set ι) (↑T : Set ι)) := by
              ext ω
              simp only [Set.mem_inter_iff]
              tauto
        _ = Aᶜ ∩ localCylinder (↑S : Set ι) (↑T : Set ι) := by rw [hBcyl]
    rw [heq, real_inter_localCylinder_eq_mul_pinnedProb w S (↑T : Set ι) hA.compl,
      pinnedProb_compl w (↑S : Set ι) (fun i => i ∈ (↑T : Set ι)) hA]
    have hcyl0 : 0 ≤
        (prodBernoulli w).real (localCylinder (↑S : Set ι) (↑T : Set ι)) :=
      measureReal_nonneg
    nlinarith
  · simp [hTBL]

/-- If an increasing collar event `O`, together with an increasing hit event `H`, forces `A`,
then the mass of collar patterns on which `A` has residual probability at most `1-δ` is bounded
by `P(O) P(Hᶜ)`.  This is the exact `a * η` estimate used for reinforced windows. -/
theorem mul_real_open_inter_low_le_mul_hit_compl
    (w : ι → unitInterval) (S : Finset ι) {A O H : Set (Set ι)}
    (hA : MeasurableSet A) (hOdet : DeterminedBy O (↑S : Set ι))
    (hOup : IsUpperSet O) (hHup : IsUpperSet H) (hHm : MeasurableSet H)
    (hforce : O ∩ H ⊆ A) (δ : ℝ) :
    δ * (prodBernoulli w).real
        (O ∩ {ω : Set ι |
          pinnedProb w (↑S : Set ι) (fun i => i ∈ ω) A ≤ 1 - δ}) ≤
      (prodBernoulli w).real O * (prodBernoulli w).real Hᶜ := by
  have hmarkov := mul_real_inter_setOf_pinnedProb_le_le w S hA hOdet δ
  have hsub : O ∩ Aᶜ ⊆ O ∩ Hᶜ := by
    rintro ω ⟨hO, hnotA⟩
    exact ⟨hO, fun hH => hnotA (hforce ⟨hO, hH⟩)⟩
  have hmono : (prodBernoulli w).real (O ∩ Aᶜ) ≤
      (prodBernoulli w).real (O ∩ Hᶜ) :=
    measureReal_mono hsub (measure_ne_top _ _)
  exact hmarkov.trans (hmono.trans
    (prodBernoulli_harris_upper_lower w hOup hHup.compl
      hOdet.measurableSet_of_finset hHm.compl))

section Selected

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

open scoped Classical

/-- The exterior transcript selects the contact `x`. -/
def selectedAt (Dom D : Finset V) (o : V) (sel : Finset V → Finset V) (x : V) :
    Set (SiteConfig V) :=
  {ω | x ∈ sel (contacts G Dom D o ω)}

theorem determinedBy_selectedAt (Dom D : Finset V) (o : V)
    (sel : Finset V → Finset V) (x : V) :
    DeterminedBy (selectedAt G Dom D o sel x) (↑(Dom \ D) : Set V) := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [selectedAt, Set.mem_setOf_eq, contacts_congr G h]

/-- **Selected bad-window bound.**  A contact set is read outside `D`; after it is known, at most
`k` collar events are inspected.  If every one of those events has probability at most `c`, their
selected union has probability at most `k*c`.  The proof partitions by the exact contact set and
uses product factorization, so the selected list may depend arbitrarily on the exterior pattern. -/
theorem real_rich_inter_selectedBad_le
    (w : V → unitInterval) (Dom D : Finset V) (o : V) (N k : ℕ)
    (sel : Finset V → Finset V) (S : Finset V) (Bad : V → Set (SiteConfig V))
    (hSD : S ⊆ D) (hsel_sub : ∀ K, sel K ⊆ K)
    (hsel_card : ∀ K, (sel K).card ≤ k)
    (hBadDet : ∀ x ∈ outerBoundary G Dom D, DeterminedBy (Bad x) (↑S : Set V))
    {c : ℝ} (hc0 : 0 ≤ c)
    (hBad : ∀ x ∈ outerBoundary G Dom D, (prodBernoulli w).real (Bad x) ≤ c) :
    (prodBernoulli w).real
        ((poor G Dom D o N)ᶜ ∩
          ⋃ x ∈ outerBoundary G Dom D, selectedAt G Dom D o sel x ∩ Bad x) ≤
      (k : ℝ) * c := by
  classical
  let 𝒦 : Finset (Finset V) :=
    (outerBoundary G Dom D).powerset.filter fun K => N ≤ K.card
  let C : Finset V → Set (SiteConfig V) :=
    fun K => {ω | contacts G Dom D o ω = K}
  let BadK : Finset V → Set (SiteConfig V) :=
    fun K => ⋃ x ∈ sel K, Bad x
  let E : Finset V → Set (SiteConfig V) := fun K => C K ∩ BadK K
  have hEq :
      (poor G Dom D o N)ᶜ ∩
          (⋃ x ∈ outerBoundary G Dom D, selectedAt G Dom D o sel x ∩ Bad x) =
        ⋃ K ∈ 𝒦, E K := by
    ext ω
    constructor
    · rintro ⟨hrich, hω⟩
      simp only [poor, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hrich
      obtain ⟨x, hxbd, hxsel, hxbad⟩ := Set.mem_iUnion₂.1 hω
      refine Set.mem_iUnion₂.2 ⟨contacts G Dom D o ω, ?_, ?_⟩
      · exact Finset.mem_filter.2
          ⟨Finset.mem_powerset.2 (contacts_subset G Dom D o ω), hrich⟩
      · exact ⟨rfl, Set.mem_iUnion₂.2 ⟨x, hxsel, hxbad⟩⟩
    · rintro hω
      obtain ⟨K, hK, hCK, hbadK⟩ := Set.mem_iUnion₂.1 hω
      have hKsub : K ⊆ outerBoundary G Dom D :=
        Finset.mem_powerset.1 (Finset.mem_filter.1 hK).1
      have hKN : N ≤ K.card := (Finset.mem_filter.1 hK).2
      change contacts G Dom D o ω = K at hCK
      obtain ⟨x, hxsel, hxbad⟩ := Set.mem_iUnion₂.1 hbadK
      have hxK : x ∈ K := hsel_sub K hxsel
      refine ⟨?_, Set.mem_iUnion₂.2 ⟨x, hKsub hxK, ?_, hxbad⟩⟩
      · simp only [poor, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
        rw [hCK]
        exact hKN
      · change x ∈ sel (contacts G Dom D o ω)
        rw [hCK]
        exact hxsel
  have hCdet : ∀ K, DeterminedBy (C K) (↑(Dom \ D) : Set V) :=
    fun K => determinedBy_contacts_eq G Dom D o K
  have hCm : ∀ K, MeasurableSet (C K) :=
    fun K => (hCdet K).measurableSet_of_finset
  have hCdisj : (↑𝒦 : Set (Finset V)).PairwiseDisjoint C := by
    intro K _ K' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hK hK'
    exact hne (hK.symm.trans hK')
  have hKsub : ∀ K ∈ 𝒦, K ⊆ outerBoundary G Dom D := fun K hK =>
    Finset.mem_powerset.1 (Finset.mem_filter.1 hK).1
  have hBadKdet : ∀ K ∈ 𝒦, DeterminedBy (BadK K) (↑S : Set V) := by
    intro K hK
    exact DeterminedBy.iUnion fun x => DeterminedBy.iUnion fun hx =>
      hBadDet x (hKsub K hK (hsel_sub K hx))
  have hBadKm : ∀ K ∈ 𝒦, MeasurableSet (BadK K) := fun K hK =>
    (hBadKdet K hK).measurableSet_of_finset
  have hEm : ∀ K ∈ 𝒦, MeasurableSet (E K) := fun K hK =>
    (hCm K).inter (hBadKm K hK)
  rw [hEq, measureReal_biUnion_finset
    (hCdisj.mono fun K => Set.inter_subset_left) hEm (fun _ _ => measure_ne_top _ _)]
  have hterm : ∀ K ∈ 𝒦, (prodBernoulli w).real (E K) ≤
      (prodBernoulli w).real (C K) * ((k : ℝ) * c) := by
    intro K hK
    have hCcomp : DeterminedBy (C K) (↑S : Set V)ᶜ := by
      refine (hCdet K).mono fun i hi hiS => ?_
      have hi' := Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)
      exact hi'.2 (hSD (Finset.mem_coe.1 hiS))
    have hfac : (prodBernoulli w).real (E K) =
        (prodBernoulli w).real (C K) * (prodBernoulli w).real (BadK K) := by
      change (prodBernoulli w).real (C K ∩ BadK K) = _
      rw [Set.inter_comm, mul_comm]
      exact prodBernoulli_real_inter_of_determinedBy w S (hBadKdet K hK) hCcomp
        (hBadKm K hK) (hCm K)
    rw [hfac]
    refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
    calc
      (prodBernoulli w).real (BadK K) ≤
          ∑ x ∈ sel K, (prodBernoulli w).real (Bad x) := by
        exact measureReal_biUnion_finset_le (sel K) (fun x => Bad x)
      _ ≤ ∑ _x ∈ sel K, c := by
        exact Finset.sum_le_sum fun x hx => hBad x (hKsub K hK (hsel_sub K hx))
      _ = ((sel K).card : ℝ) * c := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k : ℝ) * c := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsel_card K) hc0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ K ∈ 𝒦, (prodBernoulli w).real (C K) ≤ 1 := by
    rw [← measureReal_biUnion_finset hCdisj
      (fun K _ => hCm K) (fun _ _ => measure_ne_top _ _)]
    exact measureReal_le_one
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hsum (mul_nonneg (Nat.cast_nonneg k) hc0))

end Selected

end KNAll.Site.TargetExt
