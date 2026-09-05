import Mathlib.Combinatorics.SetFamily.FourFunctions
import Hypergraph.HyperMetaA2Defs

/-!
# META-A2 for independent hyperedges

The exposed record is a set of labels, whose product weight is log modular.
The only point at which its vertex trace fails to preserve intersections is
handled by an asymmetric allocation: for two records `a,b`, put their honest
meet trace into both inductive sources, and assign every additional overlap to
the first source.  Thus the inductive sources have exactly the desired union
and exactly the honest meet trace as intersection.  This removes the need to
pretend that vertex traces preserve label intersections.
-/

noncomputable section

namespace KNAll.Site.HyperMetaA2

open Set Percolation.Literature
open KNAll.Site KNAll.Site.AGBase KNAll.Site.CSHTwoB KNAll.Site.CSHThree
open Percolation.Literature.BHK2006
  (weight weight_nonneg weight_inter_mul_union)
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The generic two-source inequality from its one-source estimate. -/
theorem metaA2_of_star (H : Hypergraph V E) (w : E → ℝ)
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ omega : Set E, weight w omega = 1)
    (x o v : V) (A : Set V) {F : Finset V → ℝ}
    (hF0 : ∀ U' : Finset V, 0 ≤ F U')
    (hFv : ∀ U' : Finset V, v ∉ U' → F U' = 0) (U : Finset V)
    (hstar : ∀ U' ⊆ U, ∀ N : Set V, N ⊆ (U' : Set V) →
      Yw H w U' x F N * Mav H w U' A v ∅ ≤ Mav H w U' A v N * F U') :
    ∀ N N' : Set V, N ⊆ (U : Set V) → N' ⊆ (U : Set V) →
      Eav H w U A o v N * Yw H w U x F N' ≤
        Mav H w U A v (N ∪ N') * Xw H w U x A o v F (N ∩ N') := by
  induction U using Finset.strongInduction with
  | H U ih =>
    intro N N' hNU hN'U
    have hRHS : 0 ≤ Mav H w U A v (N ∪ N') *
        Xw H w U x A o v F (N ∩ N') :=
      mul_nonneg (Mav_nonneg (H := H) (w := w) hw0 hw1 U A v _)
        (Xw_nonneg (H := H) (w := w) hw0 hw1 U x A o v hF0 _)
    by_cases hvN : v ∈ A ∪ N
    · rw [Eav_eq_zero_of_mem H w U A o v hvN, zero_mul]
      exact hRHS
    have hvN0 : v ∉ N := fun h => hvN (Or.inr h)
    by_cases hxN' : x ∈ N'
    · rw [Yw_eq_zero_of_mem H w U x F hxN', mul_zero]
      exact hRHS
    by_cases hvU : v ∈ U
    swap
    · rw [Yw_eq_zero_of_not_mem H w x hFv hvU, mul_zero]
      exact hRHS

    set Z : Finset V := U.filter fun u => u ∈ N ∧ u ∈ N' with hZ
    have hZU : Z ⊆ U := Finset.filter_subset _ _
    have hmemZ : ∀ u, u ∈ Z ↔ u ∈ N ∧ u ∈ N' := fun u => by
      simp only [hZ, Finset.mem_filter, and_iff_right_iff_imp]
      exact fun h => hNU h.1
    have hxZ : x ∉ Z := fun h => hxN' ((hmemZ x).1 h).2
    have hvZ : v ∉ Z := fun h => hvN0 ((hmemZ v).1 h).1
    have hZN : (Z : Set V) ⊆ N := fun u hu => ((hmemZ u).1 hu).1
    have hZN' : (Z : Set V) ⊆ N' := fun u hu => ((hmemZ u).1 hu).2
    have hNN'Z : N ∩ N' = (Z : Set V) := Set.ext fun u => by
      rw [Finset.mem_coe, hmemZ]
      rfl

    rcases Z.eq_empty_or_nonempty with hZe | hZne
    · have hNN' : N ∩ N' = ∅ := by rw [hNN'Z, hZe, Finset.coe_empty]
      rw [hNN', Xw_empty H w hm]
      have hst := hstar U le_rfl N' hN'U
      have hcore := avoidCore H w hw0 hw1 hm U ({v} : Set V)
        ((A ∪ N') ∩ (U : Set V)) ((A ∪ N) ∩ (U : Set V))
        Set.inter_subset_right Set.inter_subset_right
        (fun _ => (1 : ℝ)) (AGBase.indMem o) monotone_const
        (AGBase.monotone_indMem o) (fun _ => zero_le_one)
        (AGBase.indMem_nonneg o)
      have hi : (A ∪ N') ∩ (U : Set V) ∩ ((A ∪ N) ∩ (U : Set V)) =
          (A ∪ ∅) ∩ (U : Set V) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_union, Set.union_empty, Finset.mem_coe]
        constructor
        · rintro ⟨⟨ha | hn', hu⟩, ha' | hn, -⟩
          · exact ⟨ha, hu⟩
          · exact ⟨ha, hu⟩
          · exact ⟨ha', hu⟩
          · exact absurd hNN' (Set.nonempty_iff_ne_empty.1 ⟨u, hn, hn'⟩)
        · rintro ⟨ha, hu⟩
          exact ⟨⟨Or.inl ha, hu⟩, Or.inl ha, hu⟩
      have hu : (A ∪ N') ∩ (U : Set V) ∪ ((A ∪ N) ∩ (U : Set V)) =
          (A ∪ (N ∪ N')) ∩ (U : Set V) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
        tauto
      simp only [one_mul, hi, hu] at hcore
      rw [← Mav_eq_inter H w U A hvU,
        ← Eav_eq_inter H w U A o hvU,
        ← Eav_eq_inter H w U A o hvU,
        ← Mav_eq_inter H w U A hvU] at hcore
      have hE := Eav_nonneg (H := H) (w := w) hw0 hw1 U A o v N
      have hB := hF0 U
      have hM := Mav_nonneg (H := H) (w := w) hw0 hw1 U A v (N ∪ N')
      have hM0 := Mav_nonneg (H := H) (w := w) hw0 hw1 U A v (∅ : Set V)
      have key : Eav H w U A o v N * Yw H w U x F N' * Mav H w U A v ∅ ≤
          Mav H w U A v (N ∪ N') * (Eav H w U A o v ∅ * F U) :=
        calc
          Eav H w U A o v N * Yw H w U x F N' * Mav H w U A v ∅ =
              Eav H w U A o v N *
                (Yw H w U x F N' * Mav H w U A v ∅) := by ring
          _ ≤ Eav H w U A o v N * (Mav H w U A v N' * F U) :=
            mul_le_mul_of_nonneg_left hst hE
          _ = (Mav H w U A v N' * Eav H w U A o v N) * F U := by ring
          _ ≤ (Eav H w U A o v ∅ * Mav H w U A v (N ∪ N')) * F U :=
            mul_le_mul_of_nonneg_right hcore hB
          _ = _ := by ring
      rcases hM0.eq_or_lt with hM0e | hM0p
      · have hE0 : Eav H w U A o v N = 0 := le_antisymm
          ((Eav_le_Mav (H := H) (w := w) hw0 hw1 U A o v N).trans
            ((Mav_antitone (H := H) (w := w) hw0 hw1 U A v
              (Set.empty_subset N)).trans hM0e.symm.le)) hE
        rw [hE0, zero_mul]
        exact mul_nonneg hM
          (mul_nonneg (qav_nonneg (H := H) (w := w) hw0 hw1 U A o v) hB)
      · unfold qav
        calc
          Eav H w U A o v N * Yw H w U x F N' =
              Eav H w U A o v N * Yw H w U x F N' * Mav H w U A v ∅ /
                Mav H w U A v ∅ := by field_simp
          _ ≤ Mav H w U A v (N ∪ N') * (Eav H w U A o v ∅ * F U) /
                Mav H w U A v ∅ := div_le_div_of_nonneg_right key hM0p.le
          _ = Mav H w U A v (N ∪ N') *
                (Eav H w U A o v ∅ / Mav H w U A v ∅ * F U) := by field_simp

    · have hss : U \ Z ⊂ U := Finset.sdiff_ssubset hZU hZne
      have hU'U : U \ Z ⊆ U := Finset.sdiff_subset
      have hZNN' : (Z : Set V) ⊆ N ∪ N' := hZN.trans Set.subset_union_left
      have eE := Eav_step H (U := U) (Z := Z) hvU hvZ (A := A) hZN w hm o
      have eY := Yw_step H (U := U) (Z := Z) hxZ hZN' w hm F
      have eM := Mav_step H (U := U) (Z := Z) hvU hvZ (A := A) hZNN' w hm
      have eX : Xw H w U x A o v F (N ∩ N') =
          ∑ omega : Set E, weight w omega *
            Xw H w (U \ Z) x A o v F (rTrace H U Z omega) := by
        rw [hNN'Z, Xw_step H hxZ (Set.Subset.rfl) w hm A o v F]
        simp only [Set.sdiff_self, Set.empty_union]

      set e : Set E → ℝ := fun eta =>
        Eav H w (U \ Z) A o v ((N \ (Z : Set V)) ∪ rTrace H U Z eta) with he
      set y : Set E → ℝ := fun eta =>
        Yw H w (U \ Z) x F ((N' \ (Z : Set V)) ∪ rTrace H U Z eta) with hy
      set m : Set E → ℝ := fun eta =>
        Mav H w (U \ Z) A v (((N ∪ N') \ (Z : Set V)) ∪ rTrace H U Z eta) with hm'
      set chi : Set E → ℝ := fun eta =>
        Xw H w (U \ Z) x A o v F (rTrace H U Z eta) with hchi
      have hE' : Eav H w U A o v N = ∑ eta : Set E, weight w eta * e eta := by
        simpa only [he] using eE
      have hY' : Yw H w U x F N' = ∑ eta : Set E, weight w eta * y eta := by
        simpa only [hy] using eY
      have hM' : Mav H w U A v (N ∪ N') =
          ∑ eta : Set E, weight w eta * m eta := by
        simpa only [hm'] using eM
      have hX' : Xw H w U x A o v F (N ∩ N') =
          ∑ eta : Set E, weight w eta * chi eta := by
        simpa only [hchi] using eX
      have he0 : ∀ eta, 0 ≤ e eta := fun eta =>
        Eav_nonneg (H := H) (w := w) hw0 hw1 _ A o v _
      have hy0 : ∀ eta, 0 ≤ y eta := fun eta =>
        Yw_nonneg (H := H) (w := w) hw0 hw1 _ x hF0 _
      have hm0 : ∀ eta, 0 ≤ m eta := fun eta =>
        Mav_nonneg (H := H) (w := w) hw0 hw1 _ A v _
      have hchi0 : ∀ eta, 0 ≤ chi eta := fun eta =>
        Xw_nonneg (H := H) (w := w) hw0 hw1 _ x A o v hF0 _
      have hstar' : ∀ U'' ⊆ U \ Z, ∀ R : Set V, R ⊆ (U'' : Set V) →
          Yw H w U'' x F R * Mav H w U'' A v ∅ ≤
            Mav H w U'' A v R * F U'' :=
        fun U'' hU'' => hstar U'' (hU''.trans hU'U)
      have IH := ih (U \ Z) hss hstar'
      rw [hE', hY', hM', hX', mul_comm (∑ eta, weight w eta * m eta)]
      refine four_functions_theorem_univ
        (fun eta => weight w eta * e eta)
        (fun eta => weight w eta * y eta)
        (fun eta => weight w eta * chi eta)
        (fun eta => weight w eta * m eta)
        (fun eta => mul_nonneg (weight_nonneg hw0 hw1 eta) (he0 eta))
        (fun eta => mul_nonneg (weight_nonneg hw0 hw1 eta) (hy0 eta))
        (fun eta => mul_nonneg (weight_nonneg hw0 hw1 eta) (hchi0 eta))
        (fun eta => mul_nonneg (weight_nonneg hw0 hw1 eta) (hm0 eta)) ?_
      intro a b
      set S' : Set V := rTrace H U Z a with hS'
      set T' : Set V := rTrace H U Z b with hT'
      set R : Set V := rTrace H U Z (a ∩ b) with hR
      set P' : Set V := (N' \ (Z : Set V)) ∪ T' with hP'
      set P : Set V := R ∪ (((N \ (Z : Set V)) ∪ S') \ P') with hP
      have hRS : R ⊆ S' := fun u hu => (rTrace_inter_subset H U Z a b hu).1
      have hRT : R ⊆ T' := fun u hu => (rTrace_inter_subset H U Z a b hu).2
      have hA0U : N \ (Z : Set V) ⊆ (U \ Z : Finset V) := by
        intro u hu
        exact Finset.mem_sdiff.2 ⟨hNU hu.1, hu.2⟩
      have hB0U : N' \ (Z : Set V) ⊆ (U \ Z : Finset V) := by
        intro u hu
        exact Finset.mem_sdiff.2 ⟨hN'U hu.1, hu.2⟩
      have hSU : S' ⊆ (U \ Z : Finset V) := rTrace_subset H U Z a
      have hTU : T' ⊆ (U \ Z : Finset V) := rTrace_subset H U Z b
      have hRU : R ⊆ (U \ Z : Finset V) := rTrace_subset H U Z (a ∩ b)
      have hP'U : P' ⊆ (U \ Z : Finset V) := Set.union_subset hB0U hTU
      have hPU : P ⊆ (U \ Z : Finset V) := by
        exact Set.union_subset hRU (Set.Subset.trans Set.sdiff_subset
          (Set.union_subset hA0U hSU))
      have hPsub : P ⊆ (N \ (Z : Set V)) ∪ S' := by
        exact Set.union_subset (hRS.trans Set.subset_union_right) Set.sdiff_subset
      have hI := IH P P' hPU hP'U
      have h1 : e a ≤ Eav H w (U \ Z) A o v P :=
        Eav_antitone (H := H) (w := w) hw0 hw1 (U \ Z) A o v hPsub
      have h2 : y b = Yw H w (U \ Z) x F P' := by rfl
      have hinter : P ∩ P' = R := by
        ext u
        constructor
        · rintro ⟨hR' | ⟨_, hnot⟩, hp'⟩
          · exact hR'
          · exact absurd hp' hnot
        · intro hu
          exact ⟨Or.inl hu, Or.inr (hRT hu)⟩
      have hunion : P ∪ P' =
          ((N ∪ N') \ (Z : Set V)) ∪ rTrace H U Z (a ∪ b) := by
        rw [rTrace_union]
        ext u
        simp only [hP, hP', hS', hT', hR, Set.mem_union, Set.mem_sdiff]
        constructor
        · rintro ((hR' | ⟨hN | hS, _⟩) | hN' | hT)
          · exact Or.inr (Or.inl (hRS hR'))
          · exact Or.inl ⟨Or.inl hN.1, hN.2⟩
          · exact Or.inr (Or.inl hS)
          · exact Or.inl ⟨Or.inr hN'.1, hN'.2⟩
          · exact Or.inr (Or.inr hT)
        · rintro (⟨hN | hN', hz⟩ | hS | hT)
          · by_cases hp' : u ∈ P'
            · exact Or.inr hp'
            · exact Or.inl (Or.inr ⟨Or.inl ⟨hN, hz⟩, hp'⟩)
          · exact Or.inr (Or.inl ⟨hN', hz⟩)
          · by_cases hp' : u ∈ P'
            · exact Or.inr hp'
            · exact Or.inl (Or.inr ⟨Or.inr hS, hp'⟩)
          · exact Or.inr (Or.inr hT)
      have h3 : e a * y b ≤ m (a ∪ b) * chi (a ∩ b) :=
        calc
          e a * y b ≤ Eav H w (U \ Z) A o v P * Yw H w (U \ Z) x F P' :=
            mul_le_mul h1 h2.le (hy0 b)
              (Eav_nonneg (H := H) (w := w) hw0 hw1 _ A o v _)
          _ ≤ Mav H w (U \ Z) A v (P ∪ P') *
                Xw H w (U \ Z) x A o v F (P ∩ P') := hI
          _ = m (a ∪ b) * chi (a ∩ b) := by rw [hunion, hinter]
      have hwab := weight_inter_mul_union w a b
      show weight w a * e a * (weight w b * y b) ≤
        weight w (a ∩ b) * chi (a ∩ b) *
          (weight w (a ∪ b) * m (a ∪ b))
      calc
        weight w a * e a * (weight w b * y b) =
            (weight w a * weight w b) * (e a * y b) := by ring
        _ ≤ (weight w (a ∩ b) * weight w (a ∪ b)) *
              (m (a ∪ b) * chi (a ∩ b)) := by
          rw [hwab]
          exact mul_le_mul_of_nonneg_left h3
            (mul_nonneg (weight_nonneg hw0 hw1 _) (weight_nonneg hw0 hw1 _))
        _ = _ := by ring

end KNAll.Site.HyperMetaA2

end

#print axioms KNAll.Site.HyperMetaA2.metaA2_of_star
