import Hypergraph.CorridorGeometry

/-!
# Packing for the greedy corridor selection

The greedy selection `sel b K` is maximal: every point of `K` is within sup-distance `2 * b`
of a selected point.  Covering `K` by the corresponding boxes gives the packing estimate

`K.card ≤ (sel b K).card * (4 * b + 1) ^ d`.

For the corridor selection, `ballRad = ℓ + 2M`.  Thus the packing constant is
`(4 * (ℓ + 2M) + 1) ^ d`, and at certificate scales it is
`(8 * faceTarget + 5) ^ d`.
-/

noncomputable section

namespace KNAll.Site.Corridor

set_option linter.unusedSectionVars false

open Set Percolation.Literature.LatticeModels
open KNAll.Site

section GreedyCover

variable {d : ℕ}

open Classical in
/-- Along the greedy fold the accumulator only grows, and every processed point is eventually
within sup-distance `2 * b` of a retained point. -/
theorem sel_foldl_cover (b : ℤ) (hb : 0 ≤ b) :
    ∀ (l : List (Site d)) (acc : Finset (Site d)),
      acc ⊆ l.foldl (fun acc x => if ∀ s ∈ acc, Far b s x then insert x acc else acc) acc ∧
      ∀ x ∈ l, ∃ s ∈ l.foldl
        (fun acc x => if ∀ s ∈ acc, Far b s x then insert x acc else acc) acc,
        ¬ Far b s x := by
  intro l
  induction l with
  | nil =>
    intro acc
    exact ⟨Finset.Subset.refl _, fun x hx => absurd hx (List.not_mem_nil)⟩
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons]
    have hself : ¬ Far b x x := by
      rintro ⟨q, hq⟩
      simp only [sub_self, abs_zero] at hq
      omega
    by_cases hfar : ∀ s ∈ acc, Far b s x
    · rw [if_pos hfar]
      obtain ⟨hmono, hcover⟩ := ih (insert x acc)
      refine ⟨(Finset.subset_insert _ _).trans hmono, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨y, hmono (Finset.mem_insert_self _ _), hself⟩
      · exact hcover y hy
    · rw [if_neg hfar]
      obtain ⟨hmono, hcover⟩ := ih acc
      refine ⟨hmono, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · push Not at hfar
        obtain ⟨s, hs, hsy⟩ := hfar
        exact ⟨s, hmono hs, hsy⟩
      · exact hcover y hy

/-- Every point of `K` fails `Far b` with some greedily selected point. -/
theorem exists_mem_sel_not_far (b : ℤ) (hb : 0 ≤ b) (K : Finset (Site d)) {x : Site d}
    (hx : x ∈ K) : ∃ s ∈ sel b K, ¬ Far b s x := by
  classical
  exact (sel_foldl_cover b hb K.toList ∅).2 x (Finset.mem_toList.2 hx)

/-- Failure of `Far b` means membership in the sup-box of radius `2 * b`. -/
theorem mem_rbox_two_mul_of_not_far {b : ℤ} {s x : Site d} (h : ¬ Far b s x) :
    x ∈ rbox s (fun _ => 2 * b) := by
  rw [mem_rbox]
  intro q
  have hq : |s q - x q| < 2 * b + 1 := not_le.1 fun hq => h ⟨q, hq⟩
  rw [abs_lt] at hq
  omega

/-- Every point of `K` lies in a sup-box of radius `2 * b` around a selected point. -/
theorem exists_mem_sel_rbox (b : ℕ) (K : Finset (Site d)) {x : Site d} (hx : x ∈ K) :
    ∃ s ∈ sel (b : ℤ) K, x ∈ rbox s (fun _ => 2 * (b : ℤ)) := by
  obtain ⟨s, hs, hfar⟩ := exists_mem_sel_not_far (b : ℤ) (by positivity) K hx
  exact ⟨s, hs, mem_rbox_two_mul_of_not_far hfar⟩

/-- Coordinate form of the greedy covering property: the sup-distance is at most `2 * b`. -/
theorem exists_mem_sel_abs_sub_le (b : ℕ) (K : Finset (Site d)) {x : Site d} (hx : x ∈ K) :
    ∃ s ∈ sel (b : ℤ) K, ∀ q, |x q - s q| ≤ 2 * (b : ℤ) := by
  obtain ⟨s, hs, hxbox⟩ := exists_mem_sel_rbox b K hx
  refine ⟨s, hs, fun q => ?_⟩
  exact abs_sub_le_of_mem_rbox hxbox q

/-- A constant-radius box in `ℤ^d` has `(2 * ρ + 1).toNat ^ d` points. -/
theorem card_rbox_const (c : Site d) (ρ : ℤ) :
    (rbox c fun _ => ρ).card = (2 * ρ + 1).toNat ^ d := by
  unfold rbox
  rw [Fintype.card_piFinset]
  have hcard : ∀ q : Fin d, (Finset.Icc (c q - ρ) (c q + ρ)).card = (2 * ρ + 1).toNat := by
    intro q
    rw [Int.card_Icc]
    congr 1
    ring
  simp only [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Greedy packing bound.**  At separation scale `b`, every selected point accounts for at
most `(4 * b + 1) ^ d` points of `K`. -/
theorem card_le_card_sel_mul (b : ℕ) (K : Finset (Site d)) :
    K.card ≤ (sel (b : ℤ) K).card * (4 * b + 1) ^ d := by
  classical
  have hsub : K ⊆ (sel (b : ℤ) K).biUnion fun s => rbox s fun _ => 2 * (b : ℤ) := by
    intro x hx
    obtain ⟨s, hs, hxbox⟩ := exists_mem_sel_rbox b K hx
    exact Finset.mem_biUnion.2 ⟨s, hs, hxbox⟩
  have hcard : ∀ s : Site d, (rbox s fun _ => 2 * (b : ℤ)).card = (4 * b + 1) ^ d := by
    intro s
    rw [card_rbox_const]
    congr 1
    omega
  calc
    K.card ≤ ((sel (b : ℤ) K).biUnion fun s => rbox s fun _ => 2 * (b : ℤ)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ s ∈ sel (b : ℤ) K, (rbox s fun _ => 2 * (b : ℤ)).card :=
      Finset.card_biUnion_le
    _ = ∑ _s ∈ sel (b : ℤ) K, (4 * b + 1) ^ d :=
      Finset.sum_congr rfl fun s _ => hcard s
    _ = (sel (b : ℤ) K).card * (4 * b + 1) ^ d := by
      rw [Finset.sum_const, smul_eq_mul]

end GreedyCover

section CorridorSelection

variable {d : ℕ} [NeZero d]

/-- The integer-valued corridor ball radius is the cast of the corresponding natural number. -/
theorem ballRad_eq_nat (Sc : Scales d) :
    ballRad Sc = ((Sc.ℓ + 2 * Sc.M : ℕ) : ℤ) := by
  unfold ballRad
  push_cast
  ring

/-- If every point of `K` is a contact, the corridor selection retains at least `k` points whenever
`K` has at least `N` points and `k * (4 * (ℓ + 2M) + 1) ^ d ≤ N`. -/
theorem le_card_selC_of_contacts (Sc : Scales d) (c : Site d) (j : ℕ)
    (K : Finset (Site d)) {k N : ℕ}
    (hcontacts : ∀ x ∈ K, IsContact c (ρD Sc j) x)
    (hpack : k * (4 * (Sc.ℓ + 2 * Sc.M) + 1) ^ d ≤ N) (hK : N ≤ K.card) :
    k ≤ (selC Sc c j K).card := by
  rw [selC_eq_of_contacts Sc c j hcontacts, ballRad_eq_nat]
  have hbound := card_le_card_sel_mul (Sc.ℓ + 2 * Sc.M) K
  have hpos : 0 < (4 * (Sc.ℓ + 2 * Sc.M) + 1) ^ d := by positivity
  exact Nat.le_of_mul_le_mul_right (hpack.trans (hK.trans hbound)) hpos

/-- Outer-boundary points are contacts, so the packing consequence applies to every sufficiently
large subset of the outer boundary. -/
theorem le_card_selC_of_subset_outerBoundary (Sc : Scales d) (c : Site d) (j : ℕ)
    (Dom K : Finset (Site d)) {k N : ℕ}
    (hsubset : K ⊆ TargetExt.outerBoundary (zdGraph d) Dom (Dbox Sc c j))
    (hpack : k * (4 * (Sc.ℓ + 2 * Sc.M) + 1) ^ d ≤ N) (hK : N ≤ K.card) :
    k ≤ (selC Sc c j K).card := by
  apply le_card_selC_of_contacts Sc c j K
  · intro x hx
    exact isContact_of_mem_outerBoundary Sc c j Dom (hsubset hx)
  · exact hpack
  · exact hK

/-- At certificate scales, `b = 1 + 2 * faceTarget`, hence `4 * b + 1 = 8 * faceTarget + 5`. -/
theorem packing_constant_scalesOf (C : LeftImp2.Certificate2 d) :
    4 * ((scalesOf C).ℓ + 2 * (scalesOf C).M) + 1 = 8 * C.faceTarget + 5 := by
  simp only [scalesOf]
  ring

/-- The downstream selection consequence at certificate scales, with the packing constant forced
by the actual definition of `Far`. -/
theorem le_card_selC_scalesOf (C : LeftImp2.Certificate2 d) (c : Site d) (j : ℕ)
    (Dom K : Finset (Site d))
    (hsubset : K ⊆ TargetExt.outerBoundary (zdGraph d) Dom (Dbox (scalesOf C) c j))
    (hpack : C.seedCount * (8 * C.faceTarget + 5) ^ d ≤ C.contacts)
    (hK : C.contacts ≤ K.card) :
    C.seedCount ≤ (selC (scalesOf C) c j K).card := by
  exact le_card_selC_of_subset_outerBoundary (scalesOf C) c j Dom K
    (k := C.seedCount) (N := C.contacts) hsubset
    (by simpa only [packing_constant_scalesOf] using hpack) hK

end CorridorSelection

/-! ## A concrete non-vacuity check in dimension two -/

/-- The greedy selection of the one-point set in `ℤ²` really has one point. -/
example : (sel (1 : ℤ) ({0} : Finset (Site 2))).card = 1 := by
  apply Nat.le_antisymm
  · simpa using Finset.card_le_card (sel_subset (d := 2) (1 : ℤ) ({0} : Finset (Site 2)))
  · have hzero : (0 : Site 2) ∈ sel (1 : ℤ) ({0} : Finset (Site 2)) := by
      obtain ⟨s, hs, -⟩ := exists_mem_sel_not_far (d := 2) (1 : ℤ) (by norm_num)
        ({0} : Finset (Site 2)) (Finset.mem_singleton_self 0)
      have hsK : s ∈ ({0} : Finset (Site 2)) := sel_subset (1 : ℤ) ({0} : Finset (Site 2)) hs
      have hs0 : s = 0 := Finset.mem_singleton.1 hsK
      simpa [hs0] using hs
    exact Finset.card_pos.2 ⟨0, hzero⟩

#print axioms KNAll.Site.Corridor.exists_mem_sel_abs_sub_le
#print axioms KNAll.Site.Corridor.card_le_card_sel_mul
#print axioms KNAll.Site.Corridor.le_card_selC_of_contacts
#print axioms KNAll.Site.Corridor.le_card_selC_of_subset_outerBoundary
#print axioms KNAll.Site.Corridor.le_card_selC_scalesOf

end KNAll.Site.Corridor

end
