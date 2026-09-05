import KNConjectures.AvoidedPeelTools

/-!
# Avoided peeling: (S5D) with a base avoided set from the conditioned slack hierarchy

`surplusMarginY_nonneg_of_csh`: the development's `CSH.surplusMargin_nonneg_of_csh` with every avoidance set enlarged by a base
avoided set `Y` (the hierarchy is invoked with owner `k`, avoided set `Y ∪ T'`, the same decoys and observers).
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH Percolation.Literature.KNPreFKG
open scoped Classical

variable {n : ℕ}

/-- **(S5D) with avoided set `Y` from CSH.** For non-degenerate weights and observers `o ≠ v` outside `Y`, IF the conditioned slack
hierarchy holds for every owner / avoided set / decoy list with the named vertices distinct, THEN the avoided surplus margin
`surplusMarginY w Y T r D o v F` is nonnegative for every relay set `T` disjoint from `Y`, every `m^Y`-compatible injective rank, every
decoy list `D` (outside `Y`) and every monotone `F`. -/
theorem surplusMarginY_nonneg_of_csh (w : Sym2 (Fin n) → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (Y : Set (Fin n))
    (o v : Fin n) (hoY : o ∉ Y) (hvY : v ∉ Y)
    (hCSH : ∀ (x : Fin n) (Y' : Set (Fin n)) (D : List (Fin n)),
      x ∉ Y' → o ≠ x → v ≠ x → o ∉ Y' → v ∉ Y' → D.Nodup → (∀ d ∈ D, d ≠ x ∧ d ∉ Y' ∧ d ≠ o ∧ d ≠ v) →
      CSHHolds w x Y' D o v) :
    ∀ (T : Finset (Fin n)) (r : Fin n → ℕ) (D : List (Fin n)) (F : Set (Fin n) → ℝ),
      (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' → condMean w Y F a ≤ condMean w Y F a') →
      (∀ a ∈ T, a ∉ Y) → o ∉ T → v ∉ T → D.Nodup → (∀ d ∈ D, d ∉ T ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      0 ≤ surplusMarginY w Y T r D o v F := by
  -- strong induction on `|T|`
  have main : ∀ (N : ℕ) (T : Finset (Fin n)) (r : Fin n → ℕ) (D : List (Fin n)) (F : Set (Fin n) → ℝ), T.card = N →
      (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' → condMean w Y F a ≤ condMean w Y F a') →
      (∀ a ∈ T, a ∉ Y) → o ∉ T → v ∉ T → D.Nodup → (∀ d ∈ D, d ∉ T ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      0 ≤ surplusMarginY w Y T r D o v F := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro T r D F hN hF hr hcompat hTY hoT hvT hD hDT
    set μ := prodBernoulli w with hμ
    have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
    have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
    rcases T.eq_empty_or_nonempty with hT0 | hne
    · -- no relays: the surplus vanishes identically
      subst hT0
      have h0 : surplusY w Y (∅ : Finset (Fin n)) r F = fun _ => 0 := by
        funext u; simp [surplusY]
      rw [surplusMarginY, h0]
      have := slForm_zero (decoyList w (Y ∪ (↑(∅ : Finset (Fin n)) : Set (Fin n))) D)
      simp only [cshMarg]
      rw [show (fun _ : Fin n => (0 : ℝ)) = (0 : Fin n → ℝ) from rfl, this]
      simp
    -- the rank-maximal relay `k` and `T' = T.erase k`
    obtain ⟨k, hkT, hkmax⟩ := Finset.exists_max_image T r hne
    set T' : Finset (Fin n) := T.erase k with hT'
    have hTcard : T'.card < N := by
      have hpos : 0 < T.card := Finset.card_pos.2 hne
      rw [hT', Finset.card_erase_of_mem hkT]; omega
    have hT'T : ∀ a ∈ T', a ∈ T := fun a ha => Finset.mem_of_mem_erase ha
    have hkT' : k ∉ T' := Finset.notMem_erase k T
    have hlt : ∀ a ∈ T', r a < r k := by
      intro a ha
      rcases (hkmax a (hT'T a ha)).lt_or_eq with h | h
      · exact h
      · exact absurd (hr (hT'T a ha) hkT h) (Finset.ne_of_mem_erase ha)
    have hrT' : Set.InjOn r ↑T' := hr.mono (by intro a ha; exact hT'T a ha)
    have hcompatT' : ∀ a ∈ T', ∀ a' ∈ T', r a < r a' → condMean w Y F a ≤ condMean w Y F a' :=
      fun a ha a' ha' h => hcompat a (hT'T a ha) a' (hT'T a' ha') h
    have hmle : ∀ a ∈ T', condMean w Y F a ≤ condMean w Y F k :=
      fun a ha => hcompat a (hT'T a ha) k hkT (hlt a ha)
    have hkY : k ∉ Y := hTY k hkT
    have hko : o ≠ k := fun h => hoT (h ▸ hkT)
    have hkv : v ≠ k := fun h => hvT (h ▸ hkT)
    have hkD : k ∉ D := fun h => (hDT k h).1 hkT
    -- the avoided set of the peeled relay
    set A : Set (Fin n) := Y ∪ (↑T' : Set (Fin n)) with hA
    have hkA : k ∉ A := by
      rw [hA, mem_union, not_or]; exact ⟨hkY, fun h => hkT' (Finset.mem_coe.1 h)⟩
    have hoA : o ∉ A := by
      rw [hA, mem_union, not_or]; exact ⟨hoY, fun h => hoT (hT'T o (Finset.mem_coe.1 h))⟩
    have hvA : v ∉ A := by
      rw [hA, mem_union, not_or]; exact ⟨hvY, fun h => hvT (hT'T v (Finset.mem_coe.1 h))⟩
    -- the objects
    set Dk : Set (BondConfig (Fin n)) := {ω : BondConfig (Fin n) | ∀ a ∈ A, ¬ (openGraph ω).Reachable k a} with hDk
    set mk : ℝ := condMean w Y F k with hmk
    set κ : ℝ := mk * μ.real Dk - ∫ ω in Dk, F (openCluster ω k) ∂μ with hκ
    set L := decoyList w (Y ∪ (↑T : Set (Fin n))) D with hL
    set p : ℝ := obsConst w o v (Y ∪ (↑T : Set (Fin n)) ∪ {d | d ∈ D}) with hp
    set ck : Fin n → ℝ := avoidConst w k A with hck
    set Fh : Set (Sym2 (Fin n)) → ℝ := fun C => F {a | a = k ∨ ∃ e ∈ C, a ∈ e} with hFh
    set Tk : Fin n → ℝ := fun u => (∫ ω in Dk ∩ openConn k u, F (openCluster ω k) ∂μ) - μ.real (Dk ∩ openConn k u) * mk
      with hTk
    -- positivity of the conditioning events (non-degenerate weights)
    have hempty_Dk : (∅ : BondConfig (Fin n)) ∈ Dk := by
      intro a ha h
      rw [HullPort.reachable_empty_iff] at h
      exact hkA (h ▸ ha)
    have hDkpos : 0 < μ.real Dk := prodBernoulli_real_pos_of_nonempty hw ⟨∅, hempty_Dk⟩
    have hisopos : 0 < μ.real (Dk ∩ {ω | openEdgeCluster ω k = ∅}) :=
      prodBernoulli_real_pos_of_nonempty hw ⟨∅, hempty_Dk, subset_empty_iff.1 (openEdgeCluster_subset ∅ k)⟩
    -- set identities between the systems `(T; D)`, `(T'; k; D)` and `(T'; k :: D)`
    have hins : insert k A = Y ∪ (↑T : Set (Fin n)) := by
      rw [hA, hT', Finset.coe_erase, ← union_insert, insert_sdiff_singleton, insert_eq_of_mem (Finset.mem_coe.2 hkT)]
    have hset2 : A ∪ {d | d ∈ k :: D} = Y ∪ (↑T : Set (Fin n)) ∪ {d | d ∈ D} := by
      ext a
      simp only [hA, mem_union, Finset.mem_coe, hT', Finset.mem_erase, mem_setOf_eq, List.mem_cons]
      constructor
      · rintro ((ha | ⟨_, ha⟩) | rfl | ha)
        · exact Or.inl (Or.inl ha)
        · exact Or.inl (Or.inr ha)
        · exact Or.inl (Or.inr hkT)
        · exact Or.inr ha
      · rintro ((ha | ha) | ha)
        · exact Or.inl (Or.inl ha)
        · by_cases hak : a = k
          · exact Or.inr (Or.inl hak)
          · exact Or.inl (Or.inr ⟨hak, ha⟩)
        · exact Or.inr (Or.inr ha)
    have hcshMargin : ∀ f : Set (Sym2 (Fin n)) → ℝ,
        cshMargin w k A D o v f = cshMarg L p o v (covD w k A f) := by
      intro f
      rw [cshMargin, hins]
    have hnext : surplusMarginY w Y T' r (k :: D) o v F =
        cshMarg L p o v (surplusY w Y T' r F) - surplusY w Y T' r F k * cshMarg L p o v ck := by
      rw [surplusMarginY, ← hA, hset2, decoyList, hins, cshMarg_cons]
    -- (1) Lemma P: peel `k`
    have hpeel : surplusY w Y T r F = (surplusY w Y T' r F) + Tk := by
      funext u
      rw [Pi.add_apply, surplusY_erase_add w Y T r F hkT hlt u]
    -- (2) the top-relay term through `covD`
    have hTk_cov : (μ.real Dk) • Tk = covD w k A Fh - (κ * μ.real Dk) • ck := by
      funext u
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have h1 := covD_clusterFun_eq' w A F k u mk
      have h2 : μ.real (Dk ∩ openConn k u) = μ.real Dk * ck u := by
        simp only [hck, avoidConst, hDk]
        rw [mul_div_cancel₀ _ (ne_of_gt hDkpos)]
      simp only [hTk, hFh, hκ, hDk] at h1 h2 ⊢
      rw [h1, h2]
      ring
    -- (3) CSH for the peeled relay, functional `F̂`
    have hCSHk := hCSH k A D hkA hko hkv hoA hvA hD
      (fun d hd => ⟨fun h => hkD (h ▸ hd),
        by rw [hA, mem_union, not_or]; exact ⟨(hDT d hd).2.1, fun h => (hDT d hd).1 (hT'T d (Finset.mem_coe.1 h))⟩,
        (hDT d hd).2.2.1, (hDT d hd).2.2.2⟩)
    have h3 : 0 ≤ cshMarg L p o v (covD w k A Fh) := by
      rw [← hcshMargin]
      exact hCSHk Fh (monotone_clusterFun k F hF)
    -- (4) Lemma AC: `Marg[c_k] ≥ 0` from CSH applied to `Ψ_iso`
    have h4 : 0 ≤ cshMarg L p o v ck := by
      have hiso := hCSHk psiIso psiIso_mono
      rw [hcshMargin] at hiso
      have hLk : ∀ dc ∈ L, dc.1 ≠ k := fun dc hdc h => hkD (h ▸ mem_decoyList w _ D dc hdc)
      rw [cshMarg_congr L p o v (covD w k A psiIso)
        ((μ.real (Dk ∩ {ω | openEdgeCluster ω k = ∅}) * μ.real Dk) • ck) (fun u => u ≠ k) hLk hko hkv
        (fun u hu => by
          rw [covD_psiIso' w A k u hu, Pi.smul_apply, smul_eq_mul]
          simp only [hck, avoidConst, hDk]
          rw [mul_assoc, mul_div_cancel₀ _ (ne_of_gt hDkpos)]), cshMarg_smul] at hiso
      exact (mul_nonneg_iff_of_pos_left (mul_pos hisopos hDkpos)).1 hiso
    -- (5) Lemma κ
    have h5 : κ ≤ surplusY w Y T' r F k := kappaY_le_surplusY w Y T' r F k hrT' hmle
    -- (6) the next level by induction
    have h6 : 0 ≤ surplusMarginY w Y T' r (k :: D) o v F :=
      ih T'.card hTcard T' r (k :: D) F rfl hF hrT' hcompatT' (fun a ha => hTY a (hT'T a ha))
        (fun h => hoT (hT'T o h)) (fun h => hvT (hT'T v h))
        (List.nodup_cons.2 ⟨hkD, hD⟩)
        (fun d hd => by
          rcases List.mem_cons.1 hd with rfl | hd
          · exact ⟨hkT', hkY, hko.symm, hkv.symm⟩
          · exact ⟨fun h => (hDT d hd).1 (hT'T d h), (hDT d hd).2.1, (hDT d hd).2.2.1, (hDT d hd).2.2.2⟩)
    -- (7) combine: `μ(Dk) · surplusMarginY(T; D) ≥ μ(Dk) · surplusMarginY(T'; k :: D) ≥ 0`
    have hmain : μ.real Dk * surplusMarginY w Y T r D o v F =
        μ.real Dk * cshMarg L p o v (surplusY w Y T' r F) + cshMarg L p o v (covD w k A Fh) -
          κ * μ.real Dk * cshMarg L p o v ck := by
      have e1 : μ.real Dk * cshMarg L p o v Tk =
          cshMarg L p o v (covD w k A Fh) - κ * μ.real Dk * cshMarg L p o v ck := by
        rw [← cshMarg_smul, hTk_cov, cshMarg_sub, cshMarg_smul]
      rw [surplusMarginY, ← hL, ← hp, hpeel, cshMarg_add, mul_add, e1]
      ring
    have hbound : μ.real Dk * surplusMarginY w Y T' r (k :: D) o v F ≤ μ.real Dk * surplusMarginY w Y T r D o v F := by
      rw [hmain, hnext]
      have := mul_le_mul_of_nonneg_right h5 (mul_nonneg hDkpos.le h4)
      nlinarith [h3, h4, this, hDkpos.le]
    exact le_of_mul_le_mul_left (by linarith [mul_nonneg hDkpos.le h6]) hDkpos
  intro T r D F hF hr hcompat hTY hoT hvT hD hDT
  exact main T.card T r D F rfl hF hr hcompat hTY hoT hvT hD hDT

end KNAll

end
