import KNConjectures.SourceGeneralCSH
import KNConjectures.PairSurplusClosure
import KNConjectures.Conjectures

/-!
# Arbitrary-source avoided surplus

This module removes the two-point restriction from the surplus argument in
`KN.PairSurplus`.  The primary source is an arbitrary vertex set `O`.  The empty and
singleton primary sources are handled separately; the guarded hierarchy is used only when
`O` is not a singleton.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {V : Type*} [Fintype V]

/-- Placement assumptions for the arbitrary-primary source-surplus hierarchy. -/
def SourceSurplusAdmissible (Y : Set V) (T : Finset V) (D : List V)
    (O : Set V) (v : V) : Prop :=
  Disjoint (↑T : Set V) Y ∧ D.Nodup ∧
    v ∉ Y ∪ (↑T : Set V) ∪ listSet D ∧
    (∀ d ∈ D, d ∉ Y ∪ (↑T : Set V) ∧ d ≠ v) ∧
    Disjoint O (insert v (Y ∪ (↑T : Set V) ∪ listSet D)) ∧
    ∀ u : V, O ≠ ({u} : Set V)

private theorem mem_guardDecoyList_fst_source (w : Sym2 V → unitInterval) :
    ∀ (A : Set V) (D : List V) (dc : Set V × (Set V → ℝ)),
      dc ∈ guardDecoyList w A D → ∃ d ∈ D, dc.1 = ({d} : Set V)
  | _, [], _, h => by simp [guardDecoyList] at h
  | A, d :: ds, dc, h => by
      simp only [guardDecoyList, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨d, List.mem_cons_self, rfl⟩
      · obtain ⟨q, hq, heq⟩ := mem_guardDecoyList_fst_source w (insert d A) ds dc h
        exact ⟨q, List.mem_cons_of_mem d hq, heq⟩

private theorem source_guardAvoidConst_margin_nonneg
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (z : V) (B : Set V) (D : List V) (O : Set V) (v : V)
    (hadm : SourceGuardAdmissible z B D O v) :
    0 ≤ cshMarg (guardDecoyList w (insert z B) D)
      (guardObsConst w O v (insert z B ∪ listSet D)) O ({v} : Set V)
      (guardAvoidConst w z B) := by
  rcases hadm with ⟨hzB, hv, hDnodup, hD, hdis, hOnot⟩
  have hmono : Monotone (nonIsolationFun (V := V)) := by
    intro K L hKL
    unfold nonIsolationFun
    by_cases hK : K.Nonempty
    · rw [if_pos hK, if_pos (hK.mono hKL)]
    · rw [if_neg hK]
      split_ifs <;> norm_num
  have hguard : 0 ≤ guardCSHMargin w z B D O v
      (nonIsolationFun (V := V)) :=
    (source_guardCSH_nondegenerate w hw z B D O v
      ⟨hzB, hv, hDnodup, hD, hdis, hOnot⟩)
      (nonIsolationFun (V := V)) hmono
  have hemptyAvoid : (∅ : BondConfig V) ∈ sourceAvoid ({z} : Set V) B := by
    intro q hq b hb hreach
    rw [mem_singleton_iff] at hq
    subst q
    rw [Percolation.Continuity.HullPort.reachable_empty_iff] at hreach
    exact hzB (hreach ▸ hb)
  have havoidPos : 0 < (prodBernoulli w).real (sourceAvoid ({z} : Set V) B) :=
    prodBernoulli_real_pos_of_nonempty hw ⟨∅, hemptyAvoid⟩
  have hemptyCluster : openCluster (∅ : BondConfig V) z = ({z} : Set V) := by
    ext q
    simp only [openCluster, mem_setOf_eq, mem_singleton_iff]
    rw [Percolation.Continuity.HullPort.reachable_empty_iff]
    exact eq_comm
  have hisoPos : 0 < isolatedAvoidMass w z B := by
    unfold isolatedAvoidMass
    exact prodBernoulli_real_pos_of_nonempty hw
      ⟨∅, hemptyAvoid, hemptyCluster⟩
  let c : ℝ := isolatedAvoidMass w z B *
    (prodBernoulli w).real (sourceAvoid ({z} : Set V) B)
  have hc : 0 < c := mul_pos hisoPos havoidPos
  let L := guardDecoyList w (insert z B) D
  let p := guardObsConst w O v (insert z B ∪ listSet D)
  let W : Set V := {v}
  have hzO : z ∉ O := by
    intro hz
    exact Set.disjoint_left.1 hdis hz (by simp)
  have hzW : z ∉ W := by
    intro hz
    have hzv : z = v := by simpa [W] using hz
    exact hv (by simp [hzv])
  have hL : ∀ dc ∈ L, z ∉ dc.1 := by
    intro dc hdc hzdc
    obtain ⟨d, hdD, hdcfst⟩ :=
      mem_guardDecoyList_fst_source w (insert z B) D dc hdc
    have hdz : d ≠ z := by
      intro hdz
      exact (hD d hdD).1 (by simp [hdz])
    rw [hdcfst] at hzdc
    exact hdz (by simpa using hzdc.symm)
  have hfun : ∀ R : Set V, z ∉ R →
      guardCovD w z B nonIsolationFun R = c * guardAvoidConst w z B R := by
    intro R hzR
    rw [guardCovD_nonIsolation w z B R hzR]
    unfold c guardAvoidConst
    rw [mul_assoc, mul_div_cancel₀ _ havoidPos.ne']
  unfold guardCSHMargin at hguard
  change 0 ≤ cshMarg L p O W (guardCovD w z B nonIsolationFun) at hguard
  have heq : cshMarg L p O W (guardCovD w z B nonIsolationFun) =
      cshMarg L p O W (c • guardAvoidConst w z B) := by
    apply CSH.cshMarg_congr L p O W _ _ (fun R : Set V => z ∉ R) hL hzO hzW
    intro R hzR
    rw [Pi.smul_apply, smul_eq_mul, hfun R hzR]
  rw [heq, CSH.cshMarg_smul] at hguard
  exact (mul_nonneg_iff_of_pos_left hc).1 hguard

private theorem source_guard_cshMarg_le_of_primary
    (w : Sym2 V → unitInterval) (A : Set V) (D : List V)
    (O : Set V) (v : V) (f g : Set V → ℝ)
    (hO : g O ≤ f O) (hsing : ∀ u : V, g ({u} : Set V) = f ({u} : Set V)) :
    cshMarg (guardDecoyList w A D) (guardObsConst w O v (A ∪ listSet D))
        O ({v} : Set V) g ≤
      cshMarg (guardDecoyList w A D) (guardObsConst w O v (A ∪ listSet D))
        O ({v} : Set V) f := by
  obtain ⟨coeff, hshape⟩ := guard_tail_shape w A D O v
  rw [hshape g, hshape f]
  have hsum : ∑ u, coeff u * g ({u} : Set V) =
      ∑ u, coeff u * f ({u} : Set V) :=
    Finset.sum_congr rfl fun u _ => by rw [hsing u]
  rw [hsum]
  linarith

/-- The guarded surplus-margin induction for an arbitrary nonsingleton primary source. -/
theorem sourceSurplusMarginY_nondegenerate
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (D : List V)
    (O : Set V) (v : V) (F : Set V → ℝ)
    (hadm : SourceSurplusAdmissible Y T D O v)
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ sourceSurplusMarginY w Y T r D O v F := by
  have main : ∀ (N : ℕ) (T : Finset V) (D : List V), T.card = N →
      SourceSurplusAdmissible Y T D O v →
      Set.InjOn r (↑T : Set V) →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        condMean w Y F a ≤ condMean w Y F a') →
      0 ≤ sourceSurplusMarginY w Y T r D O v F := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro T D hcard hadm hr hcompat
      rcases hadm with ⟨hTY, hDnodup, hv, hDaway, hOaway, hOnot⟩
      rcases T.eq_empty_or_nonempty with rfl | hTne
      · have hzero : sourceSurplusY w Y (∅ : Finset V) r F =
            (0 : Set V → ℝ) := by
          funext R
          unfold sourceSurplusY
          have hc : sourceConn R (↑(∅ : Finset V) : Set V) = ∅ := by
            ext ω
            simp [sourceConn]
          rw [hc]
          simp
        unfold sourceSurplusMarginY
        rw [hzero, CSH.cshMarg_zero]
      obtain ⟨z, hzT, hzmax⟩ := Finset.exists_max_image T r hTne
      let T' : Finset V := T.erase z
      have hT'T : ∀ a ∈ T', a ∈ T := fun a ha => Finset.mem_of_mem_erase ha
      have hzT' : z ∉ T' := Finset.notMem_erase z T
      have hT'card : T'.card < N := by
        have hpos : 0 < N := by
          rw [← hcard]
          exact Finset.card_pos.2 hTne
        dsimp [T']
        rw [Finset.card_erase_of_mem hzT, hcard]
        omega
      have hlt : ∀ a ∈ T', r a < r z := by
        intro a ha
        rcases (hzmax a (hT'T a ha)).lt_or_eq with h | h
        · exact h
        · exact absurd (hr (hT'T a ha) hzT h) (Finset.ne_of_mem_erase ha)
      have hr' : Set.InjOn r (↑T' : Set V) :=
        hr.mono (fun _ ha => hT'T _ ha)
      have hcompat' : ∀ a ∈ T', ∀ a' ∈ T', r a < r a' →
          condMean w Y F a ≤ condMean w Y F a' :=
        fun a ha a' ha' h => hcompat a (hT'T a ha) a' (hT'T a' ha') h
      have hmle : ∀ a ∈ T', condMean w Y F a ≤ condMean w Y F z :=
        fun a ha => hcompat a (hT'T a ha) z hzT (hlt a ha)
      have hzY : z ∉ Y := fun hzY =>
        Set.disjoint_left.1 hTY (show z ∈ (↑T : Set V) from hzT) hzY
      have hzv : z ≠ v := by
        intro hzv
        exact hv (Or.inl (Or.inr
          (show v ∈ (↑T : Set V) by simpa [hzv] using hzT)))
      have hzD : z ∉ D := by
        intro hzD
        exact (hDaway z hzD).1
          (Or.inr (show z ∈ (↑T : Set V) from hzT))
      let B : Set V := Y ∪ (↑T' : Set V)
      have hzB : z ∉ B := by
        change z ∉ Y ∪ (↑T' : Set V)
        rw [mem_union, not_or]
        exact ⟨hzY, fun h => hzT' h⟩
      have hinsertB : insert z B = Y ∪ (↑T : Set V) := by
        ext q
        simp only [B, mem_insert_iff, mem_union, Finset.mem_coe, T',
          Finset.mem_erase]
        constructor
        · rintro (rfl | hY | ⟨-, hT⟩)
          · exact Or.inr hzT
          · exact Or.inl hY
          · exact Or.inr hT
        · rintro (hY | hT)
          · exact Or.inr (Or.inl hY)
          · by_cases hqz : q = z
            · exact Or.inl hqz
            · exact Or.inr (Or.inr ⟨hqz, hT⟩)
      have hvB : v ∉ insert z B := by
        rw [hinsertB]
        intro hv'
        exact hv (Or.inl hv')
      have hdecB : ∀ d ∈ D, d ∉ insert z B ∧ d ≠ v := by
        intro d hd
        refine ⟨?_, (hDaway d hd).2⟩
        rw [hinsertB]
        intro hd'
        exact (hDaway d hd).1 hd'
      have hOguard : Disjoint O
          (insert z (insert v (B ∪ listSet D))) := by
        apply hOaway.mono_right
        intro q hq
        change q = z ∨ q = v ∨ q ∈ B ∨ q ∈ listSet D at hq
        change q = v ∨ (q ∈ Y ∨ q ∈ (↑T : Set V)) ∨ q ∈ listSet D
        rcases hq with hqz | hqv | hqB | hqD
        · exact Or.inr (Or.inl (Or.inr (hqz ▸ hzT)))
        · exact Or.inl hqv
        · change q ∈ Y ∪ (↑T' : Set V) at hqB
          rcases hqB with hqY | hqT'
          · exact Or.inr (Or.inl (Or.inl hqY))
          · exact Or.inr (Or.inl (Or.inr (hT'T q hqT')))
        · exact Or.inr (Or.inr hqD)
      have hadmGuard : SourceGuardAdmissible z B D O v :=
        ⟨hzB, hvB, hDnodup, hdecB, hOguard, hOnot⟩
      have hauxSub : Y ∪ (↑T' : Set V) ∪ listSet (z :: D) ⊆
          Y ∪ (↑T : Set V) ∪ listSet D := by
        intro q hq
        rcases hq with hqYT' | hqList
        · rcases hqYT' with hqY | hqT'
          · exact Or.inl (Or.inl hqY)
          · exact Or.inl (Or.inr (hT'T q hqT'))
        · change q ∈ z :: D at hqList
          rcases List.mem_cons.1 hqList with hqz | hqD
          · exact Or.inl (Or.inr (hqz ▸ hzT))
          · exact Or.inr hqD
      have hnextAdm : SourceSurplusAdmissible Y T' (z :: D) O v := by
        refine ⟨hTY.mono_left (fun _ h => hT'T _ h),
          List.nodup_cons.2 ⟨hzD, hDnodup⟩, ?_, ?_, ?_, hOnot⟩
        · exact fun hv' => hv (hauxSub hv')
        · intro d hd
          rcases List.mem_cons.1 hd with hdz | hd
          · subst d
            exact ⟨hzB, hzv⟩
          · exact ⟨fun hd' => (hDaway d hd).1
                (hd'.elim Or.inl (fun h => Or.inr (hT'T d h))),
              (hDaway d hd).2⟩
        · apply hOaway.mono_right
          intro q hq
          rcases hq with hqv | hqrest
          · exact Or.inl hqv
          · exact Or.inr (hauxSub hqrest)
      have hTrestore : insert z T' = T := Finset.insert_erase hzT
      have hobsNext : Y ∪ (↑T' : Set V) ∪ listSet (z :: D) =
          Y ∪ (↑T : Set V) ∪ listSet D := by
        apply Set.Subset.antisymm hauxSub
        intro q hq
        rcases hq with hqYT | hqD
        · rcases hqYT with hqY | hqT
          · exact Or.inl (Or.inl hqY)
          · by_cases hqz : q = z
            · refine Or.inr ?_
              change q ∈ z :: D
              exact List.mem_cons.2 (Or.inl hqz)
            · exact Or.inl (Or.inr
                (show q ∈ T' from Finset.mem_erase.2 ⟨hqz, hqT⟩))
        · refine Or.inr ?_
          change q ∈ z :: D
          exact List.mem_cons_of_mem z hqD
      let W : Set V := {v}
      let L := guardDecoyList w (Y ∪ (↑T : Set V)) D
      let p := guardObsConst w O v (Y ∪ (↑T : Set V) ∪ listSet D)
      let S := sourceSurplusY w Y T r F
      let S' := sourceSurplusY w Y T' r F
      let K := sourceTopIncrement w Y T' F z
      let Γ := guardCovD w z B (vertexClusterFun z F)
      let c := guardAvoidConst w z B
      let κ := sourceKappa w Y T' F z
      let dmass := (prodBernoulli w).real (sourceAvoid ({z} : Set V) B)
      have hempty : (∅ : BondConfig V) ∈ sourceAvoid ({z} : Set V) B := by
        intro q hq b hb hreach
        rw [mem_singleton_iff] at hq
        subst q
        rw [Percolation.Continuity.HullPort.reachable_empty_iff] at hreach
        exact hzB (hreach ▸ hb)
      have hdpos : 0 < dmass :=
        prodBernoulli_real_pos_of_nonempty hw ⟨∅, hempty⟩
      have hL : guardDecoyList w (insert z B) D = L := by rw [hinsertB]
      have hp : guardObsConst w O v (insert z B ∪ listSet D) = p := by
        rw [hinsertB]
      have hpeel :
          cshMarg L p O W (S' + K) ≤ cshMarg L p O W S := by
        apply source_guard_cshMarg_le_of_primary w
          (Y ∪ (↑T : Set V)) D O v
        · simpa [S, S', K, Pi.add_apply, hTrestore] using
            sourceSurplusY_peel_top w Y T' r F O z hzT' hlt hF
        · intro u
          simpa [S, S', K, Pi.add_apply, hTrestore] using
            (sourceSurplusY_peel_top_singleton w Y T' r F u z hzT' hlt).symm
      rw [CSH.cshMarg_add] at hpeel
      have hΓmono : Monotone (vertexClusterFun z F) := by
        intro A A' hAA'
        apply hF
        intro q hq
        rcases hq with hqz | ⟨e, he, hqe⟩
        · simp [hqz]
        · exact Or.inr ⟨e, hAA' he, hqe⟩
      have hΓnonneg : 0 ≤ cshMarg L p O W Γ := by
        have h := (source_guardCSH_nondegenerate w hw z B D O v hadmGuard)
          (vertexClusterFun z F) hΓmono
        unfold SourceGuardCSHHolds guardCSHMargin at h
        simpa [W, L, p, Γ, hL, hp] using h
      have hcNonneg : 0 ≤ cshMarg L p O W c := by
        have h := source_guardAvoidConst_margin_nonneg w hw z B D O v hadmGuard
        simpa [W, L, p, c, hL, hp] using h
      have htopFun : dmass • K = Γ - (κ * dmass) • c := by
        funext R
        rw [Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        have hid := sourceKappa_guardCovD_identity w Y T' F z R
        change dmass * K R = Γ R - κ *
          (prodBernoulli w).real (guardEv R ({z} : Set V) B) at hid
        have hmass : (prodBernoulli w).real (guardEv R ({z} : Set V) B) =
            dmass * c R := by
          unfold c guardAvoidConst dmass
          rw [mul_div_cancel₀ _ hdpos.ne']
        rw [hmass] at hid
        linarith
      have htopMarg : dmass * cshMarg L p O W K =
          cshMarg L p O W Γ - κ * dmass * cshMarg L p O W c := by
        rw [← CSH.cshMarg_smul, htopFun, CSH.cshMarg_sub,
          CSH.cshMarg_smul]
      have hrepricing : κ ≤ S' ({z} : Set V) := by
        have hid := sourceKappa_rank_identity w Y T' r F z hr' hlt
        change S' ({z} : Set V) - κ = _ at hid
        have hsum : 0 ≤ ∑ u ∈ T', (prodBernoulli w).real
            (sourceFirstPattern ({z} : Set V) Y T' r u) *
              (condMean w Y F z - condMean w Y F u) := by
          exact Finset.sum_nonneg fun u hu => mul_nonneg measureReal_nonneg
            (sub_nonneg.2 (hmle u hu))
        linarith
      have hnext : sourceSurplusMarginY w Y T' r (z :: D) O v F =
          cshMarg L p O W S' - S' ({z} : Set V) * cshMarg L p O W c := by
        unfold sourceSurplusMarginY
        change cshMarg (({z}, c) :: guardDecoyList w (insert z B) D)
            (guardObsConst w O v
              (Y ∪ (↑T' : Set V) ∪ listSet (z :: D))) O W S' = _
        rw [hL, hobsNext]
        change cshMarg (({z}, c) :: L) p O W S' = _
        rw [CSH.cshMarg_cons]
      have hnextNonneg :
          0 ≤ sourceSurplusMarginY w Y T' r (z :: D) O v F :=
        ih T'.card hT'card T' (z :: D) rfl hnextAdm hr' hcompat'
      have hrepriced :
          0 ≤ cshMarg L p O W S' - κ * cshMarg L p O W c := by
        have hmul := mul_le_mul_of_nonneg_right hrepricing hcNonneg
        rw [hnext] at hnextNonneg
        linarith
      have hlow : 0 ≤ dmass *
          (cshMarg L p O W S' + cshMarg L p O W K) := by
        have hdrep := mul_nonneg hdpos.le hrepriced
        nlinarith [htopMarg, hΓnonneg]
      have hmul := mul_le_mul_of_nonneg_left hpeel hdpos.le
      have hMT : 0 ≤ cshMarg L p O W S := by
        apply (mul_nonneg_iff_of_pos_left hdpos).1
        exact hlow.trans hmul
      simpa [sourceSurplusMarginY, W, L, p, S] using hMT
  exact main T.card T D rfl hadm hr hcompat

/-- Decoy-free surplus transfer for an arbitrary nonsingleton primary source. -/
theorem sourceSurplusTransfer_nondegenerate
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (O : Set V) (k : V)
    (F : Set V → ℝ) (hadm : SourceSurplusAdmissible Y T [] O k)
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    (prodBernoulli w).real
        (sourceAvoid ({k} : Set V) (Y ∪ (↑T : Set V))) *
          sourceSurplusY w Y T r F O ≥
      (prodBernoulli w).real
          (guardEv O ({k} : Set V) (Y ∪ (↑T : Set V))) *
        sourceSurplusY w Y T r F ({k} : Set V) := by
  have hmarg := sourceSurplusMarginY_nondegenerate w hw Y T r [] O k F
    hadm hF hr hcompat
  have hk : k ∉ Y ∪ (↑T : Set V) := by
    obtain ⟨_, _, hkfull, _, _, _⟩ := hadm
    simpa [listSet] using hkfull
  have hempty : (∅ : BondConfig V) ∈
      sourceAvoid ({k} : Set V) (Y ∪ (↑T : Set V)) := by
    intro q hq b hb hreach
    rw [mem_singleton_iff] at hq
    subst q
    rw [Percolation.Continuity.HullPort.reachable_empty_iff] at hreach
    exact hk (hreach ▸ hb)
  have hdpos : 0 < (prodBernoulli w).real
      (sourceAvoid ({k} : Set V) (Y ∪ (↑T : Set V))) :=
    prodBernoulli_real_pos_of_nonempty hw ⟨∅, hempty⟩
  unfold sourceSurplusMarginY at hmarg
  simp only [guardDecoyList, CSH.cshMarg_nil, guardObsConst, listSet,
    List.not_mem_nil, setOf_false, union_empty] at hmarg
  let d := (prodBernoulli w).real
    (sourceAvoid ({k} : Set V) (Y ∪ (↑T : Set V)))
  let j := (prodBernoulli w).real
    (guardEv O ({k} : Set V) (Y ∪ (↑T : Set V)))
  let so := sourceSurplusY w Y T r F O
  let sk := sourceSurplusY w Y T r F ({k} : Set V)
  change 0 ≤ so - j / d * sk at hmarg
  have hd : 0 < d := hdpos
  have hmul : 0 ≤ d * (so - j / d * sk) := mul_nonneg hd.le hmarg
  have heq : d * (so - j / d * sk) = d * so - j * sk := by
    field_simp
  change j * sk ≤ d * so
  linarith

/-- The top-relay conditional-BHK estimate for an arbitrary primary source. -/
theorem sourceTopRelay (w : Sym2 V → unitInterval) (Y : Set V)
    (T : Finset V) (F : Set V → ℝ) (O : Set V) (k : V)
    (hdis : Disjoint O (insert k (Y ∪ (↑T : Set V))))
    (hF : Monotone F) :
    (prodBernoulli w).real
        (sourceAvoid ({k} : Set V) (Y ∪ (↑T : Set V))) *
      (∫ ω in guardEv O ({k} : Set V) (Y ∪ (↑T : Set V)),
        (F (sourceCluster ω O) - condMean w Y F k) ∂(prodBernoulli w)) ≥
      -((prodBernoulli w).real
          (guardEv O ({k} : Set V) (Y ∪ (↑T : Set V))) *
        sourceKappa w Y T F k) := by
  let B : Set V := Y ∪ (↑T : Set V)
  let R : Set V := O
  let μ := prodBernoulli w
  let E : Set (BondConfig V) := sourceAvoid ({k} : Set V) B
  let J : Set (BondConfig V) := guardEv R ({k} : Set V) B
  by_cases hkB : k ∈ B
  · have hE : E = ∅ := by
      ext ω
      constructor
      · intro hω
        exact (hω k (by simp) k hkB (SimpleGraph.Reachable.refl k)).elim
      · simp
    have hJ : J = ∅ := by
      ext ω
      constructor
      · rintro ⟨havoid, q, hqR, k', hk', hqk⟩
        have hk'k : k' = k := by simpa using hk'
        subst k'
        exact (havoid q hqR k hkB hqk).elim
      · simp
    simp [B, R, E, J, hE, hJ]
  let q : Set (Sym2 V) → ℝ := fun K =>
    sourceKernel w Set.univ R B (insert k {u | ∃ e ∈ K, u ∈ e})
  let f : Set (Sym2 V) → ℝ := vertexClusterFun k F
  have hRB : Disjoint R (insert k B) := by simpa [R, B] using hdis
  have hfmono : Monotone f := by
    intro K K' hKK'
    apply hF
    intro u hu
    rcases hu with rfl | ⟨e, he, hue⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, hKK' he, hue⟩
  have hqmono : Monotone q := by
    intro K K' hKK'
    apply sourceKernel_mono_cluster w Set.univ R B
    · intro u hu
      rcases hu with rfl | ⟨e, he, hue⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨e, hKK' he, hue⟩
    · exact Set.subset_univ _
  have hBHK := BHK2006_clusterConditionalPositiveAssociation_holds
    V w k B f q hfmono hqmono hkB
  have hkernel : ∀ ω : BondConfig V,
      q (openEdgeCluster ω k) =
        sourceKernel w Set.univ R B (openCluster ω k) := by
    intro ω
    exact congrArg (sourceKernel w Set.univ R B)
      (CSH.openCluster_eq_insert_span ω k).symm
  have hfcluster : ∀ ω : BondConfig V,
      f (openEdgeCluster ω k) = F (openCluster ω k) := by
    intro ω
    change F (insert k {u | ∃ e ∈ openEdgeCluster ω k, u ∈ e}) =
      F (openCluster ω k)
    rw [← CSH.openCluster_eq_insert_span]
  have hiw : inducedWeight w (Set.univ : Set V) = w := by
    funext e
    simp [inducedWeight]
  have htowerQ :
      (∫ ω in E, F (openCluster ω k) *
          sourceKernel w Set.univ R B (openCluster ω k) ∂μ) =
        ∫ ω in J, F (openCluster ω k) ∂μ := by
    have hinside : insert k (R ∪ B) ⊆ (Set.univ : Set V) := Set.subset_univ _
    have h := sourceKernel_tower_mul w Set.univ R B k F hinside
    rw [hiw] at h
    simpa [E, J, μ] using h
  have htowerOne :
      (∫ ω in E, sourceKernel w Set.univ R B (openCluster ω k) ∂μ) =
        μ.real J := by
    have hinside : insert k (R ∪ B) ⊆ (Set.univ : Set V) := Set.subset_univ _
    have h := sourceKernel_tower w Set.univ R B k hinside
    simp only [sourceCluster_singleton] at h
    rw [hiw] at h
    unfold worldGuardMass worldProb at h
    simp only [Set.mem_univ, if_true, Set.inter_univ, hiw] at h
    simpa [E, J, μ] using h
  have hEraw :
      {ω : BondConfig V | ∀ x ∈ B, ¬ (openGraph ω).Reachable k x} = E := by
    ext ω
    simp [E, sourceAvoid]
  rw [hEraw] at hBHK
  simp_rw [hfcluster] at hBHK
  simp_rw [hkernel] at hBHK
  change (∫ ω in E, F (openCluster ω k) ∂μ) *
      (∫ ω in E, sourceKernel w Set.univ R B (openCluster ω k) ∂μ) ≤
    μ.real E *
      ∫ ω in E, F (openCluster ω k) *
        sourceKernel w Set.univ R B (openCluster ω k) ∂μ at hBHK
  rw [htowerOne, htowerQ] at hBHK
  have hcluster : ∫ ω in J, F (openCluster ω k) ∂μ ≤
      ∫ ω in J, F (sourceCluster ω R) ∂μ := by
    refine setIntegral_mono_on (Integrable.of_finite).integrableOn
      (Integrable.of_finite).integrableOn MeasurableSet.of_discrete ?_
    intro ω hω
    exact hF (openCluster_subset_sourceCluster_of_guard hω.2)
  have hscaled : μ.real E * (∫ ω in J, F (openCluster ω k) ∂μ) ≤
      μ.real E * ∫ ω in J, F (sourceCluster ω R) ∂μ :=
    mul_le_mul_of_nonneg_left hcluster measureReal_nonneg
  have hcore :
      (∫ ω in E, F (openCluster ω k) ∂μ) * μ.real J ≤
        μ.real E * ∫ ω in J, F (sourceCluster ω R) ∂μ :=
    hBHK.trans hscaled
  unfold sourceKappa
  change -(μ.real J *
      (condMean w Y F k * μ.real E -
        ∫ ω in E, F (openCluster ω k) ∂μ)) ≤
    μ.real E *
      ∫ ω in J, F (sourceCluster ω R) - condMean w Y F k ∂μ
  rw [integral_sub (Integrable.of_finite).integrableOn
    (Integrable.of_finite).integrableOn, setIntegral_const, smul_eq_mul]
  calc
    -(μ.real J * (condMean w Y F k * μ.real E -
        ∫ ω in E, F (openCluster ω k) ∂μ)) =
        (∫ ω in E, F (openCluster ω k) ∂μ) * μ.real J -
          condMean w Y F k * μ.real E * μ.real J := by ring
    _ ≤ μ.real E * (∫ ω in J, F (sourceCluster ω R) ∂μ) -
          condMean w Y F k * μ.real E * μ.real J :=
      sub_le_sub_right hcore _
    _ = μ.real E *
        ((∫ ω in J, F (sourceCluster ω R) ∂μ) -
          μ.real J * condMean w Y F k) := by ring

/-- Avoided first-relay surplus for a disjoint nonsingleton source at nondegenerate weights. -/
theorem sourceSurplusY_nondegenerate_nonsingleton
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (O : Set V)
    (F : Set V → ℝ)
    (hdis : Disjoint O (Y ∪ (↑T : Set V)))
    (hOnot : ∀ u : V, O ≠ ({u} : Set V))
    (hTY : Disjoint (↑T : Set V) Y) (hF : Monotone F)
    (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ sourceSurplusY w Y T r F O := by
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · unfold sourceSurplusY
    have hc : sourceConn O (↑(∅ : Finset V) : Set V) = ∅ := by
      ext ω
      simp [sourceConn]
    rw [hc]
    simp
  obtain ⟨k, hkT, hkmax⟩ := Finset.exists_max_image T r hTne
  let T₀ : Finset V := T.erase k
  let S : Set V := O
  let B : Set V := Y ∪ (↑T₀ : Set V)
  let μ := prodBernoulli w
  let E : Set (BondConfig V) := sourceAvoid ({k} : Set V) B
  let J : Set (BondConfig V) := guardEv S ({k} : Set V) B
  let I : ℝ := ∫ ω in J,
    (F (sourceCluster ω S) - condMean w Y F k) ∂μ
  let surS : ℝ := sourceSurplusY w Y T₀ r F S
  let surK : ℝ := sourceSurplusY w Y T₀ r F ({k} : Set V)
  let κ : ℝ := sourceKappa w Y T₀ F k
  have hT₀T : ∀ a ∈ T₀, a ∈ T := fun a ha => Finset.mem_of_mem_erase ha
  have hkT₀ : k ∉ T₀ := Finset.notMem_erase k T
  have hlt : ∀ a ∈ T₀, r a < r k := by
    intro a ha
    rcases (hkmax a (hT₀T a ha)).lt_or_eq with h | h
    · exact h
    · exact absurd (hr (hT₀T a ha) hkT h) (Finset.ne_of_mem_erase ha)
  have hr₀ : Set.InjOn r (↑T₀ : Set V) :=
    hr.mono (fun _ ha => hT₀T _ ha)
  have hcompat₀ : ∀ a ∈ T₀, ∀ a' ∈ T₀, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a' :=
    fun a ha a' ha' h => hcompat a (hT₀T a ha) a' (hT₀T a' ha') h
  have hmle : ∀ a ∈ T₀, condMean w Y F a ≤ condMean w Y F k :=
    fun a ha => hcompat a (hT₀T a ha) k hkT (hlt a ha)
  have hkY : k ∉ Y := by
    intro hkY
    exact Set.disjoint_left.1 hTY (show k ∈ (↑T : Set V) from hkT) hkY
  have hkB : k ∉ B := by
    intro hkB'
    rcases hkB' with hkY' | hkT₀'
    · exact hkY hkY'
    · exact hkT₀ hkT₀'
  have hTY₀ : Disjoint (↑T₀ : Set V) Y :=
    hTY.mono_left (fun _ ha => hT₀T _ ha)
  have hguard : Disjoint S (insert k B) := by
    apply hdis.mono_right
    intro q hq
    rcases hq with hqk | hqB
    · exact Or.inr (show q ∈ (↑T : Set V) by simpa [hqk] using hkT)
    · rcases hqB with hqY | hqT₀
      · exact Or.inl hqY
      · exact Or.inr (hT₀T q hqT₀)
  have hadm : SourceSurplusAdmissible Y T₀ [] S k := by
    refine ⟨hTY₀, List.nodup_nil, ?_, ?_, ?_, ?_⟩
    · simpa [listSet, B] using hkB
    · intro d hd
      simp at hd
    · simpa [S, B, listSet] using hguard
    · simpa [S] using hOnot
  have htransfer : μ.real E * surS ≥ μ.real J * surK := by
    simpa [μ, E, J, S, B, surS, surK] using
      sourceSurplusTransfer_nondegenerate w hw Y T₀ r S k F hadm hF
        hr₀ hcompat₀
  have htop : μ.real E * I ≥ -(μ.real J * κ) := by
    simpa [μ, E, J, I, κ, S, B] using
      sourceTopRelay w Y T₀ F S k hguard hF
  have hreprice : κ ≤ surK := by
    have hid := sourceKappa_rank_identity w Y T₀ r F k hr₀ hlt
    have hsum : 0 ≤ ∑ a ∈ T₀, (prodBernoulli w).real
        (sourceFirstPattern ({k} : Set V) Y T₀ r a) *
          (condMean w Y F k - condMean w Y F a) :=
      Finset.sum_nonneg fun a ha => mul_nonneg measureReal_nonneg
        (sub_nonneg.2 (hmle a ha))
    change surK - κ = _ at hid
    linarith
  have hjprice : μ.real J * κ ≤ μ.real J * surK :=
    mul_le_mul_of_nonneg_left hreprice measureReal_nonneg
  have hrestore : insert k T₀ = T := Finset.insert_erase hkT
  have hsplit : sourceSurplusY w Y T r F S = surS + I := by
    have h := sourceSurplusY_insert_add w Y T₀ r F S k hkT₀ hlt
    rw [hrestore] at h
    simpa [surS, I, J, S, B, μ] using h
  have hempty : (∅ : BondConfig V) ∈ E := by
    intro q hq b hb hreach
    rw [mem_singleton_iff] at hq
    subst q
    rw [Percolation.Continuity.HullPort.reachable_empty_iff] at hreach
    exact hkB (hreach ▸ hb)
  have hdpos : 0 < μ.real E := by
    simpa [μ] using prodBernoulli_real_pos_of_nonempty hw ⟨∅, hempty⟩
  have hmul : 0 ≤ μ.real E * (surS + I) := by
    nlinarith [htransfer, htop, hjprice]
  rw [hsplit]
  exact (mul_nonneg_iff_of_pos_left hdpos).1 hmul

private theorem sourceSurplusY_nondegenerate_disjoint
    {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set (Fin n)) (T : Finset (Fin n)) (r : Fin n → ℕ)
    (O : Set (Fin n)) (F : Set (Fin n) → ℝ)
    (hdis : Disjoint O (Y ∪ (↑T : Set (Fin n))))
    (hTY : Disjoint (↑T : Set (Fin n)) Y)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli w).real
      (sourceAvoid ({a} : Set (Fin n)) Y))
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set (Fin n)))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ sourceSurplusY w Y T r F O := by
  by_cases hOempty : O = ∅
  · subst O
    unfold sourceSurplusY sourceFirstPattern
    have hc : sourceConn (∅ : Set (Fin n)) (↑T : Set (Fin n)) = ∅ := by
      ext ω
      simp [sourceConn]
    have hca : ∀ a : Fin n,
        sourceConn (∅ : Set (Fin n)) ({a} : Set (Fin n)) = ∅ := by
      intro a
      ext ω
      simp [sourceConn]
    rw [hc]
    simp only [hca, inter_empty]
    simp
  by_cases hOsing : ∃ u : Fin n, O = ({u} : Set (Fin n))
  · obtain ⟨u, rfl⟩ := hOsing
    rw [sourceSurplusY_singleton_eq_surplusY]
    apply KNAll.genY_all w Y F hF T u r
    · intro a ha haY
      exact Set.disjoint_left.1 hTY
        (show a ∈ (↑T : Set (Fin n)) from ha) haY
    · intro a ha
      have heq :
          {ω : BondConfig (Fin n) |
            ∀ y ∈ Y, ¬ (openGraph ω).Reachable a y} =
            sourceAvoid ({a} : Set (Fin n)) Y := by
        ext ω
        simp [sourceAvoid]
      rw [heq]
      exact hact a ha
    · exact hr
    · exact hcompat
  apply sourceSurplusY_nondegenerate_nonsingleton w hw Y T r O F hdis
    (fun u h => hOsing ⟨u, h⟩) hTY hF hr hcompat

/-- Avoided first-relay surplus for every finite disjoint source and arbitrary edge weights. -/
theorem sourceSurplusY_all_disjoint {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (Y : Set (Fin n))
    (T : Finset (Fin n)) (r : Fin n → ℕ) (O : Set (Fin n))
    (F : Set (Fin n) → ℝ)
    (hdis : Disjoint O (Y ∪ (↑T : Set (Fin n))))
    (hTY : Disjoint (↑T : Set (Fin n)) Y)
    (hact : ∀ a ∈ T, 0 < (prodBernoulli w).real
      (sourceAvoid ({a} : Set (Fin n)) Y))
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set (Fin n)))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ sourceSurplusY w Y T r F O := by
  have hmin : 0 ≤ sourceMinFormY w Y T F O := by
    apply KNAll.weights_le_of_forall_pos_lt_one_at w continuousAt_const
      (continuousAt_sourceMinFormY w Y T F O hact)
    intro p hp
    obtain ⟨r', hr', hc'⟩ :=
      AGloc.exists_rank_compat T (fun a => condMean p Y F a)
    have hactp : ∀ a ∈ T, 0 < (prodBernoulli p).real
        (sourceAvoid ({a} : Set (Fin n)) Y) := by
      intro a ha
      have haY : a ∉ Y := by
        intro haY
        exact Set.disjoint_left.1 hTY
          (show a ∈ (↑T : Set (Fin n)) from ha) haY
      have hempty : (∅ : BondConfig (Fin n)) ∈
          sourceAvoid ({a} : Set (Fin n)) Y := by
        intro q hq y hy hreach
        rw [mem_singleton_iff] at hq
        subst q
        rw [Percolation.Continuity.HullPort.reachable_empty_iff] at hreach
        exact haY (hreach ▸ hy)
      exact prodBernoulli_real_pos_of_nonempty hp ⟨∅, hempty⟩
    have h := sourceSurplusY_nondegenerate_disjoint p hp Y T r' O F
      hdis hTY hactp hF hr' hc'
    rwa [sourceSurplusY_eq_sourceMinFormY p Y T r' F O hr' hc'] at h
  rw [sourceSurplusY_eq_sourceMinFormY w Y T r F O hr hcompat]
  exact hmin

#print axioms sourceSurplusMarginY_nondegenerate
#print axioms sourceSurplusTransfer_nondegenerate
#print axioms sourceTopRelay
#print axioms sourceSurplusY_nondegenerate_nonsingleton
#print axioms sourceSurplusY_all_disjoint

end KNAll.Guarded

end
