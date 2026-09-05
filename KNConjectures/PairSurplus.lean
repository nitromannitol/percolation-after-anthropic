
import KNConjectures.GuardedDefs
import KNConjectures.GuardedBasic
import KNConjectures.GuardedKernel
import KNConjectures.GuardedDecoy
import KNConjectures.GuardedTwoCluster
import KNConjectures.PairGuardedCSH
set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {V : Type*} [Fintype V]

/-! ## Source-surplus peeling and transfer -/

/-- Spec item 33: singleton set-source surplus is the existing `surplusY`. -/
theorem sourceSurplusY_singleton_eq_surplusY (w : Sym2 V → unitInterval)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (u : V) :
    sourceSurplusY w Y T r F ({u} : Set V) = surplusY w Y T r F u := by
  have havoid : sourceAvoid ({u} : Set V) Y =
      { ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable u y } := by
    ext ω
    simp [sourceAvoid]
  have hconn : sourceConn ({u} : Set V) (↑T : Set V) =
      ⋃ a ∈ T, openConn u a := by
    ext ω
    simp [sourceConn, openConn]
  have hpattern : ∀ a : V, sourceFirstPattern ({u} : Set V) Y T r a =
      ({ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable u y} ∩
        (openConn u a ∩
          ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn u a')ᶜ) :
        Set (BondConfig V)) := by
    intro a
    ext ω
    simp [sourceFirstPattern, sourceAvoid, sourceConn, openConn]
  unfold sourceSurplusY surplusY
  rw [havoid, hconn]
  simp_rw [hpattern]
  simp_rw [KNAll.Guarded.sourceCluster_singleton]

/-- Exact bookkeeping identity behind items 34 and 35. -/
theorem sourceSurplusY_insert_add (w : Sym2 V → unitInterval)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ)
    (R : Set V) (z : V) (hzT : z ∉ T) (hmax : ∀ u ∈ T, r u < r z) :
    sourceSurplusY w Y (insert z T) r F R =
      sourceSurplusY w Y T r F R +
        ∫ ω in guardEv R ({z} : Set V) (Y ∪ (↑T : Set V)),
          (F (sourceCluster ω R) - condMean w Y F z) ∂(prodBernoulli w) := by
  set μ := prodBernoulli w with hμ
  set Av : Set (BondConfig V) := sourceAvoid R Y with hAv
  set UT : Set (BondConfig V) := sourceConn R (↑T : Set V) with hUT
  set Oz : Set (BondConfig V) := sourceConn R ({z} : Set V) with hOz
  set H : Set (BondConfig V) := guardEv R ({z} : Set V) (Y ∪ (↑T : Set V)) with hH
  set f : BondConfig V → ℝ := fun ω => F (sourceCluster ω R) with hf
  have hmeas : ∀ S : Set (BondConfig V), MeasurableSet S :=
    fun _ => MeasurableSet.of_discrete
  have hint : ∀ (q : BondConfig V → ℝ) (S : Set (BondConfig V)),
      IntegrableOn q S μ := fun _ _ => (Integrable.of_finite).integrableOn
  have hfilt_old : ∀ a ∈ T,
      (insert z T).filter (fun a' => r a' < r a) =
        T.filter (fun a' => r a' < r a) := by
    intro a ha
    rw [Finset.filter_insert]
    simp only [if_neg (not_lt_of_ge (Nat.le_of_lt (hmax a ha)))]
  have hfilt_z : (insert z T).filter (fun a' => r a' < r z) = T := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | ha, hlt⟩
      · exact (lt_irrefl _ hlt).elim
      · exact ha
    · intro ha
      exact ⟨Or.inr ha, hmax a ha⟩
  have hpat_old : ∀ a ∈ T,
      sourceFirstPattern R Y (insert z T) r a =
        sourceFirstPattern R Y T r a := by
    intro a ha
    unfold sourceFirstPattern
    rw [hfilt_old a ha]
  have hpat_z : sourceFirstPattern R Y (insert z T) r z = H := by
    rw [sourceFirstPattern, hfilt_z, hH]
    ext ω
    constructor
    · rintro ⟨hY, hconnz, hnoT⟩
      refine ⟨?_, hconnz⟩
      intro q hq t ht hqt
      rcases ht with ht | ht
      · exact hY q hq t ht hqt
      · exact ((mem_compl_iff _ _).1 (mem_iInter₂.1 hnoT t ht))
          ⟨q, hq, t, rfl, hqt⟩
    · rintro ⟨hA, hconnz⟩
      refine ⟨fun q hq y hy => hA q hq y (Or.inl hy), hconnz, ?_⟩
      refine mem_iInter₂.2 ?_
      intro t ht
      rw [mem_compl_iff]
      rintro ⟨q, hq, t', ht', hqt⟩
      rw [mem_singleton_iff] at ht'
      subst t'
      exact hA q hq t (Or.inr ht) hqt
  have hsum :
      ∑ a ∈ insert z T, μ.real (sourceFirstPattern R Y (insert z T) r a) *
          condMean w Y F a =
        (∑ a ∈ T, μ.real (sourceFirstPattern R Y T r a) *
          condMean w Y F a) + μ.real H * condMean w Y F z := by
    rw [Finset.sum_insert hzT, hpat_z]
    have hsumeq :
        ∑ a ∈ T, μ.real (sourceFirstPattern R Y (insert z T) r a) *
            condMean w Y F a =
          ∑ a ∈ T, μ.real (sourceFirstPattern R Y T r a) *
            condMean w Y F a := by
      exact Finset.sum_congr rfl fun a ha => by rw [hpat_old a ha]
    rw [hsumeq]
    ring
  have hcontact : sourceAvoid R Y ∩ sourceConn R (↑(insert z T) : Set V) =
      (Av ∩ UT) ∪ (Av ∩ Oz) := by
    ext ω
    constructor
    · rintro ⟨hY, ⟨q, hq, t, ht, hqt⟩⟩
      rw [Finset.mem_coe, Finset.mem_insert] at ht
      rcases ht with ht | ht
      · exact Or.inr ⟨hY, ⟨q, hq, t, by simp [ht], hqt⟩⟩
      · exact Or.inl ⟨hY, ⟨q, hq, t, ht, hqt⟩⟩
    · rintro (⟨hY, ⟨q, hq, t, ht, hqt⟩⟩ | ⟨hY, ⟨q, hq, t, ht, hqt⟩⟩)
      · exact ⟨hY, ⟨q, hq, t, Finset.mem_insert_of_mem ht, hqt⟩⟩
      · have htz : t = z := mem_singleton_iff.1 ht
        exact ⟨hY, ⟨q, hq, t, Finset.mem_insert.2 (Or.inl htz), hqt⟩⟩
  have hdiff : ((Av ∩ UT) ∪ (Av ∩ Oz)) \ (Av ∩ UT) = H := by
    rw [hH]
    ext ω
    constructor
    · rintro ⟨hold | hz, hnot⟩
      · exact (hnot hold).elim
      · refine ⟨?_, hz.2⟩
        intro q hq t ht hqt
        rcases ht with ht | ht
        · exact hz.1 q hq t ht hqt
        · exact hnot ⟨hz.1, ⟨q, hq, t, ht, hqt⟩⟩
    · rintro ⟨hA, hconnz⟩
      have hY : ω ∈ Av := by
        intro q hq y hy
        exact hA q hq y (Or.inl hy)
      refine ⟨Or.inr ⟨hY, hconnz⟩, ?_⟩
      rintro ⟨-, ⟨q, hq, t, ht, hqt⟩⟩
      exact hA q hq t (Or.inr ht) hqt
  have hsplit :
      ∫ ω in (Av ∩ UT) ∪ (Av ∩ Oz), f ω ∂μ =
        (∫ ω in Av ∩ UT, f ω ∂μ) + ∫ ω in H, f ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas (Av ∩ UT)) (hint f _),
      inter_eq_right.2 subset_union_left, hdiff]
  unfold sourceSurplusY
  rw [← hμ, hsum, hcontact, hsplit]
  rw [integral_sub (hint _ _) (hint _ _), setIntegral_const, smul_eq_mul]
  ring

/-- Spec item 34: peeling a rank-maximal relay is one-sided at a set source. -/
theorem sourceSurplusY_peel_top (w : Sym2 V → unitInterval) (Y : Set V)
    (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (R : Set V) (z : V)
    (hzT : z ∉ T) (hmax : ∀ u ∈ T, r u < r z)
    (hF : Monotone F) :
    sourceSurplusY w Y (insert z T) r F R ≥
      sourceSurplusY w Y T r F R + sourceTopIncrement w Y T F z R := by
  rw [sourceSurplusY_insert_add w Y T r F R z hzT hmax]
  unfold sourceTopIncrement
  have hle : (∫ ω in guardEv R ({z} : Set V) (Y ∪ (↑T : Set V)),
      F (openCluster ω z) - condMean w Y F z ∂(prodBernoulli w)) ≤
      ∫ ω in guardEv R ({z} : Set V) (Y ∪ (↑T : Set V)),
        F (sourceCluster ω R) - condMean w Y F z ∂(prodBernoulli w) := by
    refine setIntegral_mono_on (Integrable.of_finite).integrableOn
      (Integrable.of_finite).integrableOn MeasurableSet.of_discrete ?_
    intro ω hω
    exact sub_le_sub_right
      (hF (KNAll.Guarded.openCluster_subset_sourceCluster_of_guard hω.2)) _
  simpa [add_comm] using add_le_add_left hle (sourceSurplusY w Y T r F R)

/-- Spec item 35: the same peel is exact at singleton evaluations. -/
theorem sourceSurplusY_peel_top_singleton (w : Sym2 V → unitInterval)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ)
    (u z : V) (hzT : z ∉ T) (hmax : ∀ a ∈ T, r a < r z) :
    sourceSurplusY w Y (insert z T) r F ({u} : Set V) =
      sourceSurplusY w Y T r F ({u} : Set V) +
        sourceTopIncrement w Y T F z ({u} : Set V) := by
  rw [sourceSurplusY_insert_add w Y T r F ({u} : Set V) z hzT hmax]
  unfold sourceTopIncrement
  rw [add_right_inj]
  refine setIntegral_congr_fun MeasurableSet.of_discrete ?_
  intro ω hω
  change F (sourceCluster ω ({u} : Set V)) - condMean w Y F z =
    F (openCluster ω z) - condMean w Y F z
  rw [KNAll.Guarded.sourceCluster_eq_openCluster_of_singleton_guard u z hω.2]

/-- Spec item 36: covariance/`kappa` identity for the top increment. -/
theorem sourceKappa_guardCovD_identity (w : Sym2 V → unitInterval)
    (Y : Set V) (T : Finset V) (F : Set V → ℝ) (z : V) (R : Set V) :
    (prodBernoulli w).real
        (sourceAvoid ({z} : Set V) (Y ∪ (↑T : Set V))) *
          sourceTopIncrement w Y T F z R =
      guardCovD w z (Y ∪ (↑T : Set V)) (vertexClusterFun z F) R -
        sourceKappa w Y T F z *
          (prodBernoulli w).real
            (guardEv R ({z} : Set V) (Y ∪ (↑T : Set V))) := by
  unfold sourceTopIncrement sourceKappa guardCovD vertexClusterFun
  simp_rw [← CSH.openCluster_eq_insert_span]
  rw [integral_sub (Integrable.of_finite).integrableOn
    (Integrable.of_finite).integrableOn, setIntegral_const, smul_eq_mul]
  ring

/-- Spec item 37: the non-isolation covariance represents the guarded profile. -/
theorem guardCovD_nonIsolation (w : Sym2 V → unitInterval) (z : V)
    (B R : Set V) (hzR : z ∉ R) :
    guardCovD w z B nonIsolationFun R =
      isolatedAvoidMass w z B * (prodBernoulli w).real
        (guardEv R ({z} : Set V) B) := by
  set μ := prodBernoulli w with hμ
  set D : Set (BondConfig V) := sourceAvoid ({z} : Set V) B with hD
  set H : Set (BondConfig V) := guardEv R ({z} : Set V) B with hH
  set I : Set (BondConfig V) := {ω | openEdgeCluster ω z = ∅} with hI
  have hmeas : ∀ S : Set (BondConfig V), MeasurableSet S :=
    fun _ => MeasurableSet.of_discrete
  have hint : ∀ (q : BondConfig V → ℝ) (S : Set (BondConfig V)),
      IntegrableOn q S μ := fun _ _ => (Integrable.of_finite).integrableOn
  have hni : ∀ K : Set (Sym2 V), nonIsolationFun K = CSH.psiIso K := by
    intro K
    unfold nonIsolationFun CSH.psiIso
    by_cases hK : K.Nonempty
    · rw [if_pos hK, if_neg (Set.nonempty_iff_ne_empty.1 hK)]
    · rw [if_neg hK, if_pos (not_nonempty_iff_eq_empty.1 hK)]
  have hHval : ∀ ω ∈ H, nonIsolationFun (openEdgeCluster ω z) = 1 := by
    intro ω hω
    obtain ⟨q, hq, z', hz', hqz⟩ := hω.2
    rw [mem_singleton_iff] at hz'
    subst z'
    rw [hni]
    exact CSH.psiIso_eq_one_of_reachable (fun h => hzR (h.symm ▸ hq)) hqz.symm
  have hHint : ∫ ω in H, nonIsolationFun (openEdgeCluster ω z) ∂μ = μ.real H := by
    rw [setIntegral_congr_fun (hmeas H) hHval, setIntegral_const, smul_eq_mul,
      mul_one]
  have hcluster_iff : I = {ω : BondConfig V | openCluster ω z = ({z} : Set V)} := by
    ext ω
    constructor
    · intro hω
      change openEdgeCluster ω z = ∅ at hω
      change openCluster ω z = ({z} : Set V)
      rw [CSH.openCluster_eq_insert_span, hω]
      simp
    · intro hω
      change openCluster ω z = ({z} : Set V) at hω
      change openEdgeCluster ω z = ∅
      apply Set.eq_empty_iff_forall_notMem.2
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
          have haR := he.2.2 a (Sym2.mem_mk_left a b)
          have hbR := he.2.2 b (Sym2.mem_mk_right a b)
          have ha : a = z := by
            have : a ∈ openCluster ω z := haR
            rw [hω] at this
            simpa using this
          have hb : b = z := by
            have : b ∈ openCluster ω z := hbR
            rw [hω] at this
            simpa using this
          exact he.2.1 (Sym2.mk_isDiag_iff.2 (ha.trans hb.symm))
  have hDint : ∫ ω in D, nonIsolationFun (openEdgeCluster ω z) ∂μ =
      μ.real D - μ.real (D ∩ I) := by
    have hsplit := (integral_inter_add_sdiff (hmeas I)
      (hint (fun ω => nonIsolationFun (openEdgeCluster ω z)) D)).symm
    rw [hsplit]
    have hzero : ∫ ω in D ∩ I, nonIsolationFun (openEdgeCluster ω z) ∂μ = 0 := by
      refine (setIntegral_congr_fun (hmeas _) (g := fun _ => (0 : ℝ)) ?_).trans (by simp)
      intro ω hω
      change nonIsolationFun (openEdgeCluster ω z) = 0
      unfold nonIsolationFun
      rw [if_neg]
      exact not_nonempty_iff_eq_empty.2 (by simpa [hI] using hω.2)
    have hone : ∫ ω in D \ I, nonIsolationFun (openEdgeCluster ω z) ∂μ =
        μ.real (D \ I) := by
      rw [setIntegral_congr_fun (hmeas _) (fun ω hω => by
        unfold nonIsolationFun
        rw [if_pos]
        exact Set.nonempty_iff_ne_empty.2 (by simpa [hI] using hω.2)),
        setIntegral_const, smul_eq_mul, mul_one]
    rw [hzero, hone, zero_add]
    have hm := measureReal_inter_add_sdiff (h := measure_ne_top μ D) (hmeas I)
    linarith
  unfold guardCovD isolatedAvoidMass
  rw [← hμ, ← hD, ← hH, hHint, hDint, ← hcluster_iff]
  ring

private theorem mem_guardDecoyList_fst (w : Sym2 V → unitInterval) :
    ∀ (A : Set V) (D : List V) (dc : Set V × (Set V → ℝ)),
      dc ∈ guardDecoyList w A D → ∃ d ∈ D, dc.1 = ({d} : Set V)
  | _, [], _, h => by simp [guardDecoyList] at h
  | A, d :: ds, dc, h => by
      simp only [guardDecoyList, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨d, List.mem_cons_self, rfl⟩
      · obtain ⟨q, hq, heq⟩ := mem_guardDecoyList_fst w (insert d A) ds dc h
        exact ⟨q, List.mem_cons_of_mem d hq, heq⟩

/-- The placement part of `PairGuardAdmissible`, without requiring distinct primary
endpoints.  Equal endpoints reduce to the ordinary conditioned slack hierarchy. -/
private def PairGuardAdmissibleWeak (x : V) (Y : Set V) (D : List V)
    (s₁ s₂ v : V) : Prop :=
  x ∉ Y ∧ v ∉ insert x Y ∧ D.Nodup ∧
    (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ v) ∧
    Disjoint ({s₁, s₂} : Set V) (insert x (insert v (Y ∪ listSet D)))

private theorem pair_guardCSH_nondegenerate_weak
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (x : V) (Y : Set V) (D : List V) (s₁ s₂ v : V)
    (hadm : PairGuardAdmissibleWeak x Y D s₁ s₂ v) :
    PairGuardCSHHolds w x Y D s₁ s₂ v := by
  rcases hadm with ⟨hxY, hv, hDnodup, hD, hdis⟩
  by_cases hsne : s₁ ≠ s₂
  · exact KNAll.Guarded.pair_guardCSH_nondegenerate w hw x Y D s₁ s₂ v
      ⟨hsne, hxY, hv, hDnodup, hD, hdis⟩
  · have hs : s₁ = s₂ := not_ne_iff.mp hsne
    subst s₂
    intro g hg
    rw [KNAll.Guarded.guardCSHMargin_pair_self_eq_cshMargin]
    have hsfull : s₁ ∉ insert x (insert v (Y ∪ listSet D)) := by
      intro hs
      exact Set.disjoint_left.1 hdis (by simp) hs
    have hs : s₁ ∉ insert x Y := by
      intro hsxy
      apply hsfull
      rcases hsxy with rfl | hsY
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl hsY))
    have hsv : s₁ ≠ v := by
      intro hsv
      apply hsfull
      exact Or.inr (Or.inl hsv)
    have hD' : ∀ d ∈ D, d ∉ insert x Y ∧ d ≠ s₁ ∧ d ≠ v := by
      intro d hd
      refine ⟨(hD d hd).1, ?_, (hD d hd).2⟩
      intro hds
      apply hsfull
      exact Or.inr (Or.inr (Or.inr
        (show s₁ ∈ listSet D by simpa [listSet, hds] using hd)))
    exact CSH.cshHolds w hw x Y D s₁ v hxY hs hv hsv hDnodup hD' g hg

private theorem guardAvoidConst_margin_nonneg_weak (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (z : V) (B : Set V) (D : List V)
    (s₁ s₂ v : V) (hadm : PairGuardAdmissibleWeak z B D s₁ s₂ v) :
    0 ≤ cshMarg (guardDecoyList w (insert z B) D)
      (guardObsConst w ({s₁, s₂} : Set V) v (insert z B ∪ listSet D))
      ({s₁, s₂} : Set V) ({v} : Set V) (guardAvoidConst w z B) := by
  rcases hadm with ⟨hzB, hv, hDnodup, hD, hdis⟩
  have hadm' : PairGuardAdmissibleWeak z B D s₁ s₂ v :=
    ⟨hzB, hv, hDnodup, hD, hdis⟩
  have hmono : Monotone (nonIsolationFun (V := V)) := by
    intro K L hKL
    unfold nonIsolationFun
    by_cases hK : K.Nonempty
    · rw [if_pos hK, if_pos (hK.mono hKL)]
    · rw [if_neg hK]
      split_ifs <;> norm_num
  have hguard : 0 ≤ guardCSHMargin w z B D ({s₁, s₂} : Set V) v
      (nonIsolationFun (V := V)) :=
    (pair_guardCSH_nondegenerate_weak w hw z B D s₁ s₂ v hadm')
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
  let p := guardObsConst w ({s₁, s₂} : Set V) v (insert z B ∪ listSet D)
  let O : Set V := {s₁, s₂}
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
    obtain ⟨d, hdD, hdcfst⟩ := mem_guardDecoyList_fst w (insert z B) D dc hdc
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

/-- Spec item 38: the margin of a guarded avoidance profile is nonnegative. -/
theorem guardAvoidConst_margin_nonneg (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (z : V) (B : Set V) (D : List V)
    (s₁ s₂ v : V) (hadm : PairGuardAdmissible z B D s₁ s₂ v) :
    0 ≤ cshMarg (guardDecoyList w (insert z B) D)
      (guardObsConst w ({s₁, s₂} : Set V) v (insert z B ∪ listSet D))
      ({s₁, s₂} : Set V) ({v} : Set V) (guardAvoidConst w z B) := by
  rcases hadm with ⟨_, hzB, hv, hDnodup, hD, hdis⟩
  exact guardAvoidConst_margin_nonneg_weak w hw z B D s₁ s₂ v
    ⟨hzB, hv, hDnodup, hD, hdis⟩

/-! The following three finite-partition helpers are also used by the closure layer. -/

theorem sourceFirstPattern_disjoint (R Y : Set V) (T : Finset V)
    (r : V → ℕ) (hr : Set.InjOn r (↑T : Set V)) :
    Set.PairwiseDisjoint (↑T : Set V) (fun a => sourceFirstPattern R Y T r a) := by
  intro a ha b hb hab
  rw [Function.onFun, Set.disjoint_left]
  intro ω hωa hωb
  rcases lt_or_gt_of_ne (fun h => hab (hr ha hb h)) with hlt | hlt
  · have hna : ω ∈ (sourceConn R ({a} : Set V))ᶜ := by
      exact mem_iInter₂.1 hωb.2.2 a (Finset.mem_filter.2 ⟨ha, hlt⟩)
    exact hna hωa.2.1
  · have hnb : ω ∈ (sourceConn R ({b} : Set V))ᶜ := by
      exact mem_iInter₂.1 hωa.2.2 b (Finset.mem_filter.2 ⟨hb, hlt⟩)
    exact hnb hωb.2.1

theorem sourceFirstPattern_cover (R Y : Set V) (T : Finset V) (r : V → ℕ) :
    (⋃ a ∈ T, sourceFirstPattern R Y T r a) =
      sourceAvoid R Y ∩ sourceConn R (↑T : Set V) := by
  ext ω
  simp only [mem_iUnion, exists_prop, mem_inter_iff]
  constructor
  · rintro ⟨a, ha, hpat⟩
    obtain ⟨q, hq, a', ha', hqa⟩ := hpat.2.1
    rw [mem_singleton_iff] at ha'
    subst a'
    exact ⟨hpat.1, ⟨q, hq, a, ha, hqa⟩⟩
  · rintro ⟨havoid, hcontact⟩
    classical
    let Q : Finset V := T.filter fun a => ω ∈ sourceConn R ({a} : Set V)
    have hQ : Q.Nonempty := by
      obtain ⟨q, hq, a, ha, hqa⟩ := hcontact
      exact ⟨a, Finset.mem_filter.2 ⟨ha, ⟨q, hq, a, rfl, hqa⟩⟩⟩
    obtain ⟨a, haQ, hmin⟩ := Finset.exists_min_image Q r hQ
    have ha := Finset.mem_filter.1 haQ
    refine ⟨a, ha.1, havoid, ha.2, ?_⟩
    refine mem_iInter₂.2 ?_
    intro a' ha'
    rw [mem_compl_iff]
    intro ha'conn
    have ha'Q : a' ∈ Q := Finset.mem_filter.2
      ⟨(Finset.mem_filter.1 ha').1, ha'conn⟩
    exact (not_lt_of_ge (hmin a' ha'Q)) (Finset.mem_filter.1 ha').2

theorem sum_measureReal_sourceFirstPattern (w : Sym2 V → unitInterval)
    (R Y : Set V) (T : Finset V) (r : V → ℕ)
    (hr : Set.InjOn r (↑T : Set V)) :
    ∑ a ∈ T, (prodBernoulli w).real (sourceFirstPattern R Y T r a) =
      (prodBernoulli w).real (sourceAvoid R Y ∩ sourceConn R (↑T : Set V)) := by
  rw [← sourceFirstPattern_cover R Y T r,
    measureReal_biUnion_finset (sourceFirstPattern_disjoint R Y T r hr)
      (fun _ _ => MeasurableSet.of_discrete) (fun _ _ => measure_ne_top _ _)]

theorem setIntegral_eq_condMean_mul_sourceAvoid (w : Sym2 V → unitInterval)
    (Y : Set V) (F : Set V → ℝ) (a : V) :
    ∫ ω in sourceAvoid ({a} : Set V) Y, F (openCluster ω a) ∂(prodBernoulli w) =
      condMean w Y F a *
        (prodBernoulli w).real (sourceAvoid ({a} : Set V) Y) := by
  have hset : sourceAvoid ({a} : Set V) Y =
      {ω : BondConfig V | ∀ y ∈ Y, ¬(openGraph ω).Reachable a y} := by
    ext ω
    simp [sourceAvoid]
  rw [hset]
  unfold condMean
  by_cases hzero : (prodBernoulli w).real
      {ω : BondConfig V | ∀ y ∈ Y, ¬(openGraph ω).Reachable a y} = 0
  · rw [hzero, mul_zero]
    have hmzero : (prodBernoulli w)
        {ω : BondConfig V | ∀ y ∈ Y, ¬(openGraph ω).Reachable a y} = 0 := by
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff,
        or_iff_left (measure_ne_top _ _)] at hzero
    rw [Measure.restrict_eq_zero.2 hmzero, integral_zero_measure]
  · rw [div_mul_cancel₀ _ hzero]

/-- Spec item 39: exact rank repricing at a maximal relay. -/
theorem sourceKappa_rank_identity (w : Sym2 V → unitInterval) (Y : Set V)
    (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (z : V)
    (hr : Set.InjOn r (↑T : Set V))
    (hmax : ∀ u ∈ T, r u < r z) :
    sourceSurplusY w Y T r F ({z} : Set V) - sourceKappa w Y T F z =
      ∑ u ∈ T, (prodBernoulli w).real
          (sourceFirstPattern ({z} : Set V) Y T r u) *
        (condMean w Y F z - condMean w Y F u) := by
  set μ := prodBernoulli w with hμ
  set Av : Set (BondConfig V) := sourceAvoid ({z} : Set V) Y with hAv
  set W : Set (BondConfig V) := sourceConn ({z} : Set V) (↑T : Set V) with hW
  set D : Set (BondConfig V) :=
    sourceAvoid ({z} : Set V) (Y ∪ (↑T : Set V)) with hD
  set f : BondConfig V → ℝ := fun ω => F (openCluster ω z) with hf
  set m : V → ℝ := fun u => condMean w Y F u with hm
  have hmeas : ∀ S : Set (BondConfig V), MeasurableSet S :=
    fun _ => MeasurableSet.of_discrete
  have hint : ∀ (q : BondConfig V → ℝ) (S : Set (BondConfig V)),
      IntegrableOn q S μ := fun _ _ => (Integrable.of_finite).integrableOn
  have hDW : D = Av \ W := by
    ext ω
    constructor
    · intro hω
      refine ⟨?_, ?_⟩
      · intro q hq y hy
        exact hω q hq y (Or.inl hy)
      · rintro ⟨q, hq, t, ht, hqt⟩
        exact hω q hq t (Or.inr ht) hqt
    · rintro ⟨hY, hnoT⟩
      intro q hq t ht hqt
      rcases ht with ht | ht
      · exact hY q hq t ht hqt
      · exact hnoT ⟨q, hq, t, ht, hqt⟩
  have hAint : ∫ ω in Av, f ω ∂μ =
      (∫ ω in Av ∩ W, f ω ∂μ) + ∫ ω in D, f ω ∂μ := by
    rw [hDW]
    exact (integral_inter_add_sdiff (hmeas W) (hint f Av)).symm
  have hAmeasure : μ.real Av = μ.real (Av ∩ W) + μ.real D := by
    rw [hDW]
    exact (measureReal_inter_add_sdiff (s := Av) (h := measure_ne_top _ _)
      (hmeas W)).symm
  have hmA : ∫ ω in Av, f ω ∂μ = m z * μ.real Av := by
    simpa [hAv, hf, hm, hμ] using
      setIntegral_eq_condMean_mul_sourceAvoid w Y F z
  have hpatMeasure :
      ∑ u ∈ T, μ.real (sourceFirstPattern ({z} : Set V) Y T r u) =
        μ.real (Av ∩ W) := by
    simpa [hAv, hW, hμ] using
      sum_measureReal_sourceFirstPattern w ({z} : Set V) Y T r hr
  have hrhs :
      ∑ u ∈ T, μ.real (sourceFirstPattern ({z} : Set V) Y T r u) *
          (m z - m u) =
        m z * μ.real (Av ∩ W) -
          ∑ u ∈ T, μ.real (sourceFirstPattern ({z} : Set V) Y T r u) *
            m u := by
    calc
      _ = (∑ u ∈ T, μ.real (sourceFirstPattern ({z} : Set V) Y T r u) * m z) -
          ∑ u ∈ T, μ.real (sourceFirstPattern ({z} : Set V) Y T r u) * m u := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun u hu => by ring
      _ = _ := by rw [← Finset.sum_mul, hpatMeasure]; ring
  unfold sourceSurplusY sourceKappa
  simp_rw [KNAll.Guarded.sourceCluster_singleton]
  change (∫ ω in Av ∩ W, f ω ∂μ) -
      (∑ u ∈ T, μ.real (sourceFirstPattern ({z} : Set V) Y T r u) * m u) -
        (m z * μ.real D - ∫ ω in D, f ω ∂μ) =
    ∑ u ∈ T, μ.real (sourceFirstPattern ({z} : Set V) Y T r u) *
      (m z - m u)
  rw [hrhs]
  have hbalance :
      (∫ ω in Av ∩ W, f ω ∂μ) + ∫ ω in D, f ω ∂μ =
        m z * μ.real (Av ∩ W) + m z * μ.real D := by
    calc
      _ = ∫ ω in Av, f ω ∂μ := hAint.symm
      _ = m z * μ.real Av := hmA
      _ = m z * (μ.real (Av ∩ W) + μ.real D) := by rw [hAmeasure]
      _ = _ := by ring
  linarith [hbalance]

private theorem guard_cshMarg_le_of_primary
    (w : Sym2 V → unitInterval) (A : Set V) (D : List V)
    (O : Set V) (v : V) (f g : Set V → ℝ)
    (hO : g O ≤ f O) (hsing : ∀ u : V, g ({u} : Set V) = f ({u} : Set V)) :
    cshMarg (guardDecoyList w A D) (guardObsConst w O v (A ∪ listSet D))
        O ({v} : Set V) g ≤
      cshMarg (guardDecoyList w A D) (guardObsConst w O v (A ∪ listSet D))
        O ({v} : Set V) f := by
  obtain ⟨coeff, hshape⟩ := KNAll.Guarded.guard_tail_shape w A D O v
  rw [hshape g, hshape f]
  have hsum : ∑ u, coeff u * g ({u} : Set V) =
      ∑ u, coeff u * f ({u} : Set V) := by
    exact Finset.sum_congr rfl fun u _ => by rw [hsing u]
  rw [hsum]
  linarith

/-- The placement part of `PairSurplusAdmissible`, allowing coincident source endpoints. -/
private def PairSurplusAdmissibleWeak (Y : Set V) (T : Finset V) (D : List V)
    (s₁ s₂ v : V) : Prop :=
  Disjoint (↑T : Set V) Y ∧ D.Nodup ∧
    v ∉ Y ∪ (↑T : Set V) ∪ listSet D ∧
    (∀ d ∈ D, d ∉ Y ∪ (↑T : Set V) ∧ d ≠ v) ∧
    Disjoint ({s₁, s₂} : Set V)
      (insert v (Y ∪ (↑T : Set V) ∪ listSet D))

private theorem pairSource_surplusMarginY_nondegenerate_weak
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (D : List V)
    (s₁ s₂ v : V) (F : Set V → ℝ)
    (hadm : PairSurplusAdmissibleWeak Y T D s₁ s₂ v)
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ sourceSurplusMarginY w Y T r D ({s₁, s₂} : Set V) v F := by
  have main : ∀ (N : ℕ) (T : Finset V) (D : List V), T.card = N →
      PairSurplusAdmissibleWeak Y T D s₁ s₂ v →
      Set.InjOn r (↑T : Set V) →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        condMean w Y F a ≤ condMean w Y F a') →
      0 ≤ sourceSurplusMarginY w Y T r D ({s₁, s₂} : Set V) v F := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro T D hcard hadm hr hcompat
      rcases hadm with ⟨hTY, hDnodup, hv, hDaway, hSaway⟩
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
        exact hv (Or.inl (Or.inr (show v ∈ (↑T : Set V) by simpa [hzv] using hzT)))
      have hzD : z ∉ D := by
        intro hzD
        exact (hDaway z hzD).1 (Or.inr (show z ∈ (↑T : Set V) from hzT))
      let B : Set V := Y ∪ (↑T' : Set V)
      have hzB : z ∉ B := by
        change z ∉ Y ∪ (↑T' : Set V)
        rw [mem_union, not_or]
        exact ⟨hzY, fun h => hzT' h⟩
      have hinsertB : insert z B = Y ∪ (↑T : Set V) := by
        ext q
        simp only [B, mem_insert_iff, mem_union, Finset.mem_coe, T', Finset.mem_erase]
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
      have hSguard : Disjoint ({s₁, s₂} : Set V)
          (insert z (insert v (B ∪ listSet D))) := by
        apply hSaway.mono_right
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
      have hadmGuard : PairGuardAdmissibleWeak z B D s₁ s₂ v :=
        ⟨hzB, hvB, hDnodup, hdecB, hSguard⟩
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
      have hnextAdm : PairSurplusAdmissibleWeak Y T' (z :: D) s₁ s₂ v := by
        refine ⟨hTY.mono_left (fun _ h => hT'T _ h),
          List.nodup_cons.2 ⟨hzD, hDnodup⟩, ?_, ?_, ?_⟩
        · exact fun hv' => hv (hauxSub hv')
        · intro d hd
          rcases List.mem_cons.1 hd with hdz | hd
          · subst d
            exact ⟨hzB, hzv⟩
          · exact ⟨fun hd' => (hDaway d hd).1
                (hd'.elim Or.inl (fun h => Or.inr (hT'T d h))),
              (hDaway d hd).2⟩
        · apply hSaway.mono_right
          intro q hq
          rcases hq with hqv | hqrest
          · exact Or.inl hqv
          · exact Or.inr (hauxSub hqrest)
      have hTrestore : insert z T' = T := by
        exact Finset.insert_erase hzT
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
            · exact Or.inl (Or.inr (show q ∈ T' from
                Finset.mem_erase.2 ⟨hqz, hqT⟩))
        · refine Or.inr ?_
          change q ∈ z :: D
          exact List.mem_cons_of_mem z hqD
      let O : Set V := {s₁, s₂}
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
      have hbase : B = Y ∪ (↑T' : Set V) := rfl
      have hL : guardDecoyList w (insert z B) D = L := by
        rw [hinsertB]
      have hp : guardObsConst w O v (insert z B ∪ listSet D) = p := by
        rw [hinsertB]
      have hpeel :
          cshMarg L p O W (S' + K) ≤ cshMarg L p O W S := by
        apply guard_cshMarg_le_of_primary w (Y ∪ (↑T : Set V)) D O v
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
        have h := (pair_guardCSH_nondegenerate_weak w hw z B D s₁ s₂ v hadmGuard)
          (vertexClusterFun z F) hΓmono
        unfold guardCSHMargin at h
        simpa [O, W, L, p, Γ, hL, hp] using h
      have hcNonneg : 0 ≤ cshMarg L p O W c := by
        have h := guardAvoidConst_margin_nonneg_weak w hw z B D s₁ s₂ v hadmGuard
        simpa [O, W, L, p, c, hL, hp] using h
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
        rw [← CSH.cshMarg_smul, htopFun, CSH.cshMarg_sub, CSH.cshMarg_smul]
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
            (guardObsConst w O v (Y ∪ (↑T' : Set V) ∪ listSet (z :: D)))
            O W S' = _
        rw [hL, hobsNext]
        change cshMarg (({z}, c) :: L) p O W S' = _
        rw [CSH.cshMarg_cons]
      have hnextNonneg : 0 ≤ sourceSurplusMarginY w Y T' r (z :: D) O v F :=
        ih T'.card hT'card T' (z :: D) rfl hnextAdm hr' hcompat'
      have hrepriced : 0 ≤ cshMarg L p O W S' - κ * cshMarg L p O W c := by
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
      simpa [sourceSurplusMarginY, O, W, L, p, S] using hMT
  exact main T.card T D rfl hadm hr hcompat

/-- Spec item 40: pair-source surplus-margin induction at nondegenerate weights. -/
theorem pairSource_surplusMarginY_nondegenerate
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (D : List V)
    (s₁ s₂ v : V) (F : Set V → ℝ)
    (hadm : PairSurplusAdmissible Y T D s₁ s₂ v)
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ sourceSurplusMarginY w Y T r D ({s₁, s₂} : Set V) v F := by
  rcases hadm with ⟨_, hTY, hDnodup, hv, hDaway, hSaway⟩
  exact pairSource_surplusMarginY_nondegenerate_weak w hw Y T r D s₁ s₂ v F
    ⟨hTY, hDnodup, hv, hDaway, hSaway⟩ hF hr hcompat

private theorem pairSource_surplusTransfer_nondegenerate_weak
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (s₁ s₂ k : V)
    (F : Set V → ℝ) (hadm : PairSurplusAdmissibleWeak Y T [] s₁ s₂ k)
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    (prodBernoulli w).real
        (sourceAvoid ({k} : Set V) (Y ∪ (↑T : Set V))) *
          sourceSurplusY w Y T r F ({s₁, s₂} : Set V) ≥
      (prodBernoulli w).real
          (guardEv ({s₁, s₂} : Set V) ({k} : Set V)
            (Y ∪ (↑T : Set V))) *
        sourceSurplusY w Y T r F ({k} : Set V) := by
  have hmarg := pairSource_surplusMarginY_nondegenerate_weak w hw Y T r []
    s₁ s₂ k F hadm hF hr hcompat
  have hk : k ∉ Y ∪ (↑T : Set V) := by
    obtain ⟨_, _, hkfull, _, _⟩ := hadm
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
    (guardEv ({s₁, s₂} : Set V) ({k} : Set V) (Y ∪ (↑T : Set V)))
  let so := sourceSurplusY w Y T r F ({s₁, s₂} : Set V)
  let sk := sourceSurplusY w Y T r F ({k} : Set V)
  change 0 ≤ so - j / d * sk at hmarg
  have hd : 0 < d := hdpos
  have hmul : 0 ≤ d * (so - j / d * sk) := mul_nonneg hd.le hmarg
  have heq : d * (so - j / d * sk) = d * so - j * sk := by
    field_simp
  change j * sk ≤ d * so
  linarith

/-- Spec item 41: the decoy-free surplus transfer inequality. -/
theorem pairSource_surplusTransfer_nondegenerate
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (s₁ s₂ k : V)
    (F : Set V → ℝ) (hadm : PairSurplusAdmissible Y T [] s₁ s₂ k)
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    (prodBernoulli w).real
        (sourceAvoid ({k} : Set V) (Y ∪ (↑T : Set V))) *
          sourceSurplusY w Y T r F ({s₁, s₂} : Set V) ≥
      (prodBernoulli w).real
          (guardEv ({s₁, s₂} : Set V) ({k} : Set V)
            (Y ∪ (↑T : Set V))) *
        sourceSurplusY w Y T r F ({k} : Set V) := by
  rcases hadm with ⟨_, hTY, hDnodup, hk, hDaway, hSaway⟩
  exact pairSource_surplusTransfer_nondegenerate_weak w hw Y T r s₁ s₂ k F
    ⟨hTY, hDnodup, hk, hDaway, hSaway⟩ hF hr hcompat

/-! A weighted version of the source-kernel tower.  Item 14 is its constant-function
specialization; the extra factor is what lets conditional positive association identify its
mixed moment with an integral on the guarded event. -/

private def pairTowerCarrier (z : V) (L : Set (Sym2 V)) : Set V :=
  insert z {u | ∃ e ∈ L, u ∈ e}

private theorem pairTowerCarrier_openEdgeCluster (ω : BondConfig V) (z : V) :
    pairTowerCarrier z (openEdgeCluster ω z) = openCluster ω z := by
  exact (CSH.openCluster_eq_insert_span ω z).symm

private theorem pairTower_singletonAvoid_iff (ω : BondConfig V)
    (z : V) (B : Set V) :
    ω ∈ sourceAvoid ({z} : Set V) B ↔ Disjoint (openCluster ω z) B := by
  rw [Set.disjoint_left]
  constructor
  · intro h u huC huB
    exact h z (by simp) u huB huC
  · intro h q hq b hb hqb
    have hqz : q = z := by simpa using hq
    subst q
    exact h hqb hb

private theorem pairTower_singletonContact_iff (ω : BondConfig V)
    (R : Set V) (z : V) :
    ω ∈ sourceConn R ({z} : Set V) ↔ (openCluster ω z ∩ R).Nonempty := by
  constructor
  · rintro ⟨q, hqR, z', hz', hqz⟩
    have hz'z : z' = z := by simpa using hz'
    subst z'
    exact ⟨q, hqz.symm, hqR⟩
  · rintro ⟨q, hzq, hqR⟩
    exact ⟨q, hqR, z, by simp, hzq.symm⟩

private theorem pairTower_sourceAvoid_residual_iff (ω : BondConfig V) (z : V)
    (R B : Set V) (hzB : ω ∈ sourceAvoid ({z} : Set V) B) :
    ω ∈ sourceAvoid R B ↔
      ω \ bar (openCluster ω z) ∈ sourceAvoid (R \ openCluster ω z) B := by
  constructor
  · intro h q hq b hb hconn
    exact h q hq.1 b hb (hconn.mono (openGraph_mono Set.sdiff_subset))
  · intro h q hq b hb hconn
    by_cases hqC : q ∈ openCluster ω z
    · exact hzB z (by simp) b hb (hqC.trans hconn)
    · have hzq : ¬ (openGraph ω).Reachable z q := hqC
      have hbar :
          {e : Sym2 V | ∃ u ∈ e,
            u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'} =
            bar (openCluster ω z) := by
        simpa [BHK2006.barOf] using (barOf_singleton_eq_bar z ω)
      have hres := LonePortSumGeneral.reachable_sdiff_bar_iff
        (s := z) (x := q) (ω := ω) hzq b
      rw [hbar] at hres
      exact h q ⟨hq, hqC⟩ b hb (hres.2 hconn)

private theorem pairTower_inducedWeight_delete_bar (w : Sym2 V → unitInterval)
    (U K : Set V) :
    (fun e => if e ∈ bar K then (0 : unitInterval) else inducedWeight w U e) =
      inducedWeight w (U \ K) := by
  funext e
  simp only [inducedWeight]
  by_cases heK : e ∈ bar K
  · rw [if_pos heK]
    have hnot : ¬ ∀ u ∈ e, u ∈ U \ K := by
      rcases heK with ⟨u, hue, huK⟩
      exact fun h => (h u hue).2 huK
    rw [if_neg hnot]
  · rw [if_neg heK]
    have hnoK : ∀ u ∈ e, u ∉ K := by
      intro u hue huK
      exact heK ⟨u, hue, huK⟩
    by_cases hU : ∀ u ∈ e, u ∈ U
    · rw [if_pos hU, if_pos (fun u hu => ⟨hU u hu, hnoK u hu⟩)]
    · rw [if_neg hU]
      have hUK : ¬ ∀ u ∈ e, u ∈ U \ K := fun h => hU fun u hu => (h u hu).1
      rw [if_neg hUK]

private theorem pairTower_sum_weight_sdiff_bar
    (w : Sym2 V → unitInterval) (U K : Set V)
    (E : Set (BondConfig V)) :
    (∑ η, BHK2006.weight (fun e => (inducedWeight w U e : ℝ)) η *
        Percolation.Literature.DecisionTree.ind E (η \ bar K)) =
      worldProb w (U \ K) E := by
  rw [Percolation.Continuity.CovTau.sum_weight_mul_eq_integral]
  rw [BHK2006.integral_comp_sdiff_prodBernoulli]
  rw [pairTower_inducedWeight_delete_bar]
  rw [Percolation.Continuity.CovTau.ind_eq_indicator_one,
    integral_indicator_one MeasurableSet.of_discrete]
  rfl

theorem sourceKernel_tower_mul (w : Sym2 V → unitInterval)
    (U R B : Set V) (z : V) (Q : Set V → ℝ)
    (hinside : insert z (R ∪ B) ⊆ U) :
    (∫ ω in sourceAvoid ({z} : Set V) B,
      Q (openCluster ω z) * sourceKernel w U R B (openCluster ω z)
        ∂(prodBernoulli (inducedWeight w U))) =
      ∫ ω in guardEv R ({z} : Set V) B,
        Q (openCluster ω z) ∂(prodBernoulli (inducedWeight w U)) := by
  classical
  have hzU : z ∈ U := hinside (by simp)
  have hRU : R ⊆ U := fun q hq => hinside (by simp [hq])
  have hBU : B ⊆ U := fun q hq => hinside (by simp [hq])
  have hRi : R ∩ U = R := Set.inter_eq_left.2 hRU
  have hBi : B ∩ U = B := Set.inter_eq_left.2 hBU
  let p : Sym2 V → unitInterval := inducedWeight w U
  let pr : Sym2 V → ℝ := fun e => (p e : ℝ)
  have hm : ∑ ω, BHK2006.weight pr ω = 1 := by
    have h1 := BHK2006.integral_prodBernoulli_eq_sum p fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  let Ψ : Set (Sym2 V) → BondConfig V → ℝ := fun L η =>
    if Disjoint (pairTowerCarrier z L) B then
      if (pairTowerCarrier z L ∩ R).Nonempty then
        Percolation.Literature.DecisionTree.ind
          (sourceAvoid (R \ pairTowerCarrier z L) B) η
      else 0
    else 0
  let Φ : Set (Sym2 V) → BondConfig V → ℝ := fun L η =>
    Q (pairTowerCarrier z L) * Ψ L η
  have hbar (ω : BondConfig V) :
      {e : Sym2 V | ∃ u ∈ e,
        u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'} =
          bar (openCluster ω z) := by
    simpa [BHK2006.barOf] using (barOf_singleton_eq_bar z ω)
  have hleftΨ : ∀ ω : BondConfig V,
      Ψ (openEdgeCluster ω z)
          (ω \ {e : Sym2 V | ∃ u ∈ e,
            u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'}) =
        Percolation.Literature.DecisionTree.ind (guardEv R ({z} : Set V) B) ω := by
    intro ω
    rw [hbar]
    dsimp only [Ψ]
    rw [pairTowerCarrier_openEdgeCluster]
    by_cases hzavoid : ω ∈ sourceAvoid ({z} : Set V) B
    · have hdis := (pairTower_singletonAvoid_iff ω z B).1 hzavoid
      rw [if_pos hdis]
      by_cases hcontact : ω ∈ sourceConn R ({z} : Set V)
      · have hne := (pairTower_singletonContact_iff ω R z).1 hcontact
        rw [if_pos hne]
        have hres := pairTower_sourceAvoid_residual_iff ω z R B hzavoid
        by_cases hRavoid : ω ∈ sourceAvoid R B
        · rw [Percolation.Literature.DecisionTree.ind_of_mem (hres.1 hRavoid),
            Percolation.Literature.DecisionTree.ind_of_mem
              (show ω ∈ guardEv R ({z} : Set V) B from ⟨hRavoid, hcontact⟩)]
        · rw [Percolation.Literature.DecisionTree.ind_of_not_mem
              (fun h => hRavoid (hres.2 h)),
            Percolation.Literature.DecisionTree.ind_of_not_mem
              (fun h => hRavoid h.1)]
      · have hempty : ¬ (openCluster ω z ∩ R).Nonempty :=
          fun h => hcontact ((pairTower_singletonContact_iff ω R z).2 h)
        rw [if_neg hempty,
          Percolation.Literature.DecisionTree.ind_of_not_mem (fun h => hcontact h.2)]
    · have hdis : ¬ Disjoint (openCluster ω z) B :=
        fun h => hzavoid ((pairTower_singletonAvoid_iff ω z B).2 h)
      rw [if_neg hdis,
        Percolation.Literature.DecisionTree.ind_of_not_mem]
      rintro ⟨hRavoid, hcontact⟩
      rcases hcontact with ⟨q, hqR, z', hz', hqz⟩
      have hz'z : z' = z := by simpa using hz'
      subst z'
      apply hzavoid
      intro z' hz' b hb hzb
      have hz'z : z' = z := by simpa using hz'
      subst z'
      exact hRavoid q hqR b hb (hqz.trans hzb)
  have hrightΨ : ∀ ω : BondConfig V,
      (∑ η, BHK2006.weight pr η *
        Ψ (openEdgeCluster ω z)
          (η \ {e : Sym2 V | ∃ u ∈ e,
            u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'})) =
        sourceKernel w U R B (openCluster ω z) *
          Percolation.Literature.DecisionTree.ind
            (sourceAvoid ({z} : Set V) B) ω := by
    intro ω
    rw [hbar]
    dsimp only [Ψ]
    rw [pairTowerCarrier_openEdgeCluster]
    by_cases hzavoid : ω ∈ sourceAvoid ({z} : Set V) B
    · have hdis := (pairTower_singletonAvoid_iff ω z B).1 hzavoid
      simp only [if_pos hdis,
        Percolation.Literature.DecisionTree.ind_of_mem hzavoid, mul_one]
      by_cases hne : (openCluster ω z ∩ R).Nonempty
      · simp only [if_pos hne]
        rw [pairTower_sum_weight_sdiff_bar]
        simp only [sourceKernel, hRi, hBi, if_pos hne]
      · simp only [if_neg hne, mul_zero, Finset.sum_const_zero]
        simp [sourceKernel, hRi, hne]
    · have hdis : ¬ Disjoint (openCluster ω z) B :=
        fun h => hzavoid ((pairTower_singletonAvoid_iff ω z B).2 h)
      simp only [if_neg hdis, mul_zero, Finset.sum_const_zero,
        Percolation.Literature.DecisionTree.ind_of_not_mem hzavoid]
  have hleftΦ : ∀ ω : BondConfig V,
      Φ (openEdgeCluster ω z)
          (ω \ {e : Sym2 V | ∃ u ∈ e,
            u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'}) =
        Q (openCluster ω z) *
          Percolation.Literature.DecisionTree.ind
            (guardEv R ({z} : Set V) B) ω := by
    intro ω
    dsimp only [Φ]
    rw [pairTowerCarrier_openEdgeCluster, hleftΨ]
  have hrightΦ : ∀ ω : BondConfig V,
      (∑ η, BHK2006.weight pr η *
        Φ (openEdgeCluster ω z)
          (η \ {e : Sym2 V | ∃ u ∈ e,
            u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'})) =
        (Q (openCluster ω z) * sourceKernel w U R B (openCluster ω z)) *
          Percolation.Literature.DecisionTree.ind
            (sourceAvoid ({z} : Set V) B) ω := by
    intro ω
    have hfactor :
        (∑ η, BHK2006.weight pr η *
          Φ (openEdgeCluster ω z)
            (η \ {e : Sym2 V | ∃ u ∈ e,
              u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'})) =
          Q (openCluster ω z) *
            (∑ η, BHK2006.weight pr η *
              Ψ (openEdgeCluster ω z)
                (η \ {e : Sym2 V | ∃ u ∈ e,
                  u = z ∨ ∃ e' ∈ openEdgeCluster ω z, u ∈ e'})) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun η _ => ?_
      dsimp only [Φ]
      rw [pairTowerCarrier_openEdgeCluster]
      ring
    rw [hfactor, hrightΨ]
    ring
  have key := BHK2006.sum_cond_cluster_sdiff pr hm z Φ
  simp_rw [hleftΦ] at key
  simp_rw [hrightΦ] at key
  rw [← Percolation.Continuity.CovTau.sum_weight_mul_ind p
      (fun ω => Q (openCluster ω z) * sourceKernel w U R B (openCluster ω z))
      (sourceAvoid ({z} : Set V) B)]
  rw [← Percolation.Continuity.CovTau.sum_weight_mul_ind p
      (fun ω => Q (openCluster ω z)) (guardEv R ({z} : Set V) B)]
  simpa only [pr, p, mul_assoc, mul_comm, mul_left_comm] using key.symm

/-- Spec item 42: the top-relay conditional-BHK estimate. -/
theorem sourceTopRelay_pair (w : Sym2 V → unitInterval) (Y : Set V)
    (T : Finset V) (F : Set V → ℝ) (s₁ s₂ k : V)
    (hdis : Disjoint ({s₁, s₂} : Set V)
      (insert k (Y ∪ (↑T : Set V)))) (hF : Monotone F) :
    (prodBernoulli w).real
        (sourceAvoid ({k} : Set V) (Y ∪ (↑T : Set V))) *
      (∫ ω in guardEv ({s₁, s₂} : Set V) ({k} : Set V)
          (Y ∪ (↑T : Set V)),
        (F (sourceCluster ω ({s₁, s₂} : Set V)) - condMean w Y F k)
          ∂(prodBernoulli w)) ≥
      -((prodBernoulli w).real
          (guardEv ({s₁, s₂} : Set V) ({k} : Set V)
            (Y ∪ (↑T : Set V))) * sourceKappa w Y T F k) := by
  let B : Set V := Y ∪ (↑T : Set V)
  let R : Set V := {s₁, s₂}
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
    apply KNAll.Guarded.sourceKernel_mono_cluster w Set.univ R B
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
    have h := KNAll.Guarded.sourceKernel_tower w Set.univ R B k hinside
    simp only [KNAll.Guarded.sourceCluster_singleton] at h
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
    exact hF (KNAll.Guarded.openCluster_subset_sourceCluster_of_guard hω.2)
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

/-- Spec item 43: pair-source avoided first-relay inequality at nondegenerate weights. -/
theorem pairSource_surplusY_nondegenerate
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (Y : Set V) (T : Finset V) (r : V → ℕ) (s₁ s₂ : V)
    (F : Set V → ℝ)
    (hdis : Disjoint ({s₁, s₂} : Set V) (Y ∪ (↑T : Set V)))
    (hTY : Disjoint (↑T : Set V) Y)
    (hF : Monotone F) (hr : Set.InjOn r (↑T : Set V))
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      condMean w Y F a ≤ condMean w Y F a') :
    0 ≤ sourceSurplusY w Y T r F ({s₁, s₂} : Set V) := by
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · unfold sourceSurplusY
    have hc : sourceConn ({s₁, s₂} : Set V) (↑(∅ : Finset V) : Set V) = ∅ := by
      ext ω
      simp [sourceConn]
    rw [hc]
    simp
  obtain ⟨k, hkT, hkmax⟩ := Finset.exists_max_image T r hTne
  let T₀ : Finset V := T.erase k
  let S : Set V := {s₁, s₂}
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
  have hadm : PairSurplusAdmissibleWeak Y T₀ [] s₁ s₂ k := by
    refine ⟨hTY₀, List.nodup_nil, ?_, ?_, ?_⟩
    · simpa [listSet, B] using hkB
    · intro d hd
      simp at hd
    · simpa [S, B, listSet] using hguard
  have htransfer : μ.real E * surS ≥ μ.real J * surK := by
    simpa [μ, E, J, S, B, surS, surK] using
      pairSource_surplusTransfer_nondegenerate_weak w hw Y T₀ r s₁ s₂ k F
        hadm hF hr₀ hcompat₀
  have htop : μ.real E * I ≥ -(μ.real J * κ) := by
    simpa [μ, E, J, I, κ, S, B] using
      sourceTopRelay_pair w Y T₀ F s₁ s₂ k hguard hF
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

end KNAll.Guarded

end
