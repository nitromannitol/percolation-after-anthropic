
import Percolation.Continuity.CSH.Unfold

import KNConjectures.GuardedDefs
import KNConjectures.GuardedBasic
import KNConjectures.GuardedKernel
set_option linter.unusedSectionVars false

/-!
# The corrected guarded decoy identity

This file proves items 19--25 of `spec6.md`.  The key point in item 19 is that
the complete edge-valued set cluster `BHK2006.setCl ω R` is exposed.  Its
vertex carrier is `sourceCluster ω R`; no conditioning on the carrier alone is
used.
-/

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels
  Percolation.Literature Percolation.Continuity
open scoped Classical
open BHK2006 DecisionTree HullPort

variable {V : Type*} [Fintype V]

/-! ## Complete set-source exploration -/

/-- The vertex carrier represented by a complete edge-valued source cluster. -/
private def sourceCarrier (R : Set V) (W : Set (Sym2 V)) : Set V :=
  {u | u ∈ R ∨ ∃ e ∈ W, u ∈ e}

private theorem sourceCluster_eq_sourceCarrier (omega : BondConfig V) (R : Set V) :
    sourceCluster omega R = sourceCarrier R (BHK2006.setCl omega R) := by
  ext u
  simp only [sourceCluster, sourceCarrier, Set.mem_iUnion, exists_prop,
    Set.mem_setOf_eq]
  change (∃ r, r ∈ R ∧ (openGraph omega).Reachable r u) ↔ _
  exact BHK2006.setReach_iff omega R u

private theorem barOf_eq_edgesOf_sourceCarrier (R : Set V)
    (W : Set (Sym2 V)) :
    BHK2006.barOf R W = CSH.edgesOf (sourceCarrier R W) := by
  ext e
  simp only [BHK2006.mem_barOf_iff, CSH.edgesOf, sourceCarrier,
    Set.mem_setOf_eq]

/-- The guarded event is a function of the complete explored source cluster. -/
private def sourceGuardInd (R : Set V) (d : V) (A : Set V)
    (W : Set (Sym2 V)) : ℝ :=
  if (∀ a ∈ A, ¬ (a ∈ R ∨ ∃ e ∈ W, a ∈ e)) ∧
      (d ∈ R ∨ ∃ e ∈ W, d ∈ e) then 1 else 0

private theorem sourceGuardInd_setCl (R : Set V) (d : V) (A : Set V)
    (omega : BondConfig V) :
    sourceGuardInd R d A (BHK2006.setCl omega R) =
      DecisionTree.ind (guardEv R ({d} : Set V) A) omega := by
  have hp :
      ((∀ a ∈ A, ¬ (a ∈ R ∨
          ∃ e ∈ BHK2006.setCl omega R, a ∈ e)) ∧
        (d ∈ R ∨ ∃ e ∈ BHK2006.setCl omega R, d ∈ e)) ↔
        omega ∈ guardEv R ({d} : Set V) A := by
    constructor
    · rintro ⟨hav, hcon⟩
      refine ⟨?_, ?_⟩
      · intro r hr a ha hra
        exact hav a ha ((BHK2006.setReach_iff omega R a).1 ⟨r, hr, hra⟩)
      · obtain ⟨r, hr, hrd⟩ := (BHK2006.setReach_iff omega R d).2 hcon
        exact ⟨r, hr, d, Set.mem_singleton d, hrd⟩
    · rintro ⟨hav, hcon⟩
      refine ⟨?_, ?_⟩
      · intro a ha hcar
        obtain ⟨r, hr, hra⟩ := (BHK2006.setReach_iff omega R a).2 hcar
        exact hav r hr a ha hra
      · obtain ⟨r, hr, q, hq, hrq⟩ := hcon
        rw [Set.mem_singleton_iff] at hq
        subst q
        exact (BHK2006.setReach_iff omega R d).1 ⟨r, hr, hrq⟩
  unfold sourceGuardInd
  by_cases h : omega ∈ guardEv R ({d} : Set V) A
  · rw [if_pos (hp.2 h), DecisionTree.ind_of_mem h]
  · rw [if_neg (fun h' => h (hp.1 h')), DecisionTree.ind_of_not_mem h]

/-- Deleting the complete source-cluster boundary does not change the CSH
residual when the source avoids the owner and the avoided set. -/
private theorem resid_sdiff_sourceCluster (w : Sym2 V → ℝ) (x : V)
    (Y : Set V) (g : Set (Sym2 V) → ℝ) (R : Set V)
    (omega : BondConfig V) (havoid : omega ∈ sourceAvoid R (insert x Y)) :
    CSH.resid w x Y g
        (omega \ BHK2006.barOf R (BHK2006.setCl omega R)) =
      CSH.resid w x Y g omega := by
  have hsepX : ∀ r ∈ R, ∀ t ∈ ({x} : Set V),
      ¬ (openGraph omega).Reachable r t := by
    intro r hr t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    exact havoid r hr x (Set.mem_insert x Y)
  have hsepY : ∀ r ∈ R, ∀ y ∈ Y,
      ¬ (openGraph omega).Reachable r y := by
    intro r hr y hy
    exact havoid r hr y (Set.mem_insert_of_mem x hy)
  have hxcl := BHK2006.setCl_eq_sdiff_barOf
    (rfl : BHK2006.setCl omega R = BHK2006.setCl omega R)
    ((BHK2006.notJoined_iff_of_setCl_eq
      (rfl : BHK2006.setCl omega R = BHK2006.setCl omega R)).1 hsepX)
  have hYcl := BHK2006.setCl_eq_sdiff_barOf
    (rfl : BHK2006.setCl omega R = BHK2006.setCl omega R)
    ((BHK2006.notJoined_iff_of_setCl_eq
      (rfl : BHK2006.setCl omega R = BHK2006.setCl omega R)).1 hsepY)
  simp only [BHK2006.setCl_singleton] at hxcl
  have hcut :
      HullPort.cut Y
          (omega \ BHK2006.barOf R (BHK2006.setCl omega R)) =
        HullPort.cut Y omega := by
    rw [HullPort.cut_eq_barOf, HullPort.cut_eq_barOf, ← hYcl]
  have hreach : ∀ y : V,
      (openGraph (omega \ BHK2006.barOf R (BHK2006.setCl omega R))).Reachable x y ↔
        (openGraph omega).Reachable x y := by
    intro y
    rw [reachable_iff_exists_mem_openEdgeCluster,
      reachable_iff_exists_mem_openEdgeCluster, ← hxcl]
  have hind :
      DecisionTree.ind (HullPort.avoidEv x Y)
          (omega \ BHK2006.barOf R (BHK2006.setCl omega R)) =
        DecisionTree.ind (HullPort.avoidEv x Y) omega := by
    have hev :
        (omega \ BHK2006.barOf R (BHK2006.setCl omega R)) ∈
            HullPort.avoidEv x Y ↔
          omega ∈ HullPort.avoidEv x Y := by
      constructor
      · intro h y hy hxy
        exact h y hy ((hreach y).2 hxy)
      · intro h y hy hxy
        exact h y hy ((hreach y).1 hxy)
    by_cases h : omega ∈ HullPort.avoidEv x Y
    · rw [DecisionTree.ind_of_mem h,
        DecisionTree.ind_of_mem (hev.2 h)]
    · rw [DecisionTree.ind_of_not_mem h,
        DecisionTree.ind_of_not_mem (fun h' => h (hev.1 h'))]
  unfold CSH.resid CSH.wmeanOff
  rw [hxcl, hcut, hind]

/-- The residual mean in a world with all edges meeting `K` deleted is
`-Φ(K)`.  This is the set-carrier form of
`CSH.sum_resid_world_singleton`. -/
private theorem sum_resid_world_source (w : Sym2 V → unitInterval)
    (hm : ∑ omega : BondConfig V,
      BHK2006.weight (fun e => (w e : ℝ)) omega = 1)
    (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (K : Set V) :
    ∑ eta : BondConfig V, BHK2006.weight (fun e => (w e : ℝ)) eta *
        CSH.resid (fun e => (w e : ℝ)) x Y g (eta \ CSH.edgesOf K) =
      -CSH.phiFun w x Y g K := by
  unfold CSH.phiFun
  rw [BHK2006.integral_prodBernoulli_eq_sum,
    CSH.sum_phiIntegrand_eq (fun e => (w e : ℝ)) hm x Y K g,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun eta _ => ?_
  unfold CSH.resid
  ring

/-- Spec §4.1: exact whole-source-cluster exploration identity. -/
theorem guardResid_sourceCluster (w : Sym2 V → unitInterval) (x : V)
    (Y : Set V) (g : Set (Sym2 V) → ℝ) (d : V) (A R : Set V)
    (hA : insert x Y ⊆ A) :
    (∫ omega in guardEv R ({d} : Set V) A,
      CSH.resid (fun e => (w e : ℝ)) x Y g omega ∂(prodBernoulli w)) =
      -∫ omega in guardEv R ({d} : Set V) A,
        CSH.phiFun w x Y g (sourceCluster omega R) ∂(prodBernoulli w) := by
  classical
  let wr : Sym2 V → ℝ := fun e => (w e : ℝ)
  have hm : ∑ omega : BondConfig V, BHK2006.weight wr omega = 1 := by
    have h := BHK2006.integral_prodBernoulli_eq_sum w
      (fun _ : BondConfig V => (1 : ℝ))
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
    exact h.symm
  let Kfun : Set (Sym2 V) → BondConfig V → ℝ := fun W beta =>
    sourceGuardInd R d A W * CSH.resid wr x Y g beta
  have key := HullPort.set_sum_cond_sdiff wr hm R Kfun
  rw [CSH.setIntegral_eq_sum_ind, CSH.setIntegral_eq_sum_ind]
  have hL : ∀ omega : BondConfig V,
      BHK2006.weight wr omega *
          Kfun (BHK2006.setCl omega R)
            (omega \ BHK2006.barOf R (BHK2006.setCl omega R)) =
        BHK2006.weight wr omega *
          (DecisionTree.ind (guardEv R ({d} : Set V) A) omega *
            CSH.resid wr x Y g omega) := by
    intro omega
    simp only [Kfun, sourceGuardInd_setCl]
    by_cases hG : omega ∈ guardEv R ({d} : Set V) A
    · rw [DecisionTree.ind_of_mem hG,
          resid_sdiff_sourceCluster wr x Y g R omega
            (fun r hr a ha => hG.1 r hr a (hA ha))]
    · rw [DecisionTree.ind_of_not_mem hG]
      ring
  have hR : ∀ omega : BondConfig V,
      BHK2006.weight wr omega *
          (∑ eta : BondConfig V, BHK2006.weight wr eta *
            Kfun (BHK2006.setCl omega R)
              (eta \ BHK2006.barOf R (BHK2006.setCl omega R))) =
        -(BHK2006.weight wr omega *
          (DecisionTree.ind (guardEv R ({d} : Set V) A) omega *
            CSH.phiFun w x Y g (sourceCluster omega R))) := by
    intro omega
    simp only [Kfun, sourceGuardInd_setCl]
    by_cases hG : omega ∈ guardEv R ({d} : Set V) A
    · rw [DecisionTree.ind_of_mem hG]
      simp only [one_mul]
      rw [barOf_eq_edgesOf_sourceCarrier,
        ← sourceCluster_eq_sourceCarrier,
        sum_resid_world_source w hm]
      ring
    · rw [DecisionTree.ind_of_not_mem hG]
      simp
  calc
    ∑ omega, BHK2006.weight wr omega *
          (DecisionTree.ind (guardEv R ({d} : Set V) A) omega *
            CSH.resid wr x Y g omega) =
        ∑ omega, BHK2006.weight wr omega *
          Kfun (BHK2006.setCl omega R)
            (omega \ BHK2006.barOf R (BHK2006.setCl omega R)) :=
      Finset.sum_congr rfl fun omega _ => (hL omega).symm
    _ = ∑ omega, BHK2006.weight wr omega *
          (∑ eta, BHK2006.weight wr eta *
            Kfun (BHK2006.setCl omega R)
              (eta \ BHK2006.barOf R (BHK2006.setCl omega R))) := key
    _ = ∑ omega, -(BHK2006.weight wr omega *
          (DecisionTree.ind (guardEv R ({d} : Set V) A) omega *
            CSH.phiFun w x Y g (sourceCluster omega R))) :=
      Finset.sum_congr rfl fun omega _ => hR omega
    _ = -∑ omega, BHK2006.weight wr omega *
          (DecisionTree.ind (guardEv R ({d} : Set V) A) omega *
            CSH.phiFun w x Y g (sourceCluster omega R)) := by
      rw [Finset.sum_neg_distrib]

/-! ## The correction term and CGDI -/

/-- Spec §4.2: the `Delta` correction is nonnegative for increasing `g`. -/
theorem guardDelta_nonneg (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    {g : Set (Sym2 V) → ℝ} (hg : Monotone g) (d : V) (A R : Set V) :
    0 ≤ guardDelta w x Y g d A R := by
  unfold guardDelta
  exact setIntegral_nonneg MeasurableSet.of_discrete fun omega homega =>
    sub_nonneg.mpr (CSH.phiFun_mono w x Y hg
      (KNAll.Guarded.openCluster_subset_sourceCluster_of_guard homega.2))

/-- Spec §4.2: the `Delta` correction vanishes at singleton evaluations. -/
theorem guardDelta_singleton_eq_zero (w : Sym2 V → unitInterval) (x : V)
    (Y : Set V) (g : Set (Sym2 V) → ℝ) (d u : V) (A : Set V) :
    guardDelta w x Y g d A ({u} : Set V) = 0 := by
  unfold guardDelta
  rw [setIntegral_congr_fun MeasurableSet.of_discrete
    (g := fun _ => (0 : ℝ)) (fun omega homega => by
      rw [KNAll.Guarded.sourceCluster_eq_openCluster_of_singleton_guard u d homega.2]
      ring)]
  simp

private theorem guardEv_self (d : V) (A : Set V) :
    guardEv ({d} : Set V) ({d} : Set V) A =
      sourceAvoid ({d} : Set V) A := by
  ext omega
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, ⟨d, Set.mem_singleton d, d, Set.mem_singleton d,
      SimpleGraph.Reachable.refl d⟩⟩

private theorem phiT_openEdgeCluster_eq_phiFun (w : Sym2 V → unitInterval)
    (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (d : V)
    (omega : BondConfig V) :
    CSH.phiT w x Y g d (openEdgeCluster omega d) =
      CSH.phiFun w x Y g (openCluster omega d) := by
  unfold CSH.phiT
  rw [← CSH.openCluster_eq_insert_span]

private theorem guardResidMoment_as_setIntegrals
    (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (d : V) (A R : Set V) :
    guardResidMoment w x Y g d A R =
      (∫ omega in guardEv R ({d} : Set V) A,
        CSH.resid (fun e => (w e : ℝ)) x Y g omega ∂(prodBernoulli w)) -
      guardAvoidConst w d A R *
        (∫ omega in sourceAvoid ({d} : Set V) A,
          CSH.resid (fun e => (w e : ℝ)) x Y g omega
            ∂(prodBernoulli w)) := by
  unfold guardResidMoment
  rw [BHK2006.integral_prodBernoulli_eq_sum,
    CSH.setIntegral_eq_sum_ind, CSH.setIntegral_eq_sum_ind,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun omega _ => by ring

/-- Spec §4.3, corrected guarded decoy identity:
`moment = -e^-1 Gamma - Delta`. -/
theorem guardResidMoment_eq (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (d : V) (A R : Set V)
    (hA : insert x Y ⊆ A)
    (he : (prodBernoulli w).real (sourceAvoid ({d} : Set V) A) ≠ 0) :
    guardResidMoment w x Y g d A R =
      -((prodBernoulli w).real (sourceAvoid ({d} : Set V) A))⁻¹ *
          guardCovD w d A (CSH.phiT w x Y g d) R -
        guardDelta w x Y g d A R := by
  rw [guardResidMoment_as_setIntegrals]
  have hH := guardResid_sourceCluster w x Y g d A R hA
  have hE := guardResid_sourceCluster w x Y g d A ({d} : Set V) hA
  rw [guardEv_self] at hE
  have hE' :
      (∫ omega in sourceAvoid ({d} : Set V) A,
          CSH.resid (fun e => (w e : ℝ)) x Y g omega
            ∂(prodBernoulli w)) =
        -∫ omega in sourceAvoid ({d} : Set V) A,
          CSH.phiFun w x Y g (openCluster omega d)
            ∂(prodBernoulli w) := by
    simpa only [KNAll.Guarded.sourceCluster_singleton] using hE
  rw [hH, hE']
  have hphiH :
      (∫ omega in guardEv R ({d} : Set V) A,
          CSH.phiT w x Y g d (openEdgeCluster omega d)
            ∂(prodBernoulli w)) =
        ∫ omega in guardEv R ({d} : Set V) A,
          CSH.phiFun w x Y g (openCluster omega d)
            ∂(prodBernoulli w) :=
    setIntegral_congr_fun MeasurableSet.of_discrete fun omega _ =>
      phiT_openEdgeCluster_eq_phiFun w x Y g d omega
  have hphiE :
      (∫ omega in sourceAvoid ({d} : Set V) A,
          CSH.phiT w x Y g d (openEdgeCluster omega d)
            ∂(prodBernoulli w)) =
        ∫ omega in sourceAvoid ({d} : Set V) A,
          CSH.phiFun w x Y g (openCluster omega d)
            ∂(prodBernoulli w) :=
    setIntegral_congr_fun MeasurableSet.of_discrete fun omega _ =>
      phiT_openEdgeCluster_eq_phiFun w x Y g d omega
  unfold guardAvoidConst guardCovD guardDelta
  rw [integral_sub Integrable.of_finite.integrableOn
      Integrable.of_finite.integrableOn, hphiH, hphiE]
  field_simp
  ring

/-- Spec §4.3, GDI: discard the nonnegative `Delta` correction. -/
theorem guarded_decoy_inequality (w : Sym2 V → unitInterval) (x : V)
    (Y : Set V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g)
    (d : V) (A R : Set V) (hA : insert x Y ⊆ A)
    (he : (prodBernoulli w).real (sourceAvoid ({d} : Set V) A) ≠ 0) :
    guardResidMoment w x Y g d A R ≤
      -((prodBernoulli w).real (sourceAvoid ({d} : Set V) A))⁻¹ *
        guardCovD w d A (CSH.phiT w x Y g d) R := by
  rw [guardResidMoment_eq w x Y g d A R hA he]
  exact sub_le_self _ (guardDelta_nonneg w x Y hg d A R)

/-! ## Affine shape of a guarded tail -/

/-- Spec §4.4: a tail margin has one set-valued primary evaluation and
otherwise only singleton evaluations. -/
theorem guard_tail_shape (w : Sym2 V → unitInterval) (A : Set V)
    (D : List V) (O : Set V) (v : V) :
    ∃ coeff : V → ℝ, ∀ h : Set V → ℝ,
      CSH.cshMarg (guardDecoyList w A D)
          (guardObsConst w O v (A ∪ listSet D))
          O ({v} : Set V) h =
        h O + ∑ u, coeff u * h ({u} : Set V) := by
  induction D generalizing A with
  | nil =>
      refine ⟨fun u => if u = v then
        -guardObsConst w O v (A ∪ listSet ([] : List V)) else 0, ?_⟩
      intro h
      simp [guardDecoyList, CSH.cshMarg_nil]
      ring
  | cons d ds ih =>
      have hset : A ∪ listSet (d :: ds) = insert d A ∪ listSet ds := by
        ext u
        simp [listSet]
        tauto
      rw [guardDecoyList, hset]
      obtain ⟨coeff, hcoeff⟩ := ih (insert d A)
      let m : ℝ :=
        CSH.cshMarg (guardDecoyList w (insert d A) ds)
          (guardObsConst w O v (insert d A ∪ listSet ds))
          O ({v} : Set V) (guardAvoidConst w d A)
      refine ⟨fun u => coeff u - if u = d then m else 0, ?_⟩
      intro h
      rw [CSH.cshMarg_cons, hcoeff h]
      change h O + ∑ u, coeff u * h ({u} : Set V) -
          h ({d} : Set V) * m =
        h O + ∑ u, (coeff u - if u = d then m else 0) *
          h ({u} : Set V)
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      have hs :
          ∑ u : V, (if u = d then m else 0) * h ({u} : Set V) =
            m * h ({d} : Set V) := by simp
      rw [hs]
      ring

/-! Item 25 is proved below after the source-valued unfolding helpers. -/

/-! ## A source-valued residual level form -/

/-- The global residual paired with the guarded level form whose current marker
set is `S`.  This is the sum-level normal form of the within-world term. -/
private def guardResidLevel (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (O : Set V) (v : V)
    (A : Set V) (D : List V) (S : Set V) : ℝ :=
  ∑ omega : BondConfig V, BHK2006.weight (fun e => (w e : ℝ)) omega *
    (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
      CSH.cshMarg (guardDecoyList w A D)
        (guardObsConst w O v (A ∪ listSet D)) O ({v} : Set V)
        (fun R => DecisionTree.ind (guardEv R S Y) omega))

private theorem sourceAvoid_iff_not_sourceConn (R T : Set V)
    (omega : BondConfig V) :
    omega ∈ sourceAvoid R T ↔ omega ∉ sourceConn R T := by
  constructor
  · intro h ⟨r, hr, t, ht, hrt⟩
    exact h r hr t ht hrt
  · intro h r hr t ht hrt
    exact h ⟨r, hr, t, ht, hrt⟩

private theorem sourceConn_insert (R S : Set V) (d : V)
    (omega : BondConfig V) :
    omega ∈ sourceConn R (insert d S) ↔
      omega ∈ sourceConn R S ∨
        omega ∈ sourceConn R ({d} : Set V) := by
  constructor
  · rintro ⟨r, hr, t, ht, hrt⟩
    rcases Set.mem_insert_iff.1 ht with htd | ht
    · subst t
      exact Or.inr ⟨r, hr, d, Set.mem_singleton d, hrt⟩
    · exact Or.inl ⟨r, hr, t, ht, hrt⟩
  · rintro (⟨r, hr, t, ht, hrt⟩ | ⟨r, hr, t, ht, hrt⟩)
    · exact ⟨r, hr, t, Set.mem_insert_of_mem d ht, hrt⟩
    · rw [Set.mem_singleton_iff] at ht
      subst t
      exact ⟨r, hr, d, Set.mem_insert d S, hrt⟩

private theorem sourceConn_union (R S T : Set V) (omega : BondConfig V) :
    omega ∈ sourceConn R (S ∪ T) ↔
      omega ∈ sourceConn R S ∨ omega ∈ sourceConn R T := by
  constructor
  · rintro ⟨r, hr, t, ht, hrt⟩
    exact ht.elim (fun hs => Or.inl ⟨r, hr, t, hs, hrt⟩)
      (fun ht => Or.inr ⟨r, hr, t, ht, hrt⟩)
  · rintro (⟨r, hr, s, hs, hrs⟩ | ⟨r, hr, t, ht, hrt⟩)
    · exact ⟨r, hr, s, Or.inl hs, hrs⟩
    · exact ⟨r, hr, t, Or.inr ht, hrt⟩

/-- The elementary guarded decoy split, pointwise in a configuration. -/
private theorem guard_decoy_split (R S Y A : Set V) (d : V)
    (c : Set V → ℝ) (omega : BondConfig V) (hA : A = S ∪ Y) :
    DecisionTree.ind (guardEv R S Y) omega -
        c R * DecisionTree.ind (guardEv ({d} : Set V) S Y) omega =
      DecisionTree.ind (guardEv R (insert d S) Y) omega -
        (DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
          c R * DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega) -
        c R * DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega := by
  subst A
  have havRY := sourceAvoid_iff_not_sourceConn R Y omega
  have havdY := sourceAvoid_iff_not_sourceConn ({d} : Set V) Y omega
  have havRunion := sourceAvoid_iff_not_sourceConn R (S ∪ Y) omega
  have havdunion := sourceAvoid_iff_not_sourceConn ({d} : Set V) (S ∪ Y) omega
  have hcins := sourceConn_insert R S d omega
  have hcunionR := sourceConn_union R S Y omega
  have hcuniond := sourceConn_union ({d} : Set V) S Y omega
  by_cases hRY : omega ∈ sourceConn R Y <;>
    by_cases hRS : omega ∈ sourceConn R S <;>
    by_cases hRd : omega ∈ sourceConn R ({d} : Set V) <;>
    by_cases hdY : omega ∈ sourceConn ({d} : Set V) Y <;>
    by_cases hdS : omega ∈ sourceConn ({d} : Set V) S <;>
    simp only [guardEv, Set.mem_inter_iff, havRY, havdY,
      havRunion, havdunion, hcins, hcunionR, hcuniond, hRY, hRS, hRd,
      hdY, hdS, not_true_eq_false, not_false_eq_true, true_and,
      false_and, true_or, false_or, DecisionTree.ind_of_mem,
      DecisionTree.ind_of_not_mem] <;> ring

private theorem cshMarg_sub {E : Type*} (L : List (E × (E → ℝ)))
    (p : ℝ) (o v : E) (f h : E → ℝ) :
    CSH.cshMarg L p o v (f - h) =
      CSH.cshMarg L p o v f - CSH.cshMarg L p o v h := by
  simp only [CSH.cshMarg, CSH.slForm_sub, Pi.sub_apply]
  ring

private theorem cshMarg_finset_sum {E I : Type*} [Fintype E]
    (L : List (E × (E → ℝ))) (p : ℝ) (o v : E)
    (s : Finset I) (a : I → ℝ) (f : I → E → ℝ) :
    CSH.cshMarg L p o v (∑ i ∈ s, a i • f i) =
      ∑ i ∈ s, a i * CSH.cshMarg L p o v (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [CSH.cshMarg, CSH.slForm_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, CSH.cshMarg_add,
        CSH.cshMarg_smul, ih]

private theorem residual_avoid_singleton_sum_zero
    (w : Sym2 V → unitInterval)
    (hm : ∑ omega : BondConfig V,
      BHK2006.weight (fun e => (w e : ℝ)) omega = 1)
    (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (d : V) :
    ∑ omega : BondConfig V, BHK2006.weight (fun e => (w e : ℝ)) omega *
      (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
        DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega) = 0 := by
  let kappa : Set (Sym2 V) → ℝ := fun W =>
    if d ∈ Y ∨ ∃ e ∈ W, d ∈ e then 0 else 1
  have hk : ∀ omega : BondConfig V,
      kappa (BHK2006.setCl omega Y) =
        DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega := by
    intro omega
    rw [KNAll.Guarded.sourceAvoid_singleton]
    have hp := CSH.mem_avoidEv_iff_notMem_span d Y omega
    unfold kappa
    by_cases h : omega ∈ HullPort.avoidEv d Y
    · rw [if_neg (hp.1 h), DecisionTree.ind_of_mem h]
    · rw [if_pos (Classical.not_not.mp (fun hn => h (hp.2 hn))),
        DecisionTree.ind_of_not_mem h]
  have horth := CSH.residual_orthogonal
    (fun e => (w e : ℝ)) hm x Y g kappa
  rw [← horth]
  exact Finset.sum_congr rfl fun omega _ => by
    rw [← hk]
    unfold CSH.resid
    ring

private theorem guardResidMoment_eq_sum
    (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (d : V) (A R : Set V) :
    guardResidMoment w x Y g d A R =
      ∑ omega : BondConfig V,
        BHK2006.weight (fun e => (w e : ℝ)) omega *
          (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
            (DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
              guardAvoidConst w d A R *
                DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega)) := by
  unfold guardResidMoment
  rw [BHK2006.integral_prodBernoulli_eq_sum]

/-- One exact decoy step at the global residual level. -/
private theorem guardResidLevel_step
    (w : Sym2 V → unitInterval)
    (hm : ∑ omega : BondConfig V,
      BHK2006.weight (fun e => (w e : ℝ)) omega = 1)
    (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ)
    (O : Set V) (v d : V) (A S : Set V) (ds : List V)
    (hA : A = S ∪ Y) :
    guardResidLevel w x Y g O v A (d :: ds) S =
      guardResidLevel w x Y g O v (insert d A) ds (insert d S) -
        CSH.cshMarg (guardDecoyList w (insert d A) ds)
          (guardObsConst w O v (insert d A ∪ listSet ds))
          O ({v} : Set V) (guardResidMoment w x Y g d A) := by
  have hfinal : A ∪ listSet (d :: ds) =
      insert d A ∪ listSet ds := by
    ext u
    simp [listSet]
    tauto
  unfold guardResidLevel
  rw [guardDecoyList, hfinal]
  have hpoint : ∀ omega : BondConfig V,
      CSH.cshMarg
          ((({d} : Set V), guardAvoidConst w d A) ::
            guardDecoyList w (insert d A) ds)
          (guardObsConst w O v (insert d A ∪ listSet ds))
          O ({v} : Set V)
          (fun R => DecisionTree.ind (guardEv R S Y) omega) =
        CSH.cshMarg (guardDecoyList w (insert d A) ds)
          (guardObsConst w O v (insert d A ∪ listSet ds))
          O ({v} : Set V)
          (fun R => DecisionTree.ind (guardEv R (insert d S) Y) omega) -
        CSH.cshMarg (guardDecoyList w (insert d A) ds)
          (guardObsConst w O v (insert d A ∪ listSet ds))
          O ({v} : Set V)
          (fun R =>
            DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
              guardAvoidConst w d A R *
                DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega) -
        DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega *
          CSH.cshMarg (guardDecoyList w (insert d A) ds)
            (guardObsConst w O v (insert d A ∪ listSet ds))
            O ({v} : Set V) (guardAvoidConst w d A) := by
    intro omega
    change CSH.cshMarg (guardDecoyList w (insert d A) ds)
        (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
        (CSH.slStep (({d} : Set V), guardAvoidConst w d A)
          (fun R => DecisionTree.ind (guardEv R S Y) omega)) = _
    have hf : CSH.slStep (({d} : Set V), guardAvoidConst w d A)
          (fun R => DecisionTree.ind (guardEv R S Y) omega) =
        (fun R => DecisionTree.ind (guardEv R (insert d S) Y) omega) -
          (fun R => DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
            guardAvoidConst w d A R *
              DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega) -
          DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega •
            guardAvoidConst w d A := by
      funext R
      simp only [CSH.slStep, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      simpa only [mul_comm] using
        guard_decoy_split R S Y A d (guardAvoidConst w d A) omega hA
    rw [hf, cshMarg_sub, cshMarg_sub, CSH.cshMarg_smul]
  simp_rw [hpoint]
  have hmargin :
      ∑ omega : BondConfig V, BHK2006.weight (fun e => (w e : ℝ)) omega *
        (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
          CSH.cshMarg (guardDecoyList w (insert d A) ds)
            (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
            (fun R =>
              DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
                guardAvoidConst w d A R *
                  DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega)) =
        CSH.cshMarg (guardDecoyList w (insert d A) ds)
          (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
          (guardResidMoment w x Y g d A) := by
    let a : BondConfig V → ℝ := fun omega =>
      BHK2006.weight (fun e => (w e : ℝ)) omega *
        CSH.resid (fun e => (w e : ℝ)) x Y g omega
    let q : BondConfig V → Set V → ℝ := fun omega R =>
      DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
        guardAvoidConst w d A R *
          DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega
    have hq : (fun R : Set V => ∑ omega, a omega * q omega R) =
        guardResidMoment w x Y g d A := by
      funext R
      rw [guardResidMoment_eq_sum]
      exact Finset.sum_congr rfl fun omega _ => by
        simp only [a, q]
        ring
    have hnormalize :
        (∑ omega : BondConfig V,
          BHK2006.weight (fun e => (w e : ℝ)) omega *
            (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
              CSH.cshMarg (guardDecoyList w (insert d A) ds)
                (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
                (fun R =>
                  DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
                    guardAvoidConst w d A R *
                      DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega))) =
          ∑ omega, a omega *
            CSH.cshMarg (guardDecoyList w (insert d A) ds)
              (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
              (q omega) := by
      exact Finset.sum_congr rfl fun omega _ => by
        simp only [a, q]
        ring
    rw [hnormalize]
    have hlin := cshMarg_finset_sum
      (guardDecoyList w (insert d A) ds)
      (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
      (Finset.univ : Finset (BondConfig V)) a q
    rw [← hq]
    rw [← hlin]
    congr 1
    funext R
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hzero := residual_avoid_singleton_sum_zero w hm x Y g d
  let m : ℝ := CSH.cshMarg (guardDecoyList w (insert d A) ds)
    (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
    (guardAvoidConst w d A)
  have hlast :
      ∑ omega : BondConfig V, BHK2006.weight (fun e => (w e : ℝ)) omega *
        (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
          (DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega * m)) = 0 := by
    calc
      ∑ omega, BHK2006.weight (fun e => (w e : ℝ)) omega *
          (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
            (DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega * m)) =
          (∑ omega, BHK2006.weight (fun e => (w e : ℝ)) omega *
            (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
              DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega)) * m := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun omega _ => by ring
      _ = 0 := by rw [hzero, zero_mul]
  have hrearr : ∀ omega : BondConfig V,
      BHK2006.weight (fun e => (w e : ℝ)) omega *
          (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
            (CSH.cshMarg (guardDecoyList w (insert d A) ds)
                (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
                (fun R => DecisionTree.ind (guardEv R (insert d S) Y) omega) -
              CSH.cshMarg (guardDecoyList w (insert d A) ds)
                (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
                (fun R => DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
                  guardAvoidConst w d A R *
                    DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega) -
              DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega * m)) =
        (BHK2006.weight (fun e => (w e : ℝ)) omega *
          (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
            CSH.cshMarg (guardDecoyList w (insert d A) ds)
              (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
              (fun R => DecisionTree.ind (guardEv R (insert d S) Y) omega)) -
         BHK2006.weight (fun e => (w e : ℝ)) omega *
          (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
            CSH.cshMarg (guardDecoyList w (insert d A) ds)
              (guardObsConst w O v (insert d A ∪ listSet ds)) O ({v} : Set V)
              (fun R => DecisionTree.ind (guardEv R ({d} : Set V) A) omega -
                guardAvoidConst w d A R *
                  DecisionTree.ind (sourceAvoid ({d} : Set V) A) omega))) -
        BHK2006.weight (fun e => (w e : ℝ)) omega *
          (CSH.resid (fun e => (w e : ℝ)) x Y g omega *
            (DecisionTree.ind (sourceAvoid ({d} : Set V) Y) omega * m)) := by
    intro omega
    ring
  rw [Finset.sum_congr rfl (fun omega _ => hrearr omega),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, hmargin, hlast, sub_zero]

/-- A decoy step after inserting CGDI.  The two minus signs produce the
positive lower margin and the positive `Delta` term. -/
private theorem guardResidLevel_step_CGDI
    (w : Sym2 V → unitInterval)
    (hm : ∑ omega : BondConfig V,
      BHK2006.weight (fun e => (w e : ℝ)) omega = 1)
    (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ)
    (O : Set V) (v d : V) (A S : Set V) (ds : List V)
    (hAS : A = S ∪ Y) (hbase : insert x Y ⊆ A)
    (he : (prodBernoulli w).real (sourceAvoid ({d} : Set V) A) ≠ 0) :
    guardResidLevel w x Y g O v A (d :: ds) S =
      guardResidLevel w x Y g O v (insert d A) ds (insert d S) +
        ((prodBernoulli w).real (sourceAvoid ({d} : Set V) A))⁻¹ *
          guardCSHMargin w d A ds O v (CSH.phiT w x Y g d) +
        guardDelta w x Y g d A O := by
  rw [guardResidLevel_step w hm x Y g O v d A S ds hAS]
  let L := guardDecoyList w (insert d A) ds
  let p := guardObsConst w O v (insert d A ∪ listSet ds)
  let e := (prodBernoulli w).real (sourceAvoid ({d} : Set V) A)
  let gamma := guardCovD w d A (CSH.phiT w x Y g d)
  let delta := guardDelta w x Y g d A
  have hfun : guardResidMoment w x Y g d A =
      fun R => -(e⁻¹) * gamma R - delta R := by
    funext R
    exact guardResidMoment_eq w x Y g d A R hbase he
  have hlinear :
      CSH.cshMarg L p O ({v} : Set V)
          (fun R => -(e⁻¹) * gamma R - delta R) =
        -(e⁻¹) * CSH.cshMarg L p O ({v} : Set V) gamma -
          CSH.cshMarg L p O ({v} : Set V) delta := by
    have hsmul : (fun R => -(e⁻¹) * gamma R) = -(e⁻¹) • gamma := by
      funext R
      simp only [Pi.smul_apply, smul_eq_mul]
    change CSH.cshMarg L p O ({v} : Set V)
        ((fun R => -(e⁻¹) * gamma R) - delta) = _
    rw [cshMarg_sub, hsmul, CSH.cshMarg_smul]
  obtain ⟨coeff, hshape⟩ := guard_tail_shape w (insert d A) ds O v
  have hdelta : CSH.cshMarg L p O ({v} : Set V) delta = delta O := by
    change CSH.cshMarg (guardDecoyList w (insert d A) ds)
        (guardObsConst w O v (insert d A ∪ listSet ds))
        O ({v} : Set V) (guardDelta w x Y g d A) =
      guardDelta w x Y g d A O
    rw [hshape (guardDelta w x Y g d A)]
    simp only [guardDelta_singleton_eq_zero, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hfun, hlinear, hdelta]
  change guardResidLevel w x Y g O v (insert d A) ds (insert d S) -
      (-(e⁻¹) *
          guardCSHMargin w d A ds O v (CSH.phiT w x Y g d) - delta O) =
    guardResidLevel w x Y g O v (insert d A) ds (insert d S) +
      e⁻¹ * guardCSHMargin w d A ds O v (CSH.phiT w x Y g d) +
        delta O
  ring

/-- Iteration of the corrected one-step identity along a guarded decoy list. -/
private theorem guardResidLevel_unfold
    (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ)
    (O : Set V) (v : V) :
    ∀ (D : List V) (A S : Set V), D.Nodup →
      (∀ d ∈ D, d ∉ A) → insert x Y ⊆ A → A = S ∪ Y →
      guardResidLevel w x Y g O v A D S =
        guardResidLevel w x Y g O v (A ∪ listSet D) []
          (S ∪ listSet D) +
        guardUnfoldTerms w x Y g O v A D := by
  have hm : ∑ omega : BondConfig V,
      BHK2006.weight (fun e => (w e : ℝ)) omega = 1 := by
    have h := BHK2006.integral_prodBernoulli_eq_sum w
      (fun _ : BondConfig V => (1 : ℝ))
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
    exact h.symm
  intro D
  induction D with
  | nil =>
      intro A S _ _ _ _
      have hempty : listSet ([] : List V) = (∅ : Set V) := by
        ext q
        simp [listSet]
      rw [hempty, union_empty, union_empty]
      simp only [guardUnfoldTerms, add_zero]
  | cons d ds ih =>
      intro A S hnd hout hbase hAS
      have hdA : d ∉ A := hout d List.mem_cons_self
      have hdsnd : ds.Nodup := (List.nodup_cons.1 hnd).2
      have hd_ds : d ∉ ds := (List.nodup_cons.1 hnd).1
      have hout' : ∀ q ∈ ds, q ∉ insert d A := by
        intro q hq hqin
        rcases Set.mem_insert_iff.1 hqin with hqd | hqA
        · exact hd_ds (hqd ▸ hq)
        · exact hout q (List.mem_cons_of_mem d hq) hqA
      have hbase' : insert x Y ⊆ insert d A :=
        fun q hq => Set.mem_insert_of_mem d (hbase hq)
      have hAS' : insert d A = insert d S ∪ Y := by
        rw [hAS, Set.insert_union]
      have he : (prodBernoulli w).real
          (sourceAvoid ({d} : Set V) A) ≠ 0 := by
        have hs := CSH.sum_ind_avoidEv_ne_zero w hw hdA
        rw [← TwoAvoidanceSets.real_eq_sum_ind,
          ← KNAll.Guarded.sourceAvoid_singleton] at hs
        exact hs
      have hstep := guardResidLevel_step_CGDI w hm x Y g O v d A S ds
        hAS hbase he
      have htail := ih (insert d A) (insert d S) hdsnd hout' hbase' hAS'
      have hAfinal : insert d A ∪ listSet ds =
          A ∪ listSet (d :: ds) := by
        ext q
        simp [listSet]
        tauto
      have hSfinal : insert d S ∪ listSet ds =
          S ∪ listSet (d :: ds) := by
        ext q
        simp [listSet]
        tauto
      rw [hstep, htail, hAfinal, hSfinal]
      simp only [guardUnfoldTerms]
      ring

/-! ## Markov merge at the complete `Y`-cluster -/

/-- `CSH.markov_merge_Y` with a test that may also read the complete exposed
edge cluster of `Y`. -/
private theorem markov_merge_Y_kernel (w : Sym2 V → ℝ)
    (hm : ∑ omega : BondConfig V, BHK2006.weight w omega = 1)
    (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ)
    (psi : Set (Sym2 V) → BondConfig V → ℝ) :
    ∑ omega : BondConfig V, BHK2006.weight w omega *
      (DecisionTree.ind (HullPort.avoidEv x Y) omega *
        (∑ eta : BondConfig V, BHK2006.weight w eta *
          ((g (openEdgeCluster
              (eta \ HullPort.cut Y omega) x) -
            CSH.wmeanOff w Y (fun beta => g (openEdgeCluster beta x)) omega) *
            psi (BHK2006.setCl omega Y)
              (eta \ HullPort.cut Y omega)))) =
      ∑ zeta : BondConfig V, BHK2006.weight w zeta *
        (CSH.resid w x Y g zeta *
          psi (BHK2006.setCl zeta Y)
            (zeta \ HullPort.cut Y zeta)) := by
  classical
  let K : Set (Sym2 V) → BondConfig V → ℝ := fun W beta =>
    (if x ∈ Y ∨ ∃ e ∈ W, x ∈ e then 0 else 1) *
      ((g (openEdgeCluster beta x) -
          ∑ eta', BHK2006.weight w eta' *
            g (openEdgeCluster
              (eta' \ BHK2006.barOf Y W) x)) * psi W beta)
  have hind : ∀ zeta : BondConfig V,
      DecisionTree.ind (HullPort.avoidEv x Y) zeta =
        if x ∈ Y ∨ ∃ e ∈ BHK2006.setCl zeta Y, x ∈ e
        then 0 else 1 := by
    intro zeta
    by_cases h : x ∈ Y ∨ ∃ e ∈ BHK2006.setCl zeta Y, x ∈ e
    · rw [if_pos h, DecisionTree.ind_of_not_mem
        (fun h' => (CSH.mem_avoidEv_iff_notMem_span x Y zeta).1 h' h)]
    · rw [if_neg h, DecisionTree.ind_of_mem
        ((CSH.mem_avoidEv_iff_notMem_span x Y zeta).2 h)]
  have hmean : ∀ zeta : BondConfig V,
      CSH.wmeanOff w Y (fun beta => g (openEdgeCluster beta x)) zeta =
        ∑ eta', BHK2006.weight w eta' *
          g (openEdgeCluster
            (eta' \ BHK2006.barOf Y (BHK2006.setCl zeta Y)) x) := by
    intro zeta
    rw [CSH.wmeanOff, HullPort.cut_eq_barOf]
  have key := HullPort.set_sum_cond_sdiff w hm Y K
  have hR : ∀ omega : BondConfig V,
      BHK2006.weight w omega *
          (∑ eta, BHK2006.weight w eta *
            K (BHK2006.setCl omega Y)
              (eta \ BHK2006.barOf Y (BHK2006.setCl omega Y))) =
        BHK2006.weight w omega *
          (DecisionTree.ind (HullPort.avoidEv x Y) omega *
            (∑ eta, BHK2006.weight w eta *
              ((g (openEdgeCluster (eta \ HullPort.cut Y omega) x) -
                  CSH.wmeanOff w Y
                    (fun beta => g (openEdgeCluster beta x)) omega) *
                psi (BHK2006.setCl omega Y)
                  (eta \ HullPort.cut Y omega)))) := by
    intro omega
    rw [hind, hmean, HullPort.cut_eq_barOf]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun eta _ => by
      simp only [K]
      ring
  have hL : ∀ zeta : BondConfig V,
      BHK2006.weight w zeta *
          K (BHK2006.setCl zeta Y)
            (zeta \ BHK2006.barOf Y (BHK2006.setCl zeta Y)) =
        BHK2006.weight w zeta *
          (CSH.resid w x Y g zeta *
            psi (BHK2006.setCl zeta Y)
              (zeta \ HullPort.cut Y zeta)) := by
    intro zeta
    simp only [K]
    unfold CSH.resid
    rw [hind, hmean, HullPort.cut_eq_barOf]
    by_cases h : x ∈ Y ∨
        ∃ e ∈ BHK2006.setCl zeta Y, x ∈ e
    · rw [if_pos h]
      ring
    · have hz : zeta ∈ HullPort.avoidEv x Y :=
        (CSH.mem_avoidEv_iff_notMem_span x Y zeta).2 h
      have hcluster := CSH.openEdgeCluster_sdiff_cut_of_avoid hz
      rw [HullPort.cut_eq_barOf] at hcluster
      rw [if_neg h, hcluster]
      ring
  calc
    ∑ omega, BHK2006.weight w omega *
        (DecisionTree.ind (HullPort.avoidEv x Y) omega *
          (∑ eta, BHK2006.weight w eta *
            ((g (openEdgeCluster (eta \ HullPort.cut Y omega) x) -
                CSH.wmeanOff w Y
                  (fun beta => g (openEdgeCluster beta x)) omega) *
              psi (BHK2006.setCl omega Y)
                (eta \ HullPort.cut Y omega)))) =
      ∑ omega, BHK2006.weight w omega *
        (∑ eta, BHK2006.weight w eta *
          K (BHK2006.setCl omega Y)
            (eta \ BHK2006.barOf Y (BHK2006.setCl omega Y))) :=
        Finset.sum_congr rfl fun omega _ => (hR omega).symm
    _ = ∑ zeta, BHK2006.weight w zeta *
        K (BHK2006.setCl zeta Y)
          (zeta \ BHK2006.barOf Y (BHK2006.setCl zeta Y)) := key.symm
    _ = _ := Finset.sum_congr rfl fun zeta _ => hL zeta

private theorem twoClusterCondCovFirst_eq_sum
    (w : Sym2 V → ℝ) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ)
    (omega : BondConfig V) :
    twoClusterCondCovFirst w ({x} : Set V) Y g h
        (BHK2006.setCl omega Y) =
      ∑ eta : BondConfig V, BHK2006.weight w eta *
        ((g (openEdgeCluster (eta \ HullPort.cut Y omega) x) -
            CSH.wmeanOff w Y (fun beta => g (openEdgeCluster beta x)) omega) *
          h (BHK2006.setCl (eta \ HullPort.cut Y omega) ({x} : Set V))
            (BHK2006.setCl omega Y)) := by
  unfold twoClusterCondCovFirst BHK2006.condS BHK2006.halfS CSH.wmeanOff
  simp only [BHK2006.setCl_singleton, HullPort.cut_eq_barOf]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun eta _ => by ring

private theorem twoClusterWithinFirst_eq_resid
    (w : Sym2 V → ℝ)
    (hm : ∑ omega : BondConfig V, BHK2006.weight w omega = 1)
    (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ) :
    twoClusterWithinFirst w ({x} : Set V) Y
        (HullPort.avoidEv x Y) g h =
      ∑ zeta : BondConfig V, BHK2006.weight w zeta *
        (CSH.resid w x Y g zeta *
          h (BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V))
            (BHK2006.setCl zeta Y)) := by
  unfold twoClusterWithinFirst
  simp_rw [twoClusterCondCovFirst_eq_sum]
  have hmerge := markov_merge_Y_kernel w hm x Y g
    (fun W beta => h (BHK2006.setCl beta ({x} : Set V)) W)
  rw [← hmerge]
  exact Finset.sum_congr rfl fun omega _ => by ring

/-! ## Reading the guarded two-cluster test after the merge -/

private theorem guardContactTest_world_eq_ind (x : V) (Y R : Set V)
    (zeta : BondConfig V) (hzeta : zeta ∈ HullPort.avoidEv x Y) :
    guardContactTest x Y R
        (BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V))
        (BHK2006.setCl zeta Y) =
      DecisionTree.ind (guardEv R ({x} : Set V) Y) zeta := by
  have hxedge := CSH.openEdgeCluster_sdiff_cut_of_avoid hzeta
  have hxcarrier :
      insert x {u | ∃ e ∈
          BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V), u ∈ e} =
        openCluster zeta x := by
    rw [BHK2006.setCl_singleton, hxedge,
      ← CSH.openCluster_eq_insert_span]
  have hYcarrier :
      Y ∪ {u | ∃ e ∈ BHK2006.setCl zeta Y, u ∈ e} =
        sourceCluster zeta Y := by
    rw [sourceCluster_eq_sourceCarrier]
    ext u
    simp only [sourceCarrier, Set.mem_union, Set.mem_setOf_eq]
  have hcontact :
      ((openCluster zeta x ∩ R).Nonempty) ↔
        zeta ∈ sourceConn R ({x} : Set V) := by
    constructor
    · rintro ⟨u, hux, huR⟩
      exact ⟨u, huR, x, Set.mem_singleton x, hux.symm⟩
    · rintro ⟨r, hr, q, hq, hrq⟩
      rw [Set.mem_singleton_iff] at hq
      subst q
      exact ⟨r, hrq.symm, hr⟩
  have havoid : Disjoint (sourceCluster zeta Y) R ↔
      zeta ∈ sourceAvoid R Y := by
    constructor
    · intro hdis r hr y hy hry
      exact Set.disjoint_left.1 hdis
        (show r ∈ sourceCluster zeta Y from by
          unfold sourceCluster
          exact Set.mem_iUnion_of_mem y
            (Set.mem_iUnion_of_mem hy hry.symm)) hr
    · intro hav
      refine Set.disjoint_left.2 ?_
      intro u huY huR
      unfold sourceCluster at huY
      simp only [Set.mem_iUnion, exists_prop] at huY
      obtain ⟨y, hy, hyu⟩ := huY
      exact hav u huR y hy hyu.symm
  have hp :
      ((insert x {u | ∃ e ∈
          BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V), u ∈ e} ∩ R).Nonempty ∧
        Disjoint (Y ∪ {u | ∃ e ∈ BHK2006.setCl zeta Y, u ∈ e}) R) ↔
        zeta ∈ guardEv R ({x} : Set V) Y := by
    rw [hxcarrier, hYcarrier, hcontact, havoid]
    exact and_comm
  unfold guardContactTest
  by_cases h : zeta ∈ guardEv R ({x} : Set V) Y
  · rw [if_pos (hp.2 h), DecisionTree.ind_of_mem h]
  · rw [if_neg (fun h' => h (hp.1 h')), DecisionTree.ind_of_not_mem h]

private theorem guardEvalTest_world_eq_ind (x : V) (Y O R : Set V)
    (zeta : BondConfig V) (hzeta : zeta ∈ HullPort.avoidEv x Y) :
    guardEvalTest x Y O R
        (BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V))
        (BHK2006.setCl zeta Y) =
      DecisionTree.ind (guardEv R ({x} : Set V) Y) zeta := by
  unfold guardEvalTest
  by_cases hRO : R = O
  · rw [if_pos hRO]
    exact guardContactTest_world_eq_ind x Y R zeta hzeta
  · rw [if_neg hRO]
    by_cases hs : ∃ u : V, R = ({u} : Set V)
    · rw [dif_pos hs]
      let u := Classical.choose hs
      have hRu : R = ({u} : Set V) := Classical.choose_spec hs
      have hxedge := CSH.openEdgeCluster_sdiff_cut_of_avoid hzeta
      have hxcarrier :
          insert x {q | ∃ e ∈
              BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V), q ∈ e} =
            openCluster zeta x := by
        rw [BHK2006.setCl_singleton, hxedge,
          ← CSH.openCluster_eq_insert_span]
      have hp : u ∈ openCluster zeta x ↔
          zeta ∈ guardEv R ({x} : Set V) Y := by
        rw [hRu]
        constructor
        · intro hxu
          refine ⟨?_, ⟨u, Set.mem_singleton u, x,
            Set.mem_singleton x, hxu.symm⟩⟩
          intro q hq y hy hqy
          rw [Set.mem_singleton_iff] at hq
          subst q
          exact hzeta y hy (hxu.trans hqy)
        · rintro ⟨_, ⟨q, hq, t, ht, hqt⟩⟩
          rw [Set.mem_singleton_iff] at hq ht
          subst q
          subst t
          exact hqt.symm
      change (if u ∈ insert x {q | ∃ e ∈
          BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V), q ∈ e}
        then 1 else 0) = _
      have hmem : u ∈ insert x {q | ∃ e ∈
          BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V), q ∈ e} ↔
          u ∈ openCluster zeta x := by rw [hxcarrier]
      by_cases hu : u ∈ openCluster zeta x
      · rw [if_pos (hmem.2 hu), DecisionTree.ind_of_mem (hp.1 hu)]
      · rw [if_neg (fun h => hu (hmem.1 h)),
          DecisionTree.ind_of_not_mem (fun h => hu (hp.2 h))]
    · rw [dif_neg hs]
      exact guardContactTest_world_eq_ind x Y R zeta hzeta

private theorem guardLevelTest_world_eq (w : Sym2 V → unitInterval)
    (x : V) (Y : Set V) (D : List V) (O : Set V) (v : V)
    (zeta : BondConfig V) (hzeta : zeta ∈ HullPort.avoidEv x Y) :
    guardLevelTest w x Y D O v
        (BHK2006.setCl (zeta \ HullPort.cut Y zeta) ({x} : Set V))
        (BHK2006.setCl zeta Y) =
      CSH.cshMarg (guardDecoyList w (insert x Y) D)
        (guardObsConst w O v (insert x Y ∪ listSet D)) O ({v} : Set V)
        (fun R => DecisionTree.ind (guardEv R ({x} : Set V) Y) zeta) := by
  unfold guardLevelTest
  congr 1
  funext R
  exact guardEvalTest_world_eq_ind x Y O R zeta hzeta

private theorem guardWithin_eq_guardResidLevel
    (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (D : List V)
    (O : Set V) (v : V) (g : Set (Sym2 V) → ℝ) :
    guardWithin w x Y D O v g =
      guardResidLevel w x Y g O v (insert x Y) D ({x} : Set V) := by
  have hm : ∑ omega : BondConfig V,
      BHK2006.weight (fun e => (w e : ℝ)) omega = 1 := by
    have h := BHK2006.integral_prodBernoulli_eq_sum w
      (fun _ : BondConfig V => (1 : ℝ))
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
    exact h.symm
  unfold guardWithin
  rw [KNAll.Guarded.sourceAvoid_singleton,
    twoClusterWithinFirst_eq_resid (fun e => (w e : ℝ)) hm]
  unfold guardResidLevel
  exact Finset.sum_congr rfl fun zeta _ => by
    by_cases hzeta : zeta ∈ HullPort.avoidEv x Y
    · rw [guardLevelTest_world_eq w x Y D O v zeta hzeta]
    · unfold CSH.resid
      rw [DecisionTree.ind_of_not_mem hzeta]
      ring

/-! ## The no-decoy residual level is the horizontal term -/

private def sourceAvoidClusterInd (R Y : Set V)
    (W : Set (Sym2 V)) : ℝ :=
  if ∀ r ∈ R, ¬ (r ∈ Y ∨ ∃ e ∈ W, r ∈ e) then 1 else 0

private theorem sourceAvoidClusterInd_setCl (R Y : Set V)
    (omega : BondConfig V) :
    sourceAvoidClusterInd R Y (BHK2006.setCl omega Y) =
      DecisionTree.ind (sourceAvoid R Y) omega := by
  have hp : (∀ r ∈ R, ¬ (r ∈ Y ∨
      ∃ e ∈ BHK2006.setCl omega Y, r ∈ e)) ↔
      omega ∈ sourceAvoid R Y := by
    constructor
    · intro h r hr y hy hry
      exact h r hr ((BHK2006.setReach_iff omega Y r).1
        ⟨y, hy, hry.symm⟩)
    · intro h r hr hreach
      obtain ⟨y, hy, hyr⟩ := (BHK2006.setReach_iff omega Y r).2 hreach
      exact h r hr y hy hyr.symm
  unfold sourceAvoidClusterInd
  by_cases h : omega ∈ sourceAvoid R Y
  · rw [if_pos (hp.2 h), DecisionTree.ind_of_mem h]
  · rw [if_neg (fun h' => h (hp.1 h')),
      DecisionTree.ind_of_not_mem h]

private theorem inducedWeight_sourceCluster (w : Sym2 V → unitInterval)
    (Y : Set V) (omega : BondConfig V) :
    inducedWeight w (Set.univ \ sourceCluster omega Y) =
      fun e => if e ∈ HullPort.cut Y omega then 0 else w e := by
  have hcut : HullPort.cut Y omega = CSH.edgesOf (sourceCluster omega Y) := by
    rw [HullPort.cut_eq_barOf, barOf_eq_edgesOf_sourceCarrier,
      ← sourceCluster_eq_sourceCarrier]
  funext e
  rw [hcut]
  unfold inducedWeight CSH.edgesOf
  simp only [Set.mem_setOf_eq]
  by_cases he : ∃ u ∈ e, u ∈ sourceCluster omega Y
  · rw [if_pos he, if_neg]
    rintro hall
    obtain ⟨u, hue, huY⟩ := he
    exact (hall u hue).2 huY
  · rw [if_neg he, if_pos]
    intro u hue
    exact ⟨Set.mem_univ u, fun huY => he ⟨u, hue, huY⟩⟩

private theorem inducedWeight_sourceCluster_off
    (w : Sym2 V → unitInterval) (Y : Set V) (omega : BondConfig V) :
    inducedWeight w (Set.univ \ sourceCluster omega Y) =
      fun e => if (∃ u ∈ e, ∃ y ∈ Y,
        (openGraph omega).Reachable y u) then (0 : unitInterval) else w e := by
  rw [inducedWeight_sourceCluster]
  funext e
  simp only [HullPort.cut, Set.mem_setOf_eq]
  by_cases he : ∃ u ∈ e, ∃ y ∈ Y,
      (openGraph omega).Reachable y u
  · simp only [if_pos he]
  · simp only [if_neg he]

private theorem mem_world_of_avoid (R Y : Set V) (omega : BondConfig V)
    (havoid : omega ∈ sourceAvoid R Y) :
    R ⊆ Set.univ \ sourceCluster omega Y := by
  intro r hr
  refine ⟨Set.mem_univ r, ?_⟩
  intro hrY
  unfold sourceCluster at hrY
  simp only [Set.mem_iUnion, exists_prop] at hrY
  obtain ⟨y, hy, hyr⟩ := hrY
  exact havoid r hr y hy hyr.symm

private theorem sourceWorldCov_eq_wcovOff_of_weight
    (w : Sym2 V → unitInterval) (x : V) (Y R X U : Set V)
    (g : Set (Sym2 V) → ℝ) (omega : BondConfig V)
    (hxU : x ∈ U)
    (hweight : inducedWeight w U =
      fun e => if (∃ u ∈ e, ∃ y ∈ Y,
        (openGraph omega).Reachable y u) then (0 : unitInterval) else w e) :
    sourceWorldCov w U x g R X =
      CSH.wcovOff (fun e => (w e : ℝ)) Y
        (fun beta => g (openEdgeCluster beta x))
        (DecisionTree.ind (sourceConn (R ∩ U) (X ∩ U))) omega := by
  unfold sourceWorldCov worldProb
  rw [if_pos hxU, hweight]
  rw [← CSH.world_cov_eq_wcovOff w Y omega
    (fun beta => g (openEdgeCluster beta x))
    (sourceConn (R ∩ U) (X ∩ U))]
  refine congrArg₂ (fun a b : ℝ => a - b) ?_ ?_
  · apply congrArg (fun mu : Measure (BondConfig V) =>
      ∫ beta in sourceConn (R ∩ U) (X ∩ U),
        g (openEdgeCluster beta x) ∂mu)
    apply congrArg prodBernoulli
    funext e
    by_cases he : ∃ u ∈ e, ∃ y ∈ Y,
        (openGraph omega).Reachable y u
    · simp only [if_pos he]
    · simp only [if_neg he]
  · refine congrArg₂ (fun a b : ℝ => a * b) ?_ ?_
    · apply congrArg (fun mu : Measure (BondConfig V) =>
        ∫ beta, g (openEdgeCluster beta x) ∂mu)
      apply congrArg prodBernoulli
      funext e
      by_cases he : ∃ u ∈ e, ∃ y ∈ Y,
          (openGraph omega).Reachable y u
      · simp only [if_pos he]
      · simp only [if_neg he]
    · apply congrArg (fun mu : Measure (BondConfig V) =>
        mu.real (sourceConn (R ∩ U) (X ∩ U)))
      apply congrArg prodBernoulli
      funext e
      by_cases he : ∃ u ∈ e, ∃ y ∈ Y,
          (openGraph omega).Reachable y u
      · simp only [if_pos he]
      · simp only [if_neg he]

private theorem sourceWorldCov_eq_wcovOff
    (w : Sym2 V → unitInterval) (x : V) (Y R X : Set V)
    (g : Set (Sym2 V) → ℝ) (omega : BondConfig V)
    (hx : omega ∈ HullPort.avoidEv x Y) :
    sourceWorldCov w (Set.univ \ sourceCluster omega Y) x g R X =
      CSH.wcovOff (fun e => (w e : ℝ)) Y
        (fun beta => g (openEdgeCluster beta x))
        (DecisionTree.ind
          (sourceConn (R ∩ (Set.univ \ sourceCluster omega Y))
            (X ∩ (Set.univ \ sourceCluster omega Y)))) omega := by
  have hxU : x ∈ Set.univ \ sourceCluster omega Y := by
    refine ⟨Set.mem_univ x, ?_⟩
    intro hxY
    unfold sourceCluster at hxY
    simp only [Set.mem_iUnion, exists_prop] at hxY
    obtain ⟨y, hy, hyx⟩ := hxY
    exact hx y hy hyx.symm
  exact sourceWorldCov_eq_wcovOff_of_weight w x Y R X
    (Set.univ \ sourceCluster omega Y) g omega hxU
    (inducedWeight_sourceCluster_off w Y omega)

private theorem sourceWorldGuardInd_eq (R X Y : Set V)
    (zeta : BondConfig V) :
    sourceAvoidClusterInd R Y (BHK2006.setCl zeta Y) *
        DecisionTree.ind
          (sourceConn
            (R ∩ (Set.univ \ sourceCluster zeta Y))
            (X ∩ (Set.univ \ sourceCluster zeta Y)))
          (zeta \ HullPort.cut Y zeta) =
      DecisionTree.ind (guardEv R X Y) zeta := by
  rw [sourceAvoidClusterInd_setCl]
  by_cases hav : zeta ∈ sourceAvoid R Y
  · rw [DecisionTree.ind_of_mem hav, one_mul]
    have hRU := mem_world_of_avoid R Y zeta hav
    have hconn :
        zeta \ HullPort.cut Y zeta ∈
            sourceConn
              (R ∩ (Set.univ \ sourceCluster zeta Y))
              (X ∩ (Set.univ \ sourceCluster zeta Y)) ↔
          zeta ∈ sourceConn R X := by
      constructor
      · rintro ⟨r, hr, q, hq, hrq⟩
        exact ⟨r, hr.1, q, hq.1,
          hrq.mono (SimpleGraph.fromEdgeSet_mono Set.sdiff_subset)⟩
      · rintro ⟨r, hr, q, hq, hrq⟩
        have hrAvoid : zeta ∈ HullPort.avoidEv r Y :=
          fun y hy => hav r hr y hy
        have hrq' := (CSH.reachable_sdiff_cut_iff_of_avoid hrAvoid q).2 hrq
        have hqU : q ∈ Set.univ \ sourceCluster zeta Y := by
          refine ⟨Set.mem_univ q, ?_⟩
          intro hqY
          unfold sourceCluster at hqY
          simp only [Set.mem_iUnion, exists_prop] at hqY
          obtain ⟨y, hy, hyq⟩ := hqY
          exact hav r hr y hy (hrq.trans hyq.symm)
        exact ⟨r, ⟨hr, hRU hr⟩, q, ⟨hq, hqU⟩, hrq'⟩
    by_cases hc : zeta ∈ sourceConn R X
    · rw [DecisionTree.ind_of_mem (hconn.2 hc),
        DecisionTree.ind_of_mem (show zeta ∈ guardEv R X Y from ⟨hav, hc⟩)]
    · rw [DecisionTree.ind_of_not_mem (fun h => hc (hconn.1 h)),
        DecisionTree.ind_of_not_mem (fun h => hc h.2)]
  · rw [DecisionTree.ind_of_not_mem hav, zero_mul,
      DecisionTree.ind_of_not_mem (fun h => hav h.1)]

/-- A single explicitly guarded source covariance merges to its global
residual moment. -/
private theorem sourceHorizontalTerm_eq_resid
    (w : Sym2 V → unitInterval) (x : V) (Y R X : Set V)
    (g : Set (Sym2 V) → ℝ) :
    (∫ omega in sourceAvoid ({x} : Set V) Y ∩ sourceAvoid R Y,
      sourceWorldCov w (Set.univ \ sourceCluster omega Y) x g R X
        ∂(prodBernoulli w)) =
      ∑ zeta : BondConfig V,
        BHK2006.weight (fun e => (w e : ℝ)) zeta *
          (CSH.resid (fun e => (w e : ℝ)) x Y g zeta *
            DecisionTree.ind (guardEv R X Y) zeta) := by
  let wr : Sym2 V → ℝ := fun e => (w e : ℝ)
  have hm : ∑ omega : BondConfig V, BHK2006.weight wr omega = 1 := by
    have h := BHK2006.integral_prodBernoulli_eq_sum w
      (fun _ : BondConfig V => (1 : ℝ))
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
    exact h.symm
  let psi : Set (Sym2 V) → BondConfig V → ℝ := fun W beta =>
    sourceAvoidClusterInd R Y W *
      DecisionTree.ind
        (sourceConn
          (R ∩ (Set.univ \ sourceCarrier Y W))
          (X ∩ (Set.univ \ sourceCarrier Y W))) beta
  have hmerge := markov_merge_Y_kernel wr hm x Y g psi
  rw [CSH.setIntegral_eq_sum_ind]
  calc
    ∑ omega, BHK2006.weight wr omega *
        (DecisionTree.ind
            (sourceAvoid ({x} : Set V) Y ∩ sourceAvoid R Y) omega *
          sourceWorldCov w (Set.univ \ sourceCluster omega Y) x g R X) =
      ∑ omega, BHK2006.weight wr omega *
        (DecisionTree.ind (HullPort.avoidEv x Y) omega *
          (∑ eta, BHK2006.weight wr eta *
            ((g (openEdgeCluster (eta \ HullPort.cut Y omega) x) -
                CSH.wmeanOff wr Y
                  (fun beta => g (openEdgeCluster beta x)) omega) *
              psi (BHK2006.setCl omega Y)
                (eta \ HullPort.cut Y omega)))) := by
        refine Finset.sum_congr rfl fun omega _ => ?_
        by_cases hx : omega ∈ HullPort.avoidEv x Y
        · rw [DecisionTree.ind_of_mem hx,
              sourceWorldCov_eq_wcovOff w x Y R X g omega hx,
              CSH.wcovOff_eq_sum]
          rw [← KNAll.Guarded.sourceAvoid_singleton] at hx
          by_cases hR : omega ∈ sourceAvoid R Y
          · rw [DecisionTree.ind_of_mem
                (show omega ∈ sourceAvoid ({x} : Set V) Y ∩
                    sourceAvoid R Y from ⟨hx, hR⟩)]
            simp only [psi]
            rw [sourceAvoidClusterInd_setCl,
              DecisionTree.ind_of_mem hR, one_mul,
              ← sourceCluster_eq_sourceCarrier omega Y]
            simp only [one_mul]
            rfl
          · rw [DecisionTree.ind_of_not_mem
                (fun h => hR h.2)]
            simp only [psi]
            rw [sourceAvoidClusterInd_setCl,
              DecisionTree.ind_of_not_mem hR]
            simp only [zero_mul, mul_zero, Finset.sum_const_zero]
        · have hx' : omega ∉ sourceAvoid ({x} : Set V) Y := by
              rw [KNAll.Guarded.sourceAvoid_singleton]
              exact hx
          rw [DecisionTree.ind_of_not_mem
              (fun h => hx' h.1), DecisionTree.ind_of_not_mem hx]
          ring
    _ = ∑ zeta, BHK2006.weight wr zeta *
        (CSH.resid wr x Y g zeta *
          psi (BHK2006.setCl zeta Y)
            (zeta \ HullPort.cut Y zeta)) := hmerge
    _ = _ := Finset.sum_congr rfl fun zeta _ => by
      simp only [psi]
      rw [← sourceCluster_eq_sourceCarrier zeta Y]
      rw [sourceWorldGuardInd_eq]

private theorem sourceWorldCov_singleton_zero
    (w : Sym2 V → unitInterval) (x v : V) (Y X : Set V)
    (g : Set (Sym2 V) → ℝ) (omega : BondConfig V)
    (hx : omega ∈ sourceAvoid ({x} : Set V) Y)
    (hv : omega ∉ sourceAvoid ({v} : Set V) Y) :
    sourceWorldCov w (Set.univ \ sourceCluster omega Y) x g
      ({v} : Set V) X = 0 := by
  have hxU : x ∈ Set.univ \ sourceCluster omega Y := by
    exact mem_world_of_avoid ({x} : Set V) Y omega hx
      (Set.mem_singleton x)
  have hvU : v ∉ Set.univ \ sourceCluster omega Y := by
    intro hvU
    apply hv
    intro q hq y hy hqy
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact hvU.2 (by
      unfold sourceCluster
      exact Set.mem_iUnion_of_mem y
        (Set.mem_iUnion_of_mem hy hqy.symm))
  have hinter : ({v} : Set V) ∩
      (Set.univ \ sourceCluster omega Y) = ∅ := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hqv, hqU⟩
    rw [Set.mem_singleton_iff] at hqv
    exact hvU (hqv ▸ hqU)
  unfold sourceWorldCov
  rw [if_pos hxU, hinter]
  have hconn : sourceConn (∅ : Set V)
      (X ∩ (Set.univ \ sourceCluster omega Y)) = ∅ := by
    ext beta
    simp [sourceConn]
  rw [hconn]
  simp [worldProb]

private theorem singletonHorizontal_restrict
    (w : Sym2 V → unitInterval) (x v : V) (Y X : Set V)
    (g : Set (Sym2 V) → ℝ) :
    (∫ omega in sourceAvoid ({x} : Set V) Y,
      sourceWorldCov w (Set.univ \ sourceCluster omega Y) x g
        ({v} : Set V) X ∂(prodBernoulli w)) =
    ∫ omega in sourceAvoid ({x} : Set V) Y ∩ sourceAvoid ({v} : Set V) Y,
      sourceWorldCov w (Set.univ \ sourceCluster omega Y) x g
        ({v} : Set V) X ∂(prodBernoulli w) := by
  rw [CSH.setIntegral_eq_sum_ind, CSH.setIntegral_eq_sum_ind]
  exact Finset.sum_congr rfl fun omega _ => by
    by_cases hx : omega ∈ sourceAvoid ({x} : Set V) Y
    · by_cases hv : omega ∈ sourceAvoid ({v} : Set V) Y
      · rw [DecisionTree.ind_of_mem hx,
          DecisionTree.ind_of_mem (show omega ∈
            sourceAvoid ({x} : Set V) Y ∩ sourceAvoid ({v} : Set V) Y
            from ⟨hx, hv⟩)]
      · rw [DecisionTree.ind_of_mem hx,
          DecisionTree.ind_of_not_mem (fun h => hv h.2),
          sourceWorldCov_singleton_zero w x v Y X g omega hx hv]
        ring
    · rw [DecisionTree.ind_of_not_mem hx,
        DecisionTree.ind_of_not_mem (fun h => hx h.1)]

private theorem guardHorizontal_eq_guardResidLevel
    (w : Sym2 V → unitInterval) (x : V) (Y S O : Set V) (v : V)
    (g : Set (Sym2 V) → ℝ) :
    guardHorizontal w x Y S O v g =
      guardResidLevel w x Y g O v (S ∪ Y) [] S := by
  have hO := sourceHorizontalTerm_eq_resid w x Y O S g
  have hv := sourceHorizontalTerm_eq_resid w x Y ({v} : Set V) S g
  have hvrest := singletonHorizontal_restrict w x v Y S g
  unfold guardHorizontal
  rw [hvrest, hO, hv]
  unfold guardResidLevel
  have hempty : listSet ([] : List V) = (∅ : Set V) := by
    ext q
    simp [listSet]
  rw [hempty, union_empty]
  simp only [guardDecoyList, CSH.cshMarg_nil]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun zeta _ => by ring

/-- Spec §4.4: the exact corrected unfolding.  The lower-level and correction
terms occur with the audited `+` sign. -/
theorem guard_oneSided_unfold (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (s₁ s₂ v : V) (g : Set (Sym2 V) → ℝ)
    (hadm : PairGuardAdmissible x Y D s₁ s₂ v) (_hg : Monotone g) :
    guardWithin w x Y D ({s₁, s₂} : Set V) v g =
      guardHorizontal w x Y (insert x (listSet D)) ({s₁, s₂} : Set V) v g +
        guardUnfoldTerms w x Y g ({s₁, s₂} : Set V) v (insert x Y) D := by
  obtain ⟨_, _, _, hnd, hD, _⟩ := hadm
  have hout : ∀ d ∈ D, d ∉ insert x Y := fun d hd => (hD d hd).1
  have hAS : insert x Y = ({x} : Set V) ∪ Y := by
    ext q
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  have hAfin : insert x Y ∪ listSet D =
      insert x (listSet D) ∪ Y := by
    ext q
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  have hSfin : ({x} : Set V) ∪ listSet D = insert x (listSet D) := by
    ext q
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  calc
    guardWithin w x Y D ({s₁, s₂} : Set V) v g =
        guardResidLevel w x Y g ({s₁, s₂} : Set V) v
          (insert x Y) D ({x} : Set V) :=
      guardWithin_eq_guardResidLevel w x Y D ({s₁, s₂} : Set V) v g
    _ = guardResidLevel w x Y g ({s₁, s₂} : Set V) v
          (insert x Y ∪ listSet D) [] (({x} : Set V) ∪ listSet D) +
        guardUnfoldTerms w x Y g ({s₁, s₂} : Set V) v
          (insert x Y) D :=
      guardResidLevel_unfold w hw x Y g ({s₁, s₂} : Set V) v D
        (insert x Y) ({x} : Set V) hnd hout Set.Subset.rfl hAS
    _ = guardHorizontal w x Y (insert x (listSet D))
          ({s₁, s₂} : Set V) v g +
        guardUnfoldTerms w x Y g ({s₁, s₂} : Set V) v
          (insert x Y) D := by
      rw [hAfin, hSfin,
        ← guardHorizontal_eq_guardResidLevel w x Y (insert x (listSet D))
          ({s₁, s₂} : Set V) v g]

/-- The corrected one-sided unfolding for an arbitrary guarded source set.
The pair-source theorem above is its specialization to `O = {s₁,s₂}`. -/
theorem guard_source_oneSided_unfold (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (O : Set V) (v : V) (g : Set (Sym2 V) → ℝ)
    (hnd : D.Nodup) (hout : ∀ d ∈ D, d ∉ insert x Y) :
    guardWithin w x Y D O v g =
      guardHorizontal w x Y (insert x (listSet D)) O v g +
        guardUnfoldTerms w x Y g O v (insert x Y) D := by
  have hAS : insert x Y = ({x} : Set V) ∪ Y := by
    ext q
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  have hAfin : insert x Y ∪ listSet D =
      insert x (listSet D) ∪ Y := by
    ext q
    simp only [Set.mem_union, Set.mem_insert_iff]
    tauto
  have hSfin : ({x} : Set V) ∪ listSet D = insert x (listSet D) := by
    ext q
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  calc
    guardWithin w x Y D O v g =
        guardResidLevel w x Y g O v (insert x Y) D ({x} : Set V) :=
      guardWithin_eq_guardResidLevel w x Y D O v g
    _ = guardResidLevel w x Y g O v
          (insert x Y ∪ listSet D) [] (({x} : Set V) ∪ listSet D) +
        guardUnfoldTerms w x Y g O v (insert x Y) D :=
      guardResidLevel_unfold w hw x Y g O v D
        (insert x Y) ({x} : Set V) hnd hout Set.Subset.rfl hAS
    _ = guardHorizontal w x Y (insert x (listSet D)) O v g +
        guardUnfoldTerms w x Y g O v (insert x Y) D := by
      rw [hAfin, hSfin,
        ← guardHorizontal_eq_guardResidLevel w x Y (insert x (listSet D))
          O v g]


end KNAll.Guarded

end
