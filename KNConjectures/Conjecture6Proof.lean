
import KNConjectures.Conjecture6Reduction
import Percolation.Continuity.HullPort.TACE
import Percolation.Literature.GladkovZiminKernel
import Percolation.Literature.KozmaNitzanSeparatingTriple

import KNConjectures.GuardedDefs
import KNConjectures.GuardedBasic
import KNConjectures.GuardedKernel
import KNConjectures.GuardedDecoy
import KNConjectures.GuardedTwoCluster
import KNConjectures.PairGuardedCSH
import KNConjectures.PairSurplus
import KNConjectures.PairSurplusClosure
import KNConjectures.PairFixedMin
set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity
open scoped Classical

variable {V : Type*} [Fintype V]

private theorem integral_prodBernoulli_eq_ED {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → unitInterval) (f : Set ι → ℝ) :
    (∫ ω, f ω ∂(prodBernoulli p)) =
      Percolation.Literature.DecisionTree.ED (Finset.univ : Finset ι)
        (fun i => (p i : ℝ)) (fun S => f (↑S : Set ι)) := by
  rw [BHK2006.integral_prodBernoulli_eq_sum]
  rw [← Percolation.Continuity.HullPort.sum_powerset_wtW_eq_sum_weight]
  rfl

private theorem integral_forceOpen_eq_insert {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (e : Sym2 (Fin n))
    (f : BondConfig (Fin n) → ℝ) :
    (∫ ω, f ω ∂(prodBernoulli (forceOpen w e))) =
      ∫ ω, f (insert e ω) ∂(prodBernoulli w) := by
  let ι := Sym2 (Fin n)
  let p : ι → ℝ := fun i => (w i : ℝ)
  let q : ι → ℝ := fun i => (forceOpen w e i : ℝ)
  let D : Finset ι := Finset.univ.erase e
  let φ : Finset ι → ℝ := fun S => f (↑S : Set ι)
  let ψ : Finset ι → ℝ := fun S => f (insert e (↑S : Set ι))
  have heD : e ∉ D := Finset.notMem_erase e Finset.univ
  have huniv : insert e D = (Finset.univ : Finset ι) :=
    Finset.insert_erase (Finset.mem_univ e)
  have hqe : q e = 1 := by simp [q, forceOpen]
  have hqp : ∀ i ∈ D, q i = p i := by
    intro i hi
    have hie : i ≠ e := (Finset.mem_erase.1 hi).1
    simp [q, p, forceOpen, hie]
  have hED : ∀ h : Finset ι → ℝ,
      Percolation.Literature.DecisionTree.ED D q h =
        Percolation.Literature.DecisionTree.ED D p h := by
    intro h
    unfold Percolation.Literature.DecisionTree.ED
    refine Finset.sum_congr rfl fun S hS => ?_
    congr 1
    unfold Percolation.Literature.DecisionTree.wtW
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hqp i hi]
  have hφψ : (fun S => φ (insert e S)) = ψ := by
    funext S
    simp only [φ, ψ, Finset.coe_insert]
  have hψ : (fun S => ψ (insert e S)) = ψ := by
    funext S
    simp [ψ]
  rw [integral_prodBernoulli_eq_ED, integral_prodBernoulli_eq_ED]
  change Percolation.Literature.DecisionTree.ED (Finset.univ : Finset ι) q φ =
    Percolation.Literature.DecisionTree.ED (Finset.univ : Finset ι) p ψ
  rw [← huniv,
    Percolation.Literature.DecisionTree.ED_insert q heD φ,
    Percolation.Literature.DecisionTree.ED_insert p heD ψ,
    hqe]
  simp only [sub_self, zero_mul, one_mul]
  rw [hφψ, hψ, hED ψ]
  ring

/-- Spec item 51: forcing one coordinate preserves an insert-invariant integral. -/
theorem integral_forceOpen_eq_of_insert_invariant {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (e : Sym2 (Fin n))
    (f : BondConfig (Fin n) → ℝ) (hinv : ∀ ω, f (insert e ω) = f ω) :
    (∫ ω, f ω ∂(prodBernoulli (forceOpen w e))) =
      ∫ ω, f ω ∂(prodBernoulli w) := by
  rw [integral_forceOpen_eq_insert w e f]
  exact integral_congr_ae (Filter.Eventually.of_forall hinv)

/-- Spec item 52: opening the internal pair preserves the union of endpoint clusters. -/
theorem pairCluster_insert_internal (ω : BondConfig V) (v w' : V) :
    pairCluster (insert s(v, w') ω) v w' = pairCluster ω v w' := by
  ext x
  simp only [pairCluster, openCluster, mem_union, mem_setOf_eq]
  constructor
  · rintro (hv | hw)
    · rcases (KNSep.reachable_insert_iff ω v w' v x).1 hv with
        hvx | ⟨-, hwx⟩ | ⟨-, hvx⟩
      · exact Or.inl hvx
      · exact Or.inr hwx
      · exact Or.inl hvx
    · rcases (KNSep.reachable_insert_iff ω v w' w' x).1 hw with
        hwx | ⟨-, hwx⟩ | ⟨-, hvx⟩
      · exact Or.inr hwx
      · exact Or.inr hwx
      · exact Or.inl hvx
  · rintro (hv | hw)
    · exact Or.inl ((KNSep.reachable_insert_iff ω v w' v x).2 (Or.inl hv))
    · exact Or.inr ((KNSep.reachable_insert_iff ω v w' w' x).2 (Or.inl hw))

/-- Spec item 53: pair avoidance is invariant under the internal edge. -/
theorem pairAvoid_insert_internal (ω : BondConfig V) (v w' a : V) :
    insert s(v, w') ω ∈ pairAvoid v w' a ↔ ω ∈ pairAvoid v w' a := by
  simp only [pairAvoid, mem_setOf_eq, ← not_or]
  change a ∉ pairCluster (insert s(v, w') ω) v w' ↔
    a ∉ pairCluster ω v w'
  rw [pairCluster_insert_internal]

/-- Spec item 54: pair contact is invariant under the internal edge. -/
theorem pairConn_insert_internal (ω : BondConfig V) (v w' : V) (T : Finset V) :
    insert s(v, w') ω ∈ pairConn v w' T ↔ ω ∈ pairConn v w' T := by
  constructor
  · rintro ⟨t, ht, hv | hw⟩
    · have hm : t ∈ pairCluster (insert s(v, w') ω) v w' := Or.inl hv
      rw [pairCluster_insert_internal] at hm
      exact ⟨t, ht, hm⟩
    · have hm : t ∈ pairCluster (insert s(v, w') ω) v w' := Or.inr hw
      rw [pairCluster_insert_internal] at hm
      exact ⟨t, ht, hm⟩
  · rintro ⟨t, ht, hv | hw⟩
    · have hm : t ∈ pairCluster ω v w' := Or.inl hv
      rw [← pairCluster_insert_internal ω v w'] at hm
      exact ⟨t, ht, hm⟩
    · have hm : t ∈ pairCluster ω v w' := Or.inr hw
      rw [← pairCluster_insert_internal ω v w'] at hm
      exact ⟨t, ht, hm⟩

/-- Spec item 55: on pair avoidance, the minimizing cluster is unchanged. -/
theorem openCluster_insert_internal_of_pairAvoid (ω : BondConfig V)
    (v w' a : V) (hω : ω ∈ pairAvoid v w' a) :
    openCluster (insert s(v, w') ω) a = openCluster ω a := by
  ext x
  simp only [openCluster, mem_setOf_eq]
  constructor
  · intro hax
    rcases (KNSep.reachable_insert_iff ω v w' a x).1 hax with
      hax | ⟨hav, -⟩ | ⟨haw, -⟩
    · exact hax
    · exact (hω.1 hav.symm).elim
    · exact (hω.2 haw.symm).elim
  · intro hax
    exact (KNSep.reachable_insert_iff ω v w' a x).2 (Or.inl hax)

/-- Spec item 56: FM2 is invariant when the internal edge is forced open. -/
theorem pairFixedMinGap_forceOpen {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (v w' a : Fin n) (F : Set (Fin n) → ℝ) :
    pairFixedMinGap (forceOpen w s(v, w')) A v w' a F =
      pairFixedMinGap w A v w' a F := by
  letI : DecidableEq (Fin n) := Classical.decEq _
  let e : Sym2 (Fin n) := s(v, w')
  let E : Set (BondConfig (Fin n)) :=
    pairAvoid v w' a ∩ pairConn v w' (A.erase a)
  let g : BondConfig (Fin n) → ℝ := fun ω =>
    E.indicator (fun η => F (pairCluster η v w') - F (openCluster η a)) ω
  have hE : ∀ ω, insert e ω ∈ E ↔ ω ∈ E := by
    intro ω
    exact and_congr (pairAvoid_insert_internal ω v w' a)
      (pairConn_insert_internal ω v w' (A.erase a))
  have hginv : ∀ ω, g (insert e ω) = g ω := by
    intro ω
    by_cases hω : ω ∈ E
    · have hω' : insert e ω ∈ E := (hE ω).2 hω
      dsimp only [g]
      rw [indicator_of_mem hω', indicator_of_mem hω]
      dsimp only [e]
      rw [pairCluster_insert_internal,
        openCluster_insert_internal_of_pairAvoid ω v w' a hω.1]
    · have hω' : insert e ω ∉ E := fun h => hω ((hE ω).1 h)
      dsimp only [g]
      rw [indicator_of_notMem hω', indicator_of_notMem hω]
  have hforce := integral_forceOpen_eq_of_insert_invariant w e g hginv
  have hmeas : MeasurableSet E := MeasurableSet.of_discrete
  have hset :
      (∫ ω in E, F (pairCluster ω v w') - F (openCluster ω a)
          ∂(prodBernoulli (forceOpen w e))) =
        ∫ ω in E, F (pairCluster ω v w') - F (openCluster ω a)
          ∂(prodBernoulli w) := by
    rw [← integral_indicator hmeas, ← integral_indicator hmeas]
    exact hforce
  simpa [KNAll.pairFixedMinGap, e, E] using hset

private theorem openCluster_insert_internal_left (ω : BondConfig V) (v w' : V) :
    openCluster (insert s(v, w') ω) v = pairCluster ω v w' := by
  ext x
  simp only [openCluster, pairCluster, mem_setOf_eq, mem_union]
  rw [KNSep.reachable_insert_iff]
  constructor
  · rintro (hvx | ⟨-, hwx⟩ | ⟨-, hvx⟩)
    · exact Or.inl hvx
    · exact Or.inr hwx
    · exact Or.inl hvx
  · rintro (hvx | hwx)
    · exact Or.inl hvx
    · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl v, hwx⟩)

private theorem union_openConn_insert_internal_iff (ω : BondConfig V)
    (v w' : V) (A : Finset V) :
    insert s(v, w') ω ∈ (⋃ y ∈ A, openConn v y) ↔ ω ∈ pairConn v w' A := by
  constructor
  · rintro h
    obtain ⟨y, hyA, hvy⟩ := mem_iUnion₂.1 h
    rcases (KNSep.reachable_insert_iff ω v w' v y).1 hvy with
      hvy | ⟨-, hwy⟩ | ⟨-, hvy⟩
    · exact ⟨y, hyA, Or.inl hvy⟩
    · exact ⟨y, hyA, Or.inr hwy⟩
    · exact ⟨y, hyA, Or.inl hvy⟩
  · rintro ⟨y, hyA, hvy | hwy⟩
    · exact mem_iUnion₂.2 ⟨y, hyA,
        (KNSep.reachable_insert_iff ω v w' v y).2 (Or.inl hvy)⟩
    · exact mem_iUnion₂.2 ⟨y, hyA,
        (KNSep.reachable_insert_iff ω v w' v y).2
          (Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl v, hwy⟩))⟩

/-- Spec item 57: the indicator instance of FM2 is the pinned probability gap. -/
theorem forceOpen_pairFixedMinGap {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (v w' b a : Fin n) :
    pairFixedMinGap w A v w' a (fun K => if b ∈ K then 1 else 0) =
      (prodBernoulli (forceOpen w s(v, w'))).real
          (openConn v b ∩ ⋃ y ∈ A, openConn v y) -
        (prodBernoulli (forceOpen w s(v, w'))).real
          (openConn a b ∩ ⋃ y ∈ A, openConn v y) := by
  letI : DecidableEq (Fin n) := Classical.decEq _
  let e : Sym2 (Fin n) := s(v, w')
  let U : Set (BondConfig (Fin n)) := ⋃ y ∈ A, openConn v y
  let Bv : Set (BondConfig (Fin n)) := openConn v b ∩ U
  let Ba : Set (BondConfig (Fin n)) := openConn a b ∩ U
  let E : Set (BondConfig (Fin n)) :=
    pairAvoid v w' a ∩ pairConn v w' (A.erase a)
  let d : BondConfig (Fin n) → ℝ := fun ω =>
    (if b ∈ pairCluster ω v w' then 1 else 0) -
      if b ∈ openCluster ω a then 1 else 0
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S :=
    fun _ => MeasurableSet.of_discrete
  have hpoint : ∀ ω,
      E.indicator d ω =
        Bv.indicator 1 (insert e ω) - Ba.indicator 1 (insert e ω) := by
    intro ω
    have hCv : insert e ω ∈ openConn v b ↔ b ∈ pairCluster ω v w' := by
      change b ∈ openCluster (insert e ω) v ↔ b ∈ pairCluster ω v w'
      dsimp only [e]
      rw [openCluster_insert_internal_left]
    have hU : insert e ω ∈ U ↔ ω ∈ pairConn v w' A := by
      dsimp only [e, U]
      exact union_openConn_insert_internal_iff ω v w' A
    by_cases hav : ω ∈ pairAvoid v w' a
    · have hCa : insert e ω ∈ openConn a b ↔ b ∈ openCluster ω a := by
        change b ∈ openCluster (insert e ω) a ↔ b ∈ openCluster ω a
        dsimp only [e]
        rw [openCluster_insert_internal_of_pairAvoid ω v w' a hav]
      have hconn : ω ∈ pairConn v w' A ↔
          ω ∈ pairConn v w' (A.erase a) := by
        constructor
        · rintro ⟨x, hxA, hvx | hwx⟩
          · have hxa : x ≠ a := by
              intro hxa
              subst x
              exact hav.1 hvx
            exact ⟨x, Finset.mem_erase.2 ⟨hxa, hxA⟩, Or.inl hvx⟩
          · have hxa : x ≠ a := by
              intro hxa
              subst x
              exact hav.2 hwx
            exact ⟨x, Finset.mem_erase.2 ⟨hxa, hxA⟩, Or.inr hwx⟩
        · rintro ⟨x, hxA, hx⟩
          exact ⟨x, Finset.mem_of_mem_erase hxA, hx⟩
      by_cases hωE : ω ∈ E
      · have hBv : insert e ω ∈ Bv ↔ b ∈ pairCluster ω v w' := by
          constructor
          · intro h
            exact hCv.1 h.1
          · intro hb
            exact ⟨hCv.2 hb, hU.2 (hconn.2 hωE.2)⟩
        have hBa : insert e ω ∈ Ba ↔ b ∈ openCluster ω a := by
          constructor
          · intro h
            exact hCa.1 h.1
          · intro hb
            exact ⟨hCa.2 hb, hU.2 (hconn.2 hωE.2)⟩
        dsimp only [d]
        rw [indicator_of_mem hωE]
        simp only [Set.indicator, hBv, hBa, Pi.one_apply]
      · have hnconn : ω ∉ pairConn v w' (A.erase a) := by
          intro hc
          exact hωE ⟨hav, hc⟩
        have hnU : insert e ω ∉ U := fun hu => hnconn (hconn.1 (hU.1 hu))
        have hnBv : insert e ω ∉ Bv := fun h => hnU h.2
        have hnBa : insert e ω ∉ Ba := fun h => hnU h.2
        rw [indicator_of_notMem hωE, indicator_of_notMem hnBv,
          indicator_of_notMem hnBa]
        simp
    · have hnotE : ω ∉ E := fun h => hav h.1
      have hva : (openGraph (insert e ω)).Reachable v a := by
        by_cases hva₀ : (openGraph ω).Reachable v a
        · dsimp only [e]
          exact (KNSep.reachable_insert_iff ω v w' v a).2 (Or.inl hva₀)
        · have hwa₀ : (openGraph ω).Reachable w' a := by
            by_contra hwa₀
            exact hav ⟨hva₀, hwa₀⟩
          dsimp only [e]
          exact (KNSep.reachable_insert_iff ω v w' v a).2
            (Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl v, hwa₀⟩))
      have hvb : insert e ω ∈ openConn v b ↔ insert e ω ∈ openConn a b := by
        change b ∈ openCluster (insert e ω) v ↔
          b ∈ openCluster (insert e ω) a
        rw [KNPreFKG.openCluster_eq_of_reachable hva]
      have hBB : insert e ω ∈ Bv ↔ insert e ω ∈ Ba :=
        and_congr hvb Iff.rfl
      rw [indicator_of_notMem hnotE]
      by_cases h : insert e ω ∈ Bv
      · rw [indicator_of_mem h, indicator_of_mem (hBB.1 h)]
        simp
      · rw [indicator_of_notMem h, indicator_of_notMem (fun ha => h (hBB.2 ha))]
        simp
  unfold pairFixedMinGap
  change (∫ ω in E, d ω ∂(prodBernoulli w)) =
    (prodBernoulli (forceOpen w e)).real Bv -
      (prodBernoulli (forceOpen w e)).real Ba
  rw [← integral_indicator (hmeas E), ← integral_indicator_one (hmeas Bv),
    ← integral_indicator_one (hmeas Ba),
    integral_forceOpen_eq_insert w e (Bv.indicator 1),
    integral_forceOpen_eq_insert w e (Ba.indicator 1),
    ← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- Spec item 58: the strong form of Kozma--Nitzan Conjecture 6. -/
theorem conjecture6Strong_holds : Conjecture6Strong := by
  intro n w A v w' b a ha hmin
  let F : Set (Fin n) → ℝ := fun K => if b ∈ K then 1 else 0
  have hFmono : Monotone F := by
    intro S T hST
    by_cases hbS : b ∈ S
    · simp [F, hbS, hST hbS]
    · simp only [F, if_neg hbS]
      split_ifs <;> norm_num
  have hFind : ∀ x : Fin n,
      (fun ω : BondConfig (Fin n) => F (openCluster ω x)) =
        (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
    intro x
    funext ω
    simp [F, Set.indicator, openConn, openCluster]
  have hmin' : ∀ x ∈ A,
      (∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
        ∫ ω, F (openCluster ω x) ∂(prodBernoulli w) := by
    intro x hx
    rw [hFind a, hFind x,
      integral_indicator_one MeasurableSet.of_discrete,
      integral_indicator_one MeasurableSet.of_discrete]
    exact hmin x hx
  have hgap := pair_fixedMin w A v w' a F ha hFmono hmin'
  have hgap' : 0 ≤ pairFixedMinGap w A v w' a
      (fun K => if b ∈ K then 1 else 0) := by
    simpa only [F] using hgap
  rw [forceOpen_pairFixedMinGap] at hgap'
  linarith

/-- Spec item 59: the paper's multiplicative Conjecture 6. -/
theorem conjecture6_holds : Conjecture6 := by
  exact KNAll.conjecture6_of_conjecture6Strong conjecture6Strong_holds

end KNAll.Guarded

end

#print axioms KNAll.Guarded.conjecture6Strong_holds
#print axioms KNAll.Guarded.conjecture6_holds
