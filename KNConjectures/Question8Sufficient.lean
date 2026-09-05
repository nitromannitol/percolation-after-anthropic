import KNConjectures.Question8Defs
import KNConjectures.AvoidedGen
import Percolation.Literature.TwoClusterConditionalAssociationProofs

/-!
# Question 8: the target split and a first-relay sufficient criterion

This file proves the exact cancellation identity on the branch where the observer
reaches another relay but not `a`, and then combines the two-cluster BHK inequality
with the avoided first-relay bound.  The resulting theorem is only a sufficient
criterion; it makes no claim that Question 8 minimality implies that criterion.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open Percolation.Literature.KNPreFKG
open scoped Classical

/-- The branch `E_a = {o ↮ a, o ↔ A.erase a}` on which the two target
probabilities need to be compared. -/
def q8TargetBranch {n : ℕ} (A : Finset (Fin n)) (o a : Fin n) :
    Set (BondConfig (Fin n)) :=
  (openConn o a)ᶜ ∩ U (A.erase a) o

/-- The conditional connection probability
`P(x ↔ b | x ↮ a)`, written without a conditional-probability API. -/
def q8RelayMean {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (a b x : Fin n) : ℝ :=
  (prodBernoulli w).real (openConn x b ∩ (openConn x a)ᶜ) /
    (prodBernoulli w).real (openConn x a)ᶜ

/-- Relays for which the conditioning event `{x ↮ a}` has positive
probability. -/
def q8ActiveRelays {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  (A.erase a).filter fun x ↦ 0 < (prodBernoulli w).real (openConn x a)ᶜ

/-- The avoided first-in-rank event for an active relay. -/
def q8FirstRelay {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (o a : Fin n) (r : Fin n → ℕ) (x : Fin n) :
    Set (BondConfig (Fin n)) :=
  (openConn o a)ᶜ ∩
    (openConn o x ∩
      ⋂ y ∈ (q8ActiveRelays w A a).filter (fun y ↦ r y < r x),
        (openConn o y)ᶜ)

/-- On a relay set containing `a`, the observer hits a relay iff it hits `a` or
one of the remaining relays. -/
private theorem U_eq_insert_erase {n : ℕ} (A : Finset (Fin n))
    (o a : Fin n) (ha : a ∈ A) :
    U A o = openConn o a ∪ U (A.erase a) o := by
  ext ω
  constructor
  · intro h
    obtain ⟨x, hx, hox⟩ := mem_iUnion₂.1 h
    by_cases hxa : x = a
    · subst x
      exact Or.inl hox
    · exact Or.inr (mem_iUnion₂.2 ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩, hox⟩)
  · rintro (hoa | hT)
    · exact mem_iUnion₂.2 ⟨a, ha, hoa⟩
    · obtain ⟨x, hx, hox⟩ := mem_iUnion₂.1 hT
      exact mem_iUnion₂.2 ⟨x, Finset.mem_of_mem_erase hx, hox⟩

/-- **Q8.9 / equation (delta-core).**  The contributions on `{o ↔ a}`
cancel, leaving only the target branch `E_a`. -/
theorem q8_target_split {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (A : Finset (Fin n)) (o b a : Fin n) (ha : a ∈ A) :
    q8L w A o b a - q8R w A o b =
      (prodBernoulli w).real (openConn a b ∩ q8TargetBranch A o a) -
        (prodBernoulli w).real (openConn o b ∩ q8TargetBranch A o a) := by
  let μ := prodBernoulli w
  let C : Set (BondConfig (Fin n)) := openConn o a
  let E : Set (BondConfig (Fin n)) := q8TargetBranch A o a
  have hU : U A o = C ∪ U (A.erase a) o := U_eq_insert_erase A o a ha
  have hsplit : ∀ S : Set (BondConfig (Fin n)),
      μ.real S = μ.real (S ∩ C) + μ.real (S ∩ Cᶜ) := by
    intro S
    rw [← measureReal_inter_add_sdiff (s := S)
      (MeasurableSet.of_discrete : MeasurableSet C), Set.sdiff_eq]
  have hagree :
      (openConn a b ∩ U A o) ∩ C = (openConn o b ∩ U A o) ∩ C := by
    ext ω
    constructor
    · rintro ⟨⟨hab, hUA⟩, hoa⟩
      exact ⟨⟨hoa.trans hab, hUA⟩, hoa⟩
    · rintro ⟨⟨hob, hUA⟩, hoa⟩
      exact ⟨⟨hoa.symm.trans hob, hUA⟩, hoa⟩
  have hleft : (openConn a b ∩ U A o) ∩ Cᶜ = openConn a b ∩ E := by
    ext ω
    constructor
    · rintro ⟨⟨hab, hUA⟩, hnoa⟩
      have hu : ω ∈ C ∪ U (A.erase a) o := hU ▸ hUA
      rcases hu with hC | hT
      · exact absurd hC hnoa
      · exact ⟨hab, hnoa, hT⟩
    · rintro ⟨hab, hnoa, hT⟩
      have hUA : ω ∈ U A o := hU.symm ▸ Or.inr hT
      exact ⟨⟨hab, hUA⟩, hnoa⟩
  have hright : (openConn o b ∩ U A o) ∩ Cᶜ = openConn o b ∩ E := by
    ext ω
    constructor
    · rintro ⟨⟨hob, hUA⟩, hnoa⟩
      have hu : ω ∈ C ∪ U (A.erase a) o := hU ▸ hUA
      rcases hu with hC | hT
      · exact absurd hC hnoa
      · exact ⟨hob, hnoa, hT⟩
    · rintro ⟨hob, hnoa, hT⟩
      have hUA : ω ∈ U A o := hU.symm ▸ Or.inr hT
      exact ⟨⟨hob, hUA⟩, hnoa⟩
  have hLsplit := hsplit (openConn a b ∩ U A o)
  have hRsplit := hsplit (openConn o b ∩ U A o)
  unfold q8L q8R
  change μ.real (openConn a b ∩ U A o) -
      μ.real (openConn o b ∩ U A o) =
        μ.real (openConn a b ∩ E) - μ.real (openConn o b ∩ E)
  rw [hLsplit, hRsplit, hagree, hleft, hright]
  ring

/-- The increasing cluster functional used for the target `b`. -/
private def connVertexIndicator {n : ℕ} (b : Fin n) (S : Set (Fin n)) : ℝ :=
  if b ∈ S then 1 else 0

private theorem connVertexIndicator_mono {n : ℕ} (b : Fin n) :
    ∀ S T : Set (Fin n), S ⊆ T → connVertexIndicator b S ≤ connVertexIndicator b T := by
  intro S T hST
  unfold connVertexIndicator
  by_cases hb : b ∈ S
  · rw [if_pos hb, if_pos (hST hb)]
  · rw [if_neg hb]
    split_ifs <;> norm_num

private theorem connVertexIndicator_cluster {n : ℕ} (b x : Fin n) :
    (fun ω : BondConfig (Fin n) ↦ connVertexIndicator b (openCluster ω x)) =
      (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
  funext ω
  by_cases hxb : ω ∈ (openConn x b : Set (BondConfig (Fin n)))
  · rw [Set.indicator_of_mem hxb, Pi.one_apply, connVertexIndicator,
      if_pos (show b ∈ openCluster ω x from hxb)]
  · rw [Set.indicator_of_notMem hxb, connVertexIndicator,
      if_neg (show b ∉ openCluster ω x from hxb)]

/-- The quotient in `q8RelayMean` is exactly the avoided conditional mean used
by the first-relay machinery. -/
private theorem condMean_connVertexIndicator {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a b x : Fin n) :
    condMean w ({a} : Set (Fin n)) (connVertexIndicator b) x =
      q8RelayMean w a b x := by
  unfold condMean q8RelayMean
  have hD :
      { ω : BondConfig (Fin n) |
          ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y } =
        (openConn x a)ᶜ := by
    ext ω
    simp only [mem_setOf_eq, mem_singleton_iff, forall_eq, mem_compl_iff]
    rfl
  rw [hD, connVertexIndicator_cluster,
    KNPreFKG.setIntegral_indicator_one_eq]
  rw [inter_comm]

/-- The family of edge clusters from `o` that hit at least one relay of `T`. -/
private def hitsRelayFamily {n : ℕ} (o : Fin n) (T : Finset (Fin n)) :
    Set (Set (Sym2 (Fin n))) :=
  ⋃ x ∈ T, connFamily o x

private theorem hitsRelayFamily_upper {n : ℕ} (o : Fin n)
    (T : Finset (Fin n)) : IsUpperSet (hitsRelayFamily o T) := by
  intro C C' hCC' hC
  obtain ⟨x, hx, hCx⟩ := mem_iUnion₂.1 hC
  exact mem_iUnion₂.2 ⟨x, hx, isUpperSet_connFamily o x hCC' hCx⟩

private theorem edgeCluster_mem_hitsRelayFamily {n : ℕ} (o : Fin n)
    (T : Finset (Fin n)) :
    { ω : BondConfig (Fin n) | openEdgeCluster ω o ∈ hitsRelayFamily o T } =
      U T o := by
  ext ω
  simp only [hitsRelayFamily, mem_iUnion, exists_prop, U]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, (show ω ∈ openConn o x by
      rw [openConn_eq_setOf_connFamily]
      exact h)⟩
  · rintro ⟨x, hx, h⟩
    rw [openConn_eq_setOf_connFamily] at h
    exact ⟨x, hx, h⟩

/-- **Q8.10 / A formalizable sufficient criterion.**

The displayed hypothesis is the denominator-free criterion from the note.  The
rank orders the active relays by their conditional connection means.  BHK bounds
the `a`-target probability on `E_a`, and the avoided first-relay theorem bounds
the corresponding `o`-target probability from below. -/
theorem q8_of_firstRelayCriterion {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) (r : Fin n → ℕ) (ha : a ∈ A)
    (havoid : 0 < (prodBernoulli w).real (openConn o a)ᶜ)
    (hr : Set.InjOn r (↑(q8ActiveRelays w A a) : Set (Fin n)))
    (hcompat : ∀ x ∈ q8ActiveRelays w A a,
      ∀ y ∈ q8ActiveRelays w A a, r x < r y →
        q8RelayMean w a b x ≤ q8RelayMean w a b y)
    (hcriterion :
      (prodBernoulli w).real
          (openConn a b ∩ (openConn o a)ᶜ) *
          (prodBernoulli w).real (q8TargetBranch A o a) ≤
        (prodBernoulli w).real (openConn o a)ᶜ *
          ∑ x ∈ q8ActiveRelays w A a,
            (prodBernoulli w).real (q8FirstRelay w A o a r x) *
              q8RelayMean w a b x) :
    q8L w A o b a ≤ q8R w A o b := by
  let μ := prodBernoulli w
  let T := q8ActiveRelays w A a
  let D : Set (BondConfig (Fin n)) := (openConn o a)ᶜ
  let E : Set (BondConfig (Fin n)) := q8TargetBranch A o a
  let F : Set (Fin n) → ℝ := connVertexIndicator b
  have hao : a ≠ o := by
    intro hao
    subst a
    have hself : (openConn o o : Set (BondConfig (Fin n))) = Set.univ :=
      eq_univ_of_forall fun ω ↦ SimpleGraph.Reachable.refl o
    rw [hself, compl_univ, measureReal_empty] at havoid
    exact (lt_irrefl 0 havoid)
  have hTmem : ∀ x ∈ T, x ∈ A.erase a := by
    intro x hx
    exact (Finset.mem_filter.1 hx).1
  have hTY : ∀ x ∈ T, x ∉ ({a} : Set (Fin n)) := by
    intro x hx hxa
    exact Finset.ne_of_mem_erase (hTmem x hx) (mem_singleton_iff.1 hxa)
  have hact : ∀ x ∈ T,
      0 < μ.real { ω : BondConfig (Fin n) |
        ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y } := by
    intro x hx
    have hpos := (Finset.mem_filter.1 hx).2
    have hDx :
        { ω : BondConfig (Fin n) |
            ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable x y } =
          (openConn x a)ᶜ := by
      ext ω
      simp only [mem_setOf_eq, mem_singleton_iff, forall_eq, mem_compl_iff]
      rfl
    rw [hDx]
    exact hpos
  have hFmono : ∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S' :=
    connVertexIndicator_mono b
  have hcompat' : ∀ x ∈ T, ∀ y ∈ T, r x < r y →
      condMean w ({a} : Set (Fin n)) F x ≤
        condMean w ({a} : Set (Fin n)) F y := by
    intro x hx y hy hxy
    rw [condMean_connVertexIndicator, condMean_connVertexIndicator]
    exact hcompat x hx y hy hxy
  have hgen := genY_all w ({a} : Set (Fin n)) F hFmono T o r
    hTY hact hr hcompat'
  have hsum := sum_le_setIntegral_of_genY w ({a} : Set (Fin n)) T r F o hgen
  have hsum' :
      ∑ x ∈ T, μ.real (q8FirstRelay w A o a r x) *
          q8RelayMean w a b x ≤
        μ.real (openConn o b ∩ E) := by
    have hAvoid :
        { ω : BondConfig (Fin n) |
            ∀ y ∈ ({a} : Set (Fin n)), ¬ (openGraph ω).Reachable o y } = D := by
      ext ω
      simp only [mem_setOf_eq, mem_singleton_iff, forall_eq, D,
        mem_compl_iff]
      rfl
    have hInt :
        ∫ ω in D ∩ ⋃ x ∈ T, openConn o x,
            F (openCluster ω o) ∂μ =
          μ.real ((D ∩ ⋃ x ∈ T, openConn o x) ∩ openConn o b) := by
      rw [connVertexIndicator_cluster,
        KNPreFKG.setIntegral_indicator_one_eq]
    rw [hAvoid] at hsum
    have hsum₀ :
      ∑ x ∈ T, μ.real (q8FirstRelay w A o a r x) *
          q8RelayMean w a b x ≤
        ∫ ω in D ∩ ⋃ x ∈ T, openConn o x,
          F (openCluster ω o) ∂μ := by
      simpa only [T, D, F, μ, q8FirstRelay,
        condMean_connVertexIndicator] using hsum
    rw [hInt] at hsum₀
    refine hsum₀.trans (measureReal_mono ?_)
    intro ω hω
    obtain ⟨x, hxT, hox⟩ := mem_iUnion₂.1 hω.1.2
    exact ⟨hω.2, hω.1.1,
      mem_iUnion₂.2 ⟨x, hTmem x hxT, hox⟩⟩
  have hBHK :
      μ.real D * μ.real (openConn a b ∩ E) ≤
        μ.real (openConn a b ∩ D) * μ.real E := by
    have key := bhk_two_upper_upper w a o hao
      (isUpperSet_connFamily a b)
      (hitsRelayFamily_upper o (A.erase a))
    have hDa :
        { ω : BondConfig (Fin n) | ¬ (openGraph ω).Reachable a o } = D := by
      ext ω
      simp only [D, mem_setOf_eq, mem_compl_iff]
      exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
    rw [hDa, ← openConn_eq_setOf_connFamily,
      edgeCluster_mem_hitsRelayFamily] at key
    simpa only [E, q8TargetBranch, inter_assoc, inter_left_comm,
      inter_comm] using key
  have hcrit :
      μ.real (openConn a b ∩ D) * μ.real E ≤
        μ.real D *
          ∑ x ∈ T, μ.real (q8FirstRelay w A o a r x) *
            q8RelayMean w a b x := by
    simpa only [μ, T, D, E] using hcriterion
  have hscaled : μ.real D * μ.real (openConn a b ∩ E) ≤
      μ.real D * μ.real (openConn o b ∩ E) := by
    calc
      μ.real D * μ.real (openConn a b ∩ E) ≤
          μ.real (openConn a b ∩ D) * μ.real E := hBHK
      _ ≤ μ.real D *
          ∑ x ∈ T, μ.real (q8FirstRelay w A o a r x) *
            q8RelayMean w a b x := hcrit
      _ ≤ μ.real D * μ.real (openConn o b ∩ E) :=
        mul_le_mul_of_nonneg_left hsum' measureReal_nonneg
  have hcore : μ.real (openConn a b ∩ E) ≤
      μ.real (openConn o b ∩ E) :=
    (mul_le_mul_iff_of_pos_left havoid).mp
      (by simpa only [μ, D] using hscaled)
  have hsplit := q8_target_split w A o b a ha
  change q8L w A o b a - q8R w A o b =
      μ.real (openConn a b ∩ E) - μ.real (openConn o b ∩ E) at hsplit
  linarith

end KNAll

end


#print axioms KNAll.q8_target_split
#print axioms KNAll.q8_of_firstRelayCriterion
