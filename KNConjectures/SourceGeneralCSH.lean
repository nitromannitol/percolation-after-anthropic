import KNConjectures.PairGuardedCSH

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {V : Type*} [Fintype V]

/-- Placement assumptions for a genuinely non-singleton source set. -/
def SourceGuardAdmissible (x : V) (Y : Set V) (D : List V)
    (O : Set V) (v : V) : Prop :=
  x ∉ Y ∧ v ∉ insert x Y ∧ D.Nodup ∧
    (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ v) ∧
    Disjoint O (insert x (insert v (Y ∪ listSet D))) ∧
    ∀ u : V, O ≠ ({u} : Set V)

def SourceGuardCSHHolds (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (D : List V) (O : Set V) (v : V) : Prop :=
  ∀ g : Set (Sym2 V) → ℝ, Monotone g →
    0 ≤ guardCSHMargin w x Y D O v g

private theorem sourceGuardAdmissible_tail (x : V) (Y : Set V) (d : V)
    (ds : List V) (O : Set V) (v : V)
    (hadm : SourceGuardAdmissible x Y (d :: ds) O v) :
    SourceGuardAdmissible d (insert x Y) ds O v := by
  obtain ⟨hxY, hv, hnd, hdec, hsource, hnonsing⟩ := hadm
  have hdmem : d ∈ d :: ds := List.mem_cons_self
  have htail := List.nodup_cons.1 hnd
  refine ⟨(hdec d hdmem).1, ?_, htail.2, ?_, ?_, hnonsing⟩
  · rintro (hvd | hvrest)
    · exact (hdec d hdmem).2 hvd.symm
    · exact hv hvrest
  · intro q hq
    have hqmem : q ∈ d :: ds := List.mem_cons_of_mem d hq
    have hqd : q ≠ d := fun h => htail.1 (h ▸ hq)
    refine ⟨?_, (hdec q hqmem).2⟩
    rintro (hqd' | hqbase)
    · exact hqd hqd'
    · exact (hdec q hqmem).1 hqbase
  · have hsets :
        insert d (insert v (insert x Y ∪ listSet ds)) =
          insert x (insert v (Y ∪ listSet (d :: ds))) := by
      ext z
      simp only [mem_insert_iff, mem_union, listSet, mem_setOf_eq,
        List.mem_cons]
      tauto
    rw [hsets]
    exact hsource

/-- The Gibbs-contraction passage from the within-world term to the global
source-set guarded margin.  The proof only needs `O` not to be a singleton. -/
theorem source_guardGlobal_of_within (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (O : Set V) (v : V) (hadm : SourceGuardAdmissible x Y D O v)
    (hwithin : ∀ g : Set (Sym2 V) → ℝ, Monotone g →
      0 ≤ guardWithin w x Y D O v g) :
    SourceGuardCSHHolds w x Y D O v := by
  have hw0 : ∀ e, 0 ≤ (w e : ℝ) := fun e => (w e).2.1
  have hw1 : ∀ e, (w e : ℝ) ≤ 1 := fun e => (w e).2.2
  have hm : ∑ ω, BHK2006.weight (fun e => (w e : ℝ)) ω = 1 := by
    have hmass := BHK2006.integral_prodBernoulli_eq_sum w (fun _ => (1 : ℝ))
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmass
    exact hmass.symm
  have hsep : ∀ ω, ω ∈ sourceAvoid ({x} : Set V) Y ↔
      ∀ s ∈ ({x} : Set V), ∀ t ∈ Y, ¬ (openGraph ω).Reachable s t := by
    intro ω
    simp [sourceAvoid]
  have hregen : 0 < BHK2006.regenWeight (fun e => (w e : ℝ)) Y := by
    rw [BHK2006.regenWeight_eq_prod w Y]
    refine Finset.prod_pos fun e he => ?_
    exact sub_pos.2 (unitInterval.coe_lt_one.2 (hw e).2)
  intro g hg
  rw [guardCSHMargin_eq_twoClusterCov]
  refine twoClusterCov_nonneg_of_withinFirst (fun e => (w e : ℝ))
    hw0 hw1 hm ({x} : Set V) Y (sourceAvoid ({x} : Set V) Y)
    hsep hregen (guardLevelTest w x Y D O v)
    (fun A => guardLevelTest_antitone_second w x Y D O v A hadm.2.2.2.2.2) ?_ hg
  intro g' hg' _hg'0
  exact hwithin g' hg'

theorem source_guardJoint_step (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (O : Set V) (v : V) (hadm : SourceGuardAdmissible x Y D O v)
    (hshort : ∀ (x' : V) (Y' : Set V) (D' : List V) (v' : V),
      D'.length < D.length → SourceGuardAdmissible x' Y' D' O v' →
        SourceGuardCSHHolds w x' Y' D' O v') :
    (∀ g : Set (Sym2 V) → ℝ, Monotone g →
      0 ≤ guardWithin w x Y D O v g) ∧
      SourceGuardCSHHolds w x Y D O v := by
  have hadmRoot := hadm
  obtain ⟨_hxY, hvbase, _hnd, hdec, hsource, _hnonsing⟩ := hadm
  have hxX : x ∈ insert x (listSet D) := mem_insert x _
  have hvX : v ∉ insert x (listSet D) := by
    simp only [mem_insert_iff, listSet, mem_setOf_eq, not_or]
    refine ⟨?_, ?_⟩
    · exact fun hvx => hvbase (hvx ▸ mem_insert x Y)
    · intro hvD
      exact (hdec v hvD).2 rfl
  have hsourceHorizontal : Disjoint O
      (insert v (insert x (listSet D) ∪ Y)) := by
    have hsets : insert v (insert x (listSet D) ∪ Y) =
        insert x (insert v (Y ∪ listSet D)) := by
      ext z
      simp only [mem_insert_iff, mem_union]
      tauto
    rw [hsets]
    exact hsource
  have hwithinAll : ∀ g : Set (Sym2 V) → ℝ, Monotone g →
      0 ≤ guardWithin w x Y D O v g := by
    intro g hg
    have hterms : ∀ (L : List V) (x₀ : V) (Y₀ : Set V),
        L.length ≤ D.length → SourceGuardAdmissible x₀ Y₀ L O v →
          0 ≤ guardUnfoldTerms w x Y g O v (insert x₀ Y₀) L := by
      intro L
      induction L with
      | nil =>
          intro x₀ Y₀ _hlen _hadm
          simp [guardUnfoldTerms]
      | cons d ds ih =>
          intro x₀ Y₀ hlen hadm₀
          have hadmTail : SourceGuardAdmissible d (insert x₀ Y₀) ds O v :=
            sourceGuardAdmissible_tail x₀ Y₀ d ds O v hadm₀
          have hlen' : ds.length + 1 ≤ D.length := by simpa using hlen
          have hlenTail : ds.length < D.length := by omega
          have hglobal := hshort d (insert x₀ Y₀) ds v hlenTail hadmTail
          have hlower : 0 ≤ guardCSHMargin w d (insert x₀ Y₀) ds
              O v (CSH.phiT w x Y g d) :=
            hglobal (CSH.phiT w x Y g d) (CSH.phiT_mono w x Y hg d)
          have hdelta : 0 ≤ guardDelta w x Y g d (insert x₀ Y₀) O :=
            KNAll.Guarded.guardDelta_nonneg w x Y hg d (insert x₀ Y₀) O
          have hrec : 0 ≤ guardUnfoldTerms w x Y g O v
              (insert d (insert x₀ Y₀)) ds :=
            ih d (insert x₀ Y₀) (by omega) hadmTail
          have hinv : 0 ≤
              ((prodBernoulli w).real
                (sourceAvoid ({d} : Set V) (insert x₀ Y₀)))⁻¹ :=
            inv_nonneg.2 measureReal_nonneg
          simp only [guardUnfoldTerms]
          exact add_nonneg (add_nonneg (mul_nonneg hinv hlower) hdelta) hrec
    have hhorizontal : 0 ≤ guardHorizontal w x Y (insert x (listSet D))
        O v g :=
      KNAll.Guarded.guardHorizontal_nonneg w hw x Y (insert x (listSet D))
        O v g hxX hvX hsourceHorizontal hg
    rw [KNAll.Guarded.guard_source_oneSided_unfold w hw x Y D O v g
      hadmRoot.2.2.1 (fun d hd => (hdec d hd).1)]
    exact add_nonneg hhorizontal (hterms D x Y le_rfl hadmRoot)
  exact ⟨hwithinAll,
    source_guardGlobal_of_within w hw x Y D O v hadmRoot hwithinAll⟩

theorem source_guardCSH_nondegenerate (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (O : Set V) (v : V) (hadm : SourceGuardAdmissible x Y D O v) :
    SourceGuardCSHHolds w x Y D O v := by
  have main : ∀ (N : ℕ) (x : V) (Y : Set V) (D : List V) (v : V),
      D.length = N → SourceGuardAdmissible x Y D O v →
        SourceGuardCSHHolds w x Y D O v := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro x Y D v hlen hadm
      exact (source_guardJoint_step w hw x Y D O v hadm
        (fun x' Y' D' v' hshort hadm' => by
          have hD'N : D'.length < N := by omega
          exact ih D'.length hD'N x' Y' D' v' rfl hadm')).2
  exact main D.length x Y D v rfl hadm

end KNAll.Guarded

end

#print axioms KNAll.Guarded.source_guardCSH_nondegenerate
