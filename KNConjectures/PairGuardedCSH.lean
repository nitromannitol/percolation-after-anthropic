
import KNConjectures.GuardedDefs
import KNConjectures.GuardedBasic
import KNConjectures.GuardedKernel
import KNConjectures.GuardedDecoy
import KNConjectures.GuardedTwoCluster
set_option linter.unusedSectionVars false

/-!
# The joint pair-guarded CSH induction

Items 31--32 of the guarded Conjecture 6 proof ledger.  The induction motive
contains both the within-level assertion and the global assertion; there is no
second, successive induction.
-/

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {V : Type*} [Fintype V]

private theorem pairGuardAdmissible_tail (x : V) (Y : Set V) (d : V)
    (ds : List V) (s₁ s₂ v : V)
    (hadm : PairGuardAdmissible x Y (d :: ds) s₁ s₂ v) :
    PairGuardAdmissible d (insert x Y) ds s₁ s₂ v := by
  obtain ⟨hs, hxY, hv, hnd, hdec, hpair⟩ := hadm
  have hdmem : d ∈ d :: ds := List.mem_cons_self
  have htail := List.nodup_cons.1 hnd
  refine ⟨hs, (hdec d hdmem).1, ?_, htail.2, ?_, ?_⟩
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
    exact hpair

theorem pair_guardJoint_step (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (s₁ s₂ v : V) (hadm : PairGuardAdmissible x Y D s₁ s₂ v)
    (hshort : ∀ (x' : V) (Y' : Set V) (D' : List V) (t₁ t₂ v' : V),
      D'.length < D.length → PairGuardAdmissible x' Y' D' t₁ t₂ v' →
        PairGuardCSHHolds w x' Y' D' t₁ t₂ v') :
    (∀ g : Set (Sym2 V) → ℝ, Monotone g →
      0 ≤ guardWithin w x Y D ({s₁, s₂} : Set V) v g) ∧
      PairGuardCSHHolds w x Y D s₁ s₂ v := by
  have hadmRoot := hadm
  obtain ⟨_hs, _hxY, hvbase, _hnd, hdec, hpair⟩ := hadm
  have hxX : x ∈ insert x (listSet D) := mem_insert x _
  have hvX : v ∉ insert x (listSet D) := by
    simp only [mem_insert_iff, listSet, mem_setOf_eq, not_or]
    refine ⟨?_, ?_⟩
    · exact fun hvx => hvbase (hvx ▸ mem_insert x Y)
    · intro hvD
      exact (hdec v hvD).2 rfl
  have hpairHorizontal : Disjoint ({s₁, s₂} : Set V)
      (insert v (insert x (listSet D) ∪ Y)) := by
    have hsets : insert v (insert x (listSet D) ∪ Y) =
        insert x (insert v (Y ∪ listSet D)) := by
      ext z
      simp only [mem_insert_iff, mem_union]
      tauto
    rw [hsets]
    exact hpair
  have hwithinAll : ∀ g : Set (Sym2 V) → ℝ, Monotone g →
      0 ≤ guardWithin w x Y D ({s₁, s₂} : Set V) v g := by
    intro g hg
    have hterms : ∀ (L : List V) (x₀ : V) (Y₀ : Set V),
        L.length ≤ D.length → PairGuardAdmissible x₀ Y₀ L s₁ s₂ v →
          0 ≤ guardUnfoldTerms w x Y g ({s₁, s₂} : Set V) v
            (insert x₀ Y₀) L := by
      intro L
      induction L with
      | nil =>
          intro x₀ Y₀ _hlen _hadm
          simp [guardUnfoldTerms]
      | cons d ds ih =>
          intro x₀ Y₀ hlen hadm₀
          have hadmTail : PairGuardAdmissible d (insert x₀ Y₀) ds s₁ s₂ v :=
            pairGuardAdmissible_tail x₀ Y₀ d ds s₁ s₂ v hadm₀
          have hlen' : ds.length + 1 ≤ D.length := by simpa using hlen
          have hlenTail : ds.length < D.length := by omega
          have hglobal := hshort d (insert x₀ Y₀) ds s₁ s₂ v
            hlenTail hadmTail
          have hlower : 0 ≤ guardCSHMargin w d (insert x₀ Y₀) ds
              ({s₁, s₂} : Set V) v (CSH.phiT w x Y g d) :=
            hglobal (CSH.phiT w x Y g d) (CSH.phiT_mono w x Y hg d)
          have hdelta : 0 ≤ guardDelta w x Y g d (insert x₀ Y₀)
              ({s₁, s₂} : Set V) :=
            KNAll.Guarded.guardDelta_nonneg w x Y hg d (insert x₀ Y₀)
              ({s₁, s₂} : Set V)
          have hrec : 0 ≤ guardUnfoldTerms w x Y g ({s₁, s₂} : Set V) v
              (insert d (insert x₀ Y₀)) ds :=
            ih d (insert x₀ Y₀) (by omega) hadmTail
          have hinv : 0 ≤
              ((prodBernoulli w).real
                (sourceAvoid ({d} : Set V) (insert x₀ Y₀)))⁻¹ :=
            inv_nonneg.2 measureReal_nonneg
          simp only [guardUnfoldTerms]
          exact add_nonneg (add_nonneg (mul_nonneg hinv hlower) hdelta) hrec
    have hhorizontal : 0 ≤ guardHorizontal w x Y (insert x (listSet D))
        ({s₁, s₂} : Set V) v g :=
      KNAll.Guarded.guardHorizontal_nonneg w hw x Y (insert x (listSet D))
        ({s₁, s₂} : Set V) v g hxX hvX hpairHorizontal hg
    rw [KNAll.Guarded.guard_oneSided_unfold w hw x Y D s₁ s₂ v g hadmRoot hg]
    exact add_nonneg hhorizontal (hterms D x Y le_rfl hadmRoot)
  exact ⟨hwithinAll,
    pair_guardGlobal_of_within w hw x Y D s₁ s₂ v hadmRoot hwithinAll⟩

theorem pair_guardCSH_nondegenerate (w : Sym2 V → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (s₁ s₂ v : V) (hadm : PairGuardAdmissible x Y D s₁ s₂ v) :
    PairGuardCSHHolds w x Y D s₁ s₂ v := by
  have main : ∀ (N : ℕ) (x : V) (Y : Set V) (D : List V)
      (s₁ s₂ v : V), D.length = N →
      PairGuardAdmissible x Y D s₁ s₂ v →
        PairGuardCSHHolds w x Y D s₁ s₂ v := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro x Y D s₁ s₂ v hlen hadm
      exact (pair_guardJoint_step w hw x Y D s₁ s₂ v hadm
        (fun x' Y' D' t₁ t₂ v' hshort hadm' => by
          have hD'N : D'.length < N := by omega
          exact ih D'.length hD'N x' Y' D' t₁ t₂ v' rfl hadm')).2
  exact main D.length x Y D s₁ s₂ v rfl hadm

#print axioms guardLevelTest_antitone_second
#print axioms guardCSHMargin_eq_twoClusterCov
#print axioms twoClusterCov_step
#print axioms twoClusterCov_nonneg_of_withinFirst
#print axioms pair_guardGlobal_of_within
#print axioms pair_guardJoint_step
#print axioms pair_guardCSH_nondegenerate

end KNAll.Guarded

end
