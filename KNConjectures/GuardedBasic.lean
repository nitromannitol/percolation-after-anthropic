
import KNConjectures.GuardedDefs
set_option linter.unusedSectionVars false

/-!
# Elementary set-source bridges

Items 1--11 of the guarded Conjecture 6 proof ledger.
-/

noncomputable section

namespace KNAll.Guarded

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {V : Type*} [Fintype V]

theorem sourceCluster_singleton (ω : BondConfig V) (u : V) :
    sourceCluster ω ({u} : Set V) = openCluster ω u := by
  simp [sourceCluster]

theorem sourceCluster_pair (ω : BondConfig V) (v w' : V) :
    sourceCluster ω ({v, w'} : Set V) = pairCluster ω v w' := by
  simp [sourceCluster, pairCluster]

theorem sourceAvoid_singleton (u : V) (Y : Set V) :
    sourceAvoid ({u} : Set V) Y = Percolation.Continuity.HullPort.avoidEv u Y := by
  ext ω
  simp [sourceAvoid, Percolation.Continuity.HullPort.avoidEv]

theorem sourceAvoid_pair (v w' a : V) :
    sourceAvoid ({v, w'} : Set V) ({a} : Set V) = pairAvoid v w' a := by
  ext ω
  simp [sourceAvoid, pairAvoid]

theorem sourceConn_pair (v w' : V) (T : Finset V) :
    sourceConn ({v, w'} : Set V) (↑T : Set V) = pairConn v w' T := by
  ext ω
  simp only [sourceConn, pairConn, mem_setOf_eq, mem_insert_iff,
    mem_singleton_iff, Finset.mem_coe]
  constructor
  · rintro ⟨r, rfl | rfl, t, ht, hrt⟩
    · exact ⟨t, ht, Or.inl hrt⟩
    · exact ⟨t, ht, Or.inr hrt⟩
  · rintro ⟨t, ht, hvt | hwt⟩
    · exact ⟨v, Or.inl rfl, t, ht, hvt⟩
    · exact ⟨w', Or.inr rfl, t, ht, hwt⟩

theorem sourceCluster_mono (ω : BondConfig V) :
    Monotone (sourceCluster ω) := by
  intro R R' hRR' z hz
  simp only [sourceCluster, mem_iUnion] at hz ⊢
  rcases hz with ⟨r, hrR, hzr⟩
  exact ⟨r, hRR' hrR, hzr⟩

theorem openCluster_subset_sourceCluster_of_guard {R : Set V} {d : V}
    {ω : BondConfig V} (hω : ω ∈ sourceConn R ({d} : Set V)) :
    openCluster ω d ⊆ sourceCluster ω R := by
  rcases hω with ⟨r, hrR, d', hd', hrd⟩
  have hd'd : d' = d := by simpa using hd'
  subst d'
  have hclusters : openCluster ω r = openCluster ω d :=
    KNPreFKG.openCluster_eq_of_reachable hrd
  intro z hzd
  simp only [sourceCluster, mem_iUnion]
  exact ⟨r, hrR, hclusters ▸ hzd⟩

theorem sourceCluster_eq_openCluster_of_singleton_guard (u d : V)
    {ω : BondConfig V} (hω : ω ∈ sourceConn ({u} : Set V) ({d} : Set V)) :
    sourceCluster ω ({u} : Set V) = openCluster ω d := by
  rcases hω with ⟨u', hu', d', hd', hud⟩
  have hu'u : u' = u := by simpa using hu'
  have hd'd : d' = d := by simpa using hd'
  subst u'
  subst d'
  rw [sourceCluster_singleton, KNPreFKG.openCluster_eq_of_reachable hud]

private theorem guardEv_singleton_eq (u x : V) (Y : Set V) :
    guardEv ({u} : Set V) ({x} : Set V) Y =
      sourceAvoid ({x} : Set V) Y ∩ openConn x u := by
  ext ω
  simp only [guardEv, sourceAvoid, sourceConn, mem_inter_iff, mem_setOf_eq,
    mem_singleton_iff, forall_eq, exists_eq_left, openConn]
  constructor
  · rintro ⟨huY, hux⟩
    refine ⟨?_, hux.symm⟩
    intro y hy hxy
    exact huY y hy (hux.trans hxy)
  · rintro ⟨hxY, hxu⟩
    refine ⟨?_, hxu.symm⟩
    intro y hy huy
    exact hxY y hy (hxu.trans huy)

theorem guardCovD_singleton_eq_covD (w : Sym2 V → unitInterval) (x : V)
    (Y : Set V) (g : Set (Sym2 V) → ℝ) (u : V) :
    guardCovD w x Y g ({u} : Set V) = CSH.covD w x Y g u := by
  rw [guardCovD, CSH.covD, sourceAvoid_singleton,
    guardEv_singleton_eq]
  simp only [Percolation.Continuity.HullPort.avoidEv, sourceAvoid,
    mem_singleton_iff, forall_eq]

theorem guardAvoidConst_singleton_eq_avoidConst (w : Sym2 V → unitInterval)
    (d : V) (A : Set V) (u : V) :
    guardAvoidConst w d A ({u} : Set V) = CSH.avoidConst w d A u := by
  rw [guardAvoidConst, CSH.avoidConst, sourceAvoid_singleton,
    guardEv_singleton_eq]
  simp only [Percolation.Continuity.HullPort.avoidEv, sourceAvoid,
    mem_singleton_iff, forall_eq]

private theorem guardObsConst_singleton_eq_obsConst
    (w : Sym2 V → unitInterval) (o v : V) (A : Set V) :
    guardObsConst w ({o} : Set V) v A = CSH.obsConst w o v A := by
  rw [guardObsConst, CSH.obsConst, sourceAvoid_singleton,
    guardEv_singleton_eq]
  simp only [Percolation.Continuity.HullPort.avoidEv, sourceAvoid,
    mem_singleton_iff, forall_eq, KNPreFKG.openConn_symm]

private theorem cshMarg_guard_singletons
    (w : Sym2 V → unitInterval) (A : Set V) (D : List V)
    (p : ℝ) (o v : V) (f : Set V → ℝ) (f' : V → ℝ)
    (hf : ∀ u, f ({u} : Set V) = f' u) :
    cshMarg (guardDecoyList w A D) p ({o} : Set V) ({v} : Set V) f =
      cshMarg (CSH.decoyList w A D) p o v f' := by
  induction D generalizing A f f' with
  | nil =>
      simp only [guardDecoyList, CSH.decoyList, cshMarg_nil, hf]
  | cons d ds ih =>
      simp only [guardDecoyList, CSH.decoyList, cshMarg_cons]
      rw [ih (insert d A) f f' hf,
        ih (insert d A) (guardAvoidConst w d A)
          (CSH.avoidConst w d A) (guardAvoidConst_singleton_eq_avoidConst w d A)]
      rw [hf d]

theorem guardCSHMargin_pair_self_eq_cshMargin (w : Sym2 V → unitInterval)
    (x : V) (Y : Set V) (D : List V) (s v : V)
    (g : Set (Sym2 V) → ℝ) :
    guardCSHMargin w x Y D ({s, s} : Set V) v g =
      CSH.cshMargin w x Y D s v g := by
  have hpair : ({s, s} : Set V) = ({s} : Set V) := by simp
  rw [hpair]
  unfold guardCSHMargin CSH.cshMargin
  rw [guardObsConst_singleton_eq_obsConst]
  exact cshMarg_guard_singletons w (insert x Y) D _ s v
    (guardCovD w x Y g) (CSH.covD w x Y g)
    (guardCovD_singleton_eq_covD w x Y g)

end KNAll.Guarded

end
