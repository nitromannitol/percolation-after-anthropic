import Hypergraph.ExactTargetPlan
import Hypergraph.ReinforcedLevelGeometry

/-!
# Reinforced windows and concrete hit leaves

An all-open reinforced window connects its centre to the full source cube.  Consequently a T4
hit event from that cube to a target face forces the centre-to-target event, without assuming that
the exterior contact itself is open.
-/

noncomputable section

namespace KNAll.Site.ReinforcedHit

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

theorem sourceCube_eq_siteBoxAt (m : Nat) (z : Site d) (rho : Fin d → Int)
    (x : Site d) :
    ReinforcedShell.sourceCube m z rho x =
      siteBoxAt (ReinforcedShell.centre m z rho x) m := by
  ext u
  rw [ReinforcedShell.sourceCube, CorrMove.mem_cube, mem_siteBoxAt]
  constructor
  · intro h a
    have ha := h a
    rw [abs_le] at ha
    constructor <;> omega
  · intro h a
    have ha := h a
    rw [abs_le]
    constructor <;> omega

theorem isUpperSet_hitEvent (region source target : Finset (Site d)) :
    IsUpperSet (ExactTargetPlan.hitEvent region source target) := by
  intro omega omega' hle hhit
  obtain ⟨a, ha, hconn⟩ := Set.mem_iUnion₂.1 hhit
  obtain ⟨t, ht, hat⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑region : Set (Site d)) a
      (↑target : Set (Site d)) omega).1 hconn
  exact Set.mem_iUnion₂.2 ⟨a, ha,
    (mem_connWithinSet_iff (zdGraph d) (↑region : Set (Site d)) a
      (↑target : Set (Site d)) omega').2
      ⟨t, ht, isUpperSet_connWithin (zdGraph d) (↑region : Set (Site d)) a t hle hat⟩⟩

theorem measurableSet_hitEvent (region source target : Finset (Site d)) :
    MeasurableSet (ExactTargetPlan.hitEvent region source target) := by
  unfold ExactTargetPlan.hitEvent
  exact Finset.measurableSet_biUnion source fun a _ =>
    measurableSet_connWithinSet (zdGraph d) region a (↑target : Set (Site d))

/-- The deterministic T4 implication.  Notice that no openness assumption on `x` occurs. -/
theorem openWindow_inter_hitEvent_subset_toTarget
    (m : Nat) (z : Site d) (rho : Fin d → Int) {x : Site d}
    (hx : Corridor.IsContact z rho x)
    (region face D : Finset (Site d)) (T : Set (Site d))
    (hwinD : ReinforcedShell.window m z rho x ⊆ D)
    (hregionD : region ⊆ D) (hfaceT : (↑face : Set (Site d)) ⊆ T) :
    ReinforcedTarget.openWindow (ReinforcedShell.window m z rho x) ∩
        ExactTargetPlan.hitEvent region (ReinforcedShell.sourceCube m z rho x) face ⊆
      TargetExt.toTarget (zdGraph d) D T (ReinforcedShell.centre m z rho x) := by
  rintro omega ⟨hopen, hhit⟩
  obtain ⟨a, ha, hat⟩ := Set.mem_iUnion₂.1 hhit
  obtain ⟨t, htface, hatconn⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑region : Set (Site d)) a
      (↑face : Set (Site d)) omega).1 hat
  have hva := ReinforcedShell.allOpen_connects_centre m z rho hx hopen a ha
  have hvaD := connWithin_mono_set (zdGraph d)
    (fun y hy => Finset.mem_coe.2 (hwinD (Finset.mem_coe.1 hy))) _ _ hva
  have hatD := connWithin_mono_set (zdGraph d)
    (fun y hy => Finset.mem_coe.2 (hregionD (Finset.mem_coe.1 hy))) _ _ hatconn
  rw [TargetExt.toTarget, mem_connWithinSet_iff]
  refine ⟨t, hfaceT htface, ?_⟩
  simpa only [Set.union_self] using TargetExt.connWithin_trans (zdGraph d) hvaD hatD

#print axioms KNAll.Site.ReinforcedHit.sourceCube_eq_siteBoxAt
#print axioms KNAll.Site.ReinforcedHit.isUpperSet_hitEvent
#print axioms KNAll.Site.ReinforcedHit.measurableSet_hitEvent
#print axioms KNAll.Site.ReinforcedHit.openWindow_inter_hitEvent_subset_toTarget

end KNAll.Site.ReinforcedHit

end
