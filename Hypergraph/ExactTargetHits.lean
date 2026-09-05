import Hypergraph.ExactTargetPlan
import Hypergraph.TargetAwareLattice

/-!
# Concrete orthant hits as exact-target leaves

The qualitative `thetaSite > 0` machinery in `TargetAwareLattice` produces translated finite
orthant-hit experiments.  This module proves that those experiments are literally the `hitEvent`
leaves consumed by `ExactTargetPlan`; there is no probability comparison or change of event.
-/

noncomputable section

namespace KNAll.Site.ExactTargetHits

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.MoveWindowInput TargetAwareLattice

variable {d : Nat} [NeZero d]

/-- Enlarging the finite source set enlarges an exact hit event. -/
theorem hitEvent_mono_source {region source source' target : Finset (Site d)}
    (hsource : source ⊆ source') :
    ExactTargetPlan.hitEvent region source target ⊆
      ExactTargetPlan.hitEvent region source' target := by
  intro omega homega
  rw [ExactTargetPlan.hitEvent] at homega ⊢
  simp only [Set.mem_iUnion] at homega ⊢
  obtain ⟨x, hx, hconn⟩ := homega
  exact ⟨x, hsource hx, hconn⟩

/-- A translated centred box is the coordinate box used by exact target plans. -/
theorem shiftFinset_box_eq_siteBoxAt (v : Site d) (n : Nat) :
    shiftFinset v (box d n) = siteBoxAt v n := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [mem_siteBoxAt]
    have hy' := mem_box.1 hy
    intro j
    have hj := hy' j
    simp only [Pi.add_apply]
    omega
  · intro hx
    refine Finset.mem_image.2 ⟨x - v, ?_, ?_⟩
    · rw [mem_box]
      rw [mem_siteBoxAt] at hx
      intro j
      have hj := hx j
      simp only [Pi.sub_apply]
      omega
    · ext j
      simp

@[simp] theorem shiftedSource_eq_siteBoxAt
    {p : unitInterval} {chi : Real} (S : BaseScales (d := d) p chi) (v : Site d) :
    shiftedSource S v = siteBoxAt v S.source := by
  exact shiftFinset_box_eq_siteBoxAt v S.source

/-- The translated target-hit experiment is definitionally the exact-plan hit event after
rewriting its three translated finite sets. -/
theorem shiftedTargetHit_eq_hitEvent
    {p : unitInterval} {chi : Real} (S : BaseScales (d := d) p chi)
    (n : Nat) (v : Site d) (aTau : FaceIndex d) :
    shiftedTargetHit S n v aTau =
      ExactTargetPlan.hitEvent (shiftedOwner n v) (siteBoxAt v S.source)
        (shiftedTarget n v aTau) := by
  ext omega
  constructor
  · intro h
    change siteShift v omega ∈
      TargetAware.finiteHit (zdGraph d) (box d n) (box d S.source)
        (orthantFace aTau.1 aTau.2 n) at h
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (TargetAware.mem_finiteHit_iff (zdGraph d) (box d n) (box d S.source)
        (orthantFace aTau.1 aTau.2 n) (siteShift v omega)).1 h
    rw [ExactTargetPlan.hitEvent]
    simp only [Set.mem_iUnion]
    refine ⟨a + v, ⟨?_, ?_⟩⟩
    · rw [← shiftedSource_eq_siteBoxAt S v]
      exact Finset.mem_image.2 ⟨a, ha, rfl⟩
    · refine (mem_connWithinSet_iff (zdGraph d) (↑(shiftedOwner n v) : Set (Site d))
        (a + v) (↑(shiftedTarget n v aTau) : Set (Site d)) omega).2 ⟨b + v, ?_, ?_⟩
      · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨b, hb, rfl⟩)
      · have hs := (mem_connWithin_shift_iff v omega (↑(box d n) : Set (Site d)) a b).1 hab
        simpa only [shiftedOwner, coe_shiftFinset] using hs
  · intro h
    rw [ExactTargetPlan.hitEvent] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨av, hav, havconn⟩ := h
    rw [← shiftedSource_eq_siteBoxAt S v] at hav
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.1 hav
    subst av
    obtain ⟨bv, hbv, habv⟩ :=
      (mem_connWithinSet_iff (zdGraph d) (↑(shiftedOwner n v) : Set (Site d))
        (a + v) (↑(shiftedTarget n v aTau) : Set (Site d)) omega).1 havconn
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hbv)
    subst bv
    change siteShift v omega ∈
      TargetAware.finiteHit (zdGraph d) (box d n) (box d S.source)
        (orthantFace aTau.1 aTau.2 n)
    apply (TargetAware.mem_finiteHit_iff (zdGraph d) (box d n) (box d S.source)
      (orthantFace aTau.1 aTau.2 n) (siteShift v omega)).2
    refine ⟨a, ha, b, hb, ?_⟩
    have hs := (mem_connWithin_shift_iff v omega (↑(box d n) : Set (Site d)) a b).2
    apply hs
    simpa only [shiftedOwner, coe_shiftFinset] using habv

/-- Hence a base-scale quarter-hit supplies an exact target leaf at the extraction parameter. -/
theorem one_sub_lt_prob_hitEvent
    {p : unitInterval} {chi : Real} (S : BaseScales (d := d) p chi)
    (n : Nat) (hn : S.localRadius ≤ n) (v : Site d) (aTau : FaceIndex d) :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (ExactTargetPlan.hitEvent (shiftedOwner n v) (siteBoxAt v S.source)
        (shiftedTarget n v aTau)) := by
  rw [← shiftedTargetHit_eq_hitEvent S n v aTau, prob_shiftedTargetHit]
  exact S.quarter n hn aTau

/-- The same orthant estimate remains valid when the exact plan uses a larger source cube. -/
theorem one_sub_lt_prob_hitEvent_mono_source
    {p : unitInterval} {chi : Real} (S : BaseScales (d := d) p chi)
    (m n : Nat) (hsource : S.source ≤ m) (hn : S.localRadius ≤ n)
    (v : Site d) (aTau : FaceIndex d) :
    1 - chi < (siteBernoulli (fun _ : Site d => p)).real
      (ExactTargetPlan.hitEvent (shiftedOwner n v) (siteBoxAt v m)
        (shiftedTarget n v aTau)) := by
  have hbase := one_sub_lt_prob_hitEvent S n hn v aTau
  exact hbase.trans_le (measureReal_mono
    (hitEvent_mono_source (siteBoxAt_subset v hsource)) (measure_ne_top _ _))

end KNAll.Site.ExactTargetHits

end


#print axioms KNAll.Site.ExactTargetHits.shiftedTargetHit_eq_hitEvent
#print axioms KNAll.Site.ExactTargetHits.one_sub_lt_prob_hitEvent
#print axioms KNAll.Site.ExactTargetHits.one_sub_lt_prob_hitEvent_mono_source
