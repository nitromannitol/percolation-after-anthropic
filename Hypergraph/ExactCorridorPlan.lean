import Hypergraph.ExactTargetChain
import Hypergraph.CorridorMove

/-!
# Exact finite corridor plans

This is the data-and-soundness layer of the exact corridor construction.  A plan contains `d`
quarter-face target plans and one final aspect-88 target plan.  It records the intermediate source
boxes, the exact backwards error cascade, the growing finite domains, and the two isotropic endpoint
cores.  It does not construct these data from supercriticality; that finite extraction belongs in a
separate module.

All stages are interpreted in one pinned finite product.  There are no designated tips and no
face-plus-coalescence surrogate: every probabilistic step is an `ExactTargetPlan.Plan` and the
composition is exactly `ExactTargetPlan.Plan.soundPinnedChain`.
-/

noncomputable section

namespace KNAll.Site.ExactCorridorPlan

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat}

/-- Raw data of an exact corridor plan at one fixed scale.  The `past` set at a stage is the
already available part of its domain; the full stage domain also contains that stage's active
box. -/
structure Plan (d : Nat) where
  scale : Nat
  startCentre : Site d
  endCentre : Site d
  /-- The boxes `B_0, ..., B_d`. -/
  boxes : Fin (d + 1) → Finset (Site d)
  /-- The first `d` quarter-face calls. -/
  quarter : Fin d → ExactTargetPlan.Plan d
  /-- The final aspect-88 call. -/
  aspect88 : ExactTargetPlan.Plan d
  /-- Direction of the final aspect-88 call. -/
  longAxis : Fin d
  longSign : Int
  /-- Exterior/previously available part of each stage domain. -/
  past : Fin (d + 1) → Finset (Site d)
  /-- Source errors `eta_0, ..., eta_d`. -/
  eta : Fin (d + 1) → Real
  /-- Final output error. -/
  alpha : Real

namespace Plan

/-- The `d` quarter-face plans followed by the final aspect-88 plan. -/
def stage (K : Plan d) : Fin (d + 1) → ExactTargetPlan.Plan d :=
  Fin.lastCases K.aspect88 K.quarter

@[simp] theorem stage_castSucc (K : Plan d) (i : Fin d) :
    K.stage i.castSucc = K.quarter i := by
  simp [stage]

@[simp] theorem stage_last (K : Plan d) :
    K.stage (Fin.last d) = K.aspect88 := by
  simp [stage]

/-- The whole finite graph domain at a stage. -/
def domain (K : Plan d) (i : Fin (d + 1)) : Finset (Site d) :=
  K.past i ∪ (K.stage i).active

/-- The initial isotropic radius-`3r` source core. -/
def initialCore (K : Plan d) : Finset (Site d) :=
  CorrMove.cube K.startCentre (3 * (K.scale : Int))

/-- The radius-`2r` inner target produced by the exact aspect-88 call. -/
def innerTarget (K : Plan d) : Finset (Site d) :=
  CorrMove.cube K.endCentre (2 * (K.scale : Int))

/-- The radius-`3r` output core used by the following corridor. -/
def outputCore (K : Plan d) : Finset (Site d) :=
  CorrMove.cube K.endCentre (3 * (K.scale : Int))

/-- The corridor input tolerance. -/
def beta (K : Plan d) : Real := K.eta 0

/-- Parameter-free consistency of all exact nodes, intermediate boxes, errors, and domains. -/
structure WellFormed (K : Plan d) : Prop where
  scale_pos : 0 < K.scale
  stage_wf : ∀ i, (K.stage i).WellFormed
  stage_source : ∀ i, (K.stage i).source = K.boxes i
  initial_box : K.boxes 0 = K.initialCore
  quarter_target : ∀ i : Fin d, (K.stage i.castSucc).target = K.boxes i.succ
  quarter_geometry : ∀ i : Fin d,
    CorrMove.FaceTarget ((K.quarter i).radius : Int) (K.quarter i).active
      (K.quarter i).source (K.quarter i).target
  aspect_target : K.aspect88.target = K.innerTarget
  long_sign : K.longSign = 1 ∨ K.longSign = -1
  aspect88_geometry :
    CorrMove.LongTarget ((K.aspect88.radius : Nat) : Int) K.longAxis K.longSign
      K.aspect88.active K.aspect88.source K.aspect88.target
  stage_delta : ∀ i, (K.stage i).delta = K.eta i
  quarter_epsilon : ∀ i : Fin d, (K.stage i.castSucc).epsilon = K.eta i.succ
  aspect_epsilon : K.aspect88.epsilon = K.alpha
  domain_mono : ∀ i : Fin d, K.domain i.castSucc ⊆ K.domain i.succ

/-- All `d+1` exact target plans are valid at the same product parameter. -/
def ValidAt (K : Plan d) (q : unitInterval) : Prop :=
  ∀ i, (K.stage i).ValidAt q

theorem WellFormed.alpha_pos {K : Plan d} (hK : K.WellFormed) : 0 < K.alpha := by
  have hlast := hK.stage_wf (Fin.last d)
  rw [K.stage_last] at hlast
  rw [← hK.aspect_epsilon]
  exact hlast.2.1.1

theorem WellFormed.alpha_le_one {K : Plan d} (hK : K.WellFormed) : K.alpha ≤ 1 := by
  have hlast := hK.stage_wf (Fin.last d)
  rw [K.stage_last] at hlast
  rw [← hK.aspect_epsilon]
  exact hlast.2.1.2.1

theorem WellFormed.beta_pos {K : Plan d} (hK : K.WellFormed) : 0 < K.beta := by
  have hzero := hK.stage_wf 0
  rw [beta, ← hK.stage_delta 0]
  unfold ExactTargetPlan.Plan.delta
  positivity [hzero.2.1.1]

theorem initialCore_nonempty (K : Plan d) : K.initialCore.Nonempty :=
  CorrMove.cube_nonempty K.startCentre (by positivity)

theorem innerTarget_nonempty (K : Plan d) : K.innerTarget.Nonempty :=
  CorrMove.cube_nonempty K.endCentre (by positivity)

theorem outputCore_nonempty (K : Plan d) : K.outputCore.Nonempty :=
  CorrMove.cube_nonempty K.endCentre (by positivity)

/-- The exact radius-`2r` target lies in the radius-`3r` recursive output core. -/
theorem innerTarget_subset_outputCore (K : Plan d) : K.innerTarget ⊆ K.outputCore := by
  exact CorrMove.ibox_mono (fun _ => by omega)

private theorem connWithinSet_mono_target {Dom A B : Finset (Site d)} {o : Site d}
    (hAB : A ⊆ B) :
    connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑A : Set (Site d)) ⊆
      connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑B : Set (Site d)) := by
  intro omega homega
  obtain ⟨x, hxA, hox⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d)) o
      (↑A : Set (Site d)) omega).1 homega
  exact (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d)) o
    (↑B : Set (Site d)) omega).2
      ⟨x, Finset.mem_coe.2 (hAB (Finset.mem_coe.1 hxA)), hox⟩

private theorem pinnedProb_mono_target {q : unitInterval} {R Dom A B : Finset (Site d)}
    (val : Site d → Prop) (o : Site d) (hAB : A ⊆ B) :
    pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑A : Set (Site d))) ≤
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑B : Set (Site d))) := by
  unfold pinnedProb
  exact measureReal_mono
    (Set.preimage_mono (connWithinSet_mono_target hAB)) (measure_ne_top _ _)

section Soundness

variable [NeZero d]

/-- **Pinned soundness of an exact corridor plan.**  The first source is the radius-`3r` core,
the first `d` nodes are the recorded quarter-face cascade, and the last node is the aspect-88
plan.  All nodes are evaluated under the same fixed pinned transcript. -/
theorem soundPinned (K : Plan d) (hK : K.WellFormed)
    {q : unitInterval} (hvalid : K.ValidAt q)
    (R : Finset (Site d)) (val : Site d → Prop) (o : Site d)
    (hRactive : ∀ i, Disjoint R (K.stage i).active)
    (hoR : o ∈ R) (hvalo : val o)
    (hbase : 1 - K.beta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑(K.domain 0) : Set (Site d)) o
          (↑K.initialCore : Set (Site d)))) :
    1 - K.alpha <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(K.domain (Fin.last d)) : Set (Site d)) o
          (↑K.outputCore : Set (Site d))) := by
  have hbase' : 1 - (K.stage 0).delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑(K.domain 0) : Set (Site d)) o
          (↑(K.stage 0).source : Set (Site d))) := by
    rw [hK.stage_delta 0, hK.stage_source 0, hK.initial_box]
    exact hbase
  have hchain := ExactTargetPlan.Plan.soundPinnedChain d K.stage K.domain R val o
    hK.stage_wf hvalid
    (fun i x hx => Finset.mem_union_right (K.past i) hx)
    hRactive hoR hvalo hbase' hK.domain_mono
    (fun i => by rw [hK.quarter_target i, hK.stage_source i.succ])
    (fun i => by rw [hK.quarter_epsilon i, hK.stage_delta i.succ])
  have hinner : 1 - K.alpha <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(K.domain (Fin.last d)) : Set (Site d)) o
          (↑K.innerTarget : Set (Site d))) := by
    rw [K.stage_last, hK.aspect_epsilon, hK.aspect_target] at hchain
    simpa [domain] using hchain
  exact lt_of_lt_of_le hinner
    (pinnedProb_mono_target val o K.innerTarget_subset_outputCore)

/-- **Exterior soundness of an exact corridor plan.**  Here the fixed transcript is required to
lie in `past_i \ active_i` at every stage, exactly the overlap-compatible exterior used by
`soundPinnedExteriorChain`. -/
theorem soundPinnedExterior (K : Plan d) (hK : K.WellFormed)
    {q : unitInterval} (hvalid : K.ValidAt q)
    (R : Finset (Site d)) (val : Site d → Prop) (o : Site d)
    (hRext : ∀ i, R ⊆ ExactTargetPlan.exterior (K.past i) (K.stage i).active)
    (hoR : o ∈ R) (hvalo : val o)
    (hbase : 1 - K.beta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑(K.domain 0) : Set (Site d)) o
          (↑K.initialCore : Set (Site d)))) :
    1 - K.alpha <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(K.domain (Fin.last d)) : Set (Site d)) o
          (↑K.outputCore : Set (Site d))) := by
  have hbase' : 1 - (K.stage 0).delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(K.past 0 ∪ (K.stage 0).active) : Set (Site d)) o
          (↑(K.stage 0).source : Set (Site d))) := by
    rw [hK.stage_delta 0, hK.stage_source 0, hK.initial_box]
    exact hbase
  have hchain := ExactTargetPlan.Plan.soundPinnedExteriorChain d K.stage K.past R val o
    hK.stage_wf hvalid hRext hoR hvalo hbase' hK.domain_mono
    (fun i => by rw [hK.quarter_target i, hK.stage_source i.succ])
    (fun i => by rw [hK.quarter_epsilon i, hK.stage_delta i.succ])
  have hinner : 1 - K.alpha <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(K.domain (Fin.last d)) : Set (Site d)) o
          (↑K.innerTarget : Set (Site d))) := by
    rw [K.stage_last, hK.aspect_epsilon, hK.aspect_target] at hchain
    simpa [domain] using hchain
  exact lt_of_lt_of_le hinner
    (pinnedProb_mono_target val o K.innerTarget_subset_outputCore)

end Soundness

end Plan


#print axioms KNAll.Site.ExactCorridorPlan.Plan.soundPinned
#print axioms KNAll.Site.ExactCorridorPlan.Plan.soundPinnedExterior

end KNAll.Site.ExactCorridorPlan

end
