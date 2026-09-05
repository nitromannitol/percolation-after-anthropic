import Hypergraph.ExactTargetPinnedSound

/-!
# Finite chains of exact target plans

The target supplied by one exact plan can be used as the source for the next one.  This file
performs that finite induction under one fixed pinned transcript.  Domains may grow between
stages; the only compatibility data are inclusion of domains and targets into the next sources,
together with the numerical inequality that turns the preceding target bound into the next
source bound.
-/

noncomputable section

namespace KNAll.Site.ExactTargetPlan.Plan

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

/-- A well-formed exact plan has a genuinely positive source threshold. -/
private theorem one_sub_delta_pos (C : ExactTargetPlan.Plan d) (hC : C.WellFormed) :
    0 < 1 - C.delta := by
  have heps0 : 0 < C.epsilon := hC.2.1.1
  have heps1 : C.epsilon ≤ 1 := hC.2.1.2.1
  have hprod : 0 ≤ C.epsilon * (1 - C.epsilon) :=
    mul_nonneg heps0.le (sub_nonneg.mpr heps1)
  unfold ExactTargetPlan.Plan.delta
  nlinarith [sq_nonneg C.epsilon]

/-- A positive connection-to-source bound already forces the named source vertex to belong to
the finite domain.  This supplies the domain-membership premise of `soundPinned` without adding
it to the chain interface. -/
private theorem mem_domain_of_pinned_source_gt
    (C : ExactTargetPlan.Plan d) (hC : C.WellFormed)
    {q : unitInterval} {Dom R : Finset (Site d)} (val : Site d → Prop) (o : Site d)
    (hsrc : 1 - C.delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o
          (↑C.source : Set (Site d)))) :
    o ∈ Dom := by
  by_contra hoDom
  have hevent :
      connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o
          (↑C.source : Set (Site d)) = ∅ := by
    ext omega
    simp only [Set.mem_empty_iff_false, iff_false]
    intro homega
    obtain ⟨x, -, hox⟩ :=
      (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d)) o
        (↑C.source : Set (Site d)) omega).1 homega
    exact hoDom (Finset.mem_coe.1 hox.1.2)
  have hpos := one_sub_delta_pos C hC
  rw [hevent, pinnedProb] at hsrc
  simp only [Set.preimage_empty, measureReal_empty] at hsrc
  linarith

/-- Growing the domain and the target produces an inclusion of connectivity events. -/
private theorem connWithinSet_mono_domain_target
    {Dom Dom' A A' : Finset (Site d)} {o : Site d}
    (hDom : Dom ⊆ Dom') (hAA : A ⊆ A') :
    connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑A : Set (Site d)) ⊆
      connWithinSet (zdGraph d) (↑Dom' : Set (Site d)) o (↑A' : Set (Site d)) := by
  intro omega homega
  obtain ⟨x, hxA, hox⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d)) o
      (↑A : Set (Site d)) omega).1 homega
  refine (mem_connWithinSet_iff (zdGraph d) (↑Dom' : Set (Site d)) o
    (↑A' : Set (Site d)) omega).2 ⟨x, ?_, ?_⟩
  · exact Finset.mem_coe.2 (hAA (Finset.mem_coe.1 hxA))
  · exact connWithin_mono_set (zdGraph d) (Finset.coe_subset.2 hDom) o x hox

/-- Monotonicity of a pinned law is just monotonicity of the underlying product measure after
pulling events back by substitution. -/
private theorem pinnedProb_mono_event {q : unitInterval} {R : Finset (Site d)}
    (val : Site d → Prop) {A B : Set (Set (Site d))} (hAB : A ⊆ B) :
    pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val A ≤
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val B :=
  measureReal_mono (Set.preimage_mono hAB) (measure_ne_top _ _)

/-- **Finite exact-target composition under one pinned transcript.**

There are `n + 1` plans.  Stage domains may grow.  A target at stage `i` lies in the source at
stage `i+1`, and its error is at most the next source tolerance.  Thus the strict target estimate
at one stage is a strict source estimate for the next, and `soundPinned` closes the induction. -/
theorem soundPinnedChain (n : Nat)
    (C : Fin (n + 1) → ExactTargetPlan.Plan d)
    {q : unitInterval} (Dom : Fin (n + 1) → Finset (Site d))
    (R : Finset (Site d)) (val : Site d → Prop) (o : Site d)
    (hC : ∀ i, (C i).WellFormed)
    (hvalid : ∀ i, (C i).ValidAt q)
    (hactiveDom : ∀ i, (C i).active ⊆ Dom i)
    (hRactive : ∀ i, Disjoint R (C i).active)
    (hoR : o ∈ R) (hvalo : val o)
    (hbase : 1 - (C 0).delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑(Dom 0) : Set (Site d)) o
          (↑(C 0).source : Set (Site d))))
    (hDom : ∀ i : Fin n, Dom i.castSucc ⊆ Dom i.succ)
    (hTargetSource : ∀ i : Fin n, (C i.castSucc).target ⊆ (C i.succ).source)
    (hepsdelta : ∀ i : Fin n, (C i.castSucc).epsilon ≤ (C i.succ).delta) :
    1 - (C (Fin.last n)).epsilon <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d) (↑(Dom (Fin.last n)) : Set (Site d)) o
          (↑(C (Fin.last n)).target : Set (Site d))) := by
  have hstage : ∀ j (hj : j ≤ n),
      1 - (C ⟨j, Nat.lt_succ_iff.mpr hj⟩).epsilon <
        pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
          (connWithinSet (zdGraph d)
            (↑(Dom ⟨j, Nat.lt_succ_iff.mpr hj⟩) : Set (Site d)) o
            (↑(C ⟨j, Nat.lt_succ_iff.mpr hj⟩).target : Set (Site d))) := by
    intro j
    induction j with
    | zero =>
        intro hj
        let u : Fin (n + 1) := ⟨0, Nat.lt_succ_iff.mpr hj⟩
        have hu : u = 0 := by apply Fin.ext; rfl
        rw [show (⟨0, Nat.lt_succ_iff.mpr hj⟩ : Fin (n + 1)) = 0 from hu]
        have hoDom : o ∈ Dom 0 :=
          mem_domain_of_pinned_source_gt (C 0) (hC 0) val o hbase
        exact (C 0).soundPinned (hC 0) (hvalid 0) (hactiveDom 0)
          (hRactive 0) val o hoDom hoR hvalo hbase
    | succ j ih =>
        intro hj
        have hjlt : j < n := Nat.lt_of_succ_le hj
        let i : Fin n := ⟨j, hjlt⟩
        have hprev := ih (Nat.le_of_lt hjlt)
        have hprevIndex :
            (⟨j, Nat.lt_succ_iff.mpr (Nat.le_of_lt hjlt)⟩ : Fin (n + 1)) =
              i.castSucc := by
          apply Fin.ext
          rfl
        rw [hprevIndex] at hprev
        have hevent :
            connWithinSet (zdGraph d) (↑(Dom i.castSucc) : Set (Site d)) o
                (↑(C i.castSucc).target : Set (Site d)) ⊆
              connWithinSet (zdGraph d) (↑(Dom i.succ) : Set (Site d)) o
                (↑(C i.succ).source : Set (Site d)) :=
          connWithinSet_mono_domain_target (hDom i) (hTargetSource i)
        have hprob := pinnedProb_mono_event (q := q) (R := R) val hevent
        have hsrc : 1 - (C i.succ).delta <
            pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
              (connWithinSet (zdGraph d) (↑(Dom i.succ) : Set (Site d)) o
                (↑(C i.succ).source : Set (Site d))) := by
          have hthreshold :
              1 - (C i.succ).delta ≤ 1 - (C i.castSucc).epsilon := by
            linarith [hepsdelta i]
          exact lt_of_le_of_lt hthreshold (lt_of_lt_of_le hprev hprob)
        have hoDom : o ∈ Dom i.succ :=
          mem_domain_of_pinned_source_gt (C i.succ) (hC i.succ) val o hsrc
        have hnext := (C i.succ).soundPinned (hC i.succ) (hvalid i.succ)
          (hactiveDom i.succ) (hRactive i.succ) val o hoDom hoR hvalo hsrc
        have hnextIndex :
            (⟨j + 1, Nat.lt_succ_iff.mpr hj⟩ : Fin (n + 1)) = i.succ := by
          apply Fin.ext
          rfl
        rw [hnextIndex]
        exact hnext
  have hfinal := hstage n le_rfl
  have hlast : (⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    rfl
  rwa [hlast] at hfinal

/-- Exterior-specialized chain wrapper.  At each stage the domain is `P i ∪ active_i`, while
the fixed transcript lies in the overlap-compatible exterior `P i \ active_i`. -/
theorem soundPinnedExteriorChain (n : Nat)
    (C : Fin (n + 1) → ExactTargetPlan.Plan d)
    {q : unitInterval} (P : Fin (n + 1) → Finset (Site d))
    (R : Finset (Site d)) (val : Site d → Prop) (o : Site d)
    (hC : ∀ i, (C i).WellFormed)
    (hvalid : ∀ i, (C i).ValidAt q)
    (hRext : ∀ i, R ⊆ ExactTargetPlan.exterior (P i) (C i).active)
    (hoR : o ∈ R) (hvalo : val o)
    (hbase : 1 - (C 0).delta <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(P 0 ∪ (C 0).active) : Set (Site d)) o
          (↑(C 0).source : Set (Site d))))
    (hDom : ∀ i : Fin n,
      P i.castSucc ∪ (C i.castSucc).active ⊆ P i.succ ∪ (C i.succ).active)
    (hTargetSource : ∀ i : Fin n, (C i.castSucc).target ⊆ (C i.succ).source)
    (hepsdelta : ∀ i : Fin n, (C i.castSucc).epsilon ≤ (C i.succ).delta) :
    1 - (C (Fin.last n)).epsilon <
      pinnedProb (fun _ : Site d => q) (↑R : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(P (Fin.last n) ∪ (C (Fin.last n)).active) : Set (Site d)) o
          (↑(C (Fin.last n)).target : Set (Site d))) := by
  apply soundPinnedChain n C (fun i => P i ∪ (C i).active) R val o hC hvalid
  · intro i x hx
    exact Finset.mem_union_right (P i) hx
  · intro i
    exact ExactTargetPlan.ExteriorSupported.disjoint_active (hRext i)
  · exact hoR
  · exact hvalo
  · exact hbase
  · exact hDom
  · exact hTargetSource
  · exact hepsdelta

#print axioms KNAll.Site.ExactTargetPlan.Plan.soundPinnedChain
#print axioms KNAll.Site.ExactTargetPlan.Plan.soundPinnedExteriorChain

end KNAll.Site.ExactTargetPlan.Plan

end
