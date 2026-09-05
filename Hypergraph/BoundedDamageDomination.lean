import Hypergraph.FiniteRadiusDomination

/-!
# Finite domination with bounded local damage

This file separates the centre of a failed macro trial from the vertices which that failure
declares closed.  This distinction is essential: one Bernoulli failure may damage several arena
vertices, but it is still only one failed trial.

For a set `good` of successful trial centres, `safeSites G A good` consists of the vertices of the
finite arena `A` whose whole closed graph-neighbourhood *inside `A`* consists of good centres.  A
failed trial at `z` is allowed to close any collection of vertices in the closed neighbourhood of
`z`.  Consequently no safe vertex can ever be among the collateral damage.

The main deterministic statement in this first layer is
`safeTargetConn_implies_reaches_of_boundary_eq_empty`: if every actually closed vertex is covered
by a recorded failed centre, then a terminal exploration which has not reached its target rules out
every safe path to the target.  The corresponding pinned Bernoulli value therefore vanishes at a
dead end.  Unlike a comparison which declares every collateral vertex to be an independent
failure, this keeps the sharp failure parameter: one failed batch costs one Bernoulli coordinate,
not one coordinate per damaged vertex.
-/

noncomputable section

namespace KNAll.Site.BDDom

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels

namespace Safe

variable {V : Type*}

/-- A vertex is safe when every possible failed centre in its closed graph-neighbourhood, among
the centres belonging to the finite arena, is good. -/
def sites (G : SimpleGraph V) (A : Finset V) (good : Set V) : Set V :=
  {v | v ∈ A ∧ ∀ z ∈ A, (z = v ∨ G.Adj z v) → z ∈ good}

theorem mem_sites_iff (G : SimpleGraph V) (A : Finset V) (good : Set V) (v : V) :
    v ∈ sites G A good ↔ v ∈ A ∧ ∀ z ∈ A, (z = v ∨ G.Adj z v) → z ∈ good :=
  Iff.rfl

theorem self_mem_good {G : SimpleGraph V} {A : Finset V} {good : Set V} {v : V}
    (hv : v ∈ sites G A good) : v ∈ good :=
  hv.2 v hv.1 (Or.inl rfl)

theorem mono {G : SimpleGraph V} {A : Finset V} {good good' : Set V}
    (hgg' : good ⊆ good') : sites G A good ⊆ sites G A good' := by
  rintro v ⟨hvA, hv⟩
  exact ⟨hvA, fun z hzA hzv => hgg' (hv z hzA hzv)⟩

/-- The event that the safe sites contain an open path from `o` to the target inside `A`. -/
def targetConn (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) : Set (Set V) :=
  {good | sites G A good ∈ FRDom.targetConn G A o T}

theorem mem_targetConn_iff (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V)
    (good : Set V) :
    good ∈ targetConn G A o T ↔ sites G A good ∈ FRDom.targetConn G A o T :=
  Iff.rfl

theorem determinedBy_targetConn [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    (o : V) (T : Set V) : DeterminedBy (targetConn G A o T) (↑A : Set V) := by
  rw [determinedBy_iff]
  intro good good' hagree
  have hsites : sites G A good = sites G A good' := by
    ext v
    simp only [mem_sites_iff]
    constructor
    · rintro ⟨hvA, hv⟩
      refine ⟨hvA, fun z hzA hzv => ?_⟩
      have hzmem := Set.ext_iff.1 hagree z
      simp only [Set.mem_inter_iff, Finset.mem_coe, hzA, and_true] at hzmem
      exact hzmem.1 (hv z hzA hzv)
    · rintro ⟨hvA, hv⟩
      refine ⟨hvA, fun z hzA hzv => ?_⟩
      have hzmem := Set.ext_iff.1 hagree z
      simp only [Set.mem_inter_iff, Finset.mem_coe, hzA, and_true] at hzmem
      exact hzmem.2 (hv z hzA hzv)
  change sites G A good ∈ FRDom.targetConn G A o T ↔
    sites G A good' ∈ FRDom.targetConn G A o T
  rw [hsites]

theorem measurableSet_targetConn [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    (o : V) (T : Set V) : MeasurableSet (targetConn G A o T) :=
  (determinedBy_targetConn G A o T).measurableSet_of_finset

theorem isUpperSet_targetConn (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) :
    IsUpperSet (targetConn G A o T) := by
  intro good good' hgg' hgood
  exact FRDom.isUpperSet_targetConn G A o T (mono hgg') hgood

end Safe

/-! ## Transcripts -/

/-- A bounded-damage transcript.  `base.openV` and `base.closedV` record the actual macro verdicts,
including collateral closures.  `failed` records only the centres at which a trial failed. -/
@[ext]
structure Transcript (κ V : Type*) where
  base : FRDom.Transcript κ V
  failed : Finset V

namespace Transcript

variable {κ V : Type*} (h : Transcript κ V)

abbrev inspected : Finset κ := h.base.inspected
abbrev openSites : Finset κ := h.base.openSites
abbrev openV : Finset V := h.base.openV
abbrev closedV : Finset V := h.base.closedV
abbrev state : κ → Prop := h.base.state

def prob (p : κ → unitInterval) (E : Set (Set κ)) : ℝ := h.base.prob p E

theorem prob_eq (p : κ → unitInterval) (E : Set (Set κ)) :
    h.prob p E = pinnedProb p (↑h.inspected : Set κ) h.state E := rfl

theorem prob_nonneg (p : κ → unitInterval) (E : Set (Set κ)) : 0 ≤ h.prob p E :=
  pinnedProb_nonneg_coord _ _ _ _

theorem prob_le_one (p : κ → unitInterval) (E : Set (Set κ)) : h.prob p E ≤ 1 :=
  pinnedProb_le_one_coord _ _ _ _

abbrev explored (G : SimpleGraph V) (o : V) : Set V := h.base.explored G o
abbrev boundary (G : SimpleGraph V) (A : Finset V) (o : V) : Set V := h.base.boundary G A o
abbrev Reaches (G : SimpleGraph V) (o : V) (T : Set V) : Prop := h.base.Reaches G o T
abbrev Terminal (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) : Prop :=
  h.base.Terminal G A o T
abbrev undetermined [DecidableEq V] (A : Finset V) : ℕ := h.base.undetermined A

variable [DecidableEq V]

/-- The invariant needed for the safe-site comparison.  Every actual closed vertex is covered by
one genuinely failed centre in its closed graph-neighbourhood. -/
def Sound (G : SimpleGraph V) (A : Finset V) (o : V) : Prop :=
  o ∈ h.openV ∧
  Disjoint h.openV h.closedV ∧
  h.failed ⊆ h.closedV ∧
  (∀ v ∈ h.closedV, ∃ z ∈ h.failed, z ∈ A ∧ (z = v ∨ G.Adj z v))

/-- Bernoulli safe-site value.  Successful centres (the actually open vertices) are pinned true;
failed centres are pinned false.  Collateral closed vertices are deliberately not pinned. -/
def bern (a : unitInterval) (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) : ℝ :=
  pinnedProb (fun _ : V => a) (↑(h.base.openV ∪ h.failed) : Set V)
    (fun v => v ∈ h.base.openV)
    (Safe.targetConn G A o T)

variable {G : SimpleGraph V} {A : Finset V} {o : V} {T : Set V}

theorem failed_not_open (hs : h.Sound G A o) {z : V} (hz : z ∈ h.failed) :
    z ∉ h.openV := by
  exact fun hzo => Finset.disjoint_left.1 hs.2.1 hzo (hs.2.2.1 hz)

theorem safe_not_closed_of_consistent (hs : h.Sound G A o) {good : Set V}
    (hconsistent : ∀ z ∈ h.openV ∪ h.failed, (z ∈ good ↔ z ∈ h.openV))
    {v : V} (hv : v ∈ Safe.sites G A good) : v ∉ h.closedV := by
  intro hvc
  obtain ⟨z, hzf, hzA, hzv⟩ := hs.2.2.2 v hvc
  have hzgood : z ∈ good := hv.2 z hzA hzv
  have hzpin : z ∈ h.openV := (hconsistent z (Finset.mem_union_right _ hzf)).1 hzgood
  exact h.failed_not_open hs hzf hzpin

/-- At a dead end, a safe path would inductively lie in the actually explored open component,
contradicting failure to reach the target. -/
theorem safeTargetConn_implies_reaches_of_boundary_eq_empty
    (hs : h.Sound G A o) (hb : h.boundary G A o = ∅)
    {good : Set V}
    (hconsistent : ∀ z ∈ h.openV ∪ h.failed, (z ∈ good ↔ z ∈ h.openV))
    (hconn : good ∈ Safe.targetConn G A o T) : h.Reaches G o T := by
  rw [Safe.mem_targetConn_iff, FRDom.mem_targetConn_iff] at hconn
  obtain ⟨t, ht, ⟨hoSafe, hreach⟩⟩ := hconn
  have hwalk : ∀ {u v : V},
      (openSiteGraph G (Safe.sites G A good ∩ (↑A : Set V))).Walk u v →
        u ∈ h.explored G o → v ∈ h.explored G o := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons a c _ hac w ih =>
      intro ha
      refine ih ?_
      obtain ⟨hGac, _haSafe, hcSafe⟩ :=
        (openSiteGraph_adj_iff' G _ a c).1 hac
      have hcnot : c ∉ h.closedV :=
        h.safe_not_closed_of_consistent hs hconsistent hcSafe.1
      have hcopen : c ∈ h.openV := by
        by_contra hco
        have hcb : c ∈ h.boundary G A o :=
          ⟨Finset.mem_coe.1 hcSafe.2, hco, hcnot, Or.inr ⟨a, ha, hGac⟩⟩
        rw [hb] at hcb
        exact hcb
      have haopen : a ∈ h.openV := Finset.mem_coe.1 (mem_of_mem_siteCluster G _ ha)
      refine ⟨Finset.mem_coe.2 hs.1, ha.2.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact (openSiteGraph_adj_iff' G (↑h.openV : Set V) a c).2
        ⟨hGac, Finset.mem_coe.2 haopen, Finset.mem_coe.2 hcopen⟩
  obtain ⟨w⟩ := hreach
  exact ⟨t, ht, hwalk w (mem_siteCluster_self G _ (Finset.mem_coe.2 hs.1))⟩

theorem bern_eq_zero_of_boundary_eq_empty (a : unitInterval)
    (hs : h.Sound G A o) (hb : h.boundary G A o = ∅) (hr : ¬ h.Reaches G o T) :
    h.bern a G A o T = 0 := by
  unfold bern pinnedProb
  have hpre : substitute (↑(h.openV ∪ h.failed) : Set V) (fun v => v ∈ h.openV) ⁻¹'
      Safe.targetConn G A o T = ∅ := by
    ext good
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hgood
    apply hr
    refine h.safeTargetConn_implies_reaches_of_boundary_eq_empty hs hb ?_ hgood
    intro z hz
    exact mem_substitute_of_mem (fun v => v ∈ h.openV) (Finset.mem_coe.2 hz)
  rw [hpre, measureReal_empty]

theorem bern_le_prob_of_terminal (a : unitInterval) (p : κ → unitInterval)
    (hs : h.Sound G A o) (hT : h.Terminal G A o T) :
    h.bern a G A o T ≤ h.prob p {_ω : Set κ | h.Reaches G o T} := by
  by_cases hr : h.Reaches G o T
  · have hset : {_ω : Set κ | h.Reaches G o T} = Set.univ := Set.eq_univ_of_forall fun _ => hr
    rw [hset, prob, FRDom.Transcript.prob_eq, pinnedProb_univ]
    exact pinnedProb_le_one_coord _ _ _ _
  · have hb : h.boundary G A o = ∅ := hT.resolve_left hr
    rw [h.bern_eq_zero_of_boundary_eq_empty a hs hb hr]
    exact pinnedProb_nonneg_coord _ _ _ _

/-! ### One bounded-damage examination -/

variable [DecidableEq κ]

open Classical in
/-- One examination.  A success opens its centre.  A failure records the centre in `failed` and
closes both the centre and the supplied collateral set `damage`. -/
def step (z : V) (F : Finset κ) (damage : Finset V) (b : Bool) (ω : Set κ) :
    Transcript κ V where
  base :=
    { inspected := h.inspected ∪ F
      openSites := h.openSites ∪ F.filter (fun x => x ∈ ω)
      openSites_subset :=
        Finset.union_subset_union h.base.openSites_subset (Finset.filter_subset _ _)
      openV := if b then insert z h.openV else h.openV
      closedV := if b then h.closedV else insert z h.closedV ∪ damage }
  failed := if b then h.failed else insert z h.failed

variable {z : V} {F : Finset κ} {damage : Finset V} {b : Bool} {ω : Set κ}

@[simp] theorem step_inspected : (h.step z F damage b ω).inspected = h.inspected ∪ F := rfl

@[simp] theorem step_openV :
    (h.step z F damage b ω).openV = if b then insert z h.openV else h.openV := rfl

@[simp] theorem step_closedV :
    (h.step z F damage b ω).closedV =
      if b then h.closedV else insert z h.closedV ∪ damage := rfl

@[simp] theorem step_failed :
    (h.step z F damage b ω).failed = if b then h.failed else insert z h.failed := rfl

theorem step_state (x : κ) :
    (h.step z F damage b ω).state x ↔ h.state x ∨ (x ∈ F ∧ x ∈ ω) := by
  classical
  simp [state, step, FRDom.Transcript.state, Finset.mem_union, Finset.mem_filter]

theorem step_congr {damage' : Finset V} {ω' : Set κ}
    (hdamage : damage = damage') (hagree : ∀ x ∈ F, (x ∈ ω ↔ x ∈ ω')) :
    h.step z F damage b ω = h.step z F damage' b ω' := by
  classical
  subst damage'
  refine Transcript.ext ?_ rfl
  apply FRDom.Transcript.ext <;> simp only [step]
  congr 1
  exact Finset.filter_congr fun x hx => hagree x hx

/-- Splitting by the finite read pattern freezes both the recorded states and any collateral-damage
rule which depends only on that pattern. -/
theorem setOf_step_eq_biUnion (D : Set κ → Finset V)
    (hD : ∀ ω ω' : Set κ, (∀ x ∈ F, (x ∈ ω ↔ x ∈ ω')) → D ω = D ω')
    (Q : Transcript κ V → Set κ → Prop) :
    {ω : Set κ | Q (h.step z F (D ω) b ω) ω} =
      ⋃ σ ∈ F.powerset,
        (localCylinder (↑F : Set κ) (↑σ : Set κ) ∩
          {ω | Q (h.step z F (D (↑σ : Set κ)) b (↑σ : Set κ)) ω}) := by
  classical
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop,
    Finset.mem_powerset]
  constructor
  · intro hω
    let σ := F.filter (fun x => x ∈ ω)
    have hagree : ∀ x ∈ F, (x ∈ ω ↔ x ∈ (↑σ : Set κ)) := by
      intro x hx
      simp only [σ, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe]
      exact ⟨fun hxω => ⟨hx, hxω⟩, fun hxω => hxω.2⟩
    refine ⟨σ, Finset.filter_subset _ _, ?_, ?_⟩
    · intro x hx
      exact hagree x (Finset.mem_coe.1 hx)
    · have heq : h.step z F (D ω) b ω =
          h.step z F (D (↑σ : Set κ)) b (↑σ : Set κ) :=
        h.step_congr (hD ω (↑σ : Set κ) hagree) hagree
      rwa [← heq]
  · rintro ⟨σ, -, hcyl, hrun⟩
    have hagree : ∀ x ∈ F, (x ∈ ω ↔ x ∈ (↑σ : Set κ)) := fun x hx =>
      hcyl x (Finset.mem_coe.2 hx)
    have heq : h.step z F (D ω) b ω =
        h.step z F (D (↑σ : Set κ)) b (↑σ : Set κ) :=
      h.step_congr (hD ω (↑σ : Set κ) hagree) hagree
    rwa [heq]

theorem step_trial_determined :
    (h.step z F damage b ω).openV ∪ (h.step z F damage b ω).failed =
      insert z (h.openV ∪ h.failed) := by
  cases b <;> simp [Finset.insert_union, Finset.union_insert]

theorem coe_step_trial_determined :
    (↑((h.step z F damage b ω).openV ∪ (h.step z F damage b ω).failed) : Set V) =
      insert z (↑(h.openV ∪ h.failed) : Set V) := by
  rw [step_trial_determined, Finset.coe_insert]

theorem bern_step_congr (a : unitInterval) (G : SimpleGraph V) (A : Finset V) (o : V)
    (T : Set V) {F' : Finset κ} {damage' : Finset V} {ω' : Set κ} :
    (h.step z F damage b ω).bern a G A o T =
      (h.step z F' damage' b ω').bern a G A o T := by
  unfold bern
  rw [coe_step_trial_determined, coe_step_trial_determined]
  refine pinnedProb_congr_val _ _ (fun v _ => ?_) _
  cases b <;> simp

theorem bern_split (a : unitInterval) (G : SimpleGraph V) (A : Finset V) (o : V)
    (T : Set V) (hzo : z ∉ h.openV) (hzf : z ∉ h.failed)
    (damage₁ damage₀ : Finset V) (ω₁ ω₀ : Set κ) :
    h.bern a G A o T =
      (a : ℝ) * (h.step z F damage₁ true ω₁).bern a G A o T +
        (1 - (a : ℝ)) * (h.step z F damage₀ false ω₀).bern a G A o T := by
  have hzS : z ∉ (↑(h.openV ∪ h.failed) : Set V) := by simp [hzo, hzf]
  have hsplit := pinnedProb_split (fun _ : V => a) hzS (fun v => v ∈ h.openV)
    (Safe.measurableSet_targetConn G A o T)
  have hT : pinnedProb (fun _ : V => a) (insert z (↑(h.openV ∪ h.failed) : Set V))
      (setVal (fun v => v ∈ h.openV) z True) (Safe.targetConn G A o T) =
      (h.step z F damage₁ true ω₁).bern a G A o T := by
    unfold bern
    rw [coe_step_trial_determined]
    refine pinnedProb_congr_val _ _ (fun v _ => ?_) _
    by_cases hvz : v = z
    · subst hvz
      rw [setVal_self]
      simp
    · simp [setVal_of_ne _ hvz, hvz]
  have hF : pinnedProb (fun _ : V => a) (insert z (↑(h.openV ∪ h.failed) : Set V))
      (setVal (fun v => v ∈ h.openV) z False) (Safe.targetConn G A o T) =
      (h.step z F damage₀ false ω₀).bern a G A o T := by
    unfold bern
    rw [coe_step_trial_determined]
    refine pinnedProb_congr_val _ _ (fun v _ => ?_) _
    by_cases hvz : v = z
    · subst hvz
      rw [setVal_self]
      simp [hzo]
    · simp [setVal_of_ne _ hvz, hvz]
  rw [bern, hsplit, hT, hF]

theorem bern_step_false_le_true (a : unitInterval) (G : SimpleGraph V) (A : Finset V)
    (o : V) (T : Set V) (damage₁ damage₀ : Finset V) (ω₁ ω₀ : Set κ) :
    (h.step z F damage₀ false ω₀).bern a G A o T ≤
      (h.step z F damage₁ true ω₁).bern a G A o T := by
  unfold bern
  rw [coe_step_trial_determined, coe_step_trial_determined]
  refine FRDom.pinnedProb_mono_val _ _ (fun v _ hv => ?_)
    (Safe.isUpperSet_targetConn G A o T)
  simp only [step_openV, Bool.false_eq_true, if_false] at hv
  simp only [step_openV, if_true]
  exact Finset.mem_insert_of_mem hv

/-- Local damage preserves `Sound`.  This is the intended constructor for downstream macro
explorations: the failed centre may close any subset of its closed graph-neighbourhood in `A`,
provided already open vertices are not closed. -/
theorem sound_step (hs : h.Sound G A o) (hzA : z ∈ A) (hzo : z ∉ h.openV)
    (hzc : z ∉ h.closedV) (hdA : damage ⊆ A)
    (hdlocal : ∀ v ∈ damage, z = v ∨ G.Adj z v)
    (hdopen : Disjoint damage h.openV) : (h.step z F damage b ω).Sound G A o := by
  cases b with
  | false =>
    refine ⟨hs.1, ?_, ?_, ?_⟩
    · rw [step_openV, step_closedV]
      simp only [Bool.false_eq_true, if_false]
      rw [Finset.disjoint_union_right]
      constructor
      · rw [Finset.disjoint_insert_right]
        exact ⟨hzo, hs.2.1⟩
      · exact hdopen.symm
    · intro x hx
      change x ∈ insert z h.failed at hx
      change x ∈ insert z h.closedV ∪ damage
      apply Finset.mem_union_left
      rw [Finset.mem_insert] at hx ⊢
      exact hx.imp_right (hs.2.2.1 ·)
    · intro v hv
      rw [step_closedV] at hv
      simp only [Bool.false_eq_true, if_false] at hv
      rcases Finset.mem_union.1 hv with hv | hv
      · rw [Finset.mem_insert] at hv
        rcases hv with hv | hv
        · exact ⟨v, by simpa [hv], by simpa [hv] using hzA, Or.inl rfl⟩
        · obtain ⟨x, hxf, hxA, hxv⟩ := hs.2.2.2 v hv
          exact ⟨x, by simp [hxf], hxA, hxv⟩
      · exact ⟨z, by simp, hzA, hdlocal v hv⟩
  | true =>
    refine ⟨Finset.mem_insert_of_mem hs.1, ?_, ?_, ?_⟩
    · rw [step_openV, step_closedV]
      simp only [if_true]
      rw [Finset.disjoint_insert_left]
      exact ⟨hzc, hs.2.1⟩
    · change h.failed ⊆ h.closedV
      exact hs.2.2.1
    · simpa [step_failed, step_closedV] using hs.2.2.2

/-- Each examination determines at least its centre, even if it also closes collateral vertices. -/
theorem undetermined_step_lt (A : Finset V) (hzA : z ∈ A) (hzo : z ∉ h.openV)
    (hzc : z ∉ h.closedV) :
    (h.step z F damage b ω).undetermined A < h.undetermined A := by
  change (h.step z F damage b ω).base.undetermined A < h.base.undetermined A
  have hbase := h.base.undetermined_step (F := F) (b := b) (ω := ω) hzA hzo hzc
  have hle : (h.step z F damage b ω).base.undetermined A ≤
      (h.base.step z F b ω).undetermined A := by
    unfold FRDom.Transcript.undetermined
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_union] at hv ⊢
    refine ⟨hv.1, ?_⟩
    cases b with
    | false =>
      simp only [step_openV, step_closedV, Bool.false_eq_true, if_false,
        FRDom.Transcript.step_openV, FRDom.Transcript.step_closedV] at hv ⊢
      intro hvdet
      apply hv.2
      rcases hvdet with hvdet | hvdet
      · exact Or.inl hvdet
      · exact Or.inr (Finset.mem_union_left _ hvdet)
    | true =>
      simpa only [step_openV, step_closedV, if_true,
        FRDom.Transcript.step_openV, FRDom.Transcript.step_closedV] using hv.2
  have hbase_lt : (h.base.step z F b ω).undetermined A < h.base.undetermined A := by
    omega
  exact lt_of_le_of_lt hle hbase_lt

end Transcript

/-! ## Adaptive explorations -/

/-- An adaptive finite exploration in which a failed examination can close collateral vertices.
The only probabilistic verdict is success or failure of the chosen centre.  `damage h ω` may vary
with the freshly read pattern, but `damage_congr` says it reads no coordinates outside `region h`.
All geometric restrictions on the damage are conveniently packaged in `Admissible`; the field
`admissible_sound` exposes exactly the invariant used by the comparison theorem. -/
structure Exploration (κ : Type*) [DecidableEq κ] {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (o : V) (T : Set V) where
  density : κ → unitInterval
  Admissible : Transcript κ V → Prop
  next : Transcript κ V → V
  region : Transcript κ V → Finset κ
  damage : Transcript κ V → Set κ → Finset V
  succ : Transcript κ V → Set (Set κ)
  succ_measurable : ∀ h, MeasurableSet (succ h)
  next_mem_boundary : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    next h ∈ h.boundary G A o
  region_fresh : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    Disjoint (region h) h.inspected
  damage_congr : ∀ h ω ω',
    (∀ x ∈ region h, (x ∈ ω ↔ x ∈ ω')) → damage h ω = damage h ω'
  succ_determinedBy : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    DeterminedBy (succ h) (↑(h.inspected ∪ region h) : Set κ)
  step_admissible : ∀ h, Admissible h → ¬ h.Terminal G A o T →
    ∀ (b : Bool) (ω : Set κ), (b = true ↔ ω ∈ succ h) →
      Admissible (h.step (next h) (region h) (damage h ω) b ω)
  admissible_sound : ∀ h, Admissible h → h.Sound G A o

namespace Exploration

variable {κ V : Type*} [DecidableEq κ] [DecidableEq V]
  {G : SimpleGraph V} {A : Finset V} {o : V} {T : Set V}
  (E : Exploration κ G A o T)

open Classical in
def bit (h : Transcript κ V) (ω : Set κ) : Bool := decide (ω ∈ E.succ h)

theorem bit_eq_true_iff (h : Transcript κ V) (ω : Set κ) :
    E.bit h ω = true ↔ ω ∈ E.succ h := by simp [bit]

theorem bit_of_mem {h : Transcript κ V} {ω : Set κ} (hω : ω ∈ E.succ h) :
    E.bit h ω = true := (E.bit_eq_true_iff h ω).2 hω

theorem bit_of_notMem {h : Transcript κ V} {ω : Set κ} (hω : ω ∉ E.succ h) :
    E.bit h ω = false := by
  have := (E.bit_eq_true_iff h ω).not.2 hω
  simpa using this

def advance (h : Transcript κ V) (ω : Set κ) : Transcript κ V :=
  h.step (E.next h) (E.region h) (E.damage h ω) (E.bit h ω) ω

theorem advance_admissible {h : Transcript κ V} (hadm : E.Admissible h)
    (hT : ¬ h.Terminal G A o T) (ω : Set κ) : E.Admissible (E.advance h ω) :=
  E.step_admissible h hadm hT _ ω (E.bit_eq_true_iff h ω)

theorem undetermined_advance_lt {h : Transcript κ V} (hadm : E.Admissible h)
    (hT : ¬ h.Terminal G A o T) (ω : Set κ) :
    (E.advance h ω).undetermined A < h.undetermined A := by
  obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
  exact h.undetermined_step_lt A hzA hzo hzc

open Classical in
def run (E : Exploration κ G A o T) : ℕ → Transcript κ V → Set κ → Transcript κ V
  | 0, h, _ => h
  | n + 1, h, ω =>
      if h.Terminal G A o T then h else run E n (E.advance h ω) ω

@[simp] theorem run_zero (h : Transcript κ V) (ω : Set κ) : E.run 0 h ω = h := rfl

theorem run_succ_of_terminal {h : Transcript κ V} (hT : h.Terminal G A o T)
    (n : ℕ) (ω : Set κ) : E.run (n + 1) h ω = h := by simp [run, hT]

theorem run_succ_of_not_terminal {h : Transcript κ V} (hT : ¬ h.Terminal G A o T)
    (n : ℕ) (ω : Set κ) : E.run (n + 1) h ω = E.run n (E.advance h ω) ω := by
  simp [run, hT]

theorem terminal_run :
    ∀ (n : ℕ) (h : Transcript κ V), E.Admissible h → h.undetermined A ≤ n →
      ∀ ω : Set κ, (E.run n h ω).Terminal G A o T := by
  intro n
  induction n with
  | zero =>
    intro h _ hn ω
    rw [run_zero]
    exact h.base.terminal_of_undetermined_eq_zero G A o T (Nat.le_zero.1 hn)
  | succ n ih =>
    intro h hadm hn ω
    by_cases hT : h.Terminal G A o T
    · rw [E.run_succ_of_terminal hT]
      exact hT
    · rw [E.run_succ_of_not_terminal hT]
      refine ih _ (E.advance_admissible hadm hT ω) ?_ ω
      have hlt := E.undetermined_advance_lt hadm hT ω
      omega

/-! ### Measurability of a complete finite run -/

theorem setOf_run_succ_eq {h : Transcript κ V} (hT : ¬ h.Terminal G A o T)
    (P : Transcript κ V → Prop) (n : ℕ) :
    {ω : Set κ | P (E.run (n + 1) h ω)} =
      (E.succ h ∩ {ω | P (E.run n
        (h.step (E.next h) (E.region h) (E.damage h ω) true ω) ω)}) ∪
      ((E.succ h)ᶜ ∩ {ω | P (E.run n
        (h.step (E.next h) (E.region h) (E.damage h ω) false ω) ω)}) := by
  ext ω
  by_cases hω : ω ∈ E.succ h
  · rw [Set.mem_setOf_eq, E.run_succ_of_not_terminal hT, advance, E.bit_of_mem hω]
    simp [hω]
  · rw [Set.mem_setOf_eq, E.run_succ_of_not_terminal hT, advance, E.bit_of_notMem hω]
    simp [hω]

theorem measurableSet_setOf_run (P : Transcript κ V → Prop) :
    ∀ (n : ℕ) (h : Transcript κ V), MeasurableSet {ω : Set κ | P (E.run n h ω)} := by
  intro n
  induction n with
  | zero =>
    intro h
    simpa only [run_zero] using (MeasurableSet.const (α := Set κ) (P h))
  | succ n ih =>
    intro h
    by_cases hT : h.Terminal G A o T
    · have heq : {ω : Set κ | P (E.run (n + 1) h ω)} = {_ω : Set κ | P h} := by
        ext ω
        rw [Set.mem_setOf_eq, E.run_succ_of_terminal hT]
        rfl
      rw [heq]
      exact MeasurableSet.const _
    · have hbranch : ∀ b : Bool, MeasurableSet {ω : Set κ | P (E.run n
          (h.step (E.next h) (E.region h) (E.damage h ω) b ω) ω)} := by
        intro b
        rw [h.setOf_step_eq_biUnion (E.damage h) (E.damage_congr h)
          (fun k ω => P (E.run n k ω))]
        exact Finset.measurableSet_biUnion _ fun σ _ =>
          (measurableSet_localCylinder (E.region h).finite_toSet.countable _).inter (ih _)
      rw [E.setOf_run_succ_eq hT P n]
      exact ((E.succ_measurable h).inter (hbranch true)).union
        ((E.succ_measurable h).compl.inter (hbranch false))

theorem measurableSet_setOf_run_step (P : Transcript κ V → Prop) (n : ℕ)
    (h : Transcript κ V) (z : V) (F : Finset κ) (D : Set κ → Finset V)
    (hD : ∀ ω ω' : Set κ, (∀ x ∈ F, (x ∈ ω ↔ x ∈ ω')) → D ω = D ω')
    (b : Bool) :
    MeasurableSet {ω : Set κ | P (E.run n (h.step z F (D ω) b ω) ω)} := by
  rw [h.setOf_step_eq_biUnion D hD (fun k ω => P (E.run n k ω))]
  exact Finset.measurableSet_biUnion _ fun σ _ =>
    (measurableSet_localCylinder F.finite_toSet.countable _).inter
      (E.measurableSet_setOf_run P n _)

/-! ### Bounded-damage domination -/

/-- A continuation estimate can be averaged over one finite branch event. -/
theorem branch_linear (p : κ → unitInterval) (k : Transcript κ V) (c : ℝ)
    {B Y : Set (Set κ)} (hBdet : DeterminedBy B (↑k.inspected : Set κ))
    (hYm : MeasurableSet Y)
    (hc : substitute (↑k.inspected : Set κ) k.state ∅ ∈ B → c ≤ k.prob p Y) :
    c * k.prob p B ≤ k.prob p (B ∩ Y) := by
  have hBm : MeasurableSet B := hBdet.measurableSet_of_finset
  rw [Transcript.prob_eq, Transcript.prob_eq]
  refine FRDom.le_pinnedProb_inter_of_forall_extend_of_mem p hBm hYm
    (∅ : Finset κ) (↑k.inspected : Set κ) (by simp) k.state (by simpa using hBdet) ?_
  intro val' hval' hmem
  let ω₀ : Set κ := substitute (↑k.inspected : Set κ) val' ∅
  have hω₀B : ω₀ ∈ B := by simpa [ω₀] using hmem
  have hcan : substitute (↑k.inspected : Set κ) k.state ∅ ∈ B := by
    refine ((determinedBy_iff B (↑k.inspected : Set κ)).1 hBdet ω₀
      (substitute (↑k.inspected : Set κ) k.state ∅) ?_).1 hω₀B
    ext x
    simp only [Set.mem_inter_iff]
    by_cases hx : x ∈ (↑k.inspected : Set κ)
    · rw [mem_substitute_of_mem _ hx, mem_substitute_of_mem _ hx]
      exact and_congr (hval' x hx) Iff.rfl
    · simp [hx]
  refine (hc hcan).trans_eq ?_
  rw [Transcript.prob_eq, Finset.coe_empty, Set.union_empty]
  exact pinnedProb_congr_val p _ (fun x hx => (hval' x hx).symm) _

/-- **Finite adaptive bounded-damage domination.**  If every trial centre succeeds with pinned
probability at least `a`, then the actual damaged exploration reaches its target at least as often
as Bernoulli(`a`) centres contain a safe path.  A safe path is eroded by one graph layer, so one
failed centre protects against every collateral closure it can cause. -/
theorem bern_le_prob_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : ℝ) ≤ h.prob E.density (E.succ h)) :
    ∀ (n : ℕ) (h : Transcript κ V), E.Admissible h → h.undetermined A ≤ n →
      h.bern a G A o T ≤
        h.prob E.density {ω | (E.run n h ω).Reaches G o T} := by
  intro n
  induction n with
  | zero =>
    intro h hadm hn
    have hT : h.Terminal G A o T :=
      h.base.terminal_of_undetermined_eq_zero G A o T (Nat.le_zero.1 hn)
    simpa only [run_zero] using
      h.bern_le_prob_of_terminal a E.density (E.admissible_sound h hadm) hT
  | succ n ih =>
    intro h hadm hn
    by_cases hT : h.Terminal G A o T
    · have heq : {ω : Set κ | (E.run (n + 1) h ω).Reaches G o T} =
          {_ω : Set κ | h.Reaches G o T} := by
        ext ω
        rw [Set.mem_setOf_eq, E.run_succ_of_terminal hT]
        rfl
      rw [heq]
      exact h.bern_le_prob_of_terminal a E.density (E.admissible_sound h hadm) hT
    · obtain ⟨hzA, hzo, hzc, -⟩ := E.next_mem_boundary h hadm hT
      have hs := E.admissible_sound h hadm
      have hzf : E.next h ∉ h.failed := fun hzf => hzc (hs.2.2.1 hzf)
      have hfresh : Disjoint (↑(E.region h) : Set κ) (↑h.inspected : Set κ) :=
        Finset.disjoint_coe.2 (E.region_fresh h hadm hT)
      have hund : ∀ (b : Bool) (ω : Set κ),
          (h.step (E.next h) (E.region h) (E.damage h ω) b ω).undetermined A ≤ n := by
        intro b ω
        have hlt := h.undetermined_step_lt A hzA hzo hzc
          (F := E.region h) (damage := E.damage h ω) (b := b) (ω := ω)
        omega
      let cT := (h.step (E.next h) (E.region h) ∅ true ∅).bern a G A o T
      let cF := (h.step (E.next h) (E.region h) ∅ false ∅).bern a G A o T
      have key : ∀ (b : Bool) (B : Set (Set κ)),
          DeterminedBy B ((↑h.inspected : Set κ) ∪ ↑(E.region h)) → MeasurableSet B →
          (∀ ω₀ ∈ B, (b = true ↔ ω₀ ∈ E.succ h)) →
          (if b then cT else cF) * h.prob E.density B ≤
            h.prob E.density (B ∩ {ω | (E.run n
              (h.step (E.next h) (E.region h) (E.damage h ω) b ω) ω).Reaches G o T}) := by
        intro b B hBdet hBm hbB
        rw [Transcript.prob_eq, Transcript.prob_eq]
        refine FRDom.le_pinnedProb_inter_of_forall_extend_of_mem E.density hBm
          (E.measurableSet_setOf_run_step (fun h' => h'.Reaches G o T) n h
            (E.next h) (E.region h) (E.damage h) (E.damage_congr h) b)
          (E.region h) (↑h.inspected : Set κ) hfresh h.state hBdet ?_
        intro val' hval' hmem
        set S : Set κ := (↑h.inspected : Set κ) ∪ ↑(E.region h) with hS
        set ω₀ : Set κ := substitute S val' ∅ with hω₀
        have hsub : (↑(E.region h) : Set κ) ⊆ S := Set.subset_union_right
        have hagree : ∀ ω : Set κ, ∀ x ∈ E.region h,
            (x ∈ substitute S val' ω ↔ x ∈ ω₀) := by
          intro ω x hx
          rw [mem_substitute_of_mem val' (hsub (Finset.mem_coe.2 hx)), hω₀,
            mem_substitute_of_mem val' (hsub (Finset.mem_coe.2 hx))]
        have hconst : ∀ ω : Set κ,
            h.step (E.next h) (E.region h) (E.damage h (substitute S val' ω)) b
                (substitute S val' ω) =
              h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀ := by
          intro ω
          exact h.step_congr (E.damage_congr h _ _ (hagree ω)) (hagree ω)
        have hpre : pinnedProb E.density S val'
              {ω | (E.run n (h.step (E.next h) (E.region h) (E.damage h ω) b ω) ω).Reaches G o T} =
            pinnedProb E.density S val'
              {ω | (E.run n
                (h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀) ω).Reaches G o T} := by
          unfold pinnedProb
          congr 1
          ext ω
          simp only [Set.mem_preimage, Set.mem_setOf_eq, hconst ω]
        have hinsp :
            (↑(h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀).inspected : Set κ) = S := by
          rw [Transcript.step_inspected, Finset.coe_union, hS]
        have hstate : ∀ x ∈ S, (val' x ↔
            (h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀).state x) := by
          intro x hx
          rw [Transcript.step_state]
          rcases hx with hx | hx
          · have hxF : x ∉ E.region h := fun hxF =>
              Set.disjoint_left.1 hfresh (Finset.mem_coe.2 hxF) hx
            rw [hval' x hx]
            constructor
            · exact fun hv => Or.inl hv
            · rintro (hv | ⟨hxF', -⟩)
              · exact hv
              · exact absurd hxF' hxF
          · have hxI : x ∉ h.inspected := fun hxI =>
              Set.disjoint_left.1 hfresh hx (Finset.mem_coe.2 hxI)
            have hst : ¬ h.state x := fun hsx => hxI (h.base.mem_inspected_of_state hsx)
            have hxω₀ : x ∈ ω₀ ↔ val' x := by
              rw [hω₀, mem_substitute_of_mem val' (hsub hx)]
            constructor
            · exact fun hv => Or.inr ⟨Finset.mem_coe.1 hx, hxω₀.2 hv⟩
            · rintro (hsx | ⟨-, hω⟩)
              · exact absurd hsx hst
              · exact hxω₀.1 hω
        have hchild : pinnedProb E.density S val'
              {ω | (E.run n
                (h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀) ω).Reaches G o T} =
            (h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀).prob E.density
              {ω | (E.run n
                (h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀) ω).Reaches G o T} := by
          rw [Transcript.prob_eq, hinsp]
          exact pinnedProb_congr_val E.density _ hstate _
        rw [hpre, hchild]
        have hadm₁ : E.Admissible
            (h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀) :=
          E.step_admissible h hadm hT b ω₀ (hbB ω₀ (by simpa [ω₀] using hmem))
        have hih := ih _ hadm₁ (hund b ω₀)
        have hbern : (h.step (E.next h) (E.region h) (E.damage h ω₀) b ω₀).bern
              a G A o T = if b then cT else cF := by
          cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
          · exact h.bern_step_congr a G A o T
          · exact h.bern_step_congr a G A o T
        rwa [hbern] at hih
      have hJdet : DeterminedBy (E.succ h)
          ((↑h.inspected : Set κ) ∪ ↑(E.region h)) := by
        have := E.succ_determinedBy h hadm hT
        rwa [Finset.coe_union] at this
      have hJm : MeasurableSet (E.succ h) := E.succ_measurable h
      have hkeyT := key true (E.succ h) hJdet hJm (fun ω₀ hω₀ => by simp [hω₀])
      have hkeyF := key false (E.succ h)ᶜ (determinedBy_compl hJdet) hJm.compl
        (fun ω₀ hω₀ => by simpa using hω₀)
      have hq : (a : ℝ) ≤ h.prob E.density (E.succ h) := hstep h hadm hT
      have hq1 : h.prob E.density (E.succ h) ≤ 1 := h.prob_le_one _ _
      have hqc : h.prob E.density (E.succ h)ᶜ =
          1 - h.prob E.density (E.succ h) := by
        rw [Transcript.prob_eq, Transcript.prob_eq]
        exact pinnedProb_compl _ _ _ hJm
      have hsplit : h.prob E.density
            {ω | (E.run (n + 1) h ω).Reaches G o T} =
          h.prob E.density (E.succ h ∩ {ω | (E.run n
            (h.step (E.next h) (E.region h) (E.damage h ω) true ω) ω).Reaches G o T}) +
          h.prob E.density ((E.succ h)ᶜ ∩ {ω | (E.run n
            (h.step (E.next h) (E.region h) (E.damage h ω) false ω) ω).Reaches G o T}) := by
        rw [Transcript.prob_eq, Transcript.prob_eq, Transcript.prob_eq,
          E.setOf_run_succ_eq hT (fun h' => h'.Reaches G o T) n]
        refine pinnedProb_union _ _ _
          (Set.disjoint_left.2 fun ω hω hω' => hω'.1 hω.1) ?_
        exact hJm.compl.inter
          (E.measurableSet_setOf_run_step (fun h' => h'.Reaches G o T) n h
            (E.next h) (E.region h) (E.damage h) (E.damage_congr h) false)
      have hbern := h.bern_split a G A o T hzo hzf
        (∅ : Finset V) (∅ : Finset V) (∅ : Set κ) (∅ : Set κ)
        (F := E.region h)
      have hmono := h.bern_step_false_le_true a G A o T
        (∅ : Finset V) (∅ : Finset V) (∅ : Set κ) (∅ : Set κ)
        (F := E.region h) (z := E.next h)
      change cT * h.prob E.density (E.succ h) ≤ _ at hkeyT
      change cF * h.prob E.density (E.succ h)ᶜ ≤ _ at hkeyF
      rw [hqc] at hkeyF
      have hprod : (0 : ℝ) ≤ (h.prob E.density (E.succ h) - a) * (cT - cF) := by
        apply mul_nonneg
        · linarith
        · dsimp only [cT, cF]
          exact sub_nonneg.2 hmono
      rw [hbern, hsplit]
      dsimp only [cT, cF] at hkeyT hkeyF hprod ⊢
      nlinarith [hkeyT, hkeyF, hprod]

/-- Start-state form: the root is already accepted, and no physical coordinates have been read.
The benchmark is safe-site Bernoulli percolation with the root centre pinned open. -/
theorem pinnedProb_safeTargetConn_le_real_run {a : unitInterval}
    (hstep : ∀ h, E.Admissible h → ¬ h.Terminal G A o T →
      (a : ℝ) ≤ h.prob E.density (E.succ h))
    (h₀ : Transcript κ V) (hadm : E.Admissible h₀) (hins : h₀.inspected = ∅)
    (hopen : h₀.openV = {o}) (hfailed : h₀.failed = ∅)
    (n : ℕ) (hn : h₀.undetermined A ≤ n) :
    pinnedProb (fun _ : V => a) {o} (fun _ => True) (Safe.targetConn G A o T) ≤
      (prodBernoulli E.density).real {ω | (E.run n h₀ ω).Reaches G o T} := by
  have hmain := E.bern_le_prob_run hstep n h₀ hadm hn
  rw [Transcript.prob_eq, hins, Finset.coe_empty, pinnedProb_empty] at hmain
  refine le_trans (le_of_eq ?_) hmain
  unfold Transcript.bern
  have hopen' : h₀.base.openV = {o} := hopen
  rw [hopen', hfailed, Finset.union_empty, Finset.coe_singleton]
  refine pinnedProb_congr_val _ _ (fun v hv => ?_) _
  rw [Set.mem_singleton_iff] at hv
  simp [hv]

end Exploration

#print axioms KNAll.Site.BDDom.Transcript.safeTargetConn_implies_reaches_of_boundary_eq_empty
#print axioms KNAll.Site.BDDom.Transcript.bern_eq_zero_of_boundary_eq_empty
#print axioms KNAll.Site.BDDom.Transcript.bern_le_prob_of_terminal
#print axioms KNAll.Site.BDDom.Transcript.bern_split
#print axioms KNAll.Site.BDDom.Transcript.bern_step_false_le_true
#print axioms KNAll.Site.BDDom.Transcript.sound_step
#print axioms KNAll.Site.BDDom.Transcript.undetermined_step_lt
#print axioms KNAll.Site.BDDom.Exploration.terminal_run
#print axioms KNAll.Site.BDDom.Exploration.bern_le_prob_run
#print axioms KNAll.Site.BDDom.Exploration.pinnedProb_safeTargetConn_le_real_run

end KNAll.Site.BDDom

end
