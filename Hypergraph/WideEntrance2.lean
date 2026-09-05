import Hypergraph.PinnedEntrance

/-!
# Widening the entrance of the macro corridor

`PinEnt.forcedCorridorEvent_subset_tipOut_open` identifies the structural bottleneck in the
current macro exploration: the recorded source is `MacroExp.tip d r w z`, and the only neighbour
of that source in `MacroExp.E d r t w z` is `MacroExp.tipOut d r w z`.  Thus the current incoming
connection event forces one fresh coordinate to be open.

This file records the elementary probability calculation that a widened entrance must exploit.
If a finite entry set `F` has `m` distinct fresh sites and success only asks that *some* member of
`F` be open, its probability is exactly `1 - (1-q)^m`.  It is therefore strictly larger than `q`
as soon as `0 < q < 1` and `2 <= m`, and it exceeds the certificate threshold
`1 - eps/8` once `m` is large enough.

This calculation does not claim that the macro exploration has already been widened.  What it
supplies is one arithmetic fact and its gateway consequence, and nothing about the transition
relation.  Three points fix its scope.

The current `MacroExp.succ` no longer names a source: its incoming clause asks for a connection
from the recorded origin `MacroExp.emb 0` into the target box, and the deleted `Good.stub` field,
which used to record one designated tip per pending direction, is gone.  The exploration therefore
does not need widening at a *source*; it needs the estimate of `RecordedEntry.SourceEstimate` at
the origin, which is stated in `KN/SourceEstimate.lean` and is assumed, not proved.

The wide events here are existential over a finite set `F`.  That is exactly why they escape the
one-site cap of `PinEnt.forcedCorridorExperiment_prob_le`.  The advantage survives only while the
source stays existential: replacing `∃ g ∈ F` by an equation `g = MacroExp.src ...` reinstates the
deleted stub condition, and `math/RECORDED_OPEN_ENTRY.md` §2 refutes that condition at reachable
good transcripts.

What is still missing at an accepting macro step is the geometric data, not this arithmetic: a
large recorded set on the tail face of the newly accepted vertex, an assignment of its members to
adjacent unread sites of each outgoing corridor, and a proof that an accepted head creates such a
set again.  `Corridor.inspected_disjoint_pending_E` already supplies freshness; the wide
accepted-head clause is not proved anywhere, and `wideLongBoxEvent_subset_wideEntranceEvent` runs
in the direction of an obstruction, not of a lower bound.  The one place where the wide mechanism
is carried all the way to a crossing is the initial step, `InitEnt.initial_entrance`.
-/

noncomputable section

namespace KNAll.Site.Wide2

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.LeftImp2 KNAll.Site.MacroExp

variable {d : ℕ}

/-- The widened local entrance event: at least one site of the finite entry set is open. -/
def wideEntranceEvent (F : Finset (Site d)) : Set (SiteConfig (Site d)) :=
  {ω | ∃ x ∈ F, x ∈ ω}

/-- The widened event is determined by precisely the proposed entry set. -/
theorem determinedBy_wideEntranceEvent (F : Finset (Site d)) :
    DeterminedBy (wideEntranceEvent F) (↑F : Set (Site d)) := by
  simpa only [wideEntranceEvent] using
    (KNAll.Site.TargetExt.determinedBy_exists_mem F)

theorem measurableSet_wideEntranceEvent (F : Finset (Site d)) :
    MeasurableSet (wideEntranceEvent F) :=
  (determinedBy_wideEntranceEvent F).measurableSet_of_finset

/-- The widened entrance packaged as the same finite experiment type used by certificates. -/
def wideEntranceExperiment (F : Finset (Site d)) : CylinderExperiment d where
  support := F
  event := wideEntranceEvent F
  determined := determinedBy_wideEntranceEvent F
  measurable' := measurableSet_wideEntranceEvent F

@[simp] theorem wideEntranceExperiment_support (F : Finset (Site d)) :
    (wideEntranceExperiment F).support = F := rfl

/-- Exact product-law probability of a widened entrance with `|F|` fresh alternatives. -/
theorem wideEntranceExperiment_prob_eq (F : Finset (Site d)) (q : unitInterval) :
    (wideEntranceExperiment F).prob q = 1 - (1 - (q : ℝ)) ^ F.card := by
  have hcompl :
      wideEntranceEvent F = {ω : SiteConfig (Site d) | ∀ x ∈ F, x ∉ ω}ᶜ := by
    ext ω
    simp [wideEntranceEvent]
  have hm : MeasurableSet {ω : SiteConfig (Site d) | ∀ x ∈ F, x ∉ ω} :=
    measurableSet_forall_notMem_of_countable
      (T := (↑F : Set (Site d))) F.finite_toSet.countable
  change (prodBernoulli (fun _ : Site d => q)).real (wideEntranceEvent F) = _
  rw [hcompl, measureReal_compl hm, probReal_univ,
    prodBernoulli_real_forall_notMem]
  simp

/-- In particular, `1 - (1-q)^|F|` is a machine-checked lower bound, with equality. -/
theorem one_sub_pow_le_wideEntranceExperiment_prob (F : Finset (Site d))
    (q : unitInterval) :
    1 - (1 - (q : ℝ)) ^ F.card ≤ (wideEntranceExperiment F).prob q := by
  rw [wideEntranceExperiment_prob_eq]

/-- Two or more independent entry sites already defeat every one-coordinate `<= q` cap. -/
theorem q_lt_wideEntranceExperiment_prob (F : Finset (Site d)) (q : unitInterval)
    (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (hF : 2 ≤ F.card) :
    (q : ℝ) < (wideEntranceExperiment F).prob q := by
  have hb0 : 0 ≤ 1 - (q : ℝ) := by linarith
  have hb1 : 1 - (q : ℝ) ≤ 1 := by linarith
  have hpow : (1 - (q : ℝ)) ^ F.card ≤ (1 - (q : ℝ)) ^ 2 :=
    pow_le_pow_of_le_one hb0 hb1 hF
  rw [wideEntranceExperiment_prob_eq]
  nlinarith [sq_nonneg (q : ℝ)]

/-! ## The corresponding set-source connection event -/

/-- Open every member of the recorded entry set `S` for free.  This is the finite-set analogue of
`PinEnt.forcedSourceEvent`, which opens one recorded source for free. -/
def forceOpenEntrySet (S : Finset (Site d)) (ω : SiteConfig (Site d)) :
    SiteConfig (Site d) :=
  (↑S : Set (Site d)) ∪ ω

/-- A genuine set-source entrance event.  Some recorded source in `S`, after all of `S` is opened
for free, is connected inside `S ∪ Reg` to the gateway face `F`. -/
def wideGatewayConnectionEvent (Reg S F : Finset (Site d)) :
    Set (SiteConfig (Site d)) :=
  {ω | ∃ s ∈ S,
    forceOpenEntrySet S ω ∈
      connWithinSet (zdGraph d) (↑(S ∪ Reg) : Set (Site d)) s (↑F : Set (Site d))}

/-- If every gateway is in the corridor and adjacent to some recorded source, opening any gateway
realizes the set-source connection event. -/
theorem wideEntranceEvent_subset_wideGatewayConnectionEvent
    (Reg S F : Finset (Site d)) (hFReg : F ⊆ Reg)
    (hAdj : ∀ g ∈ F, ∃ s ∈ S, (zdGraph d).Adj s g) :
    wideEntranceEvent F ⊆ wideGatewayConnectionEvent Reg S F := by
  rintro ω ⟨g, hgF, hgω⟩
  obtain ⟨s, hsS, hsg⟩ := hAdj g hgF
  refine ⟨s, hsS, ?_⟩
  rw [mem_connWithinSet_iff]
  refine ⟨g, Finset.mem_coe.2 hgF, ?_⟩
  rw [mem_connWithin_iff]
  have hsOpen : s ∈ forceOpenEntrySet S ω :=
    Set.mem_union_left ω (Finset.mem_coe.2 hsS)
  have hgOpen : g ∈ forceOpenEntrySet S ω :=
    Set.mem_union_right (↑S : Set (Site d)) hgω
  have hsDom : s ∈ (↑(S ∪ Reg) : Set (Site d)) :=
    Finset.mem_coe.2 (Finset.mem_union_left Reg hsS)
  have hgDom : g ∈ (↑(S ∪ Reg) : Set (Site d)) :=
    Finset.mem_coe.2 (Finset.mem_union_right S (hFReg hgF))
  refine ⟨⟨hsOpen, hsDom⟩, SimpleGraph.Adj.reachable ?_⟩
  exact (openSiteGraph_adj_iff' (zdGraph d)
    (forceOpenEntrySet S ω ∩ (↑(S ∪ Reg) : Set (Site d))) s g).2
      ⟨hsg, ⟨hsOpen, hsDom⟩, ⟨hgOpen, hgDom⟩⟩

/-- The actual set-source connection event inherits the full many-gateway lower bound. -/
theorem one_sub_pow_le_wideGatewayConnectionEvent_prob
    (Reg S F : Finset (Site d)) (q : unitInterval) (hFReg : F ⊆ Reg)
    (hAdj : ∀ g ∈ F, ∃ s ∈ S, (zdGraph d).Adj s g) :
    1 - (1 - (q : ℝ)) ^ F.card ≤
      (siteBernoulli (fun _ : Site d => q)).real (wideGatewayConnectionEvent Reg S F) := by
  rw [← wideEntranceExperiment_prob_eq]
  change (siteBernoulli (fun _ : Site d => q)).real (wideEntranceEvent F) ≤ _
  exact measureReal_mono
    (wideEntranceEvent_subset_wideGatewayConnectionEvent Reg S F hFReg hAdj)
    (measure_ne_top _ _)

/-- Hence the connected set-source event itself is not subject to a one-coordinate `q` cap. -/
theorem q_lt_wideGatewayConnectionEvent_prob
    (Reg S F : Finset (Site d)) (q : unitInterval) (hFReg : F ⊆ Reg)
    (hAdj : ∀ g ∈ F, ∃ s ∈ S, (zdGraph d).Adj s g)
    (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (hF : 2 ≤ F.card) :
    (q : ℝ) <
      (siteBernoulli (fun _ : Site d => q)).real (wideGatewayConnectionEvent Reg S F) := by
  calc
    (q : ℝ) < 1 - (1 - (q : ℝ)) ^ F.card := by
      rw [← wideEntranceExperiment_prob_eq]
      exact q_lt_wideEntranceExperiment_prob F q hq0 hq1 hF
    _ ≤ (siteBernoulli (fun _ : Site d => q)).real
          (wideGatewayConnectionEvent Reg S F) :=
      one_sub_pow_le_wideGatewayConnectionEvent_prob Reg S F q hFReg hAdj

/-- Consequently the connected set-source event exceeds the certificate threshold whenever the
entry face is large enough to make its all-closed probability smaller than `C.eps/8`. -/
theorem certificateThreshold_lt_wideGatewayConnectionEvent_prob
    (C : Certificate2 d) (Reg S F : Finset (Site d)) (q : unitInterval)
    (hFReg : F ⊆ Reg) (hAdj : ∀ g ∈ F, ∃ s ∈ S, (zdGraph d).Adj s g)
    (hlarge : (1 - (q : ℝ)) ^ F.card < C.eps / 8) :
    1 - C.eps / 8 <
      (siteBernoulli (fun _ : Site d => q)).real (wideGatewayConnectionEvent Reg S F) := by
  calc
    1 - C.eps / 8 < 1 - (1 - (q : ℝ)) ^ F.card := by linarith
    _ ≤ (siteBernoulli (fun _ : Site d => q)).real
          (wideGatewayConnectionEvent Reg S F) :=
      one_sub_pow_le_wideGatewayConnectionEvent_prob Reg S F q hFReg hAdj

/-- Literal "for a large enough entry face" form for the connected set-source event. -/
theorem eventually_wideGatewayConnectionEvent_prob_gt_certificateThreshold
    (C : Certificate2 d) (q : unitInterval) (hε : 0 < C.eps) (hq : 0 < (q : ℝ)) :
    ∃ m₀ : ℕ, ∀ (Reg S F : Finset (Site d)), m₀ ≤ F.card → F ⊆ Reg →
      (∀ g ∈ F, ∃ s ∈ S, (zdGraph d).Adj s g) →
      1 - C.eps / 8 <
        (siteBernoulli (fun _ : Site d => q)).real (wideGatewayConnectionEvent Reg S F) := by
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one (show 0 < C.eps / 8 by positivity)
    (show 1 - (q : ℝ) < 1 by linarith)
  refine ⟨m₀, ?_⟩
  intro Reg S F hcard hFReg hAdj
  have hb0 : 0 ≤ 1 - (q : ℝ) := sub_nonneg.2 q.2.2
  have hb1 : 1 - (q : ℝ) ≤ 1 := by linarith [q.2.1]
  have hpow : (1 - (q : ℝ)) ^ F.card ≤ (1 - (q : ℝ)) ^ m₀ :=
    pow_le_pow_of_le_one hb0 hb1 hcard
  exact certificateThreshold_lt_wideGatewayConnectionEvent_prob C Reg S F q hFReg hAdj
    (hpow.trans_lt hm₀)

/-! The existing corridor-separation development is strong enough for a widened gateway set. -/

/-- Every gateway subset of a fresh pending corridor is fresh.  The premise is supplied for good,
nonterminal transcripts by `Corridor.inspected_disjoint_pending_E`; thus widening only has to prove
that its new geometric gateway set is contained in `E`. -/
theorem entrySet_fresh_of_subset_pending_E
    {r t n : ℕ} (h : Tr d) (F : Finset (Site d))
    (hF : F ⊆ E d r t (pendW d n h) (pendZ d n h))
    (hfresh : Disjoint h.inspected (E d r t (pendW d n h) (pendZ d n h))) :
    Disjoint F h.inspected := by
  rw [Finset.disjoint_left]
  intro x hxF hxI
  exact Finset.disjoint_left.1 hfresh hxI (hF hxF)

/-! A concrete family of distinct sites, used only to witness that arbitrary entry cardinalities
really occur in `Site d`.  A translate of this row can be placed on a geometric entry face. -/

variable [NeZero d]

/-- The `k`-th site of a row in the first coordinate. -/
def entryRowPoint (m : ℕ) (k : Fin m) : Site d :=
  Pi.single 0 (k : ℤ)

theorem entryRowPoint_injective (m : ℕ) :
    Function.Injective (entryRowPoint (d := d) m) := by
  intro i j hij
  have hcoord := congrFun hij (0 : Fin d)
  simp only [entryRowPoint, Pi.single_eq_same] at hcoord
  apply Fin.ext
  exact_mod_cast hcoord

/-- A concrete `m`-site candidate entry row. -/
def entryRow (d m : ℕ) [NeZero d] : Finset (Site d) :=
  Finset.univ.image (entryRowPoint (d := d) m)

@[simp] theorem entryRow_card (m : ℕ) : (entryRow d m).card = m := by
  rw [entryRow, Finset.card_image_of_injective _ (entryRowPoint_injective (d := d) m),
    Finset.card_univ, Fintype.card_fin]

/-- For every positive density and every positive certificate tolerance, every sufficiently large
entry row exceeds the exact threshold `1 - C.eps/8` used by the corridor argument. -/
theorem eventually_entryRow_prob_gt_certificateThreshold
    (C : Certificate2 d) (q : unitInterval) (hε : 0 < C.eps) (hq : 0 < (q : ℝ)) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      1 - C.eps / 8 < (wideEntranceExperiment (entryRow d m)).prob q := by
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one (show 0 < C.eps / 8 by positivity)
    (show 1 - (q : ℝ) < 1 by linarith)
  refine ⟨m₀, fun m hm => ?_⟩
  have hb0 : 0 ≤ 1 - (q : ℝ) := sub_nonneg.2 q.2.2
  have hb1 : 1 - (q : ℝ) ≤ 1 := by linarith [q.2.1]
  have hpow : (1 - (q : ℝ)) ^ m ≤ (1 - (q : ℝ)) ^ m₀ :=
    pow_le_pow_of_le_one hb0 hb1 hm
  rw [wideEntranceExperiment_prob_eq, entryRow_card]
  linarith

/-- Existential form of `eventually_entryRow_prob_gt_certificateThreshold`. -/
theorem exists_entryRow_prob_gt_certificateThreshold
    (C : Certificate2 d) (q : unitInterval) (hε : 0 < C.eps) (hq : 0 < (q : ℝ)) :
    ∃ m : ℕ, 1 - C.eps / 8 < (wideEntranceExperiment (entryRow d m)).prob q := by
  obtain ⟨m₀, hm₀⟩ := eventually_entryRow_prob_gt_certificateThreshold C q hε hq
  exact ⟨m₀, hm₀ m₀ le_rfl⟩

#print axioms KNAll.Site.Wide2.wideEntranceExperiment_prob_eq
#print axioms KNAll.Site.Wide2.one_sub_pow_le_wideEntranceExperiment_prob
#print axioms KNAll.Site.Wide2.q_lt_wideEntranceExperiment_prob
#print axioms KNAll.Site.Wide2.one_sub_pow_le_wideGatewayConnectionEvent_prob
#print axioms KNAll.Site.Wide2.q_lt_wideGatewayConnectionEvent_prob
#print axioms KNAll.Site.Wide2.certificateThreshold_lt_wideGatewayConnectionEvent_prob
#print axioms KNAll.Site.Wide2.eventually_wideGatewayConnectionEvent_prob_gt_certificateThreshold
#print axioms KNAll.Site.Wide2.entrySet_fresh_of_subset_pending_E
#print axioms KNAll.Site.Wide2.eventually_entryRow_prob_gt_certificateThreshold
#print axioms KNAll.Site.Wide2.exists_entryRow_prob_gt_certificateThreshold

end KNAll.Site.Wide2

end
