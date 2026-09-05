import Hypergraph.SourceEstimate
import Hypergraph.CorridorFreshness

/-!
# A pinned source at the entrance of a fresh corridor

`FRDom.Transcript.prob` is a pinned probability.  A source the transcript records open is open
with probability one under it.  The right ordinary-product event to compare with such a source is
therefore one that opens it *before* asking for a confined connection; its support contains only
the fresh corridor, not the already inspected source.  That comparison,
`forcedSourceExperiment_prob_le_prob`, is proved here for an arbitrary recorded-open source and is
the honest export of this file.

**What this file no longer claims.**  Two theorems used to conclude a source estimate at the
designated tip `MacroExp.src d r n h` from the premise `hopen : src d r n h ∈ h.openSites`.  That
premise is refuted at reachable good transcripts by `math/RECORDED_OPEN_ENTRY.md` §2, whose
counterexample is cut out by a positive-probability cylinder.  Both are retired; the retirement
note near the end of this file names them.

**Why a designated tip cannot be the source.**  The tip has exactly one neighbour in its outgoing
edge region, namely `tipOut`.  Even the source-opened experiment therefore forces that one fresh
site open, so its product probability is at most `q` by `forcedCorridorExperiment_prob_le`, and
`not_pinnedEntranceBound_of_q_le` turns this into an outright impossibility at every
`q ≤ 1 - C.eps / 8`.  Chaining face and coalescence experiments farther down the corridor cannot
remove this first fresh-coordinate bottleneck.

**What is assumed now, and where it must be discharged.**  The source estimate is an explicit
interface with the recorded origin as its source: `RecordedEntry.OriginSourceEstimate` in
`KN/SourceEstimate.lean`.  This file does not prove it, and neither does any other file at a
post-step transcript; constructing it at every accepted macro vertex, inside the iterated tolerance
`CorrMove.beta`, is the remaining H2 obligation.  Its one proved instance is the initial one,
`InitBridge.hinitialLongBox_holds`.
-/

noncomputable section

namespace KNAll.Site.PinEnt

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor KNAll.Site.MacroExp

variable {d : ℕ} [NeZero d]

/-! ## The source-opened cylinder event -/

/-- Ask for a connection after opening `o` by hand.  Unlike an ordinary rooted connection event,
this event does not ask the product sample to contain `o`. -/
def forcedSourceEvent (Reg : Finset (Site d)) (o : Site d) (B : Set (Site d)) :
    Set (SiteConfig (Site d)) :=
  openSite o ⁻¹'
    connWithinSet (zdGraph d) (↑(insert o Reg) : Set (Site d)) o B

/-- Opening the source removes it from the support: the event is decided by `Reg` alone. -/
theorem determinedBy_forcedSourceEvent (Reg : Finset (Site d)) (o : Site d)
    (B : Set (Site d)) :
    DeterminedBy (forcedSourceEvent Reg o B) (↑Reg : Set (Site d)) := by
  unfold forcedSourceEvent
  have h := TargetExt.determinedBy_substitute_preimage_of_determinedBy
    (determinedBy_connWithinSet (zdGraph d) (↑(insert o Reg) : Set (Site d)) o B)
    ({o} : Set (Site d)) (fun _ => True)
  rw [funext (substitute_singleton_true (V := Site d) o)] at h
  refine h.mono ?_
  intro x hx
  simp only [Finset.coe_insert, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_coe] at hx ⊢
  exact hx.1.resolve_left hx.2

theorem measurableSet_forcedSourceEvent (Reg : Finset (Site d)) (o : Site d)
    (B : Set (Site d)) : MeasurableSet (forcedSourceEvent Reg o B) :=
  (determinedBy_forcedSourceEvent Reg o B).measurableSet_of_finset

/-- The source-opened event, packaged with its genuinely fresh support. -/
def forcedSourceExperiment (Reg : Finset (Site d)) (o : Site d) (B : Set (Site d)) :
    CylinderExperiment d where
  support := Reg
  event := forcedSourceEvent Reg o B
  determined := determinedBy_forcedSourceEvent Reg o B
  measurable' := measurableSet_forcedSourceEvent Reg o B

@[simp] theorem forcedSourceExperiment_support (Reg : Finset (Site d)) (o : Site d)
    (B : Set (Site d)) : (forcedSourceExperiment Reg o B).support = Reg := rfl

@[simp] theorem forcedSourceExperiment_event (Reg : Finset (Site d)) (o : Site d)
    (B : Set (Site d)) :
    (forcedSourceExperiment Reg o B).event = forcedSourceEvent Reg o B := rfl

/-! ## Transfer to the pinned transcript law -/

/-- A recorded-open coordinate really is open in every configuration seen by the pinned law. -/
theorem mem_substitute_of_mem_openSites (h : MacroExp.Tr d) {o : Site d}
    (ho : o ∈ h.openSites) (ω : SiteConfig (Site d)) :
    o ∈ substitute (↑h.inspected : Set (Site d)) h.state ω := by
  rw [mem_substitute_of_mem h.state]
  · exact ho
  · exact Finset.mem_coe.2 (h.openSites_subset ho)

/-- For a fresh region, the source-opened ordinary experiment is a subevent of the actual
connection event under the transcript's pinned law. -/
theorem forcedSourceExperiment_prob_le_prob
    (h : MacroExp.Tr d) (Reg : Finset (Site d)) (hfresh : Disjoint Reg h.inspected)
    (o : Site d) (ho : o ∈ h.openSites) (B : Set (Site d)) (q : unitInterval) :
    (forcedSourceExperiment Reg o B).prob q ≤
      h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑(h.inspected ∪ Reg) : Set (Site d)) o B) := by
  classical
  rw [FRDom.Transcript.prob_eq]
  unfold pinnedProb CylinderExperiment.prob forcedSourceExperiment
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_preimage] at hω ⊢
  change openSite o ω ∈
    connWithinSet (zdGraph d) (↑(insert o Reg) : Set (Site d)) o B at hω
  rw [mem_connWithinSet_iff] at hω ⊢
  obtain ⟨b, hb, hob⟩ := hω
  refine ⟨b, hb, ?_⟩
  rw [mem_connWithin_iff] at hob ⊢
  refine ⟨?_, hob.2.mono (openSiteGraph_mono (G := zdGraph d) ?_)⟩
  · exact ⟨mem_substitute_of_mem_openSites h ho ω,
      Finset.mem_coe.2 (Finset.mem_union_left Reg (h.openSites_subset ho))⟩
  · intro x hx
    obtain ⟨hxopen, hxsmall⟩ := hx
    have hxsmall' : x = o ∨ x ∈ Reg :=
      Finset.mem_insert.1 (Finset.mem_coe.1 hxsmall)
    constructor
    · rcases hxsmall' with rfl | hxReg
      · exact mem_substitute_of_mem_openSites h ho ω
      · have hxnot : x ∉ h.inspected := fun hxins =>
          Finset.disjoint_left.1 hfresh hxReg hxins
        rw [mem_substitute_of_notMem h.state (by simpa using hxnot)]
        rcases (mem_openSite o ω x).1 hxopen with hxo | hxω
        · subst x
          exact absurd (h.openSites_subset ho) hxnot
        · exact hxω
    · exact Finset.mem_coe.2 <| hxsmall'.elim
        (fun hxo => hxo ▸ Finset.mem_union_left Reg (h.openSites_subset ho))
        (fun hxReg => Finset.mem_union_right h.inspected hxReg)

/-! ## The first fresh-coordinate bottleneck -/

/-- If `g` is the only vertex of `Reg` adjacent to `o`, every source-opened connection from `o`
to a target inside `Reg` forces `g` to be open in the ordinary sample. -/
theorem forcedSourceEvent_subset_gateway {Reg : Finset (Site d)} {o g : Site d}
    {B : Set (Site d)} (hoReg : o ∉ Reg) (hB : B ⊆ (↑Reg : Set (Site d)))
    (hgate : ∀ y ∈ Reg, (zdGraph d).Adj o y → y = g) :
    forcedSourceEvent Reg o B ⊆ {ω : SiteConfig (Site d) | g ∈ ω} := by
  intro ω hω
  change openSite o ω ∈
    connWithinSet (zdGraph d) (↑(insert o Reg) : Set (Site d)) o B at hω
  rw [mem_connWithinSet_iff] at hω
  obtain ⟨b, hb, hob⟩ := hω
  have hbReg : b ∈ Reg := Finset.mem_coe.1 (hB hb)
  have hobne : o ≠ b := fun h => hoReg (h ▸ hbReg)
  rw [mem_connWithin_iff] at hob
  obtain ⟨p⟩ := hob.2
  obtain ⟨y, hoy, py, hp⟩ := p.exists_eq_cons_of_ne hobne
  have hoy' := (openSiteGraph_adj_iff' (zdGraph d)
    (openSite o ω ∩ (↑(insert o Reg) : Set (Site d))) o y).1 hoy
  have hyo : y ≠ o := hoy'.1.ne'
  have hyReg : y ∈ Reg := by
    have : y ∈ insert o Reg := Finset.mem_coe.1 hoy'.2.2.2
    exact (Finset.mem_insert.1 this).resolve_left hyo
  have hyg : y = g := hgate y hyReg hoy'.1
  rcases (mem_openSite o ω y).1 hoy'.2.2.1 with hyo' | hyω
  · exact absurd hyo' hyo
  · simpa [← hyg] using hyω

/-- The corresponding one-coordinate upper bound. -/
theorem forcedSourceExperiment_prob_le_gateway {Reg : Finset (Site d)} {o g : Site d}
    {B : Set (Site d)} (hoReg : o ∉ Reg) (hB : B ⊆ (↑Reg : Set (Site d)))
    (hgate : ∀ y ∈ Reg, (zdGraph d).Adj o y → y = g) (q : unitInterval) :
    (forcedSourceExperiment Reg o B).prob q ≤ (q : ℝ) := by
  change (siteBernoulli (fun _ : Site d => q)).real (forcedSourceEvent Reg o B) ≤ _
  calc
    (siteBernoulli (fun _ : Site d => q)).real (forcedSourceEvent Reg o B)
        ≤ (siteBernoulli (fun _ : Site d => q)).real
            {ω : SiteConfig (Site d) | g ∈ ω} :=
      measureReal_mono (forcedSourceEvent_subset_gateway hoReg hB hgate) (measure_ne_top _ _)
    _ = (q : ℝ) := prodBernoulli_real_setOf_mem _ _

/-! ## The unique gateway of the actual macro corridor -/

/-- The tip on the face of the tail box has exactly one neighbour in its outgoing edge region. -/
theorem eq_tipOut_of_adj_tip_of_mem_E (hd : 2 ≤ d) (r t : ℕ)
    {w z : Site 2} (hwz : (zdGraph 2).Adj w z) {y : Site d}
    (hoy : (zdGraph d).Adj (tip d r w z) y) (hyE : y ∈ E d r t w z) :
    y = tipOut d r w z := by
  have hnb : z ∈ MacroExp.nbrs w := mem_nbrs_of_adj hwz
  obtain ⟨j₀, σ, hσ, hemb⟩ := exists_single_emb_sub hd hnb
  have hout : tipOut d r w z = tip d r w z + Pi.single j₀ σ := by
    funext j
    show tip d r w z j + emb (z - w) j = _
    rw [hemb]
    rfl
  have hfar := le_of_mem_E_out r t hnb hσ hemb hyE
  have htip : tip d r w z j₀ = ctr d r w j₀ + 5 * (r : ℤ) * σ := by
    rw [tip_apply, hemb]
    simp
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff (tip d r w z) y).1 hoy
  · rcases hσ with rfl | rfl
    · have hij : i = j₀ := by
        by_contra hij
        have hcoord := congrFun hi j₀
        simp only [Pi.add_apply, Pi.single_apply] at hcoord
        rw [htip] at hcoord
        norm_num at hfar
        omega
      subst i
      simpa [hout] using hi
    · have hcoord := congrFun hi j₀
      simp only [Pi.add_apply, Pi.single_apply] at hcoord
      split_ifs at hcoord <;> rw [htip] at hcoord <;> norm_num at hfar <;> omega
  · rcases hσ with rfl | rfl
    · have hcoord := congrFun hi j₀
      simp only [Pi.add_apply, Pi.single_apply] at hcoord
      split_ifs at hcoord <;> rw [htip] at hcoord <;> norm_num at hfar <;> omega
    · have hij : i = j₀ := by
        by_contra hij
        have hcoord := congrFun hi j₀
        simp only [Pi.add_apply, Pi.single_apply] at hcoord
        rw [htip] at hcoord
        norm_num at hfar
        omega
      subst i
      rw [hout, hi]
      funext j
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs <;> omega

/-- Therefore every source-opened crossing of the actual corridor to a target in that corridor
still forces the fresh entrance site `tipOut` to be open. -/
theorem forcedCorridorEvent_subset_tipOut_open (hd : 2 ≤ d) (r t : ℕ)
    {w z : Site 2} (hwz : (zdGraph 2).Adj w z) {B : Set (Site d)}
    (hB : B ⊆ (↑(E d r t w z) : Set (Site d))) :
    forcedSourceEvent (E d r t w z) (tip d r w z) B ⊆
      {ω : SiteConfig (Site d) | tipOut d r w z ∈ ω} := by
  apply forcedSourceEvent_subset_gateway
  · intro htipE
    exact Finset.disjoint_left.1 (E_disjoint_Q_tail d r t w z) htipE
      (tip_mem_Q r t (mem_nbrs_of_adj hwz))
  · exact hB
  · intro y hyE hoy
    exact eq_tipOut_of_adj_tip_of_mem_E hd r t hwz hoy hyE

/-- **Second obstruction.**  Even after the already pinned source is opened for free, a crossing
from the tip into its outgoing corridor has probability at most `q`, because `tipOut` is the unique
fresh gateway. -/
theorem forcedCorridorExperiment_prob_le (hd : 2 ≤ d) (r t : ℕ)
    {w z : Site 2} (hwz : (zdGraph 2).Adj w z) {B : Set (Site d)}
    (hB : B ⊆ (↑(E d r t w z) : Set (Site d))) (q : unitInterval) :
    (forcedSourceExperiment (E d r t w z) (tip d r w z) B).prob q ≤ (q : ℝ) := by
  change (siteBernoulli (fun _ : Site d => q)).real
    (forcedSourceEvent (E d r t w z) (tip d r w z) B) ≤ _
  calc
    (siteBernoulli (fun _ : Site d => q)).real
        (forcedSourceEvent (E d r t w z) (tip d r w z) B)
        ≤ (siteBernoulli (fun _ : Site d => q)).real
            {ω : SiteConfig (Site d) | tipOut d r w z ∈ ω} :=
      measureReal_mono (forcedCorridorEvent_subset_tipOut_open hd r t hwz hB)
        (measure_ne_top _ _)
    _ = (q : ℝ) := prodBernoulli_real_setOf_mem _ _

/-- Any proposed near-one bound for the source-opened corridor experiment still forces the same
numerical inequality as the rejected unpinned entrance experiment. -/
theorem threshold_lt_q_of_forcedCorridorBound (hd : 2 ≤ d) (r t : ℕ)
    {C : LeftImp2.Certificate2 d} {w z : Site 2} (hwz : (zdGraph 2).Adj w z)
    {B : Set (Site d)} (hB : B ⊆ (↑(E d r t w z) : Set (Site d)))
    {q : unitInterval}
    (hbound : 1 - C.eps / 8 <
      (forcedSourceExperiment (E d r t w z) (tip d r w z) B).prob q) :
    1 - C.eps / 8 < (q : ℝ) :=
  hbound.trans_le (forcedCorridorExperiment_prob_le hd r t hwz hB q)

/-! ## The innermost recorded level -/

/-- The innermost level box used as `B` in
`MacroExp.lt_prob_connWithinSet_of_shellWindow`. -/
def innerBox (C : LeftImp2.Certificate2 d) (c : Site d) : Finset (Site d) :=
  Ibox (scalesOf C) c (C.levels - 1)

/-- The innermost box is contained in every outer level named by the certificate. -/
theorem innerBox_subset_Dbox (C : LeftImp2.Certificate2 d) (c : Site d) {i : ℕ}
    (hi : i < C.levels) :
    innerBox C c ⊆ Dbox (scalesOf C) c i := by
  refine (Ibox_subset_Obox (scalesOf C) c (C.levels - 1) |>.trans
    (Obox_subset_Dbox (scalesOf C) c (C.levels - 1))).trans ?_
  exact rbox_mono fun u => by
    simp only [ρD]
    omega

/-- The recorded base radius fits the anisotropic corridor radius under the two natural placement
inequalities. -/
theorem scalesOf_rho_le_rad (C : LeftImp2.Certificate2 d) {r t : ℕ}
    (hcorr : C.corridor ≤ 5 * r) (hhalf : C.halfWidth ≤ t) :
    ∀ u, (scalesOf C).ρ₀ u ≤ rad (5 * r) t u := by
  intro u
  simp only [scalesOf]
  unfold rad
  split_ifs <;> exact_mod_cast ‹_›

/-- At the intended scales the innermost level box lies in the fresh edge region. -/
theorem innerBox_subset_E (hd : 2 ≤ d) (C : LeftImp2.Certificate2 d)
    (r t : ℕ) (hr : 0 < r) {w z : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hcorr : C.corridor ≤ 5 * r) (hhalf : C.halfWidth ≤ t) :
    innerBox C (ctr d r z) ⊆ E d r t w z := by
  refine (Ibox_subset_Obox (scalesOf C) (ctr d r z) (C.levels - 1) |>.trans
    (Obox_subset_Dbox (scalesOf C) (ctr d r z) (C.levels - 1))).trans ?_
  exact Corridor.Dbox_subset_E hd r t hr hwz.ne (scalesOf C)
    (scalesOf_rho_le_rad C hcorr hhalf) (C.levels - 1)

/-- The concrete source-opened experiment aimed at the innermost box.  Its support is exactly the
fresh edge region; in particular the already pinned source is not in its support. -/
def pinnedEntranceExperiment (C : LeftImp2.Certificate2 d) (r t : ℕ)
    (w z : Site 2) : CylinderExperiment d :=
  forcedSourceExperiment (E d r t w z) (tip d r w z)
    (↑(innerBox C (ctr d r z)) : Set (Site d))

@[simp] theorem pinnedEntranceExperiment_support (C : LeftImp2.Certificate2 d) (r t : ℕ)
    (w z : Site 2) :
    (pinnedEntranceExperiment C r t w z).support = E d r t w z := rfl

/-- The second obstruction specialized to the actual innermost-level experiment. -/
theorem pinnedEntranceExperiment_prob_le (hd : 2 ≤ d) (C : LeftImp2.Certificate2 d)
    (r t : ℕ) (hr : 0 < r) {w z : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hcorr : C.corridor ≤ 5 * r) (hhalf : C.halfWidth ≤ t) (q : unitInterval) :
    (pinnedEntranceExperiment C r t w z).prob q ≤ (q : ℝ) := by
  exact forcedCorridorExperiment_prob_le hd r t hwz
    (Finset.coe_subset.2 (innerBox_subset_E hd C r t hr hwz hcorr hhalf)) q

/-- The explicit missing hypothesis one would have to add to the certificate interface.  Unlike
the rejected clause from `KN/EntranceBound.lean`, this event opens the already pinned source before
testing connectivity, and its finite support is entirely fresh.

It is still not a viable clause at general `q`, as `not_pinnedEntranceBound_of_q_le` below shows. -/
def PinnedEntranceBound (C : LeftImp2.Certificate2 d) (q : unitInterval) (r t : ℕ) : Prop :=
  ∀ w z : Site 2, (zdGraph 2).Adj w z →
    1 - C.eps / 8 < (pinnedEntranceExperiment C r t w z).prob q

/-- The named source-opened bound forces `q` above the requested threshold. -/
theorem threshold_lt_q_of_pinnedEntranceBound (hd : 2 ≤ d)
    {C : LeftImp2.Certificate2 d} {q : unitInterval} {r t : ℕ} (hr : 0 < r)
    (hcorr : C.corridor ≤ 5 * r) (hhalf : C.halfWidth ≤ t)
    (hbound : PinnedEntranceBound C q r t) {w z : Site 2}
    (hwz : (zdGraph 2).Adj w z) :
    1 - C.eps / 8 < (q : ℝ) :=
  (hbound w z hwz).trans_le
    (pinnedEntranceExperiment_prob_le hd C r t hr hwz hcorr hhalf q)

/-- **Machine-checked impossibility.**  If `q` is at or below the requested threshold, the named
source-opened entrance bound is false, despite the source itself being opened for free. -/
theorem not_pinnedEntranceBound_of_q_le (hd : 2 ≤ d)
    {C : LeftImp2.Certificate2 d} {q : unitInterval} {r t : ℕ} (hr : 0 < r)
    (hcorr : C.corridor ≤ 5 * r) (hhalf : C.halfWidth ≤ t)
    (hq : (q : ℝ) ≤ 1 - C.eps / 8) :
    ¬ PinnedEntranceBound C q r t := by
  intro hbound
  let w : Site 2 := 0
  let z : Site 2 := Pi.single 0 1
  have hwz : (zdGraph 2).Adj w z := by
    rw [zdGraph_adj_iff]
    exact ⟨0, Or.inl (by simp [w, z])⟩
  exact (not_lt_of_ge hq)
    (threshold_lt_q_of_pinnedEntranceBound hd hr hcorr hhalf hbound hwz)

/-! ## What can be concluded at a good transcript

**Two fixed-source theorems have been retired from this section:**

```
lt_prob_src_connWithinSet_of_forcedBound
lt_prob_src_connWithinSet_innerBox_of_pinnedEntranceBound
```

Each concluded a source estimate whose source was the designated tip `MacroExp.src d r n h`, from
the premise `hopen : MacroExp.src d r n h ∈ h.openSites`.  That premise is false at reachable good
transcripts: `math/RECORDED_OPEN_ENTRY.md` §2 exhibits a positive-probability cylinder whose
transcript is good, non-terminal and reachable by `MacroExp.run`, and at which the designated tip
had been inspected closed.  A repository-wide name search found no reference to either name
outside this file, so retiring them severs no proof.

What survives is the generic transfer below, parameterized by an arbitrary source that the
transcript records open.  It is the correct measure-theoretic reduction and nothing more: the
source-opened corridor bound it consumes is itself impossible at a designated tip, by
`not_pinnedEntranceBound_of_q_le` above, because the tip has exactly one neighbour in its outgoing
region.  The source used by the downstream interface is instead the recorded origin
`MacroExp.emb 0`; see `RecordedEntry.OriginSourceEstimate` in `KN/SourceEstimate.lean`. -/

/-- **The generic forced-source transfer.**  For a fresh region and a source that the transcript
records open, a source-opened ordinary cylinder bound gives the corresponding source estimate
under the pinned law.  The source is a parameter, never `MacroExp.src`. -/
theorem sourceEstimate_of_forcedBound
    {C : LeftImp2.Certificate2 d} {q : unitInterval} (h : MacroExp.Tr d)
    (Reg : Finset (Site d)) (hfresh : Disjoint Reg h.inspected)
    (o : Site d) (ho : o ∈ h.openSites) (B : Set (Site d))
    (hbound : 1 - C.eps / 8 < (forcedSourceExperiment Reg o B).prob q) :
    RecordedEntry.SourceEstimate C q h Reg o B :=
  hbound.trans_le (forcedSourceExperiment_prob_le_prob h Reg hfresh o ho B q)


#print axioms KNAll.Site.PinEnt.mem_substitute_of_mem_openSites
#print axioms KNAll.Site.PinEnt.forcedSourceExperiment_prob_le_prob
#print axioms KNAll.Site.PinEnt.eq_tipOut_of_adj_tip_of_mem_E
#print axioms KNAll.Site.PinEnt.forcedCorridorExperiment_prob_le
#print axioms KNAll.Site.PinEnt.threshold_lt_q_of_forcedCorridorBound
#print axioms KNAll.Site.PinEnt.pinnedEntranceExperiment_prob_le
#print axioms KNAll.Site.PinEnt.not_pinnedEntranceBound_of_q_le
#print axioms KNAll.Site.PinEnt.sourceEstimate_of_forcedBound

end KNAll.Site.PinEnt

end
