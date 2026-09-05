import Hypergraph.MacroExploration
import Hypergraph.StubBudget
import Hypergraph.LevelBoundOpus
import Hypergraph.CorridorFreshness

/-!
# The corrected stopped directional event and its `ρ/16` bound

`Assembly.levelEvent` is not the event the layer-by-layer argument produces.  For a still-pending
neighbour it is a single estimate, made immediately after the incoming edge has been exposed, for
reaching the deepest of the concentric `Corridor.Dbox` family around that neighbour: it exposes no
outgoing stub, it does not stop at a first good level, and it does not say that *some* level is
good.  `KN/LevelBoundOpus.lean` and `KN/LevelBound2.lean` record why the requested `ρ/16` estimate
for that event does not follow; `LevelOpus.not_hDirectionalNoCover` refutes it outright once
`MacroExp.Good.cover` is dropped.

This file builds the corrected event and proves the bound for it.

## What is defined here

* `stub c i σ r t a`, `stubFace`, `stubTarget`: the directional stubs `H^j_{z,y}`, their outgoing
  faces `F^j_{z,y}` and the corridor target.  They are longitudinal boxes growing from the outgoing
  face of `Q z` towards `y`, at signed longitudinal coordinate `lam`; they are *not* the concentric
  `Corridor.Dbox` family, which shrinks inward around `c y`.  The two families cannot be identified:
  Section 4 of the note exhibits an axial path reaching `M y` whose longitudinal coordinate never
  reaches `19 r`, so it enters no `Dbox j (c y)`.  Everything is expressed with `MacroExp.ctr`,
  `MacroExp.abox` and `MacroExp.rad`; no new geometric primitive and no new certificate field is
  needed.
* `revealSet`, `levelTr`, `stopLevel`: the reveal-only substeps and the stopping level.  A new
  transcript field is **not** needed: `FRDom.Transcript.step z F true ω` at an **already occupied**
  `z` inserts nothing into `openV` and nothing into `closedV`, so it only enlarges `inspected`
  (`levelTr_openV`, `levelTr_closedV`, `levelTr_pending`).  The fresh part of a layer is defined by
  subtraction, `revealSet = stub \ inspected`, so freshness is `Finset.sdiff_disjoint` rather than
  an assertion.
* `levelBad`, `crossEvent`, `corridorEvent`, `noGoodLevel`, `directionEvent`: the events
  `B_{y,j}`, `A_{y,j}`, `C_y`, `N_y` and the corrected directional event.

## What is proved here

* `stub_crossing`, `connWithinSet_stubFace_of_conn`, `stub_crossing_prefix_avoids`: the ordered
  crossing of the directional faces, with the prefix containment.  It is proved from
  `LevelOpus.exists_firstEntry`; the gate step is the integer intermediate-value property of `lam`
  along a lattice edge (`lam_adj`).
* `real_inter_le_of_pinnedProb_le`, `prob_inter_le_of_step_prob_le`: the tower step, proved atom by
  atom over the patterns of the revealed set and then multiplied by the pattern probability.  No
  conditional-probability denominator occurs and patterns of probability zero are harmless.
* `prob_noGoodLevel_le`: the bound `μ(N_y) ≤ ρ/32 + (1-δ₂)^K ≤ ρ/16`, obtained by instantiating
  `Budget.pinnedProb_corridor_or_allBad_le` with the events `A_{y,j} ∩ B_{y,j}` — not with
  `B_{y,j}` alone — and the deterministic inclusion `N_y ⊆ C_y^c ∪ ⋂ (A_{y,j} ∩ B_{y,j})`.
* `prob_directionEvent_compl_le`, `prob_directionEvent_compl_le_accepted`, `prob_joint_compl_le`:
  the same bound for the directional event and for the joint event `Incoming^c ∪ Direction_y`.
* `lt_prob_reservationEvent_stopLevel`: at the stopping level the revealed transcript carries a
  reservation to the whole box `M y` at tolerance `δc`, which is the clause
  `MacroExp.Good.reserve` stores.
* `stub_subset_Q_union_E`, `sep_of_fresh`, `origin_notMem_stub`, `stubTarget_subset_M`: the stub
  sits inside `Q z ∪ E z y`, so the substeps read only reserved sites; the entrance isolation and
  the position of the origin follow from `MacroExp.Good.inspected_thin` and the freshness of
  `E z y`, and the corridor target sits inside `M y`.

## The three recurring refutations

*No designated open site.*  The crossing targets are whole faces and the reservation target is the
whole box `M y`; a first-hit site is produced by the crossing lemma, never demanded in advance.
This is what `AsmVac.not_hstub` and `PinnedEntrance.not_pinnedEntranceBound_of_q_le` refute, and
neither applies here.

*No empty target.*  `stubFace_nonempty` and `stubTarget_nonempty` exhibit the axial sites
`c + σ(5r + a)eᵢ` and `c + 20 r σ eᵢ`; `stubTarget_subset_M` puts the corridor target inside
`M y`, so the corridor hypothesis is a hypothesis about a connection to the box the invariant
speaks of.

*No stale conditional estimate.*  The only conditional estimate is the tower step, and it is taken
at the actual revealed transcript with the actual pinned law.  `ProbInv.prob_step_eq_of_disjoint` is
never invoked to carry an estimate across a read that overlaps the tested support.

## What of the note does not survive as stated

1. **Proposition 5.1 is formalized under a hypothesis that is implied by, but not equal to, the
   note's (5.3).**  `stub_crossing` assumes `hsep`: a base site adjacent to a stub site beyond the
   source face has longitudinal coordinate at most `5r`.  The note's (5.3) — the base meets the
   stub only in the source face, and the base off that face is separated from the stub off that
   face — implies `hsep` (a base site adjacent to a stub site beyond the face must lie on the
   face, whose coordinate is exactly `5r`), so the theorem proved here is at least as strong.  The
   note's own proof of Proposition 5.1 instead decomposes the path at its *last* visit to the
   source face; that decomposition is not formalized, and would be needed for a base that reaches
   beyond the stub without touching it.  `sep_of_fresh` shows the point is moot in the lattice at
   hand: `hsep` follows from `MacroExp.Good.inspected_thin` together with the freshness of the
   outgoing corridor, since a site above `5r` next to the stub lies in `E z y`.
2. **The one-level estimate (7.11) is an input, not a theorem here.**  Section 8 lists it as its
   second input and Section 7.2 states the geometric side conditions (the fresh subbox (7.10), and
   the disjointness of the old inspected set, of the incoming region off the shared source face,
   and of the stubs of earlier directions from its interior).  Deriving it from
   `TargetExt.targetExtension_eps` is not done in this file; `hone` carries it.
3. **The corridor-move estimate is an input, as Section 10.2 already flags.**
   `Certificate2.WellFormed` asserts `5ε ≤ ρ` but not `ε ≤ δ_corr(ρ/32)`, so `hcorr` cannot be
   extracted from the present certificate; it is a hypothesis here, exactly as in Section 8.
4. **Section 9.1 is not needed in this arrangement, and is not formalized.**  The note removes the
   proper stubs of earlier directions from the tested allowed set and then argues, by
   irrelevant-step persistence, that conditioning on them changes nothing.  Here every level event
   is defined at the *actual* transcript, whose inspected set may already contain those stubs, and
   the tower step conditions on the actual revealed set; no invariance claim is made or needed.
   The note's requirement that earlier stubs stay disjoint from the fresh subbox of (7.10) is
   inherited by input (7.11).
5. **Section 6 is not reproved.**  Its role is to refute the old obligation, which
   `LevelBound2.lean` and `LevelOpus.not_hDirectionalNoCover` already do inside this tree.
6. **The `FRDom.Exploration` interface still has no stopped transition.**  Nothing in
   `MacroExp.Tr` or `MacroExp.Good` has to change — the substeps above are ordinary steps at an
   occupied macro-vertex — but `FRDom.Exploration.region` is configuration-independent and its one
   transition both reads and commits, so an implementation of `MacroExp.StepBound` still needs a
   transition whose recorded finite region may depend on the states read so far.  That is outside
   this file.

## Constants

With `δc = ε` and `δ₂ = ε/8` the hypotheses `hδ₂ : δ₂ ≤ 1` and `hpow : (1-δ₂)^K ≤ ρ/32` are the
note's (10.1) and (10.4); `Budget.exists_levelCount` already produces a `K` satisfying the second.
The relation `hfar : 10 s K ≤ 13 r` is implied by the note's `r = K s`, which gives `10 s K = 10 r`.
-/

noncomputable section

namespace KNAll.Site.Stopped

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## The directional stubs -/

section Geometry

variable {d : ℕ}

/-- The signed longitudinal coordinate of the stub `z → y`. -/
def lam (c : Site d) (i : Fin d) (σ : ℤ) (x : Site d) : ℤ := σ * (x i - c i)

/-- The v15 directional stub of height `a`.

Unlike the ambient macro boxes, the stopped stub is isotropic in every coordinate transverse to
its direction: its transverse half-width is exactly `2r`.  The parameter `t` is retained in the
signature so that the stopped API continues to use the macro scale tuple `(r,t,s)`, but it does
not change the set. -/
def stub (c : Site d) (i : Fin d) (σ : ℤ) (r t a : ℕ) : Finset (Site d) :=
  (MacroExp.abox c (5 * r + a) (t + 5 * r + a)).filter fun x =>
    (5 * r : ℤ) ≤ lam c i σ x ∧ lam c i σ x ≤ (5 * r + a : ℕ) ∧
      ∀ j, j ≠ i → |x j - c j| ≤ (2 * r : ℕ)

theorem lam_abs {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (c : Site d) (i : Fin d) (x : Site d) :
    |lam c i σ x| = |x i - c i| := by
  rcases hσ with rfl | rfl <;> simp [lam, abs_sub_comm]

theorem mem_stub {c x : Site d} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {r t a : ℕ} :
    x ∈ stub c i σ r t a ↔
      ((5 * r : ℤ) ≤ lam c i σ x ∧ lam c i σ x ≤ (5 * r + a : ℕ) ∧
        ∀ j, j ≠ i → |x j - c j| ≤ (2 * r : ℕ)) := by
  rw [stub, Finset.mem_filter, and_iff_right_iff_imp]
  rintro ⟨h1, h2, h3⟩
  rw [MacroExp.mem_abox]
  intro j
  have hcast : ((5 * r + a : ℕ) : ℤ) = 5 * (r : ℤ) + a := by push_cast; ring
  by_cases hj : j = i
  · subst hj
    have habs : |x j - c j| ≤ ((5 * r + a : ℕ) : ℤ) := by
      rw [← lam_abs hσ c j x, abs_le]
      constructor <;> [linarith [h1, hcast]; linarith [h2]]
    have hrad : ((5 * r + a : ℕ) : ℤ) ≤ MacroExp.rad (5 * r + a) (t + 5 * r + a) j := by
      unfold MacroExp.rad; split_ifs with h
      · exact le_rfl
      · push_cast; omega
    rw [abs_le] at habs
    constructor <;> omega
  · have h := h3 j hj
    have hrad : ((2 * r : ℕ) : ℤ) ≤ MacroExp.rad (5 * r + a) (t + 5 * r + a) j := by
      unfold MacroExp.rad; split_ifs with hb <;> push_cast <;> omega
    rw [abs_le] at h
    constructor <;> omega

/-- The stub grows with its height. -/
theorem stub_mono {c : Site d} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {r t a a' : ℕ}
    (h : a ≤ a') : stub c i σ r t a ⊆ stub c i σ r t a' := by
  intro x hx
  rw [mem_stub hσ] at hx ⊢
  refine ⟨hx.1, ?_, hx.2.2⟩
  have : ((5 * r + a : ℕ) : ℤ) ≤ ((5 * r + a' : ℕ) : ℤ) := by exact_mod_cast Nat.add_le_add_left h _
  exact hx.2.1.trans this

/-- The outgoing face of the stub at height `a`: its far cross-section. -/
def stubFace (c : Site d) (i : Fin d) (σ : ℤ) (r t a : ℕ) : Finset (Site d) :=
  (stub c i σ r t a).filter fun x => lam c i σ x = (5 * r + a : ℕ)

theorem stubFace_subset (c : Site d) (i : Fin d) (σ : ℤ) (r t a : ℕ) :
    stubFace c i σ r t a ⊆ stub c i σ r t a := Finset.filter_subset _ _

theorem mem_stubFace {c x : Site d} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {r t a : ℕ} :
    x ∈ stubFace c i σ r t a ↔
      (lam c i σ x = (5 * r + a : ℕ) ∧ ∀ j, j ≠ i → |x j - c j| ≤ (2 * r : ℕ)) := by
  rw [stubFace, Finset.mem_filter, mem_stub hσ]
  constructor
  · rintro ⟨⟨-, -, h3⟩, h⟩; exact ⟨h, h3⟩
  · rintro ⟨h, h3⟩
    refine ⟨⟨?_, le_of_eq h, h3⟩, h⟩
    rw [h]; push_cast; omega

/-- **No face is empty**: the axial site of the stub at height `a` lies on its outgoing face.  The
crossing targets are therefore never the empty set. -/
theorem axial_mem_stubFace (c : Site d) (i : Fin d) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (r t a : ℕ) :
    c + Pi.single i (σ * (5 * r + a : ℕ)) ∈ stubFace c i σ r t a := by
  rw [mem_stubFace hσ]
  constructor
  · have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
    simp only [lam, Pi.add_apply, Pi.single_eq_same, add_sub_cancel_left]
    rw [← mul_assoc, hσ2, one_mul]
  · intro j hj
    have hrad : (0 : ℤ) ≤ ((2 * r : ℕ) : ℤ) := by positivity
    simp [Pi.single_eq_of_ne hj, hrad]

theorem stubFace_nonempty (c : Site d) (i : Fin d) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (r t a : ℕ) :
    (stubFace c i σ r t a).Nonempty :=
  ⟨_, axial_mem_stubFace c i hσ r t a⟩

/-- Along a lattice edge the longitudinal coordinate moves by at most one. -/
theorem lam_adj {c : Site d} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {u v : Site d}
    (h : (zdGraph d).Adj u v) : |lam c i σ v - lam c i σ u| ≤ 1 := by
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hsub : lam c i σ v - lam c i σ u = σ * (v i - u i) := by simp [lam]; ring
  obtain ⟨k, hk | hk⟩ := (zdGraph_adj_iff u v).1 h
  · have : v i - u i = if i = k then 1 else 0 := by
      rw [hk]; by_cases hik : i = k <;> simp [hik]
    rw [hsub, this]
    by_cases hik : i = k <;> simp [hik, hσ1]
  · have : v i - u i = if i = k then -1 else 0 := by
      rw [hk]; by_cases hik : i = k <;> simp [hik]
    rw [hsub, this]
    by_cases hik : i = k <;> simp [hik, hσ1]

end Geometry

/-! ## Ordered crossing of the directional faces -/

section Crossing

variable {d : ℕ}

/-- The deep part of the stub: the sites of the full stub at longitudinal depth at least
`5r + m`.  This is the decreasing family to which the first-entry lemma is applied. -/
def deep (c : Site d) (i : Fin d) (σ : ℤ) (r t A m : ℕ) : Set (Site d) :=
  {x | x ∈ stub c i σ r t A ∧ ((5 * r + m : ℕ) : ℤ) ≤ lam c i σ x}

theorem deep_anti (c : Site d) (i : Fin d) (σ : ℤ) (r t A : ℕ) {m m' : ℕ} (h : m ≤ m') :
    deep c i σ r t A m' ⊆ deep c i σ r t A m := by
  rintro x ⟨hx, hlam⟩
  exact ⟨hx, le_trans (by exact_mod_cast Nat.add_le_add_left h _) hlam⟩

/-- Appending one open lattice edge to a confined connection. -/
theorem connWithin_snoc {V : Type*} {G : SimpleGraph V} {W : Set V} {ω : SiteConfig V} {o u v : V}
    (hconn : ω ∈ connWithin G W o u) (hu : u ∈ ω ∩ W) (hv : v ∈ ω ∩ W) (huv : G.Adj u v) :
    ω ∈ connWithin G W o v :=
  ⟨hconn.1, hconn.2.trans (SimpleGraph.Adj.reachable
    ((openSiteGraph_adj_iff' G (ω ∩ W) u v).2 ⟨huv, hu, hv⟩))⟩

/-- **Proposition 5.1, ordered crossing of the directional faces.**  A confined open connection
from a source outside the stub to a site of the stub at depth at least `5r + m`, inside the frozen
base together with the stub, has a first entry into that depth; the entry site lies on the face at
depth exactly `5r + m`, and the prefix leading to it never enters that depth.

The only property of the frozen base that is used is the entrance isolation `hsep`: a base site
adjacent to a stub site beyond the source face is itself at longitudinal coordinate at most `5r`.
This is the note's condition (5.3); no probability and no designated open site occurs. -/
theorem stub_crossing {c : Site d} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {r t A m : ℕ}
    (hm : 1 < m) {base : Finset (Site d)} {ω : SiteConfig (Site d)} {o b : Site d}
    (hsep : ∀ u ∈ base, ∀ v ∈ stub c i σ r t A, (zdGraph d).Adj u v →
      (5 * r : ℤ) < lam c i σ v → lam c i σ u ≤ 5 * r)
    (ho : o ∉ stub c i σ r t A) (hb : b ∈ deep c i σ r t A m)
    (hconn : ω ∈ connWithin (zdGraph d)
      ((↑base : Set (Site d)) ∪ ↑(stub c i σ r t A)) o b) :
    ∃ u v : Site d, (zdGraph d).Adj u v ∧ v ∈ stubFace c i σ r t m ∧
      u ∈ ω ∧ u ∈ (↑base : Set (Site d)) ∪ ↑(stub c i σ r t m) ∧ v ∈ ω ∧
      ω ∈ connWithin (zdGraph d)
        (((↑base : Set (Site d)) ∪ ↑(stub c i σ r t A)) \ deep c i σ r t A m) o u := by
  have ho' : o ∉ deep c i σ r t A m := fun hc => ho hc.1
  obtain ⟨u, v, huv, hu, hv, huS, hvS, hpre⟩ := LevelOpus.exists_firstEntry ho' hb hconn
  have hvstub : v ∈ stub c i σ r t A := hv.1
  have hvlow : ((5 * r + m : ℕ) : ℤ) ≤ lam c i σ v := hv.2
  have hcast : ((5 * r + m : ℕ) : ℤ) = 5 * (r : ℤ) + m := by push_cast; ring
  have hmz : (1 : ℤ) < m := by exact_mod_cast hm
  have hadj := lam_adj (c := c) (i := i) hσ huv
  rw [abs_le] at hadj
  have hveq : lam c i σ v = ((5 * r + m : ℕ) : ℤ) := by
    rcases huS.2 with hub | hus
    · exfalso
      have h5 : (5 * r : ℤ) < lam c i σ v := by omega
      have := hsep u (Finset.mem_coe.1 hub) v hvstub huv h5
      omega
    · have hulam : lam c i σ u < ((5 * r + m : ℕ) : ℤ) := by
        by_contra hcon
        exact hu ⟨Finset.mem_coe.1 hus, not_lt.1 hcon⟩
      omega
  have hvface : v ∈ stubFace c i σ r t m := by
    rw [mem_stubFace hσ]
    exact ⟨hveq, ((mem_stub hσ).1 hvstub).2.2⟩
  refine ⟨u, v, huv, hvface, huS.1, ?_, hvS.1, hpre⟩
  rcases huS.2 with hub | hus
  · exact Or.inl hub
  · refine Or.inr (Finset.mem_coe.2 ?_)
    have hus' : u ∈ stub c i σ r t A := Finset.mem_coe.1 hus
    have hulam : lam c i σ u < ((5 * r + m : ℕ) : ℤ) := by
      by_contra hcon
      exact hu ⟨hus', not_lt.1 hcon⟩
    rw [mem_stub hσ]
    exact ⟨((mem_stub hσ).1 hus').1, by omega, ((mem_stub hσ).1 hus').2.2⟩

/-- The prefix of a confined connection lies in the base together with the stub truncated at the
crossed face. -/
theorem sdiff_deep_subset {c : Site d} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {r t A m : ℕ}
    (base : Finset (Site d)) :
    (((↑base : Set (Site d)) ∪ ↑(stub c i σ r t A)) \ deep c i σ r t A m) ⊆
      (↑base : Set (Site d)) ∪ ↑(stub c i σ r t m) := by
  rintro x ⟨hx, hxd⟩
  rcases hx with hx | hx
  · exact Or.inl hx
  · have hx' : x ∈ stub c i σ r t A := Finset.mem_coe.1 hx
    have hlam : lam c i σ x < ((5 * r + m : ℕ) : ℤ) := by
      by_contra hcon
      exact hxd ⟨hx', not_lt.1 hcon⟩
    refine Or.inr (Finset.mem_coe.2 ?_)
    rw [mem_stub hσ]
    exact ⟨((mem_stub hσ).1 hx').1, by omega, ((mem_stub hσ).1 hx').2.2⟩

/-- **The crossing event.**  Under the hypotheses of `stub_crossing` the configuration joins the
source to the whole face at depth `5r + m` inside the base together with the truncated stub.  The
target is the entire face, which `stubFace_nonempty` shows is never empty. -/
theorem connWithinSet_stubFace_of_conn {c : Site d} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    {r t A m : ℕ} (hm : 1 < m) {base : Finset (Site d)} {ω : SiteConfig (Site d)} {o b : Site d}
    (hsep : ∀ u ∈ base, ∀ v ∈ stub c i σ r t A, (zdGraph d).Adj u v →
      (5 * r : ℤ) < lam c i σ v → lam c i σ u ≤ 5 * r)
    (ho : o ∉ stub c i σ r t A) (hb : b ∈ deep c i σ r t A m)
    (hconn : ω ∈ connWithin (zdGraph d)
      ((↑base : Set (Site d)) ∪ ↑(stub c i σ r t A)) o b) :
    ω ∈ connWithinSet (zdGraph d) ((↑base : Set (Site d)) ∪ ↑(stub c i σ r t m)) o
      (↑(stubFace c i σ r t m) : Set (Site d)) := by
  obtain ⟨u, v, huv, hvface, huω, huW, hvω, hpre⟩ := stub_crossing hσ hm hsep ho hb hconn
  have hpre' : ω ∈ connWithin (zdGraph d)
      ((↑base : Set (Site d)) ∪ ↑(stub c i σ r t m)) o u :=
    connWithin_mono_set (zdGraph d) (sdiff_deep_subset hσ base) o u hpre
  have hvW : v ∈ (↑base : Set (Site d)) ∪ ↑(stub c i σ r t m) :=
    Or.inr (Finset.mem_coe.2 (stubFace_subset c i σ r t m hvface))
  exact (mem_connWithinSet_iff _ _ _ _ _).2
    ⟨v, Finset.mem_coe.2 hvface, connWithin_snoc hpre' ⟨huω, huW⟩ ⟨hvω, hvW⟩ huv⟩

/-- **The crossings happen in order.**  Every site reached by the prefix that ends at the first
entry into depth `5r + m` avoids every deeper level.  With `stub_crossing` this is the ordered
crossing of `F¹, F², …, F^K` of Proposition 5.1. -/
theorem stub_crossing_prefix_avoids {c : Site d} {i : Fin d} {σ : ℤ} {r t A m m' : ℕ}
    (hmm : m ≤ m') {S : Set (Site d)} {ω : SiteConfig (Site d)} {o u x : Site d}
    (hpre : ω ∈ connWithin (zdGraph d) (S \ deep c i σ r t A m) o u)
    (hx : (openSiteGraph (zdGraph d) (ω ∩ (S \ deep c i σ r t A m))).Reachable o x) :
    x ∉ deep c i σ r t A m' := fun hc =>
  (LevelOpus.mem_of_reachable_of_connWithin hpre hx).2.2 (deep_anti c i σ r t A hmm hc)

end Crossing

/-! ## The tower step, atom by atom -/

section Tower

variable {κ V : Type*}

/-- **The atom bound.**  If an event `C` determined by the finite set `S` forces the pinned
probability of `A` given the pattern on `S` to be at most `c`, then `P(C ∩ A) ≤ c · P(C)`.

The proof runs over the patterns of `S` one at a time and multiplies by the pattern probability, so
no conditional-probability denominator appears and patterns of probability zero are harmless. -/
theorem real_inter_le_of_pinnedProb_le (p : κ → unitInterval) (S : Finset κ)
    {C A : Set (Set κ)} (hA : MeasurableSet A) (hC : DeterminedBy C (↑S : Set κ)) {c : ℝ}
    (hcond : ∀ ω ∈ C, pinnedProb p (↑S : Set κ) (fun i => i ∈ ω) A ≤ c) :
    (prodBernoulli p).real (C ∩ A) ≤ c * (prodBernoulli p).real C := by
  classical
  have hCm : MeasurableSet C := hC.measurableSet_of_finset
  rw [TargetExt.real_eq_sum_inter_localCylinder p S (hCm.inter hA),
    TargetExt.real_eq_sum_inter_localCylinder p S hCm, Finset.mul_sum]
  refine Finset.sum_le_sum fun T hT => ?_
  have hTS : T ⊆ S := Finset.mem_powerset.1 hT
  have hCT := TargetExt.inter_localCylinder_of_determinedBy hC hTS
  by_cases hTC : (↑T : Set κ) ∈ C
  · have hCT' : C ∩ localCylinder (↑S : Set κ) (↑T : Set κ)
        = localCylinder (↑S : Set κ) (↑T : Set κ) := by rw [hCT, if_pos hTC]
    have h1 : C ∩ A ∩ localCylinder (↑S : Set κ) (↑T : Set κ)
        = A ∩ localCylinder (↑S : Set κ) (↑T : Set κ) := by
      ext ω
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨-, hA'⟩, hcyl⟩; exact ⟨hA', hcyl⟩
      · rintro ⟨hA', hcyl⟩
        exact ⟨⟨(hCT'.symm ▸ hcyl : ω ∈ C ∩ localCylinder (↑S : Set κ) (↑T : Set κ)).1, hA'⟩, hcyl⟩
    rw [h1, hCT', TargetExt.real_inter_localCylinder_eq_mul_pinnedProb p S _ hA]
    have hle : pinnedProb p (↑S : Set κ) (fun i => i ∈ (↑T : Set κ)) A ≤ c := hcond _ hTC
    have h0 : 0 ≤ (prodBernoulli p).real (localCylinder (↑S : Set κ) (↑T : Set κ)) :=
      measureReal_nonneg
    nlinarith
  · have hCT' : C ∩ localCylinder (↑S : Set κ) (↑T : Set κ) = ∅ := by rw [hCT, if_neg hTC]
    have h1 : C ∩ A ∩ localCylinder (↑S : Set κ) (↑T : Set κ) = ∅ := by
      refine Set.eq_empty_of_subset_empty ?_
      rw [← hCT']
      rintro ω ⟨⟨hC', -⟩, hcyl⟩
      exact ⟨hC', hcyl⟩
    rw [h1, hCT', measureReal_empty, mul_zero]

/-- Revealing the fresh finite set `F` at the states of `ω` is the composition of the two
substitutions: first `ω` on `F`, then the recorded states on the old inspected set. -/
theorem substitute_step_state (h : FRDom.Transcript κ V) [DecidableEq κ] [DecidableEq V]
    (z : V) (F : Finset κ) (b : Bool) (ω ξ : Set κ) (hfresh : Disjoint F h.inspected) :
    substitute (↑(h.step z F b ω).inspected : Set κ) (h.step z F b ω).state ξ
      = substitute (↑h.inspected : Set κ) h.state
          (substitute (↑F : Set κ) (fun i => i ∈ ω) ξ) := by
  ext x
  by_cases hxI : x ∈ (↑h.inspected : Set κ)
  · have hxF : x ∉ F := fun hc => Finset.disjoint_left.1 hfresh hc (Finset.mem_coe.1 hxI)
    have hxU : x ∈ (↑(h.step z F b ω).inspected : Set κ) := by
      rw [FRDom.Transcript.step_inspected, Finset.coe_union]; exact Or.inl hxI
    rw [mem_substitute_of_mem _ hxU, mem_substitute_of_mem _ hxI]
    simp [FRDom.Transcript.step_state, hxF]
  · by_cases hxF : x ∈ (↑F : Set κ)
    · have hxU : x ∈ (↑(h.step z F b ω).inspected : Set κ) := by
        rw [FRDom.Transcript.step_inspected, Finset.coe_union]; exact Or.inr hxF
      rw [mem_substitute_of_mem _ hxU, mem_substitute_of_notMem _ hxI,
        mem_substitute_of_mem _ hxF]
      have hstate : ¬ h.state x := fun hc => hxI (Finset.mem_coe.2 (h.mem_inspected_of_state hc))
      simp [FRDom.Transcript.step_state, hstate, Finset.mem_coe.1 hxF]
    · have hxU : x ∉ (↑(h.step z F b ω).inspected : Set κ) := by
        rw [FRDom.Transcript.step_inspected, Finset.coe_union]
        rintro (hc | hc) <;> [exact hxI hc; exact hxF hc]
      rw [mem_substitute_of_notMem _ hxU, mem_substitute_of_notMem _ hxI,
        mem_substitute_of_notMem _ hxF]

/-- The pinned probability after a fresh reveal is the pinned probability of the pulled-back event
given the pattern on the revealed set. -/
theorem step_prob_eq_pinnedProb (h : FRDom.Transcript κ V) [DecidableEq κ] [DecidableEq V]
    (p : κ → unitInterval) (z : V) (F : Finset κ) (b : Bool) (ω : Set κ) (A : Set (Set κ))
    (hfresh : Disjoint F h.inspected) :
    (h.step z F b ω).prob p A
      = pinnedProb p (↑F : Set κ) (fun i => i ∈ ω)
          (substitute (↑h.inspected : Set κ) h.state ⁻¹' A) := by
  rw [FRDom.Transcript.prob_eq, pinnedProb, pinnedProb]
  congr 1
  ext ξ
  simp only [Set.mem_preimage]
  rw [substitute_step_state h z F b ω ξ hfresh]

/-- **The one-level tower step.**  Let `F` be fresh for the transcript `h`, let `C` be determined by
the old inspected set together with `F`, and suppose that whenever the pinned configuration lies in
`C` the reveal of `F` leaves the pinned probability of `A` at most `c`.  Then

`P_h(C ∩ A) ≤ c · P_h(C)`.

This is the denominator-free form of `1_C E[1_A | G] ≤ c 1_C`, and it is the only place where the
states just read are allowed to change a conditional estimate. -/
theorem prob_inter_le_of_step_prob_le [DecidableEq κ] [DecidableEq V]
    (h : FRDom.Transcript κ V) (p : κ → unitInterval) (z : V) (F : Finset κ) (b : Bool)
    (hfresh : Disjoint F h.inspected) {C A : Set (Set κ)} (hA : MeasurableSet A)
    (hC : DeterminedBy C ((↑h.inspected : Set κ) ∪ ↑F)) {c : ℝ}
    (hcond : ∀ ω : Set κ, substitute (↑h.inspected : Set κ) h.state ω ∈ C →
      (h.step z F b ω).prob p A ≤ c) :
    h.prob p (C ∩ A) ≤ c * h.prob p C := by
  have hC' : DeterminedBy (substitute (↑h.inspected : Set κ) h.state ⁻¹' C) (↑F : Set κ) := by
    refine (TargetExt.determinedBy_substitute_preimage_of_determinedBy hC
      (↑h.inspected : Set κ) h.state).mono ?_
    rintro x ⟨hx, hxI⟩
    rcases hx with hx | hx
    · exact absurd hx hxI
    · exact hx
  have hA' : MeasurableSet (substitute (↑h.inspected : Set κ) h.state ⁻¹' A) :=
    (measurable_substitute _ _) hA
  have hmain := real_inter_le_of_pinnedProb_le p F hA' hC' (c := c) ?_
  · rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq, pinnedProb, pinnedProb,
      Set.preimage_inter]
    exact hmain
  · intro ω hω
    rw [← step_prob_eq_pinnedProb h p z F b ω A hfresh]
    exact hcond ω hω

end Tower

/-! ## The reveal-only substep -/

section Reveal

variable {d : ℕ} [NeZero d]

/-- The fresh part of the directional stub of height `10 s j`: the stub sites not yet inspected.
This is the note's newly queried set (7.2), defined by subtraction, so freshness is a triviality
rather than an assertion. -/
def revealSet (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2) (i : Fin d) (σ : ℤ)
    (j : ℕ) : Finset (Site d) :=
  stub (MacroExp.ctr d r z) i σ r t (10 * s * j) \ h.inspected

theorem revealSet_fresh (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2) (i : Fin d)
    (σ : ℤ) (j : ℕ) : Disjoint (revealSet d r t s h z i σ j) h.inspected :=
  Finset.sdiff_disjoint

theorem revealSet_mono {d r t s : ℕ} [NeZero d] {h : MacroExp.Tr d} {z : Site 2} {i : Fin d}
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {j j' : ℕ} (hj : j ≤ j') :
    revealSet d r t s h z i σ j ⊆ revealSet d r t s h z i σ j' :=
  Finset.sdiff_subset_sdiff
    (stub_mono hσ (Nat.mul_le_mul_left _ hj)) (Finset.Subset.refl _)

/-- The transcript after the reveal-only substep which exposes the stub up to height `10 s j`.

`FRDom.Transcript.step` is used at the macro-vertex `z` with verdict `true`; when `z` is already
occupied this inserts nothing, so `openV` and `closedV`, and therefore the whole macro state, are
untouched: the substep only enlarges `inspected`.  No new transcript field is required. -/
def levelTr (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2) (i : Fin d) (σ : ℤ)
    (j : ℕ) (ω : SiteConfig (Site d)) : MacroExp.Tr d :=
  h.step z (revealSet d r t s h z i σ j) true ω

@[simp] theorem levelTr_inspected (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2)
    (i : Fin d) (σ : ℤ) (j : ℕ) (ω : SiteConfig (Site d)) :
    (levelTr d r t s h z i σ j ω).inspected
      = h.inspected ∪ stub (MacroExp.ctr d r z) i σ r t (10 * s * j) := by
  rw [levelTr, FRDom.Transcript.step_inspected, revealSet, Finset.union_sdiff_self_eq_union]

/-- **The substep is reveal-only.**  At an occupied `z` the macro-vertex sets do not move. -/
theorem levelTr_openV {d r t s : ℕ} [NeZero d] {h : MacroExp.Tr d} {z : Site 2} (i : Fin d)
    (σ : ℤ) (j : ℕ) (ω : SiteConfig (Site d)) (hz : z ∈ h.openV) :
    (levelTr d r t s h z i σ j ω).openV = h.openV := by
  rw [levelTr, FRDom.Transcript.step_openV, if_pos rfl, Finset.insert_eq_self.2 hz]

theorem levelTr_closedV (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2) (i : Fin d)
    (σ : ℤ) (j : ℕ) (ω : SiteConfig (Site d)) :
    (levelTr d r t s h z i σ j ω).closedV = h.closedV := by
  rw [levelTr, FRDom.Transcript.step_closedV, if_pos rfl]

/-- Consequently the pending directions of an occupied macro-vertex survive every substep. -/
theorem levelTr_pending {d r t s : ℕ} [NeZero d] {h : MacroExp.Tr d} {z : Site 2} (i : Fin d)
    (σ : ℤ) (j : ℕ) (ω : SiteConfig (Site d)) (hz : z ∈ h.openV) (v : Site 2) :
    MacroExp.pending d (levelTr d r t s h z i σ j ω) v = MacroExp.pending d h v := by
  classical
  ext y
  rw [MacroExp.mem_pending, MacroExp.mem_pending, levelTr_openV i σ j ω hz,
    levelTr_closedV d r t s h z i σ j ω]

/-- Two configurations agreeing on the revealed set produce the same transcript. -/
theorem levelTr_congr (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2) (i : Fin d)
    (σ : ℤ) (j : ℕ) {ω ω' : SiteConfig (Site d)}
    (hagree : ω ∩ ↑(revealSet d r t s h z i σ j) = ω' ∩ ↑(revealSet d r t s h z i σ j)) :
    levelTr d r t s h z i σ j ω = levelTr d r t s h z i σ j ω' :=
  h.step_congr (fun x hx => TargetExt.forall_iff_of_inter_eq hagree x (Finset.mem_coe.2 hx))

end Reveal

/-! ## The corrected stopped event -/

section Target

variable {d : ℕ}

/-- The target of the corridor move: the far part of the stub, at longitudinal coordinate at least
`18 r`.  It is a set, never a designated site. -/
def stubTarget (c : Site d) (i : Fin d) (σ : ℤ) (r t A : ℕ) : Finset (Site d) :=
  (stub c i σ r t A).filter fun x => ((18 * r : ℕ) : ℤ) ≤ lam c i σ x

/-- **The corridor target is not empty**: it contains the axial site at longitudinal coordinate
`20 r`, which is the centre of the target box of `y`. -/
theorem stubTarget_nonempty (c : Site d) (i : Fin d) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {r t A : ℕ}
    (hA : 15 * r ≤ A) : (stubTarget c i σ r t A).Nonempty := by
  refine ⟨c + Pi.single i (σ * ((20 * r : ℕ) : ℤ)), ?_⟩
  have hlam : lam c i σ (c + Pi.single i (σ * ((20 * r : ℕ) : ℤ))) = ((20 * r : ℕ) : ℤ) := by
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
    simp only [lam, Pi.add_apply, Pi.single_eq_same, add_sub_cancel_left]
    rw [← mul_assoc, hσ2, one_mul]
  have hA' : ((20 * r : ℕ) : ℤ) ≤ ((5 * r + A : ℕ) : ℤ) := by
    have : 20 * r ≤ 5 * r + A := by omega
    exact_mod_cast this
  rw [stubTarget, Finset.mem_filter, mem_stub hσ, hlam]
  refine ⟨⟨by push_cast; omega, hA', ?_⟩, by push_cast; omega⟩
  intro j hj
  have hrad : (0 : ℤ) ≤ ((2 * r : ℕ) : ℤ) := by positivity
  simp [Pi.single_eq_of_ne hj, hrad]

theorem mem_deep_of_mem_stubTarget {c : Site d} {i : Fin d} {σ : ℤ} {r t A m : ℕ}
    (hm : 5 * r + m ≤ 18 * r) {x : Site d} (hx : x ∈ stubTarget c i σ r t A) :
    x ∈ deep c i σ r t A m := by
  rw [stubTarget, Finset.mem_filter] at hx
  refine ⟨hx.1, le_trans ?_ hx.2⟩
  exact_mod_cast Nat.cast_le.2 hm

end Target

section Events

variable {d : ℕ} [NeZero d]

/-- Level `j` is **bad**: after the stub has been revealed up to height `10 s j`, the reservation
to the whole target box `M y` is not yet certain to within `δc`.  This is the note's `B_{y,j}`;
its complement is the good-level event, and the first good level is the stopping level. -/
def levelBad (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (σ : ℤ)
    (q : unitInterval) (δc : ℝ) (j : ℕ) : Set (SiteConfig (Site d)) :=
  {ω | (levelTr d r t s h z i σ j ω).prob (fun _ : Site d => q)
    (MacroExp.reservationEvent d r t (levelTr d r t s h z i σ j ω) z y) ≤ 1 - δc}

/-- The crossing event `A_{y,j}`: the origin is joined to the **whole** face at height
`10 s (j+1)` inside the frozen base together with the stub truncated at that face. -/
def crossEvent (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2) (i : Fin d) (σ : ℤ)
    (j : ℕ) : Set (SiteConfig (Site d)) :=
  connWithinSet (zdGraph d)
    (↑(h.inspected ∪ stub (MacroExp.ctr d r z) i σ r t (10 * s * (j + 1))) : Set (Site d))
    (MacroExp.emb 0) (↑(stubFace (MacroExp.ctr d r z) i σ r t (10 * s * (j + 1))) : Set (Site d))

/-- The narrow full-corridor event `C_y` of the corridor move: the origin is joined to the corridor
target inside the frozen base together with the whole stub. -/
def corridorEvent (d r t A : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2) (i : Fin d) (σ : ℤ) :
    Set (SiteConfig (Site d)) :=
  connWithinSet (zdGraph d)
    (↑(h.inspected ∪ stub (MacroExp.ctr d r z) i σ r t A) : Set (Site d))
    (MacroExp.emb 0) (↑(stubTarget (MacroExp.ctr d r z) i σ r t A) : Set (Site d))

/-- `N_y`: no level below `K` is good. -/
def noGoodLevel (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (σ : ℤ)
    (q : unitInterval) (δc : ℝ) (K : ℕ) : Set (SiteConfig (Site d)) :=
  Budget.allBad (levelBad d r t s h z y i σ q δc) K

/-- **The corrected directional event** (11.2): either `y` is already determined, or some level
below `K` is good. -/
def directionEvent (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (σ : ℤ)
    (q : unitInterval) (δc : ℝ) (K : ℕ) : Set (SiteConfig (Site d)) :=
  {_ω | y ∉ MacroExp.pending d h z} ∪ (noGoodLevel d r t s h z y i σ q δc K)ᶜ

theorem mem_allBad_iff {κ : Type*} (bad : ℕ → Set (Set κ)) (K : ℕ) (ω : Set κ) :
    ω ∈ Budget.allBad bad K ↔ ∀ j, j < K → ω ∈ bad j := by
  induction K with
  | zero => simp [Budget.allBad]
  | succ K ih =>
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih.1 h1 j hj
      · exact h2
    · intro hall
      exact ⟨ih.2 fun j hj => hall j (Nat.lt_succ_of_lt hj), hall K (Nat.lt_succ_self K)⟩

theorem determinedBy_allBad {κ : Type*} (bad : ℕ → Set (Set κ)) (S : Set κ) (K : ℕ)
    (hbad : ∀ j, j < K → DeterminedBy (bad j) S) : DeterminedBy (Budget.allBad bad K) S := by
  induction K with
  | zero => simpa [Budget.allBad] using determinedBy_univ S
  | succ K ih =>
    exact (ih fun j hj => hbad j (Nat.lt_succ_of_lt hj)).inter (hbad K (Nat.lt_succ_self K))

/-- The bad-level event reads only the coordinates revealed at that level. -/
theorem determinedBy_levelBad (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z y : Site 2)
    (i : Fin d) (σ : ℤ) (q : unitInterval) (δc : ℝ) (j : ℕ) :
    DeterminedBy (levelBad d r t s h z y i σ q δc j)
      (↑(revealSet d r t s h z i σ j) : Set (Site d)) := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  simp only [levelBad, Set.mem_setOf_eq, levelTr_congr d r t s h z i σ j hagree]

theorem determinedBy_crossEvent (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2)
    (i : Fin d) (σ : ℤ) (j : ℕ) :
    DeterminedBy (crossEvent d r t s h z i σ j)
      (↑(h.inspected ∪ stub (MacroExp.ctr d r z) i σ r t (10 * s * (j + 1))) : Set (Site d)) :=
  determinedBy_connWithinSet _ _ _ _

theorem measurableSet_crossEvent (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z : Site 2)
    (i : Fin d) (σ : ℤ) (j : ℕ) : MeasurableSet (crossEvent d r t s h z i σ j) :=
  measurableSet_connWithinSet _ _ _ _

/-- Pinning the old inspected states does not change membership in a bad-level event: the level
reads only fresh coordinates.  So the hypothesis (7.11) of the bound below may be discharged in the
form `ω ∈ levelBad …` directly. -/
theorem substitute_mem_levelBad_iff (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z y : Site 2)
    (i : Fin d) (σ : ℤ) (q : unitInterval) (δc : ℝ) (j : ℕ) (ω : SiteConfig (Site d)) :
    substitute (↑h.inspected : Set (Site d)) h.state ω ∈ levelBad d r t s h z y i σ q δc j ↔
      ω ∈ levelBad d r t s h z y i σ q δc j := by
  refine (determinedBy_iff _ _).1 (determinedBy_levelBad d r t s h z y i σ q δc j) _ _ ?_
  ext x
  simp only [Set.mem_inter_iff, and_congr_left_iff]
  intro hx
  have hxI : x ∉ (↑h.inspected : Set (Site d)) := fun hc =>
    Finset.disjoint_left.1 (revealSet_fresh d r t s h z i σ j) (Finset.mem_coe.1 hx)
      (Finset.mem_coe.1 hc)
  exact mem_substitute_of_notMem _ hxI

end Events

/-! ## The Section 8 bound -/

section MainBound

variable {d : ℕ} [NeZero d]

/-- **The corrected per-direction level bound (8.6).**

For a fixed still-pending direction, with

* `hsep`  the entrance isolation (5.3) of the frozen base from the stub beyond its source face,
* `ho`    the origin outside the stub,
* `hcorr` the corridor-move estimate `μ(C_y^c) ≤ ρ/32` for the **narrow** corridor event,
* `hpow`  the numerical choice `(1 - δ₂)^K ≤ ρ/32` of the level count, and
* `hone`  the one-level target-extension estimate (7.11) in its denominator-free contrapositive
  form: on a bad level the conditional probability of the crossing event is at most `1 - δ₂`,

no level below `K` is good with pinned probability at most `ρ/16`.

These are exactly the four inputs of Section 8 of the note.  Nothing here asks a designated site to
be open: the crossing targets are whole faces, nonempty by `stubFace_nonempty`, and the reservation
target is the whole box `M y`. -/
theorem prob_noGoodLevel_le {r t s A K : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {σ : ℤ}
    {q : unitInterval} {δc δ₂ ρ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hs : 0 < s) (hfar : 10 * s * K ≤ 13 * r)
    (hsep : ∀ u ∈ h.inspected, ∀ v ∈ stub (MacroExp.ctr d r z) i σ r t A,
      (zdGraph d).Adj u v → (5 * r : ℤ) < lam (MacroExp.ctr d r z) i σ v →
      lam (MacroExp.ctr d r z) i σ u ≤ 5 * r)
    (ho : (MacroExp.emb 0 : Site d) ∉ stub (MacroExp.ctr d r z) i σ r t A)
    (hδ₂ : δ₂ ≤ 1) (hpow : (1 - δ₂) ^ K ≤ ρ / 32)
    (hcorr : h.prob (fun _ : Site d => q) (corridorEvent d r t A h z i σ)ᶜ ≤ ρ / 32)
    (hone : ∀ j, j < K → ∀ ω : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state ω ∈ levelBad d r t s h z y i σ q δc j →
      (levelTr d r t s h z i σ j ω).prob (fun _ : Site d => q)
        (crossEvent d r t s h z i σ j) ≤ 1 - δ₂) :
    h.prob (fun _ : Site d => q) (noGoodLevel d r t s h z y i σ q δc K) ≤ ρ / 16 := by
  classical
  set c := MacroExp.ctr d r z with hcdef
  set p : Site d → unitInterval := fun _ => q with hpdef
  set bad : ℕ → Set (SiteConfig (Site d)) :=
    fun j => crossEvent d r t s h z i σ j ∩ levelBad d r t s h z y i σ q δc j with hbaddef
  have hcross : ∀ j, j < K → corridorEvent d r t A h z i σ ⊆ crossEvent d r t s h z i σ j := by
    intro j hj ω hω
    obtain ⟨b, hbT, hconn⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 hω
    have hconn' : ω ∈ connWithin (zdGraph d)
        ((↑h.inspected : Set (Site d)) ∪ ↑(stub c i σ r t A)) (MacroExp.emb 0) b := by
      rwa [Finset.coe_union] at hconn
    have hmul : 10 * s * (j + 1) ≤ 10 * s * K := Nat.mul_le_mul_left _ (by omega)
    have hm : 5 * r + 10 * s * (j + 1) ≤ 18 * r := by omega
    have hbdeep := mem_deep_of_mem_stubTarget (m := 10 * s * (j + 1)) hm (Finset.mem_coe.1 hbT)
    have h1 : 1 < 10 * s * (j + 1) := by
      have : 10 * 1 * 1 ≤ 10 * s * (j + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 10 hs) (by omega)
      omega
    have hcr := connWithinSet_stubFace_of_conn hσ h1 hsep ho hbdeep hconn'
    rw [crossEvent, Finset.coe_union]
    exact hcr
  have hsubset : noGoodLevel d r t s h z y i σ q δc K ⊆
      (corridorEvent d r t A h z i σ)ᶜ ∪ Budget.allBad bad K := by
    intro ω hω
    by_cases hcω : ω ∈ corridorEvent d r t A h z i σ
    · refine Or.inr ((mem_allBad_iff bad K ω).2 fun j hj => ⟨hcross j hj hcω, ?_⟩)
      exact (mem_allBad_iff _ K ω).1 hω j hj
    · exact Or.inl hcω
  have hstep : ∀ k, k < K →
      pinnedProb p (↑h.inspected : Set (Site d)) h.state (Budget.allBad bad k ∩ bad k) ≤
        (1 - δ₂) * pinnedProb p (↑h.inspected : Set (Site d)) h.state (Budget.allBad bad k) := by
    intro k hk
    have hEq : Budget.allBad bad k ∩ bad k
        = (Budget.allBad bad k ∩ levelBad d r t s h z y i σ q δc k) ∩
            crossEvent d r t s h z i σ k := by
      ext ω
      simp only [hbaddef, Set.mem_inter_iff]
      tauto
    have hCdet : DeterminedBy (Budget.allBad bad k ∩ levelBad d r t s h z y i σ q δc k)
        ((↑h.inspected : Set (Site d)) ∪ ↑(revealSet d r t s h z i σ k)) := by
      refine DeterminedBy.inter (determinedBy_allBad bad _ k fun j hj => ?_) ?_
      · refine DeterminedBy.inter ?_ ?_
        · refine (determinedBy_crossEvent d r t s h z i σ j).mono ?_
          intro x hx
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
          · exact Or.inl (Finset.mem_coe.2 hx)
          · by_cases hxI : x ∈ h.inspected
            · exact Or.inl (Finset.mem_coe.2 hxI)
            · refine Or.inr (Finset.mem_coe.2 ?_)
              rw [revealSet, Finset.mem_sdiff]
              exact ⟨stub_mono hσ (Nat.mul_le_mul_left _ (by omega)) hx, hxI⟩
        · refine (determinedBy_levelBad d r t s h z y i σ q δc j).mono ?_
          intro x hx
          exact Or.inr (Finset.mem_coe.2 (revealSet_mono hσ (by omega) (Finset.mem_coe.1 hx)))
      · exact (determinedBy_levelBad d r t s h z y i σ q δc k).mono fun x hx => Or.inr hx
    have htower := prob_inter_le_of_step_prob_le h p z (revealSet d r t s h z i σ k) true
      (revealSet_fresh d r t s h z i σ k) (measurableSet_crossEvent d r t s h z i σ k) hCdet
      (c := 1 - δ₂) (fun ω hωC => hone k hk ω hωC.2)
    have hmono : h.prob p (Budget.allBad bad k ∩ levelBad d r t s h z y i σ q δc k) ≤
        h.prob p (Budget.allBad bad k) := ProbInv.prob_mono h p Set.inter_subset_left
    have h0 : (0 : ℝ) ≤ 1 - δ₂ := by linarith
    calc pinnedProb p (↑h.inspected : Set (Site d)) h.state (Budget.allBad bad k ∩ bad k)
        = h.prob p ((Budget.allBad bad k ∩ levelBad d r t s h z y i σ q δc k) ∩
            crossEvent d r t s h z i σ k) := by rw [hEq]; rfl
      _ ≤ (1 - δ₂) * h.prob p (Budget.allBad bad k ∩ levelBad d r t s h z y i σ q δc k) := htower
      _ ≤ (1 - δ₂) * h.prob p (Budget.allBad bad k) := mul_le_mul_of_nonneg_left hmono h0
  have hfinal := Budget.pinnedProb_corridor_or_allBad_le p (↑h.inspected : Set (Site d)) h.state
    (corridorEvent d r t A h z i σ)ᶜ bad K ρ δ₂ hδ₂ hpow hcorr hstep
  exact le_trans (ProbInv.prob_mono h p hsubset) hfinal

end MainBound

/-! ## The stub inside the macro geometry -/

section MacroFit

variable {d : ℕ}

/-- The embedding is additive on differences. -/
theorem emb_sub_apply (y z : Site 2) (j : Fin d) :
    (MacroExp.emb (y - z) : Site d) j = MacroExp.emb y j - MacroExp.emb z j := by
  by_cases hj : j.val < 2
  · rw [MacroExp.emb_apply_of_lt _ hj, MacroExp.emb_apply_of_lt _ hj,
      MacroExp.emb_apply_of_lt _ hj]
    simp
  · rw [MacroExp.emb_apply_of_not_lt _ hj, MacroExp.emb_apply_of_not_lt _ hj,
      MacroExp.emb_apply_of_not_lt _ hj]
    ring

theorem ctr_sub_apply (r : ℕ) (y z : Site 2) (j : Fin d) :
    MacroExp.ctr d r y j - MacroExp.ctr d r z j = 20 * (r : ℤ) * (MacroExp.emb (y - z) : Site d) j := by
  rw [MacroExp.ctr, MacroExp.ctr, emb_sub_apply]
  ring

/-- **The origin is outside the stub.**  A pending direction is never the origin macro-vertex, and
the only way the embedded origin could sit in the stub of `z → y` is `y = 0`.  So the source of the
crossing argument is genuinely outside the family of faces. -/
theorem origin_notMem_stub (hd : 2 ≤ d) {r : ℕ} (hr : 0 < r) {t A : ℕ} (hA : A ≤ 17 * r)
    {z y : Site 2} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) (hy : y ≠ 0) :
    (MacroExp.emb 0 : Site d) ∉ stub (MacroExp.ctr d r z) i σ r t A := by
  intro hmem
  rw [MacroExp.emb_zero, mem_stub hσ] at hmem
  obtain ⟨hlow, hhigh, htrans⟩ := hmem
  have hrz : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
  -- the direction coordinate forces `emb z i = -σ`
  have hlam : lam (MacroExp.ctr d r z) i σ (0 : Site d)
      = -(20 * (r : ℤ)) * (σ * MacroExp.emb z i) := by
    simp only [lam, MacroExp.ctr, Pi.zero_apply, zero_sub]
    ring
  set Y : ℤ := -(σ * MacroExp.emb z i) with hY
  have h22 : ((5 * r + A : ℕ) : ℤ) ≤ 22 * (r : ℤ) := by
    have : 5 * r + A ≤ 22 * r := by omega
    calc ((5 * r + A : ℕ) : ℤ) ≤ ((22 * r : ℕ) : ℤ) := by exact_mod_cast this
      _ = 22 * (r : ℤ) := by push_cast; ring
  have hlow' : 5 * (r : ℤ) ≤ 20 * (r : ℤ) * Y := by
    rw [hlam] at hlow; rw [hY]; linarith [hlow]
  have hhigh' : 20 * (r : ℤ) * Y ≤ 22 * (r : ℤ) := by
    rw [hlam] at hhigh; rw [hY]; linarith [hhigh.trans h22]
  have hY1 : Y = 1 := by
    rcases lt_trichotomy Y 1 with hc | hc | hc
    · exfalso; nlinarith
    · exact hc
    · exfalso; nlinarith
  have hzi : MacroExp.emb z i = -σ := by
    have : σ * MacroExp.emb z i = -1 := by rw [hY] at hY1; linarith
    calc MacroExp.emb z i = (σ * σ) * MacroExp.emb z i := by rw [hσ2]; ring
      _ = σ * (σ * MacroExp.emb z i) := by ring
      _ = -σ := by rw [this]; ring
  -- the other coordinates force `emb z j = 0`
  have hzero : (MacroExp.emb y : Site d) = MacroExp.emb (0 : Site 2) := by
    rw [MacroExp.emb_zero]
    funext j
    have hsum : MacroExp.emb y j = MacroExp.emb z j + (MacroExp.emb (y - z) : Site d) j := by
      rw [emb_sub_apply]; ring
    by_cases hji : j = i
    · subst hji
      rw [hsum, hemb, Pi.single_eq_same, hzi]
      simp
    · have hd0 : (MacroExp.emb (y - z) : Site d) j = 0 := by
        rw [hemb, Pi.single_eq_of_ne hji]
      by_cases hjp : j.val < 2
      · have ht := htrans j hji
        rw [MacroExp.ctr] at ht
        simp only [Pi.zero_apply, zero_sub, abs_neg] at ht
        have habs : |20 * (r : ℤ) * MacroExp.emb z j| ≤ 2 * (r : ℤ) := ht
        have hzj : MacroExp.emb z j = 0 := by
          rcases lt_trichotomy (MacroExp.emb z j) 0 with hc | hc | hc
          · exfalso
            rw [abs_le] at habs
            nlinarith [habs.1]
          · exact hc
          · exfalso
            rw [abs_le] at habs
            nlinarith [habs.2]
        rw [hsum, hd0, hzj]; simp
      · rw [hsum, hd0, MacroExp.emb_apply_of_not_lt _ hjp]; simp
  exact hy (MacroExp.emb_injective hd hzero)

/-- The direction of a macro-step is one of the two planar coordinates. -/
theorem dir_planar {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {y z : Site 2}
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) : i.val < 2 := by
  by_contra hi
  have h1 : (MacroExp.emb (y - z) : Site d) i = 0 := MacroExp.emb_apply_of_not_lt _ hi
  rw [hemb, Pi.single_eq_same] at h1
  rcases hσ with rfl | rfl <;> simp at h1

/-- **The corridor target lies in the target box of `y`.**  So the corridor event of the crossing
argument really is a connection to `M y`, and the reservation stored at the stopping level is the
one the exploration invariant asks for. -/
theorem stubTarget_subset_M {r t A : ℕ} (hA : A ≤ 17 * r) (hrt : 2 * r ≤ t)
    {z y : Site 2} {i : Fin d}
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) :
    stubTarget (MacroExp.ctr d r z) i σ r t A ⊆ MacroExp.M d r t y := by
  intro x hx
  rw [stubTarget, Finset.mem_filter] at hx
  obtain ⟨hxstub, hxfar⟩ := hx
  rw [mem_stub hσ] at hxstub
  obtain ⟨-, hxhigh, hxtrans⟩ := hxstub
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
  have h18 : 18 * (r : ℤ) ≤ lam (MacroExp.ctr d r z) i σ x := by
    have : ((18 * r : ℕ) : ℤ) = 18 * (r : ℤ) := by push_cast; ring
    linarith [this ▸ hxfar]
  have h22 : lam (MacroExp.ctr d r z) i σ x ≤ 22 * (r : ℤ) := by
    have hc : ((5 * r + A : ℕ) : ℤ) ≤ 22 * (r : ℤ) := by
      have hn : 5 * r + A ≤ 22 * r := by omega
      calc ((5 * r + A : ℕ) : ℤ) ≤ ((22 * r : ℕ) : ℤ) := by exact_mod_cast hn
        _ = 22 * (r : ℤ) := by push_cast; ring
    linarith [hxhigh]
  rw [MacroExp.M, MacroExp.mem_abox]
  intro j
  have hctr := ctr_sub_apply (d := d) r y z j
  by_cases hji : j = i
  · subst hji
    have hcy : MacroExp.ctr d r y j = MacroExp.ctr d r z j + 20 * (r : ℤ) * σ := by
      rw [hemb, Pi.single_eq_same] at hctr; linarith
    have hkey : x j - MacroExp.ctr d r y j
        = σ * (lam (MacroExp.ctr d r z) j σ x - 20 * (r : ℤ)) := by
      have hxj : x j - MacroExp.ctr d r z j = σ * lam (MacroExp.ctr d r z) j σ x := by
        simp only [lam]
        calc x j - MacroExp.ctr d r z j
            = (σ * σ) * (x j - MacroExp.ctr d r z j) := by rw [hσ2]; ring
          _ = σ * (σ * (x j - MacroExp.ctr d r z j)) := by ring
      rw [hcy]
      have : x j - (MacroExp.ctr d r z j + 20 * (r : ℤ) * σ)
          = (x j - MacroExp.ctr d r z j) - 20 * (r : ℤ) * σ := by ring
      rw [this, hxj]; ring
    have hrad : MacroExp.rad (3 * r) t j = 3 * (r : ℤ) := by
      unfold MacroExp.rad
      rw [if_pos (dir_planar hσ hemb)]
      push_cast; ring
    have hbound : -(3 * (r : ℤ)) ≤ x j - MacroExp.ctr d r y j ∧
        x j - MacroExp.ctr d r y j ≤ 3 * (r : ℤ) := by
      rcases hσ with rfl | rfl <;> rw [hkey] <;> constructor <;> linarith
    rw [hrad]
    constructor <;> linarith [hbound.1, hbound.2]
  · have hcy : MacroExp.ctr d r y j = MacroExp.ctr d r z j := by
      rw [hemb, Pi.single_eq_of_ne hji] at hctr; linarith
    have ht := hxtrans j hji
    have hrad : ((2 * r : ℕ) : ℤ) ≤ MacroExp.rad (3 * r) t j := by
      unfold MacroExp.rad; split_ifs <;> push_cast <;> omega
    rw [abs_le] at ht
    rw [hcy]
    constructor <;> linarith [ht.1, ht.2]

/-- **Entrance isolation from the exploration invariant.**  If the inspected sites lie in the slab
and the outgoing edge region `E z y` is still unread, then no inspected site adjacent to the stub
beyond its source face has longitudinal coordinate above `5 r`: such a site would itself lie in
`E z y`.

This discharges the hypothesis `hsep` of the crossing argument from `MacroExp.Good.inspected_thin`
and the freshness of the outgoing corridor, which is what `MacroExp.Good.cover` supplies. -/
theorem sep_of_fresh [NeZero d] (hd : 2 ≤ d) {r : ℕ} (hr : 0 < r) {t A : ℕ} (hA : A ≤ 17 * r)
    {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ)
    (hthin : (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh : Disjoint h.inspected (MacroExp.E d r t z y)) :
    ∀ u ∈ h.inspected, ∀ v ∈ stub (MacroExp.ctr d r z) i σ r t A,
      (zdGraph d).Adj u v → (5 * r : ℤ) < lam (MacroExp.ctr d r z) i σ v →
      lam (MacroExp.ctr d r z) i σ u ≤ 5 * r := by
  intro u hu v hv huv hlamv
  by_contra hcon
  rw [not_le] at hcon
  refine Finset.disjoint_left.1 hfresh hu ?_
  have hrz : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hiplanar := dir_planar hσ hemb
  have hvmem := (mem_stub hσ).1 hv
  have h22 : ((5 * r + A : ℕ) : ℤ) ≤ 22 * (r : ℤ) := by
    have hn : 5 * r + A ≤ 22 * r := by omega
    calc ((5 * r + A : ℕ) : ℤ) ≤ ((22 * r : ℕ) : ℤ) := by exact_mod_cast hn
      _ = 22 * (r : ℤ) := by push_cast; ring
  have hadj := lam_adj (c := MacroExp.ctr d r z) (i := i) hσ huv
  rw [abs_le] at hadj
  have hLhi : lam (MacroExp.ctr d r z) i σ u ≤ 22 * (r : ℤ) + 1 := by
    linarith [hvmem.2.1, h22, hadj.1]
  have habsu : |u i - MacroExp.ctr d r z i| ≤ 25 * (r : ℤ) := by
    rw [← lam_abs hσ (MacroExp.ctr d r z) i u, abs_le]
    constructor <;> linarith
  have hbnd : -(20 * (r : ℤ)) ≤ 20 * (r : ℤ) * σ ∧ 20 * (r : ℤ) * σ ≤ 20 * (r : ℤ) := by
    rcases hσ with rfl | rfl <;> constructor <;> linarith
  rw [MacroExp.E, Finset.mem_sdiff]
  constructor
  · rw [MacroExp.mem_hbox]
    intro j
    have hctr := ctr_sub_apply (d := d) r y z j
    by_cases hji : j = i
    · subst hji
      have hrad : MacroExp.rad (5 * r) t j = 5 * (r : ℤ) := by
        unfold MacroExp.rad; rw [if_pos hiplanar]; push_cast; ring
      rw [hrad]
      rcases hσ with rfl | rfl
      · have hcy : MacroExp.ctr d r y j = MacroExp.ctr d r z j + 20 * (r : ℤ) := by
          rw [hemb, Pi.single_eq_same] at hctr; linarith
        have hui : lam (MacroExp.ctr d r z) j 1 u = u j - MacroExp.ctr d r z j := by
          simp [lam]
        have hmin : min (MacroExp.ctr d r z j) (MacroExp.ctr d r y j)
            = MacroExp.ctr d r z j := by rw [hcy]; exact min_eq_left (by linarith)
        have hmax : max (MacroExp.ctr d r z j) (MacroExp.ctr d r y j)
            = MacroExp.ctr d r z j + 20 * (r : ℤ) := by
          rw [hcy]; exact max_eq_right (by linarith)
        rw [hmin, hmax]
        constructor <;> linarith [hcon, hLhi, hui]
      · have hcy : MacroExp.ctr d r y j = MacroExp.ctr d r z j - 20 * (r : ℤ) := by
          rw [hemb, Pi.single_eq_same] at hctr; linarith
        have hui : lam (MacroExp.ctr d r z) j (-1) u = MacroExp.ctr d r z j - u j := by
          simp [lam]
        have hmin : min (MacroExp.ctr d r z j) (MacroExp.ctr d r y j)
            = MacroExp.ctr d r z j - 20 * (r : ℤ) := by
          rw [hcy]; exact min_eq_right (by linarith)
        have hmax : max (MacroExp.ctr d r z j) (MacroExp.ctr d r y j)
            = MacroExp.ctr d r z j := by rw [hcy]; exact max_eq_left (by linarith)
        rw [hmin, hmax]
        constructor <;> linarith [hcon, hLhi, hui]
    · have hcy : MacroExp.ctr d r y j = MacroExp.ctr d r z j := by
        rw [hemb, Pi.single_eq_of_ne hji] at hctr; linarith
      have hvj := hvmem.2.2 j hji
      have huvj := LevelOpus.abs_sub_le_one_of_adj huv j
      rw [abs_le] at hvj huvj
      push_cast at hvj
      rw [hcy, min_self, max_self]
      by_cases hjp : j.val < 2
      · have hrad5 : MacroExp.rad (5 * r) t j = 5 * (r : ℤ) := by
          unfold MacroExp.rad; rw [if_pos hjp]; push_cast; ring
        rw [hrad5]
        constructor <;> linarith [hvj.1, hvj.2, huvj.1, huvj.2]
      · have hj0 : j ≠ 0 := by
          intro hc; rw [hc] at hjp; simp at hjp
        have hj1 : j ≠ 1 := by
          intro hc; rw [hc, LevelOpus.val_one hd] at hjp; omega
        have hthinu := hthin (Finset.mem_coe.2 hu) j hj0 hj1
        have hctrz : MacroExp.ctr d r z j = 0 := MacroExp.ctr_apply_of_not_lt r z hjp
        have hrad5 : MacroExp.rad (5 * r) t j = (t : ℤ) := by
          unfold MacroExp.rad; rw [if_neg hjp]
        rw [abs_le] at hthinu
        rw [hrad5, hctrz]
        constructor <;> linarith [hthinu.1, hthinu.2]
  · intro hQ
    rw [MacroExp.Q, MacroExp.mem_abox] at hQ
    have hQi := hQ i
    have hrad : MacroExp.rad (5 * r) t i = 5 * (r : ℤ) := by
      unfold MacroExp.rad; rw [if_pos hiplanar]; push_cast; ring
    rw [hrad] at hQi
    have habs : |u i - MacroExp.ctr d r z i| ≤ 5 * (r : ℤ) := by
      rw [abs_le]; constructor <;> linarith [hQi.1, hQi.2]
    rw [← lam_abs hσ (MacroExp.ctr d r z) i u, abs_le] at habs
    linarith [habs.2]

/-- **The stub lies in the protected region.**  Its source face is the outgoing face of `Q z` and
everything beyond that face lies in the outgoing edge region `E z y`.  So the reveal-only substeps
read only sites that the incoming examination has already reserved for this direction, and nothing
outside `MacroExp.Good.cover`'s union. -/
theorem stub_subset_Q_union_E {r : ℕ} (hr : 0 < r) {t A : ℕ} (hA : A ≤ 17 * r)
    (hrt : 2 * r ≤ t) {z y : Site 2}
    {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) :
    stub (MacroExp.ctr d r z) i σ r t A ⊆ MacroExp.Q d r t z ∪ MacroExp.E d r t z y := by
  intro x hx
  have hxmem := (mem_stub hσ).1 hx
  obtain ⟨hlow, hhigh, htrans⟩ := hxmem
  have hrz : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hiplanar := dir_planar hσ hemb
  have h22 : ((5 * r + A : ℕ) : ℤ) ≤ 22 * (r : ℤ) := by
    have hn : 5 * r + A ≤ 22 * r := by omega
    calc ((5 * r + A : ℕ) : ℤ) ≤ ((22 * r : ℕ) : ℤ) := by exact_mod_cast hn
      _ = 22 * (r : ℤ) := by push_cast; ring
  have hradi5 : MacroExp.rad (5 * r) t i = 5 * (r : ℤ) := by
    unfold MacroExp.rad; rw [if_pos hiplanar]; push_cast; ring
  have habsx : |x i - MacroExp.ctr d r z i| = lam (MacroExp.ctr d r z) i σ x := by
    rw [← lam_abs hσ (MacroExp.ctr d r z) i x, abs_of_nonneg (by linarith)]
  rw [Finset.mem_union]
  by_cases hlam5 : lam (MacroExp.ctr d r z) i σ x ≤ 5 * (r : ℤ)
  · refine Or.inl ?_
    rw [MacroExp.Q, MacroExp.mem_abox]
    intro j
    by_cases hji : j = i
    · subst hji
      have : |x j - MacroExp.ctr d r z j| ≤ 5 * (r : ℤ) := by rw [habsx]; exact hlam5
      rw [abs_le] at this
      rw [hradi5]
      constructor <;> linarith [this.1, this.2]
    · have ht := htrans j hji
      have hrad : ((2 * r : ℕ) : ℤ) ≤ MacroExp.rad (5 * r) t j := by
        unfold MacroExp.rad; split_ifs <;> push_cast <;> omega
      rw [abs_le] at ht
      constructor <;> linarith [ht.1, ht.2]
  · rw [not_le] at hlam5
    refine Or.inr ?_
    rw [MacroExp.E, Finset.mem_sdiff]
    constructor
    · rw [MacroExp.mem_hbox]
      intro j
      have hctr := ctr_sub_apply (d := d) r y z j
      by_cases hji : j = i
      · subst hji
        rw [hradi5]
        rcases hσ with rfl | rfl
        · have hcy : MacroExp.ctr d r y j = MacroExp.ctr d r z j + 20 * (r : ℤ) := by
            rw [hemb, Pi.single_eq_same] at hctr; linarith
          have hui : lam (MacroExp.ctr d r z) j 1 x = x j - MacroExp.ctr d r z j := by
            simp [lam]
          have hmin : min (MacroExp.ctr d r z j) (MacroExp.ctr d r y j)
              = MacroExp.ctr d r z j := by rw [hcy]; exact min_eq_left (by linarith)
          have hmax : max (MacroExp.ctr d r z j) (MacroExp.ctr d r y j)
              = MacroExp.ctr d r z j + 20 * (r : ℤ) := by
            rw [hcy]; exact max_eq_right (by linarith)
          rw [hmin, hmax]
          constructor <;> linarith [hlam5, hhigh, h22, hui]
        · have hcy : MacroExp.ctr d r y j = MacroExp.ctr d r z j - 20 * (r : ℤ) := by
            rw [hemb, Pi.single_eq_same] at hctr; linarith
          have hui : lam (MacroExp.ctr d r z) j (-1) x = MacroExp.ctr d r z j - x j := by
            simp [lam]
          have hmin : min (MacroExp.ctr d r z j) (MacroExp.ctr d r y j)
              = MacroExp.ctr d r z j - 20 * (r : ℤ) := by
            rw [hcy]; exact min_eq_right (by linarith)
          have hmax : max (MacroExp.ctr d r z j) (MacroExp.ctr d r y j)
              = MacroExp.ctr d r z j := by rw [hcy]; exact max_eq_left (by linarith)
          rw [hmin, hmax]
          constructor <;> linarith [hlam5, hhigh, h22, hui]
      · have hcy : MacroExp.ctr d r y j = MacroExp.ctr d r z j := by
          rw [hemb, Pi.single_eq_of_ne hji] at hctr; linarith
        have ht := htrans j hji
        have hrad : ((2 * r : ℕ) : ℤ) ≤ MacroExp.rad (5 * r) t j := by
          unfold MacroExp.rad; split_ifs <;> push_cast <;> omega
        rw [abs_le] at ht
        rw [hcy, min_self, max_self]
        constructor <;> linarith [ht.1, ht.2]
    · intro hQ
      rw [MacroExp.Q, MacroExp.mem_abox] at hQ
      have hQi := hQ i
      rw [hradi5] at hQi
      have : |x i - MacroExp.ctr d r z i| ≤ 5 * (r : ℤ) := by
        rw [abs_le]; constructor <;> linarith [hQi.1, hQi.2]
      rw [habsx] at this
      linarith

end MacroFit

/-! ## The directional event -/

section Direction

variable {d : ℕ} [NeZero d]

/-- **The corrected per-direction bound with the geometry discharged.**  The entrance isolation and
the position of the origin are now consequences of the exploration invariant: `hthin` is
`MacroExp.Good.inspected_thin`, `hfreshE` is the freshness of the outgoing corridor supplied by
`MacroExp.Good.cover`, and `hy` says that the pending direction is not the origin macro-vertex,
which holds because the origin is always occupied.

What remains are exactly the three probabilistic inputs of Section 8: the corridor-move estimate
`hcorr`, the numerical choice `hpow` of the level count, and the one-level target-extension
estimate `hone`. -/
theorem prob_directionEvent_compl_le {r t s A K : ℕ} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {σ : ℤ} {q : unitInterval} {δc δ₂ ρ : ℝ}
    (hd : 2 ≤ d) (hr : 0 < r) (hs : 0 < s) (hA : A ≤ 17 * r) (hfar : 10 * s * K ≤ 13 * r)
    (hσ : σ = 1 ∨ σ = -1) (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) (hy : y ≠ 0)
    (hthin : (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfreshE : Disjoint h.inspected (MacroExp.E d r t z y))
    (hδ₂ : δ₂ ≤ 1) (hpow : (1 - δ₂) ^ K ≤ ρ / 32)
    (hcorr : h.prob (fun _ : Site d => q) (corridorEvent d r t A h z i σ)ᶜ ≤ ρ / 32)
    (hone : ∀ j, j < K → ∀ ω : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state ω ∈ levelBad d r t s h z y i σ q δc j →
      (levelTr d r t s h z i σ j ω).prob (fun _ : Site d => q)
        (crossEvent d r t s h z i σ j) ≤ 1 - δ₂) :
    h.prob (fun _ : Site d => q) (directionEvent d r t s h z y i σ q δc K)ᶜ ≤ ρ / 16 := by
  refine le_trans (ProbInv.prob_mono h _ ?_)
    (prob_noGoodLevel_le hσ hs hfar (sep_of_fresh hd hr hA hσ hemb hthin hfreshE)
      (origin_notMem_stub hd hr hA hσ hemb hy) hδ₂ hpow hcorr hone)
  intro ω hω
  by_contra hc
  exact hω (Or.inr hc)

/-- **The joint interface (11.4).**  If the implementation exposes the outgoing stubs only when the
incoming connection succeeds, the event the union budget needs is
`Incoming^c ∪ Direction_y`, and the same `ρ/16` bound covers it. -/
theorem prob_joint_compl_le {r t s K : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {σ : ℤ}
    {q : unitInterval} {δc ρ : ℝ} (incoming : Set (SiteConfig (Site d)))
    (hbound : h.prob (fun _ : Site d => q) (noGoodLevel d r t s h z y i σ q δc K) ≤ ρ / 16) :
    h.prob (fun _ : Site d => q)
      (incomingᶜ ∪ directionEvent d r t s h z y i σ q δc K)ᶜ ≤ ρ / 16 := by
  refine le_trans (ProbInv.prob_mono h _ ?_) hbound
  intro ω hω
  by_contra hc
  exact hω (Or.inr (Or.inr hc))

end Direction

/-! ## The stopping level -/

section Stopping

variable {d : ℕ} [NeZero d]

open Classical in
/-- **The stopping level**: the first level below `K` that is good, and `K` when there is none.
The layers are revealed one at a time and the examination stops here; the reveal is a genuine
substep of the transcript, so the level is a function of the states read so far. -/
def stopLevel (d r t s : ℕ) [NeZero d] (h : MacroExp.Tr d) (z y : Site 2) (i : Fin d) (σ : ℤ)
    (q : unitInterval) (δc : ℝ) (K : ℕ) (ω : SiteConfig (Site d)) : ℕ :=
  if hex : ∃ j, j < K ∧ ω ∉ levelBad d r t s h z y i σ q δc j then Nat.find hex else K

theorem exists_good_of_notMem_noGoodLevel {r t s K : ℕ} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {σ : ℤ} {q : unitInterval} {δc : ℝ} {ω : SiteConfig (Site d)}
    (hω : ω ∉ noGoodLevel d r t s h z y i σ q δc K) :
    ∃ j, j < K ∧ ω ∉ levelBad d r t s h z y i σ q δc j := by
  by_contra hc
  refine hω ((mem_allBad_iff _ K ω).2 fun j hj => ?_)
  by_contra hcj
  exact hc ⟨j, hj, hcj⟩

theorem stopLevel_lt {r t s K : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {σ : ℤ}
    {q : unitInterval} {δc : ℝ} {ω : SiteConfig (Site d)}
    (hω : ω ∉ noGoodLevel d r t s h z y i σ q δc K) :
    stopLevel d r t s h z y i σ q δc K ω < K := by
  classical
  have hex := exists_good_of_notMem_noGoodLevel hω
  rw [stopLevel, dif_pos hex]
  exact (Nat.find_spec hex).1

/-- Every level strictly below the stopping level is bad: the stop is at the **first** good
level. -/
theorem stopLevel_min {r t s K : ℕ} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {σ : ℤ}
    {q : unitInterval} {δc : ℝ} {ω : SiteConfig (Site d)}
    (hω : ω ∉ noGoodLevel d r t s h z y i σ q δc K) {m : ℕ}
    (hm : m < stopLevel d r t s h z y i σ q δc K ω) :
    ω ∈ levelBad d r t s h z y i σ q δc m := by
  classical
  have hex := exists_good_of_notMem_noGoodLevel hω
  rw [stopLevel, dif_pos hex] at hm
  have hmin := Nat.find_min hex hm
  by_contra hc
  exact hmin ⟨lt_trans hm (Nat.find_spec hex).1, hc⟩

/-- **What the stopped examination delivers.**  At the stopping level the revealed transcript
carries a reservation to the whole target box `M y` at tolerance `δc`: exactly the clause the
exploration invariant stores for a pending direction, with no existential deep target and no
designated open site. -/
theorem lt_prob_reservationEvent_stopLevel {r t s K : ℕ} {h : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {σ : ℤ} {q : unitInterval} {δc : ℝ} {ω : SiteConfig (Site d)}
    (hω : ω ∉ noGoodLevel d r t s h z y i σ q δc K) :
    1 - δc < (levelTr d r t s h z i σ (stopLevel d r t s h z y i σ q δc K ω) ω).prob
      (fun _ : Site d => q)
      (MacroExp.reservationEvent d r t
        (levelTr d r t s h z i σ (stopLevel d r t s h z y i σ q δc K ω) ω) z y) := by
  classical
  have hex := exists_good_of_notMem_noGoodLevel hω
  have hgood : ω ∉ levelBad d r t s h z y i σ q δc
      (stopLevel d r t s h z y i σ q δc K ω) := by
    rw [stopLevel, dif_pos hex]
    exact (Nat.find_spec hex).2
  rw [levelBad, Set.mem_setOf_eq, not_le] at hgood
  exact hgood

end Stopping

/-! ## The hypotheses at an accepted examination -/

section Accepted

variable {d : ℕ} [NeZero d]

/-- The invariant at any tolerance implies the invariant at the trivial tolerance, whose
probabilistic clause is vacuous.  Only the deterministic clauses of `MacroExp.Good` are used by the
freshness statements below. -/
theorem good_default_of_good {r t : ℕ} {h : MacroExp.Tr d} {q : unitInterval} {δ : ℝ}
    (hg : MacroExp.Good d r t h q δ) : MacroExp.Good d r t h where
  zero_mem := hg.zero_mem
  inspected_thin := hg.inspected_thin
  cert := hg.cert
  reserve := by
    intro v _ w _
    unfold MacroExp.reservationBound
    have hnn := FRDom.Transcript.prob_nonneg h (fun _ : Site d => (1 : unitInterval))
      (MacroExp.reservationEvent d r t h v w)
    linarith
  cover := hg.cover

/-- Everything read by an accepted examination still lies in the slab. -/
theorem accepted_inspected_thin (hd : 2 ≤ d) {r t n : ℕ} {h : MacroExp.Tr d} {q : unitInterval}
    {δ : ℝ} (hg : MacroExp.Good d r t h q δ) (ω : SiteConfig (Site d)) :
    (↑(MacroExp.accepted d r t n h ω).inspected : Set (Site d)) ⊆ MacroExp.thin d t := by
  intro x hx
  rw [Finset.mem_coe, MacroExp.accepted, FRDom.Transcript.step_inspected,
    Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact hg.inspected_thin (Finset.mem_coe.2 hx)
  · exact MacroExp.E_subset_thin hd r t _ _
      (Finset.mem_coe.2 (Finset.mem_sdiff.1 hx).1)

/-- **The outgoing corridor of a still-pending direction is unread after the examination.**  The
old inspected set misses it by `MacroExp.Good.cover`, and the incoming corridor misses it because
two oriented macro-edges with distinct heads and no reversal have disjoint regions. -/
theorem accepted_fresh_E (hd : 2 ≤ d) {r t n : ℕ} (hr : 0 < r) {h : MacroExp.Tr d}
    {q : unitInterval} {δ : ℝ} (hg : MacroExp.Good d r t h q δ)
    (hwspec : MacroExp.pendW d n h ∈ h.openV ∧
      (zdGraph 2).Adj (MacroExp.pendW d n h) (MacroExp.pendZ d n h))
    (ω : SiteConfig (Site d)) {y : Site 2}
    (hy : y ∈ MacroExp.pending d (MacroExp.accepted d r t n h ω) (MacroExp.pendZ d n h)) :
    Disjoint (MacroExp.accepted d r t n h ω).inspected
      (MacroExp.E d r t (MacroExp.pendZ d n h) y) := by
  classical
  obtain ⟨hynbr, hyund⟩ := (MacroExp.mem_pending d).1 hy
  have hopenV : (MacroExp.accepted d r t n h ω).openV
      = insert (MacroExp.pendZ d n h) h.openV := by
    rw [MacroExp.accepted, FRDom.Transcript.step_openV, if_pos rfl]
  have hclosedV : (MacroExp.accepted d r t n h ω).closedV = h.closedV := by
    rw [MacroExp.accepted, FRDom.Transcript.step_closedV, if_pos rfl]
  have hyh : y ∉ h.openV ∪ h.closedV := by
    intro hc
    refine hyund ?_
    rw [hopenV, hclosedV]
    rcases Finset.mem_union.1 hc with hc | hc
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hc)
    · exact Finset.mem_union_right _ hc
  have hyz : y ≠ MacroExp.pendZ d n h := by
    intro hc
    refine hyund ?_
    rw [hopenV, hc]
    exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  have hzy : (zdGraph 2).Adj (MacroExp.pendZ d n h) y := MacroExp.adj_of_mem_nbrs hynbr
  have hwy : MacroExp.pendW d n h ≠ y := by
    intro hc
    exact hyh (Finset.mem_union_left _ (hc ▸ hwspec.1))
  have hold : Disjoint h.inspected (MacroExp.E d r t (MacroExp.pendZ d n h) y) :=
    Corridor.inspected_disjoint_E_of_good_of_undetermined hd r t hr (good_default_of_good hg)
      hzy hyh
  have hnew : Disjoint (MacroExp.E d r t (MacroExp.pendW d n h) (MacroExp.pendZ d n h))
      (MacroExp.E d r t (MacroExp.pendZ d n h) y) :=
    MacroExp.protectedEdges_disjoint hd r t hr hwspec.2 hzy (Ne.symm hyz)
      (by rintro ⟨hc, -⟩; exact hwy hc)
  rw [MacroExp.accepted, FRDom.Transcript.step_inspected, Finset.disjoint_union_left]
  refine ⟨hold, hnew.mono_left ?_⟩
  rw [MacroExp.region]
  exact Finset.sdiff_subset

/-- **The corrected per-direction bound at an accepted examination.**  Every geometric and
freshness hypothesis is now discharged from `MacroExp.Good` and non-terminality; what is left are
the three probabilistic inputs of Section 8.

`hwspec` is `MacroExp.pendW_spec d r t n hg hT` at a non-terminal transcript: the examined
macro-vertex has an occupied macro-neighbour.  `ω₀` is the configuration read on the incoming
corridor; the bound holds for each of them, so it holds after the incoming reveal whatever was seen
there. -/
theorem prob_directionEvent_compl_le_accepted {r t s A K n : ℕ} {h : MacroExp.Tr d}
    {y : Site 2} {i : Fin d} {σ : ℤ} {q q₀ : unitInterval} {δ δc δ₂ ρ : ℝ}
    {ω₀ : SiteConfig (Site d)}
    (hd : 2 ≤ d) (hr : 0 < r) (hs : 0 < s) (hA : A ≤ 17 * r) (hfar : 10 * s * K ≤ 13 * r)
    (hg : MacroExp.Good d r t h q₀ δ)
    (hwspec : MacroExp.pendW d n h ∈ h.openV ∧
      (zdGraph 2).Adj (MacroExp.pendW d n h) (MacroExp.pendZ d n h))
    (hy : y ∈ MacroExp.pending d (MacroExp.accepted d r t n h ω₀) (MacroExp.pendZ d n h))
    (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - MacroExp.pendZ d n h) : Site d) = Pi.single i σ)
    (hδ₂ : δ₂ ≤ 1) (hpow : (1 - δ₂) ^ K ≤ ρ / 32)
    (hcorr : (MacroExp.accepted d r t n h ω₀).prob (fun _ : Site d => q)
      (corridorEvent d r t A (MacroExp.accepted d r t n h ω₀) (MacroExp.pendZ d n h) i σ)ᶜ
        ≤ ρ / 32)
    (hone : ∀ j, j < K → ∀ ω : SiteConfig (Site d),
      substitute (↑(MacroExp.accepted d r t n h ω₀).inspected : Set (Site d))
          (MacroExp.accepted d r t n h ω₀).state ω ∈
        levelBad d r t s (MacroExp.accepted d r t n h ω₀) (MacroExp.pendZ d n h) y i σ q δc j →
      (levelTr d r t s (MacroExp.accepted d r t n h ω₀) (MacroExp.pendZ d n h) i σ j ω).prob
          (fun _ : Site d => q)
          (crossEvent d r t s (MacroExp.accepted d r t n h ω₀) (MacroExp.pendZ d n h) i σ j)
        ≤ 1 - δ₂) :
    (MacroExp.accepted d r t n h ω₀).prob (fun _ : Site d => q)
      (directionEvent d r t s (MacroExp.accepted d r t n h ω₀) (MacroExp.pendZ d n h) y i σ q δc
        K)ᶜ ≤ ρ / 16 := by
  have hyzero : y ≠ 0 := by
    intro hc
    have hyund := ((MacroExp.mem_pending d).1 hy).2
    refine hyund (Finset.mem_union_left _ ?_)
    rw [MacroExp.accepted, FRDom.Transcript.step_openV, if_pos rfl, hc]
    exact Finset.mem_insert_of_mem hg.zero_mem
  exact prob_directionEvent_compl_le hd hr hs hA hfar hσ hemb hyzero
    (accepted_inspected_thin hd hg ω₀) (accepted_fresh_E hd hr hg hwspec ω₀ hy) hδ₂ hpow hcorr hone

/-- The examined macro-vertex is occupied in the accepted transcript, so every stub substep taken
from it is reveal-only: `levelTr_openV`, `levelTr_closedV` and `levelTr_pending` apply, and the
pending directions of the examined vertex are the same at every level. -/
theorem pendZ_mem_accepted_openV (d r t n : ℕ) [NeZero d] (h : MacroExp.Tr d)
    (ω : SiteConfig (Site d)) :
    MacroExp.pendZ d n h ∈ (MacroExp.accepted d r t n h ω).openV := by
  rw [MacroExp.accepted, FRDom.Transcript.step_openV, if_pos rfl]
  exact Finset.mem_insert_self _ _

theorem pending_levelTr_accepted (d r t s n : ℕ) [NeZero d] (h : MacroExp.Tr d) (i : Fin d)
    (σ : ℤ) (j : ℕ) (ω₀ ω : SiteConfig (Site d)) (v : Site 2) :
    MacroExp.pending d
        (levelTr d r t s (MacroExp.accepted d r t n h ω₀) (MacroExp.pendZ d n h) i σ j ω) v
      = MacroExp.pending d (MacroExp.accepted d r t n h ω₀) v :=
  levelTr_pending i σ j ω (pendZ_mem_accepted_openV d r t n h ω₀) v

end Accepted


#print axioms KNAll.Site.Stopped.stub_crossing
#print axioms KNAll.Site.Stopped.connWithinSet_stubFace_of_conn
#print axioms KNAll.Site.Stopped.stubFace_nonempty
#print axioms KNAll.Site.Stopped.stubTarget_nonempty
#print axioms KNAll.Site.Stopped.stubTarget_subset_M
#print axioms KNAll.Site.Stopped.origin_notMem_stub
#print axioms KNAll.Site.Stopped.sep_of_fresh
#print axioms KNAll.Site.Stopped.stub_subset_Q_union_E
#print axioms KNAll.Site.Stopped.real_inter_le_of_pinnedProb_le
#print axioms KNAll.Site.Stopped.prob_inter_le_of_step_prob_le
#print axioms KNAll.Site.Stopped.levelTr_pending
#print axioms KNAll.Site.Stopped.pending_levelTr_accepted
#print axioms KNAll.Site.Stopped.lt_prob_reservationEvent_stopLevel
#print axioms KNAll.Site.Stopped.prob_noGoodLevel_le
#print axioms KNAll.Site.Stopped.prob_directionEvent_compl_le
#print axioms KNAll.Site.Stopped.prob_directionEvent_compl_le_accepted
#print axioms KNAll.Site.Stopped.prob_joint_compl_le


end KNAll.Site.Stopped

end
