import Hypergraph.RenormPlan
import Hypergraph.TargetExtension

/-!
# Finite exact target plans

This is the data layer of the exact target construction.  It formalizes the finite geometry,
leaf pointers, supports, and thresholds in (T1)--(T6).  `WellFormed` is deterministic and
parameter-free apart from the stored extraction parameter; `ValidAt` is only a finite table of
cylinder inequalities.  No target-soundness implication is a field of the plan.
-/

noncomputable section

namespace KNAll.Site.ExactTargetPlan

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat}

/-! ## Finite integer boxes -/

/-- A closed axis-parallel integer box, represented by its two corners. -/
structure IntBox (d : Nat) where
  lower : Site d
  upper : Site d

/-- The finite set of integer sites in a box. -/
def IntBox.sites (B : IntBox d) : Finset (Site d) :=
  Fintype.piFinset fun j => Finset.Icc (B.lower j) (B.upper j)

/-- Coordinatewise consistency of the two stored corners. -/
def IntBox.Ordered (B : IntBox d) : Prop := ∀ j, B.lower j ≤ B.upper j

theorem IntBox.mem_sites {B : IntBox d} {x : Site d} :
    x ∈ B.sites ↔ ∀ j, B.lower j ≤ x j ∧ x j ≤ B.upper j := by
  simp only [sites, Fintype.mem_piFinset, Finset.mem_Icc]

theorem IntBox.lower_mem_sites {B : IntBox d} (hB : B.Ordered) : B.lower ∈ B.sites := by
  rw [IntBox.mem_sites]
  exact fun j => ⟨le_rfl, hB j⟩

theorem IntBox.sites_nonempty {B : IntBox d} (hB : B.Ordered) : B.sites.Nonempty :=
  ⟨B.lower, B.lower_mem_sites hB⟩

/-- Coordinate-radius enlargement of an integer box. -/
def IntBox.inflate (B : IntBox d) (R : Nat) : IntBox d where
  lower j := B.lower j - R
  upper j := B.upper j + R

theorem IntBox.inflate_ordered {B : IntBox d} (hB : B.Ordered) (R : Nat) :
    (B.inflate R).Ordered := by
  intro j
  dsimp [IntBox.inflate]
  have := hB j
  omega

theorem IntBox.sites_subset_inflate {B : IntBox d} (R : Nat) :
    B.sites ⊆ (B.inflate R).sites := by
  intro x hx
  rw [IntBox.mem_sites] at hx ⊢
  intro j
  dsimp [IntBox.inflate]
  have hj := hx j
  omega

/-! ## Exact finite events used by leaves -/

/-- One fully instantiated finite hit geometry.  The plan stores only finitely many of these;
there is no run-time existential choice of scale or translate. -/
structure Geometry (d : Nat) where
  centre : Site d
  scale : Nat
  region : Finset (Site d)
  face : Finset (Site d)

/-- Some point of `source` is joined to `target` inside `region`. -/
def hitEvent (region source target : Finset (Site d)) : Set (SiteConfig (Site d)) :=
  ⋃ x ∈ source,
    connWithinSet (zdGraph d) (↑region : Set (Site d)) x
      (↑target : Set (Site d))

/-- At least one named seed block is entirely open. -/
def seedEvent {k : Nat} (block : Fin k → Finset (Site d)) :
    Set (SiteConfig (Site d)) :=
  {omega | ∃ i, (↑(block i) : Set (Site d)) ⊆ omega}

/-- Every coordinate of a named barrier support is closed. -/
def barrierEvent (support : Finset (Site d)) : Set (SiteConfig (Site d)) :=
  {omega | ∀ x ∈ support, x ∉ omega}

def seedSupport {k : Nat} (block : Fin k → Finset (Site d)) : Finset (Site d) :=
  Finset.univ.biUnion block

/-! ## Plan data -/

/-- Finite data of (T1)--(T6).  All uses point into the one finite leaf table. -/
structure Plan (d : Nat) where
  /-- Common extraction parameter `p₀`. -/
  p0 : unitInterval
  /-- Source box `B` and active box `D`. -/
  sourceBox : IntBox d
  activeBox : IntBox d
  /-- Nonempty finite target. -/
  target : Finset (Site d)
  radius : Nat
  /-- Finite geometry table. -/
  numGeometries : Nat
  geometry : Fin numGeometries → Geometry d
  /-- Error and arithmetic fields. -/
  epsilon : Real
  m : Nat
  k : Nat
  N : Nat
  L : Nat
  /-- One finite table contains the hit, seed, and barrier leaves. -/
  numLeaves : Nat
  leaf : Fin numLeaves → ProbabilityBound d
  /-- The preselected T4 use at every possible translated contact. -/
  hitGeometry : (sourceBox.inflate radius).sites → Fin numGeometries
  hitLeaf : (sourceBox.inflate radius).sites → Fin numLeaves
  /-- The T5 canonical partition and its leaf. -/
  seedBlock : Fin k → Finset (Site d)
  seedLeaf : Fin numLeaves
  /-- The T6 canonical barrier and its leaf. -/
  barrierSupport : Finset (Site d)
  barrierLeaf : Fin numLeaves
  barrierLower : Real

namespace Plan

def source (C : Plan d) : Finset (Site d) := C.sourceBox.sites
def active (C : Plan d) : Finset (Site d) := C.activeBox.sites
def sourcePlus (C : Plan d) : Finset (Site d) := (C.sourceBox.inflate C.radius).sites

def deltaC (C : Plan d) : Real := C.epsilon / 4
def delta (C : Plan d) : Real := C.epsilon ^ 2 / 64
def eta (C : Plan d) : Real := C.delta ^ 2 * C.deltaC
def seedCard (C : Plan d) : Nat := (2 * C.m + 2) * (4 * C.m + 1) ^ (d - 1)

def selectedRegion (C : Plan d) (v : C.sourcePlus) : Finset (Site d) :=
  (C.geometry (C.hitGeometry v)).region

def selectedFace (C : Plan d) (v : C.sourcePlus) : Finset (Site d) :=
  (C.geometry (C.hitGeometry v)).face

/-! ### T1--T6 as deterministic propositions -/

def T1 (C : Plan d) : Prop :=
  0 < (C.p0 : Real) ∧ (C.p0 : Real) < 1 ∧
  C.sourceBox.Ordered ∧ C.activeBox.Ordered ∧ C.target.Nonempty ∧
  C.sourcePlus ⊆ C.active ∧ C.target ⊆ C.active ∧
  1 ≤ C.radius ∧ 0 < C.numGeometries ∧ 0 < C.numLeaves

def T2 (C : Plan d) : Prop :=
  0 < C.epsilon ∧ C.epsilon ≤ 1 ∧
  0 < C.m ∧ 0 < C.k ∧ 0 < C.N ∧ 0 < C.L

def T3 (C : Plan d) : Prop :=
  2 * C.m + C.L + 2 ≤ C.radius ∧
  C.k * (siteBox d (8 * C.m)).card ≤ C.N ∧
  (C.k : Real) * (C.p0 : Real) ^ C.seedCard ≤ C.delta⁻¹

def T4 (C : Plan d) : Prop := ∀ v : C.sourcePlus,
  (C.geometry (C.hitGeometry v)).centre = v.1 ∧
  C.radius ≤ (C.geometry (C.hitGeometry v)).scale ∧
  C.selectedRegion v ⊆ C.active ∧
  C.selectedFace v ⊆ C.target ∧
  siteBoxAt v.1 C.m ⊆ C.selectedRegion v ∧
  (C.leaf (C.hitLeaf v)).experiment.support = C.selectedRegion v ∧
  (C.leaf (C.hitLeaf v)).experiment.event =
    hitEvent (C.selectedRegion v) (siteBoxAt v.1 C.m) (C.selectedFace v) ∧
  (C.leaf (C.hitLeaf v)).lower = 1 - C.eta

def T5 (C : Plan d) : Prop :=
  (∀ i, (C.seedBlock i).card = C.seedCard) ∧
  (∀ i j, i ≠ j → Disjoint (C.seedBlock i) (C.seedBlock j)) ∧
  (C.leaf C.seedLeaf).experiment.support = seedSupport C.seedBlock ∧
  (C.leaf C.seedLeaf).experiment.event = seedEvent C.seedBlock ∧
  (C.leaf C.seedLeaf).lower = 1 - C.delta

def T6 (C : Plan d) : Prop :=
  C.barrierSupport.card = 2 * d * C.N ∧
  (C.leaf C.barrierLeaf).experiment.support = C.barrierSupport ∧
  (C.leaf C.barrierLeaf).experiment.event = barrierEvent C.barrierSupport ∧
  (C.leaf C.barrierLeaf).lower = C.barrierLower ∧
  0 < C.barrierLower ∧ C.barrierLower < 1 ∧
  1 < (C.L : Real) * C.delta * C.barrierLower

/-- Parameter-free geometry, indexing, support, threshold, and arithmetic checks. -/
def WellFormed (C : Plan d) : Prop :=
  C.T1 ∧ C.T2 ∧ C.T3 ∧ C.T4 ∧ C.T5 ∧ C.T6

/-- Finite validity: the current parameter is below the common extraction parameter and every
stored cylinder leaf beats its stored threshold. -/
def ValidAt (C : Plan d) (q : unitInterval) : Prop :=
  0 < (q : Real) ∧ (q : Real) ≤ (C.p0 : Real) ∧
  ∀ i, (C.leaf i).HoldsAt q

theorem validAt_iff (C : Plan d) (q : unitInterval) :
    C.ValidAt q ↔
      0 < (q : Real) ∧ (q : Real) ≤ (C.p0 : Real) ∧
      ∀ i, (C.leaf i).lower < (C.leaf i).experiment.prob q := Iff.rfl

/-! ### Nonvacuity of every finite index family -/

theorem WellFormed.source_nonempty {C : Plan d} (hC : C.WellFormed) :
    C.source.Nonempty := by
  rcases hC.1 with ⟨_, _, hsource, _, _, _, _, _, _, _⟩
  exact C.sourceBox.sites_nonempty hsource

theorem WellFormed.sourcePlus_nonempty {C : Plan d} (hC : C.WellFormed) :
    C.sourcePlus.Nonempty := by
  rcases hC.1 with ⟨_, _, hsource, _, _, _, _, _, _, _⟩
  exact IntBox.sites_nonempty (C.sourceBox.inflate_ordered hsource C.radius)

theorem WellFormed.active_nonempty {C : Plan d} (hC : C.WellFormed) :
    C.active.Nonempty := by
  rcases hC.1 with ⟨_, _, _, _, _, hsubset, _, _, _, _⟩
  obtain ⟨x, hx⟩ := hC.sourcePlus_nonempty
  exact ⟨x, hsubset hx⟩

theorem WellFormed.target_nonempty {C : Plan d} (hC : C.WellFormed) :
    C.target.Nonempty := by
  rcases hC.1 with ⟨_, _, _, _, htarget, _, _, _, _, _⟩
  exact htarget

theorem WellFormed.geometryIndex_nonempty {C : Plan d} (hC : C.WellFormed) :
    Nonempty (Fin C.numGeometries) := by
  rcases hC.1 with ⟨_, _, _, _, _, _, _, _, hgeom, _⟩
  exact ⟨⟨0, hgeom⟩⟩

theorem WellFormed.leafIndex_nonempty {C : Plan d} (_hC : C.WellFormed) :
    Nonempty (Fin C.numLeaves) :=
  ⟨C.seedLeaf⟩

theorem WellFormed.seedBlockIndex_nonempty {C : Plan d} (hC : C.WellFormed) :
    Nonempty (Fin C.k) := by
  rcases hC.2.1 with ⟨_, _, _, hk, _, _⟩
  exact ⟨⟨0, hk⟩⟩

theorem WellFormed.seedCard_pos {C : Plan d} (hC : C.WellFormed) :
    0 < C.seedCard := by
  rcases hC.2.1 with ⟨_, _, hm, _, _, _⟩
  unfold Plan.seedCard
  positivity

theorem WellFormed.seedBlock_nonempty {C : Plan d} (hC : C.WellFormed)
    (i : Fin C.k) : (C.seedBlock i).Nonempty := by
  apply Finset.card_pos.mp
  rw [hC.2.2.2.2.1.1 i]
  exact hC.seedCard_pos

/-- T5 really uses `k * s` distinct canonical coordinates. -/
theorem WellFormed.seedSupport_card {C : Plan d} (hC : C.WellFormed) :
    (seedSupport C.seedBlock).card = C.k * C.seedCard := by
  have h5 := hC.2.2.2.2.1
  unfold seedSupport
  rw [Finset.card_biUnion]
  · simp_rw [h5.1]
    simp
  · intro i _ j _ hij
    exact h5.2.1 i j hij

theorem WellFormed.barrierSupport_nonempty [NeZero d]
    {C : Plan d} (hC : C.WellFormed) : C.barrierSupport.Nonempty := by
  apply Finset.card_pos.mp
  rw [hC.2.2.2.2.2.1]
  rcases hC.2.1 with ⟨_, _, _, _, hN, _⟩
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hN

/-- Every point in the nonempty T4 domain has concrete geometry, scale, and leaf indices, with
all of their T4 specifications. -/
theorem WellFormed.hitUse {C : Plan d} (hC : C.WellFormed) (v : C.sourcePlus) :
    ∃ (g : Fin C.numGeometries) (i : Fin C.numLeaves),
      g = C.hitGeometry v ∧ i = C.hitLeaf v ∧
      (C.geometry g).centre = v.1 ∧ C.radius ≤ (C.geometry g).scale ∧
      (C.geometry g).region ⊆ C.active ∧
      (C.geometry g).face ⊆ C.target ∧
      siteBoxAt v.1 C.m ⊆ (C.geometry g).region ∧
      (C.leaf i).experiment.support = (C.geometry g).region ∧
      (C.leaf i).experiment.event =
        hitEvent (C.geometry g).region (siteBoxAt v.1 C.m) (C.geometry g).face ∧
      (C.leaf i).lower = 1 - C.eta := by
  refine ⟨C.hitGeometry v, C.hitLeaf v, rfl, rfl, ?_⟩
  exact hC.2.2.2.1 v

theorem WellFormed.exists_hitUse {C : Plan d} (hC : C.WellFormed) :
    ∃ (v : C.sourcePlus) (g : Fin C.numGeometries) (i : Fin C.numLeaves),
      g = C.hitGeometry v ∧ i = C.hitLeaf v := by
  obtain ⟨v, hv⟩ := hC.sourcePlus_nonempty
  let v' : C.sourcePlus := ⟨v, hv⟩
  exact ⟨v', C.hitGeometry v', C.hitLeaf v', rfl, rfl⟩

theorem WellFormed.seedLeaf_spec {C : Plan d} (hC : C.WellFormed) :
    (C.leaf C.seedLeaf).experiment.support = seedSupport C.seedBlock ∧
    (C.leaf C.seedLeaf).experiment.event = seedEvent C.seedBlock ∧
    (C.leaf C.seedLeaf).lower = 1 - C.delta := hC.2.2.2.2.1.2.2

theorem WellFormed.barrierLeaf_spec {C : Plan d} (hC : C.WellFormed) :
    (C.leaf C.barrierLeaf).experiment.support = C.barrierSupport ∧
    (C.leaf C.barrierLeaf).experiment.event = barrierEvent C.barrierSupport ∧
    (C.leaf C.barrierLeaf).lower = C.barrierLower := by
  have h6 := hC.2.2.2.2.2
  exact ⟨h6.2.1, h6.2.2.1, h6.2.2.2.1⟩

theorem ValidAt.hitLeaf_holds {C : Plan d} {q : unitInterval} (hvalid : C.ValidAt q)
    (v : C.sourcePlus) : (C.leaf (C.hitLeaf v)).HoldsAt q := hvalid.2.2 _

theorem ValidAt.seedLeaf_holds {C : Plan d} {q : unitInterval} (hvalid : C.ValidAt q) :
    (C.leaf C.seedLeaf).HoldsAt q := hvalid.2.2 _

theorem ValidAt.barrierLeaf_holds {C : Plan d} {q : unitInterval} (hvalid : C.ValidAt q) :
    (C.leaf C.barrierLeaf).HoldsAt q := hvalid.2.2 _

end Plan

/-! ## Exterior support bookkeeping -/

/-- Coordinates of the finite realization outside its active box. -/
def exterior (P D : Finset (Site d)) : Finset (Site d) := P \ D

/-- A transcript/query support is wholly exterior to the active box. -/
def ExteriorSupported (P D S : Finset (Site d)) : Prop := S ⊆ exterior P D

theorem exterior_eq_sdiff (P D : Finset (Site d)) : exterior P D = P \ D := rfl

/-- The overlap-compatible identity: replacing `P` by its exterior part does not change the
union with the active box, even when `P` and `D` overlap. -/
theorem union_active_eq_exterior_union (P D : Finset (Site d)) :
    P ∪ D = exterior P D ∪ D := by
  rw [exterior, Finset.sdiff_union_self_eq_union]

theorem exterior_union_active_eq_of_subset {P D : Finset (Site d)} (hDP : D ⊆ P) :
    exterior P D ∪ D = P := by
  exact Finset.sdiff_union_of_subset hDP

theorem ExteriorSupported.subset_ambient {P D S : Finset (Site d)}
    (hS : ExteriorSupported P D S) : S ⊆ P :=
  hS.trans Finset.sdiff_subset

theorem ExteriorSupported.disjoint_active {P D S : Finset (Site d)}
    (hS : ExteriorSupported P D S) : Disjoint S D :=
  (Finset.sdiff_disjoint : Disjoint (P \ D) D).mono_left hS

/-- Existing target-extension contacts are automatically exterior-supported. -/
theorem outerBoundary_mem_exterior {P D : Finset (Site d)}
    {x : Site d} (hx : x ∈ TargetExt.outerBoundary (zdGraph d) P D) :
    x ∈ exterior P D :=
  TargetExt.outerBoundary_subset (zdGraph d) P D hx

#print axioms KNAll.Site.ExactTargetPlan.IntBox.sites_nonempty
#print axioms KNAll.Site.ExactTargetPlan.Plan.WellFormed.hitUse
#print axioms KNAll.Site.ExactTargetPlan.union_active_eq_exterior_union
#print axioms KNAll.Site.ExactTargetPlan.ExteriorSupported.disjoint_active

end KNAll.Site.ExactTargetPlan

end
