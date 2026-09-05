import Hypergraph.FreshLeafTransport
import Hypergraph.ReinforcedHitBridge

/-!
# Construction of exact target plans from finite hit data

This module is the finite assembly counterpart of `ExactTargetPlan.Plan.soundProduct`.  Its input
contains no exploration or conditional probability: it is one admissible numerical parameter
record, one concrete finite target, and one explicitly indexed family of homogeneous hit events.
The constructor builds the finite geometry table, all hit leaves, and canonical seed and barrier
leaves.
-/

noncomputable section

namespace KNAll.Site.ExactTargetPlan

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

/-! ## Numerical and concrete inputs -/

/-- The numerical data shared by every concrete target instantiated from one target scheme. -/
structure ConstructorParams (d : Nat) where
  p0 : unitInterval
  epsilon : Real
  m : Nat
  k : Nat
  N : Nat
  L : Nat
  radius : Nat
  barrierLower : Real

namespace ConstructorParams

def deltaC (P : ConstructorParams d) : Real := P.epsilon / 4
def delta (P : ConstructorParams d) : Real := P.epsilon ^ 2 / 64
def eta (P : ConstructorParams d) : Real := P.delta ^ 2 * P.deltaC
def seedCard (P : ConstructorParams d) : Nat :=
  (2 * P.m + 2) * (4 * P.m + 1) ^ (d - 1)

/-- Exactly the scalar clauses needed for T1--T3 and for validity of the canonical T5/T6 leaves. -/
structure Admissible (P : ConstructorParams d) : Prop where
  p0_pos : 0 < (P.p0 : Real)
  p0_lt_one : (P.p0 : Real) < 1
  epsilon_pos : 0 < P.epsilon
  epsilon_le_one : P.epsilon ≤ 1
  m_pos : 0 < P.m
  k_pos : 0 < P.k
  N_pos : 0 < P.N
  L_pos : 0 < P.L
  radius_large : 2 * P.m + P.L + 2 ≤ P.radius
  packing : P.k * (siteBox d (8 * P.m)).card ≤ P.N
  selected_budget :
    (P.k : Real) * (P.p0 : Real) ^ P.seedCard ≤ P.delta⁻¹
  seed_valid :
    (1 - (P.p0 : Real) ^ P.seedCard) ^ P.k < P.delta
  barrier_pos : 0 < P.barrierLower
  barrier_lt_one : P.barrierLower < 1
  barrier_valid :
    P.barrierLower < (1 - (P.p0 : Real)) ^ (2 * d * P.N)
  barrier_budget : 1 < (P.L : Real) * P.delta * P.barrierLower

end ConstructorParams

/-- Concrete finite boxes and target to which the common numerical data are applied. -/
structure ConcreteTarget (P : ConstructorParams d) where
  sourceBox : IntBox d
  activeBox : IntBox d
  target : Finset (Site d)
  source_ordered : sourceBox.Ordered
  active_ordered : activeBox.Ordered
  target_nonempty : target.Nonempty
  sourcePlus_subset_active : (sourceBox.inflate P.radius).sites ⊆ activeBox.sites
  target_subset_active : target ⊆ activeBox.sites

/-- The already descended, fully finite T4 data for every possible relay centre. -/
structure ConcreteHits (P : ConstructorParams d) (X : ConcreteTarget P) where
  scale : (X.sourceBox.inflate P.radius).sites → Nat
  region : (X.sourceBox.inflate P.radius).sites → Finset (Site d)
  face : (X.sourceBox.inflate P.radius).sites → Finset (Site d)
  scale_ge : ∀ v, P.radius ≤ scale v
  region_subset_active : ∀ v, region v ⊆ X.activeBox.sites
  face_subset_target : ∀ v, face v ⊆ X.target
  source_subset_region : ∀ v, siteBoxAt v.1 P.m ⊆ region v
  hit_valid : ∀ v,
    1 - P.eta <
      (siteBernoulli (fun _ : Site d => P.p0)).real
        (hitEvent (region v) (siteBoxAt v.1 P.m) (face v))

/-! ## Canonical finite coordinates -/

private def firstAxis : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩

/-- An explicit infinite ray of pairwise distinct lattice sites. -/
def canonicalSite (n : Nat) : Site d :=
  fun a => if a = firstAxis (d := d) then (n : Int) else 0

theorem canonicalSite_injective : Function.Injective (canonicalSite (d := d)) := by
  intro n n' h
  have h0 := congrFun h (firstAxis (d := d))
  simpa [canonicalSite, firstAxis] using h0

/-- The `i`th consecutive block of `s` canonical coordinates. -/
def canonicalSeedBlock (s : Nat) {k : Nat} (i : Fin k) : Finset (Site d) :=
  (Finset.univ : Finset (Fin s)).image fun j => canonicalSite (d := d) (i.1 * s + j.1)

theorem card_canonicalSeedBlock (s : Nat) {k : Nat} (i : Fin k) :
    (canonicalSeedBlock (d := d) s i).card = s := by
  rw [canonicalSeedBlock, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Fin.ext
    have hab' := canonicalSite_injective (d := d) hab
    omega

theorem disjoint_canonicalSeedBlock (s : Nat) {k : Nat} (i j : Fin k) (hij : i ≠ j) :
    Disjoint (canonicalSeedBlock (d := d) s i) (canonicalSeedBlock (d := d) s j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [canonicalSeedBlock, Finset.mem_image] at hxi hxj
  obtain ⟨a, _, rfl⟩ := hxi
  obtain ⟨b, _, hab⟩ := hxj
  have hab' : i.1 * s + a.1 = j.1 * s + b.1 :=
    canonicalSite_injective (d := d) hab.symm
  have hij' : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hij' with hijlt | hjilt
  · have hmul : (i.1 + 1) * s ≤ j.1 * s :=
      Nat.mul_le_mul_right s (Nat.succ_le_iff.2 hijlt)
    have hlt : i.1 * s + a.1 < j.1 * s + b.1 := by
      calc
        i.1 * s + a.1 < i.1 * s + s := Nat.add_lt_add_left a.2 _
        _ = (i.1 + 1) * s := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ j.1 * s := hmul
        _ ≤ j.1 * s + b.1 := Nat.le_add_right _ _
    exact (Nat.ne_of_lt hlt) hab'
  · have hmul : (j.1 + 1) * s ≤ i.1 * s :=
      Nat.mul_le_mul_right s (Nat.succ_le_iff.2 hjilt)
    have hlt : j.1 * s + b.1 < i.1 * s + a.1 := by
      calc
        j.1 * s + b.1 < j.1 * s + s := Nat.add_lt_add_left b.2 _
        _ = (j.1 + 1) * s := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ i.1 * s := hmul
        _ ≤ i.1 * s + a.1 := Nat.le_add_right _ _
    exact (Nat.ne_of_lt hlt) hab'.symm

/-- A canonical support of any prescribed finite cardinality. -/
def canonicalSupport (n : Nat) : Finset (Site d) :=
  (Finset.univ : Finset (Fin n)).image fun i => canonicalSite (d := d) i.1

theorem card_canonicalSupport (n : Nat) : (canonicalSupport (d := d) n).card = n := by
  rw [canonicalSupport, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact Fin.ext (canonicalSite_injective (d := d) hab)

/-! ## Experiments and indexed tables -/

private abbrev HitSite (P : ConstructorParams d) (X : ConcreteTarget P) :=
  (X.sourceBox.inflate P.radius).sites

private def hitEquiv (P : ConstructorParams d) (X : ConcreteTarget P) :
    HitSite P X ≃ Fin (Fintype.card (HitSite P X)) :=
  Fintype.equivFin (HitSite P X)

def hitExperiment (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (v : HitSite P X) : CylinderExperiment d where
  support := H.region v
  event := hitEvent (H.region v) (siteBoxAt v.1 P.m) (H.face v)
  determined := by
    unfold hitEvent
    exact DeterminedBy.iUnion fun x => DeterminedBy.iUnion fun _ =>
      determinedBy_connWithinSet (zdGraph d) (↑(H.region v) : Set (Site d)) x
        (↑(H.face v) : Set (Site d))
  measurable' := ReinforcedHit.measurableSet_hitEvent _ _ _

def hitBound (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (v : HitSite P X) : ProbabilityBound d where
  experiment := hitExperiment P X H v
  lower := 1 - P.eta

private abbrev seedBlocks (P : ConstructorParams d) : Fin P.k → Finset (Site d) :=
  canonicalSeedBlock (d := d) P.seedCard

def seedExperiment (P : ConstructorParams d) : CylinderExperiment d where
  support := seedSupport (seedBlocks P)
  event := seedEvent (seedBlocks P)
  determined := FreshLeafTransport.determinedBy_seedEvent (seedBlocks P)
  measurable' := FreshLeafTransport.measurableSet_seedEvent (seedBlocks P)

def seedBound (P : ConstructorParams d) : ProbabilityBound d where
  experiment := seedExperiment P
  lower := 1 - P.delta

private abbrev barrierCard (P : ConstructorParams d) : Nat := 2 * d * P.N

def barrierExperiment (P : ConstructorParams d) : CylinderExperiment d where
  support := canonicalSupport (d := d) (barrierCard P)
  event := barrierEvent (canonicalSupport (d := d) (barrierCard P))
  determined := FreshLeafTransport.determinedBy_barrierEvent _
  measurable' := FreshLeafTransport.measurableSet_barrierEvent _

def barrierBound (P : ConstructorParams d) : ProbabilityBound d where
  experiment := barrierExperiment P
  lower := P.barrierLower

private def geometryTable (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (i : Fin (Fintype.card (HitSite P X))) : Geometry d :=
  let v := (hitEquiv P X).symm i
  { centre := v.1
    scale := H.scale v
    region := H.region v
    face := H.face v }

private def hitTable (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (i : Fin (Fintype.card (HitSite P X))) : ProbabilityBound d :=
  hitBound P X H ((hitEquiv P X).symm i)

private def lastTwo (P : ConstructorParams d) (i : Fin 2) : ProbabilityBound d :=
  if i = 0 then seedBound P else barrierBound P

private def leafTable (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) :
    Fin (Fintype.card (HitSite P X) + 2) → ProbabilityBound d :=
  Fin.append (hitTable P X H) (lastTwo P)

@[simp] private theorem geometryTable_hit (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (v : HitSite P X) :
    geometryTable P X H (hitEquiv P X v) =
      { centre := v.1, scale := H.scale v, region := H.region v, face := H.face v } := by
  simp [geometryTable]

@[simp] private theorem leafTable_hit (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (v : HitSite P X) :
    leafTable P X H (Fin.castAdd 2 (hitEquiv P X v)) = hitBound P X H v := by
  simp [leafTable, hitTable]

@[simp] private theorem leafTable_seed (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) :
    leafTable P X H (Fin.natAdd (Fintype.card (HitSite P X)) (0 : Fin 2)) =
      seedBound P := by
  simp [leafTable, lastTwo]

@[simp] private theorem leafTable_barrier (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) :
    leafTable P X H (Fin.natAdd (Fintype.card (HitSite P X)) (1 : Fin 2)) =
      barrierBound P := by
  simp [leafTable, lastTwo]

/-! ## The actual plan and its realization equations -/

/-- Assemble the exact finite plan.  The first block of leaf indices contains the T4 leaves and
the final two indices are respectively the canonical T5 and T6 leaves. -/
def buildPlan (P : ConstructorParams d) (X : ConcreteTarget P) (H : ConcreteHits P X) : Plan d where
  p0 := P.p0
  sourceBox := X.sourceBox
  activeBox := X.activeBox
  target := X.target
  radius := P.radius
  numGeometries := Fintype.card (HitSite P X)
  geometry := geometryTable P X H
  epsilon := P.epsilon
  m := P.m
  k := P.k
  N := P.N
  L := P.L
  numLeaves := Fintype.card (HitSite P X) + 2
  leaf := leafTable P X H
  hitGeometry := fun v => hitEquiv P X v
  hitLeaf := fun v => Fin.castAdd 2 (hitEquiv P X v)
  seedBlock := seedBlocks P
  seedLeaf := Fin.natAdd (Fintype.card (HitSite P X)) (0 : Fin 2)
  barrierSupport := canonicalSupport (d := d) (barrierCard P)
  barrierLeaf := Fin.natAdd (Fintype.card (HitSite P X)) (1 : Fin 2)
  barrierLower := P.barrierLower

@[simp] theorem buildPlan_sourceBox (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) : (buildPlan P X H).sourceBox = X.sourceBox := rfl

@[simp] theorem buildPlan_activeBox (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) : (buildPlan P X H).activeBox = X.activeBox := rfl

@[simp] theorem buildPlan_target (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) : (buildPlan P X H).target = X.target := rfl

@[simp] theorem buildPlan_selectedRegion (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (v : HitSite P X) :
    (buildPlan P X H).selectedRegion v = H.region v := by
  simp [Plan.selectedRegion, buildPlan, geometryTable, hitEquiv]

@[simp] theorem buildPlan_selectedFace (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (v : HitSite P X) :
    (buildPlan P X H).selectedFace v = H.face v := by
  simp [Plan.selectedFace, buildPlan, geometryTable, hitEquiv]

@[simp] theorem buildPlan_selectedScale (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (v : (X.sourceBox.inflate P.radius).sites) :
    ((buildPlan P X H).geometry ((buildPlan P X H).hitGeometry v)).scale = H.scale v := by
  simp [buildPlan, geometryTable, hitEquiv]

/-- The hit pointer realizes exactly the probability bound supplied for its concrete centre. -/
@[simp] theorem buildPlan_hitLeaf (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) (v : (X.sourceBox.inflate P.radius).sites) :
    (buildPlan P X H).leaf ((buildPlan P X H).hitLeaf v) = hitBound P X H v := by
  simp [buildPlan]

/-- The distinguished seed pointer realizes the canonical seed bound. -/
@[simp] theorem buildPlan_seedLeaf (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) :
    (buildPlan P X H).leaf (buildPlan P X H).seedLeaf = seedBound P := by
  simp [buildPlan]

/-- The distinguished barrier pointer realizes the canonical all-closed bound. -/
@[simp] theorem buildPlan_barrierLeaf (P : ConstructorParams d) (X : ConcreteTarget P)
    (H : ConcreteHits P X) :
    (buildPlan P X H).leaf (buildPlan P X H).barrierLeaf = barrierBound P := by
  simp [buildPlan]

/-! ## Correctness -/

theorem buildPlan_wellFormed (P : ConstructorParams d) (hP : P.Admissible)
    (X : ConcreteTarget P) (H : ConcreteHits P X) : (buildPlan P X H).WellFormed := by
  have hhitNonempty : Nonempty (HitSite P X) := by
    obtain ⟨v, hv⟩ := IntBox.sites_nonempty
      (IntBox.inflate_ordered X.source_ordered P.radius)
    exact ⟨⟨v, hv⟩⟩
  have hgeomPos : 0 < Fintype.card (HitSite P X) :=
    Fintype.card_pos_iff.2 hhitNonempty
  have hradius : 1 ≤ P.radius := by
    exact le_trans (by omega : 1 ≤ 2 * P.m + P.L + 2) hP.radius_large
  unfold Plan.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Plan.T1
    exact ⟨hP.p0_pos, hP.p0_lt_one, X.source_ordered, X.active_ordered,
      X.target_nonempty, X.sourcePlus_subset_active, X.target_subset_active,
      hradius, hgeomPos, by simp [buildPlan]⟩
  · unfold Plan.T2
    exact ⟨hP.epsilon_pos, hP.epsilon_le_one, hP.m_pos, hP.k_pos,
      hP.N_pos, hP.L_pos⟩
  · unfold Plan.T3
    exact ⟨hP.radius_large, hP.packing, hP.selected_budget⟩
  · unfold Plan.T4
    intro v
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [buildPlan, geometryTable, hitEquiv]
    · simpa [buildPlan, geometryTable, hitEquiv] using H.scale_ge v
    · simpa [buildPlan, Plan.selectedRegion, Plan.active, geometryTable, hitEquiv]
        using H.region_subset_active v
    · simpa [buildPlan, Plan.selectedFace, geometryTable, hitEquiv]
        using H.face_subset_target v
    · simpa [buildPlan, Plan.selectedRegion, geometryTable, hitEquiv]
        using H.source_subset_region v
    · simp [buildPlan, Plan.selectedRegion, geometryTable, hitEquiv, leafTable,
        hitTable, hitBound, hitExperiment]
    · simp [buildPlan, Plan.selectedRegion, Plan.selectedFace, geometryTable, hitEquiv,
        leafTable, hitTable, hitBound, hitExperiment]
    · simp [buildPlan, leafTable, hitTable, hitBound, Plan.eta,
        ConstructorParams.eta, Plan.delta, Plan.deltaC, ConstructorParams.delta,
        ConstructorParams.deltaC]
  · unfold Plan.T5
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa [buildPlan, seedBlocks, Plan.seedCard, ConstructorParams.seedCard] using
        card_canonicalSeedBlock (d := d) P.seedCard i
    · intro i j hij
      exact disjoint_canonicalSeedBlock (d := d) P.seedCard i j hij
    · simp [buildPlan, leafTable, lastTwo, seedBound, seedExperiment]
    · simp [buildPlan, leafTable, lastTwo, seedBound, seedExperiment]
    · simp [buildPlan, leafTable, lastTwo, seedBound, Plan.delta,
        ConstructorParams.delta]
  · unfold Plan.T6
    refine ⟨?_, ?_, ?_, ?_, hP.barrier_pos, hP.barrier_lt_one, ?_⟩
    · simpa [buildPlan, barrierCard] using
        card_canonicalSupport (d := d) (barrierCard P)
    · simp [buildPlan, leafTable, lastTwo, barrierBound, barrierExperiment]
    · simp [buildPlan, leafTable, lastTwo, barrierBound, barrierExperiment]
    · simp [buildPlan, leafTable, lastTwo, barrierBound]
    · simpa [buildPlan, Plan.delta, ConstructorParams.delta] using hP.barrier_budget

theorem buildPlan_validAt (P : ConstructorParams d) (hP : P.Admissible)
    (X : ConcreteTarget P) (H : ConcreteHits P X) : (buildPlan P X H).ValidAt P.p0 := by
  have hseed : (seedBound P).HoldsAt P.p0 := by
    unfold ProbabilityBound.HoldsAt
    change 1 - P.delta <
      (siteBernoulli (fun _ : Site d => P.p0)).real (seedEvent (seedBlocks P))
    rw [FreshLeafTransport.real_seedEvent_eq P.p0 (seedBlocks P) P.seedCard
      (fun i j hij => disjoint_canonicalSeedBlock (d := d) P.seedCard i j hij)
      (fun i => card_canonicalSeedBlock (d := d) P.seedCard i)]
    linarith [hP.seed_valid]
  have hbarrier : (barrierBound P).HoldsAt P.p0 := by
    unfold ProbabilityBound.HoldsAt
    change P.barrierLower <
      (siteBernoulli (fun _ : Site d => P.p0)).real
        (barrierEvent (canonicalSupport (d := d) (barrierCard P)))
    rw [FreshLeafTransport.real_barrierEvent_eq_of_card P.p0 _ (barrierCard P)
      (card_canonicalSupport (d := d) (barrierCard P))]
    exact hP.barrier_valid
  unfold Plan.ValidAt
  refine ⟨hP.p0_pos, le_rfl, ?_⟩
  intro i
  change (leafTable P X H i).HoldsAt P.p0
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · let v : HitSite P X := (hitEquiv P X).symm j
    simpa [leafTable, hitTable, hitBound, hitExperiment, ProbabilityBound.HoldsAt,
      CylinderExperiment.prob, v] using H.hit_valid v
  · fin_cases j
    · simpa [leafTable, lastTwo] using hseed
    · simpa [leafTable, lastTwo] using hbarrier

/-- The promised construction theorem.  Equality with the public transparent `buildPlan` exposes
all realization equations, while the simp lemmas above expose the selected T4 regions and faces. -/
theorem exists_plan_of_concrete_hits (P : ConstructorParams d) (hP : P.Admissible)
    (X : ConcreteTarget P) (H : ConcreteHits P X) :
    ∃ C : Plan d, C = buildPlan P X H ∧ C.WellFormed ∧ C.ValidAt P.p0 := by
  exact ⟨buildPlan P X H, rfl, buildPlan_wellFormed P hP X H,
    buildPlan_validAt P hP X H⟩

#print axioms KNAll.Site.ExactTargetPlan.exists_plan_of_concrete_hits

end KNAll.Site.ExactTargetPlan

end
