import Hypergraph.CoreFaceTargetPackaging
import Hypergraph.ExactTargetSchemeExtraction
import Hypergraph.ExactTargetChain
import Hypergraph.LongBox700

/-!
# An exact 700-node aspect-88 chain

This file instantiates the finite exact-target-plan extractor on each of the literal 700 tiles
from `LongBox700`.  The nodes use the backwards error schedule: node `t` has output error
`tol alpha (t+1)`.  Thus adjacent exact plans compose by `ExactTargetPlan.Plan.soundPinnedChain`,
and the last target is the far face of the enclosing aspect-88 box.
-/

noncomputable section

namespace KNAll.Site.ExactLongBox700

set_option maxRecDepth 4096

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.MoveWindowInput
open KNAll.Site.LongBox700
open scoped Classical

variable {d : Nat} [NeZero d]

/-! ## Integer-box adapters for the literal faces and tiles -/

/-- The hyperplane patch `B_t`, represented as an exact-plan integer box. -/
def faceBox (i : Fin d) (sigma : Int) (s rem R t : Nat) : ExactTargetPlan.IntBox d where
  lower j := if j = i then sigma * (L s rem t : Int) else -(width s rem R t : Int)
  upper j := if j = i then sigma * (L s rem t : Int) else width s rem R t

/-- The tile `D_t`, represented as an exact-plan integer box. -/
def tileBox (i : Fin d) (sigma : Int) (s rem R t : Nat) : ExactTargetPlan.IntBox d where
  lower j := if j = i then
      if sigma = 1 then (L s rem t : Int) - 2 * (s : Int)
      else -((L s rem t : Int) + (s : Int))
    else -(longScale s rem : Int)
  upper j := if j = i then
      if sigma = 1 then (L s rem t : Int) + (s : Int)
      else -((L s rem t : Int) - 2 * (s : Int))
    else longScale s rem

theorem faceBox_ordered (i : Fin d) (sigma : Int) (s rem R t : Nat) :
    (faceBox i sigma s rem R t).Ordered := by
  intro j
  by_cases hji : j = i
  · simp [faceBox, hji]
  · simp only [faceBox, hji, if_false]
    omega

theorem tileBox_ordered (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s rem R t : Nat) :
    (tileBox i sigma s rem R t).Ordered := by
  intro j
  by_cases hji : j = i
  · subst j
    rcases hsigma with rfl | rfl <;> simp [tileBox] <;> omega
  · simp only [tileBox, hji, if_false]
    omega

theorem faceBox_sites_eq (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s rem R t : Nat) :
    (faceBox i sigma s rem R t).sites = Bset i sigma s rem R t := by
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, mem_Bset hsigma]
  constructor
  · intro hx
    have hi := hx i
    simp only [faceBox, if_pos rfl] at hi
    constructor
    · rcases hsigma with rfl | rfl <;> norm_num at hi ⊢ <;> omega
    · intro j hji
      have hj := hx j
      simp only [faceBox, if_neg hji] at hj
      exact abs_le.2 hj
  · rintro ⟨hi, hoff⟩ j
    by_cases hji : j = i
    · subst j
      simp only [faceBox, if_pos rfl]
      rcases hsigma with rfl | rfl <;> norm_num at hi ⊢ <;> omega
    · simp only [faceBox, if_neg hji]
      exact abs_le.1 (hoff j hji)

theorem tileBox_sites_eq (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s rem R t : Nat) :
    (tileBox i sigma s rem R t).sites = Dset i sigma s rem R t := by
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, mem_Dset hsigma]
  constructor
  · intro hx
    have hi := hx i
    constructor
    · rcases hsigma with rfl | rfl <;> simp only [tileBox, if_pos rfl] at hi ⊢ <;>
        norm_num at hi ⊢ <;> omega
    · intro j hji
      have hj := hx j
      simp only [tileBox, hji, if_false] at hj
      exact abs_le.2 hj
  · rintro ⟨hi, hoff⟩ j
    by_cases hji : j = i
    · subst j
      rcases hsigma with rfl | rfl <;> simp only [tileBox, if_pos rfl] <;>
        norm_num at hi ⊢ <;> omega
    · simp only [tileBox, hji, if_false]
      exact abs_le.1 (hoff j hji)

/-- Every point of an inflated ordered integer box has an explicit coordinatewise-near point in
the original box. -/
theorem exists_near_of_mem_inflate (B : ExactTargetPlan.IntBox d) (hB : B.Ordered)
    (R : Nat) {x : Site d} (hx : x ∈ (B.inflate R).sites) :
    ∃ b ∈ B.sites, ∀ j, |x j - b j| ≤ (R : Int) := by
  let b : Site d := fun j => max (B.lower j) (min (B.upper j) (x j))
  have hx' := (ExactTargetPlan.IntBox.mem_sites).1 hx
  refine ⟨b, (ExactTargetPlan.IntBox.mem_sites).2 ?_, ?_⟩
  · intro j
    have hj := hB j
    dsimp [b]
    omega
  · intro j
    have hjx := hx' j
    have hjB := hB j
    dsimp [ExactTargetPlan.IntBox.inflate] at hjx
    dsimp [b]
    rw [abs_le]
    omega

theorem nextFace_subset_tile (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s rem R k n1 t : Nat}
    (hrem : rem ≤ 7) (ht : t < stepCount)
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    Bset i sigma s rem R (t + 1) ⊆ Dset i sigma s rem R t := by
  intro x hx
  rw [mem_Bset hsigma] at hx
  rw [mem_Dset hsigma]
  have hbase : 272 + 264 * R ≤ s := by
    simp only [aspect] at hscale
    omega
  have hwidth : width s rem R (t + 1) ≤ longScale s rem := by
    rw [width_step]
    have hfinal := tile_budget hrem hbase
    have hmono : width s rem R t ≤ width s rem R stepCount :=
      width_mono (show t ≤ stepCount by omega)
    omega
  constructor
  · rw [hx.1, L_step]
    push_cast
    omega
  · intro j hji
    exact (hx.2 j hji).trans (by exact_mod_cast hwidth)

/-! ## The finite choice attached to a literal `FaceTarget` -/

structure TileChoice {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (R : Nat) (Fresh B T : Finset (Site d)) (v : Site d) where
  radius : Nat
  face : FaceIndex d
  common_le_radius : R ≤ radius
  local_le_radius : S.scales.localRadius ≤ radius
  owner_subset : TargetAwareLattice.shiftedOwner radius v ⊆ Fresh
  face_subset : TargetAwareLattice.shiftedTarget radius v face ⊆ T

theorem exists_tileChoice {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (R : Nat) (hlocal : S.scales.localRadius ≤ R)
    {Fresh B T : Finset (Site d)} (hface : CorrMove.FaceTarget (R : Int) Fresh B T)
    (v : Site d) (hnear : ∃ b ∈ B, ∀ j, |v j - b j| ≤ (R : Int)) :
    Nonempty (TileChoice S R Fresh B T v) := by
  obtain ⟨ell, a, sigma, tau, hRell, hsigma, howner, htarget⟩ := hface v hnear
  have hell0 : 0 ≤ ell := (Int.natCast_nonneg R).trans hRell
  let n := ell.toNat
  have hn : (n : Int) = ell := Int.toNat_of_nonneg hell0
  have hRn : R ≤ n := by exact_mod_cast (show (R : Int) ≤ (n : Int) by simpa [hn] using hRell)
  refine ⟨{
    radius := n
    face := (a, TargetAwareLattice.qfaceUnits a sigma tau)
    common_le_radius := hRn
    local_le_radius := hlocal.trans hRn
    owner_subset := ?_
    face_subset := ?_ }⟩
  · rw [TargetAwareLattice.shiftedOwner,
      TargetAwareLattice.shiftFinset_box_eq_cube, hn]
    exact howner
  · exact (TargetAwareLattice.shiftedTarget_subset_qface n v a sigma tau hsigma).trans
      (by simpa only [hn] using htarget)

def tileChoice {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (R : Nat) (hlocal : S.scales.localRadius ≤ R)
    {Fresh B T : Finset (Site d)} (hface : CorrMove.FaceTarget (R : Int) Fresh B T)
    (v : Site d) (hnear : ∃ b ∈ B, ∀ j, |v j - b j| ≤ (R : Int)) :
    TileChoice S R Fresh B T v :=
  Classical.choice (exists_tileChoice S R hlocal hface v hnear)

/-! ## One exact plan on each tile -/

/-- Instantiate an extracted orthant scheme on the literal transition `B_t -> B_(t+1)` inside
`D_t`. -/
def tileInstantiation {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (R : Nat) (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius ≤ R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount)
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    ExactTargetScheme.OrthantInstantiation S := by
  let B := faceBox i sigma s rem R t
  let D := tileBox i sigma s rem R t
  have hBsites : B.sites = Bset i sigma s rem R t :=
    faceBox_sites_eq i hsigma s rem R t
  have hDsites : D.sites = Dset i sigma s rem R t :=
    tileBox_sites_eq i hsigma s rem R t
  have hface : CorrMove.FaceTarget (R : Int) (Dset i sigma s rem R t)
      (Bset i sigma s rem R t) (Bset i sigma s rem R (t + 1)) :=
    faceTarget_tile i hsigma hrem ht hscale
  let pick : ∀ v : (B.inflate R).sites,
      TileChoice S R (Dset i sigma s rem R t) (Bset i sigma s rem R t)
        (Bset i sigma s rem R (t + 1)) v.1 := fun v =>
    tileChoice S R hlocal hface v.1 (by
      obtain ⟨b, hb, hnear⟩ :=
        exists_near_of_mem_inflate B (faceBox_ordered i sigma s rem R t) R v.2
      exact ⟨b, hBsites ▸ hb, hnear⟩)
  exact {
    sourceBox := B
    activeBox := D
    target := Bset i sigma s rem R (t + 1)
    radius := R
    source_ordered := faceBox_ordered i sigma s rem R t
    active_ordered := tileBox_ordered i hsigma s rem R t
    target_nonempty := Bset_nonempty i hsigma s rem R (t + 1)
    radius_ge := hR0
    sourcePlus_subset_active := by
      intro v hv
      let v' : (B.inflate R).sites := ⟨v, hv⟩
      have hvowner : v ∈ TargetAwareLattice.shiftedOwner (pick v').radius v := by
        rw [TargetAwareLattice.shiftedOwner,
          TargetAwareLattice.shiftFinset_box_eq_cube]
        exact CorrMove.centre_mem_cube (by positivity)
      rw [hDsites]
      exact (pick v').owner_subset hvowner
    target_subset_active := by
      rw [hDsites]
      exact nextFace_subset_tile i hsigma hrem ht hscale
    targetRadius := fun v => (pick v).radius
    targetFace := fun v => (pick v).face
    radius_le := fun v => (pick v).common_le_radius
    localRadius_le := fun v => (pick v).local_le_radius
    owner_subset_active := fun v => by
      rw [hDsites]
      exact (pick v).owner_subset
    face_subset_target := fun v => (pick v).face_subset }

/-- The extracted exact target plan for a literal tile, including its three realization
equalities. -/
theorem exists_tile_plan {p0 : unitInterval} {epsilon : Real}
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (R : Nat) (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius ≤ R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount)
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    ∃ C : ExactTargetPlan.Plan d,
      C.WellFormed ∧ C.ValidAt p0 ∧
      C.p0 = p0 ∧
      C.source = Bset i sigma s rem R t ∧
      C.active = Dset i sigma s rem R t ∧
      C.target = Bset i sigma s rem R (t + 1) ∧
      C.epsilon = epsilon := by
  let I := tileInstantiation S R hR0 hlocal i hsigma hrem ht hscale
  let P := S.params I
  let X := S.concreteTarget I
  let H := S.concreteHits I
  let C := ExactTargetPlan.buildPlan P X H
  have hP : P.Admissible := S.params_admissible hp0 hp1 he0 he1 I
  refine ⟨C, ExactTargetPlan.buildPlan_wellFormed P hP X H,
    ExactTargetPlan.buildPlan_validAt P hP X H, rfl, ?_, ?_, ?_, ?_⟩
  · change I.sourceBox.sites = Bset i sigma s rem R t
    exact faceBox_sites_eq i hsigma s rem R t
  · change I.activeBox.sites = Dset i sigma s rem R t
    exact tileBox_sites_eq i hsigma s rem R t
  · rfl
  · rfl

/-! ## The exact 700-node plan -/

/-- Raw finite data for the literal aspect-88 chain. -/
structure Plan (d : Nat) (p0 : unitInterval) (alpha : Real) where
  axis : Fin d
  sigma : Int
  rem : Nat
  radius : Nat
  macroScale : Nat
  node : Fin 700 → ExactTargetPlan.Plan d

namespace Plan

/-- The deterministic geometry and all node-wise exact-plan consistency checks. -/
def WellFormed {p0 : unitInterval} {alpha : Real} (K : Plan d p0 alpha) : Prop :=
  (K.sigma = 1 ∨ K.sigma = -1) ∧
  K.rem ≤ 7 ∧
  3 * aspect + 3 * aspect * K.radius + 8 ≤ K.macroScale ∧
  ∀ t : Fin 700,
    (K.node t).WellFormed ∧
    (K.node t).p0 = p0 ∧
    (K.node t).source = Bset K.axis K.sigma K.macroScale K.rem K.radius t.val ∧
    (K.node t).active = Dset K.axis K.sigma K.macroScale K.rem K.radius t.val ∧
    (K.node t).target =
      Bset K.axis K.sigma K.macroScale K.rem K.radius (t.val + 1) ∧
    (K.node t).epsilon = tol alpha (t.val + 1)

/-- All 700 finite leaf tables are valid at the same parameter. -/
def ValidAt {p0 : unitInterval} {alpha : Real} (K : Plan d p0 alpha)
    (q : unitInterval) : Prop :=
  ∀ t, (K.node t).ValidAt q

theorem WellFormed.node_wf {p0 : unitInterval} {alpha : Real}
    {K : Plan d p0 alpha} (hK : K.WellFormed) (t : Fin 700) :
    (K.node t).WellFormed := (hK.2.2.2 t).1

theorem WellFormed.node_source {p0 : unitInterval} {alpha : Real}
    {K : Plan d p0 alpha} (hK : K.WellFormed) (t : Fin 700) :
    (K.node t).source =
      Bset K.axis K.sigma K.macroScale K.rem K.radius t.val :=
  (hK.2.2.2 t).2.2.1

theorem WellFormed.node_active {p0 : unitInterval} {alpha : Real}
    {K : Plan d p0 alpha} (hK : K.WellFormed) (t : Fin 700) :
    (K.node t).active =
      Dset K.axis K.sigma K.macroScale K.rem K.radius t.val :=
  (hK.2.2.2 t).2.2.2.1

theorem WellFormed.node_target {p0 : unitInterval} {alpha : Real}
    {K : Plan d p0 alpha} (hK : K.WellFormed) (t : Fin 700) :
    (K.node t).target =
      Bset K.axis K.sigma K.macroScale K.rem K.radius (t.val + 1) :=
  (hK.2.2.2 t).2.2.2.2.1

theorem WellFormed.node_epsilon {p0 : unitInterval} {alpha : Real}
    {K : Plan d p0 alpha} (hK : K.WellFormed) (t : Fin 700) :
    (K.node t).epsilon = tol alpha (t.val + 1) :=
  (hK.2.2.2 t).2.2.2.2.2

/-- The last exact node targets the literal `B_700`, which is contained in the far face of the
aspect-88 box. -/
theorem final_target_subset_longFace {p0 : unitInterval} {alpha : Real}
    (K : Plan d p0 alpha) (hK : K.WellFormed) :
    (K.node (Fin.last 699)).target ⊆
      CorrMove.longFace 0 (longScale K.macroScale K.rem : Int)
        K.axis K.sigma 88 := by
  have hcount : stepCount = 700 := stepCount_eq
  have hlastVal : (Fin.last 699 : Fin 700).val + 1 = stepCount := by
    simp [hcount]
  rw [hK.node_target, hlastVal]
  have hbase : 272 + 264 * K.radius ≤ K.macroScale := by
    rcases hK.1 with hsigma
    have hs := hK.2.2.1
    simp only [aspect] at hs
    omega
  exact final_Bset_subset_longFace K.axis hK.1 hK.2.1 hbase

end Plan

/-- One common radius dominates both the arithmetic and local-hit thresholds of all 700 schemes. -/
def commonRadius {p0 : unitInterval} {alpha : Real}
    (S : ∀ t : Fin 700,
      ExactTargetScheme.OrthantScheme d p0 (tol alpha (t.val + 1))) : Nat :=
  (Finset.univ.sup fun t : Fin 700 =>
    max (S t).scales.localRadius (S t).numbers.R0) + 1

theorem localRadius_le_commonRadius {p0 : unitInterval} {alpha : Real}
    (S : ∀ t : Fin 700,
      ExactTargetScheme.OrthantScheme d p0 (tol alpha (t.val + 1)))
    (t : Fin 700) : (S t).scales.localRadius ≤ commonRadius S := by
  have ht := Finset.le_sup (s := (Finset.univ : Finset (Fin 700)))
    (f := fun u => max (S u).scales.localRadius (S u).numbers.R0)
    (Finset.mem_univ t)
  exact (le_max_left _ _).trans (ht.trans (Nat.le_succ _))

theorem arithmeticRadius_le_commonRadius {p0 : unitInterval} {alpha : Real}
    (S : ∀ t : Fin 700,
      ExactTargetScheme.OrthantScheme d p0 (tol alpha (t.val + 1)))
    (t : Fin 700) : (S t).numbers.R0 ≤ commonRadius S := by
  have ht := Finset.le_sup (s := (Finset.univ : Finset (Fin 700)))
    (f := fun u => max (S u).scales.localRadius (S u).numbers.R0)
    (Finset.mem_univ t)
  exact (le_max_right _ _).trans (ht.trans (Nat.le_succ _))

/-- Supercriticality constructs all 700 exact tile plans, with a common finite radius and a
literal macro-scale satisfying every tile containment inequality. -/
theorem exists_plan_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (alpha : Real) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1) :
    ∃ K : Plan d p0 alpha, K.WellFormed ∧ K.ValidAt p0 := by
  have he0 : ∀ t : Fin 700, 0 < tol alpha (t.val + 1) :=
    fun t => tol_pos ha0 (t.val + 1)
  have he1 : ∀ t : Fin 700, tol alpha (t.val + 1) ≤ 1 :=
    fun t => tol_le_one ha0 ha1 (t.val + 1)
  let S : ∀ t : Fin 700,
      ExactTargetScheme.OrthantScheme d p0 (tol alpha (t.val + 1)) := fun t =>
    Classical.choice (ExactTargetScheme.exists_orthantScheme_of_thetaSite_pos
      (d := d) p0 hp0 hp1 htheta (tol alpha (t.val + 1)) (he0 t) (he1 t))
  let R := commonRadius S
  let s := 3 * aspect + 3 * aspect * R + 8
  have hscale : 3 * aspect + 3 * aspect * R + 0 + 0 + 8 ≤ s := by
    simp [s]
  choose C hCwf hCvalid hCp0 hCsource hCactive hCtarget hCepsilon using
    fun t : Fin 700 => exists_tile_plan hp0 hp1 (he0 t) (he1 t) (S t) R
      (arithmeticRadius_le_commonRadius S t) (localRadius_le_commonRadius S t)
      axis hsigma (s := s) (rem := 0) (k := 0) (n1 := 0) (t := t.val)
      (show (0 : Nat) ≤ 7 by omega) (by simpa [stepCount, aspect] using t.isLt) hscale
  let K : Plan d p0 alpha := {
    axis := axis
    sigma := sigma
    rem := 0
    radius := R
    macroScale := s
    node := C }
  refine ⟨K, ?_, hCvalid⟩
  refine ⟨hsigma, ?_, ?_, ?_⟩
  · simp [K]
  · simp [K, s]
  · intro t
    exact ⟨hCwf t, hCp0 t, hCsource t, hCactive t, hCtarget t, hCepsilon t⟩

/-! ## Exact-chain soundness -/

theorem Dset_subset_allowedRegion (i : Fin d) (sigma : Int) (s rem R t : Nat)
    (ht : t < stepCount) :
    Dset i sigma s rem R t ⊆ allowedRegion i sigma s rem R := by
  intro x hx
  rw [allowedRegion, Finset.mem_union]
  right
  rw [tileRegion, Finset.mem_biUnion]
  exact ⟨t, Finset.mem_range.2 ht, hx⟩

private theorem connWithinSet_mono_target {Dom A B : Finset (Site d)} {o : Site d}
    (hAB : A ⊆ B) :
    connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑A : Set (Site d)) ⊆
      connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑B : Set (Site d)) := by
  intro omega homega
  obtain ⟨x, hx, hox⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d)) o
      (↑A : Set (Site d)) omega).1 homega
  exact (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d)) o
    (↑B : Set (Site d)) omega).2
      ⟨x, Finset.mem_coe.2 (hAB (Finset.mem_coe.1 hx)), hox⟩

/-- The 700 exact plans compose under one pinned transcript.  The initial error is the literal
`tol alpha 0`; the terminal target is the far face of the aspect-88 box. -/
theorem Plan.soundPinned {p0 q : unitInterval} {alpha : Real}
    (K : Plan d p0 alpha) (hK : K.WellFormed) (hvalid : K.ValidAt q)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (Rpin : Finset (Site d)) (val : Site d → Prop) (o : Site d)
    (hRactive : ∀ t, Disjoint Rpin (K.node t).active)
    (hoR : o ∈ Rpin) (hvalo : val o)
    (hbase : 1 - tol alpha 0 <
      pinnedProb (fun _ : Site d => q) (↑Rpin : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(allowedRegion K.axis K.sigma K.macroScale K.rem K.radius) : Set (Site d)) o
          (↑(Bset K.axis K.sigma K.macroScale K.rem K.radius 0) : Set (Site d)))) :
    1 - alpha <
      pinnedProb (fun _ : Site d => q) (↑Rpin : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(allowedRegion K.axis K.sigma K.macroScale K.rem K.radius) : Set (Site d)) o
          (↑(CorrMove.longFace 0 (longScale K.macroScale K.rem : Int)
            K.axis K.sigma 88) : Set (Site d))) := by
  have hcount : stepCount = 700 := stepCount_eq
  have hbase' : 1 - (K.node 0).delta <
      pinnedProb (fun _ : Site d => q) (↑Rpin : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(allowedRegion K.axis K.sigma K.macroScale K.rem K.radius) : Set (Site d)) o
          (↑(K.node 0).source : Set (Site d))) := by
    rw [hK.node_source]
    apply lt_of_le_of_lt ?_ hbase
    have heps : (K.node 0).epsilon = tol alpha 1 := by
      simpa using hK.node_epsilon (0 : Fin 700)
    have hrec := tol_rec alpha (show 0 < stepCount by simp [hcount])
    rw [ExactTargetPlan.Plan.delta, heps, hrec, CorrMove.f]
    nlinarith [sq_nonneg (tol alpha 1)]
  have hchain := ExactTargetPlan.Plan.soundPinnedChain 699 K.node
    (fun _ => allowedRegion K.axis K.sigma K.macroScale K.rem K.radius)
    Rpin val o
    (fun t => hK.node_wf t) hvalid
    (fun t => by
      rw [hK.node_active]
      exact Dset_subset_allowedRegion K.axis K.sigma K.macroScale K.rem K.radius t.val t.isLt)
    hRactive hoR hvalo hbase'
    (fun _ => Finset.Subset.rfl)
    (fun t => by
      rw [hK.node_target, hK.node_source]
      rfl)
    (fun t => by
      rw [hK.node_epsilon, ExactTargetPlan.Plan.delta, hK.node_epsilon]
      change tol alpha (t.val + 1) ≤ tol alpha (t.val + 2) ^ 2 / 64
      have ht : t.val + 1 < stepCount := by simp [hcount]; omega
      rw [tol_rec alpha ht, CorrMove.f]
      nlinarith [sq_nonneg (tol alpha (t.val + 2))])
  have hlastEps : (K.node (Fin.last 699)).epsilon = alpha := by
    rw [hK.node_epsilon]
    have hv : (Fin.last 699 : Fin 700).val + 1 = stepCount := by simp [hcount]
    rw [hv, tol_final]
  rw [hlastEps] at hchain
  have htarget : (K.node (Fin.last 699)).target ⊆
      CorrMove.longFace 0 (longScale K.macroScale K.rem : Int)
        K.axis K.sigma 88 := K.final_target_subset_longFace hK
  have hevent := connWithinSet_mono_target (Dom :=
    allowedRegion K.axis K.sigma K.macroScale K.rem K.radius) (o := o) htarget
  exact hchain.trans_le (by
    unfold pinnedProb
    exact measureReal_mono (Set.preimage_mono hevent) (measure_ne_top _ _))

#print axioms KNAll.Site.ExactLongBox700.exists_plan_of_thetaSite_pos
#print axioms KNAll.Site.ExactLongBox700.Plan.soundPinned

end KNAll.Site.ExactLongBox700

end
