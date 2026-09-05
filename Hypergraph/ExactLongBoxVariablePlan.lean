import Hypergraph.ExactTargetSchemeExtraction
import Hypergraph.ExactTargetChain
import Hypergraph.ExactQuarterPlanExtraction
import Hypergraph.LongBoxVariable

/-!
# Exact variable-aspect long-box chains

This is the finite exact-plan realization of `LongBoxVariable`.  For aspect `A` it stores
exactly `8*A-4` quarter-face target plans.  A scheme family is extracted once from
supercriticality; it exposes its common radius and can then be instantiated at every literal
long-box scale satisfying the deterministic tile inequalities.
-/

noncomputable section

namespace KNAll.Site.ExactLongBoxVariablePlan

set_option maxRecDepth 4096

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open KNAll.Site.LongBoxVariable
open scoped Classical

variable {d : Nat} [NeZero d]

/-! ## Integer-box adapters -/

/-- The literal hyperplane patch `B_t` as an exact-plan integer box. -/
def faceBox (A : Nat) (i : Fin d) (sigma : Int) (s rem R t : Nat) :
    ExactTargetPlan.IntBox d where
  lower j :=
    if j = i then sigma * (L A s rem t : Int) else -(width A s rem R t : Int)
  upper j :=
    if j = i then sigma * (L A s rem t : Int) else width A s rem R t

/-- The literal tile `D_t` as an exact-plan integer box. -/
def tileBox (A : Nat) (i : Fin d) (sigma : Int) (s rem R t : Nat) :
    ExactTargetPlan.IntBox d where
  lower j :=
    if j = i then
      if sigma = 1 then (L A s rem t : Int) - 2 * (s : Int)
      else -((L A s rem t : Int) + (s : Int))
    else -(longScale s rem : Int)
  upper j :=
    if j = i then
      if sigma = 1 then (L A s rem t : Int) + (s : Int)
      else -((L A s rem t : Int) - 2 * (s : Int))
    else longScale s rem

theorem faceBox_ordered (A : Nat) (i : Fin d) (sigma : Int) (s rem R t : Nat) :
    (faceBox A i sigma s rem R t).Ordered := by
  intro j
  by_cases hji : j = i
  · simp [faceBox, hji]
  · simp only [faceBox, hji, if_false]
    omega

theorem tileBox_ordered (A : Nat) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s rem R t : Nat) :
    (tileBox A i sigma s rem R t).Ordered := by
  intro j
  by_cases hji : j = i
  · subst j
    rcases hsigma with rfl | rfl <;> simp [tileBox] <;> omega
  · simp only [tileBox, hji, if_false]
    omega

theorem faceBox_sites_eq (A : Nat) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s rem R t : Nat) :
    (faceBox A i sigma s rem R t).sites =
      Bset A i sigma s rem R t := by
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

theorem tileBox_sites_eq (A : Nat) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s rem R t : Nat) :
    (tileBox A i sigma s rem R t).sites =
      Dset A i sigma s rem R t := by
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, mem_Dset hsigma]
  constructor
  · intro hx
    have hi := hx i
    constructor
    · rcases hsigma with rfl | rfl <;>
        simp only [tileBox, if_pos rfl] at hi ⊢ <;>
        norm_num at hi ⊢ <;> omega
    · intro j hji
      have hj := hx j
      simp only [tileBox, hji, if_false] at hj
      exact abs_le.2 hj
  · rintro ⟨hi, hoff⟩ j
    by_cases hji : j = i
    · subst j
      rcases hsigma with rfl | rfl <;>
        simp only [tileBox, if_pos rfl] <;>
        norm_num at hi ⊢ <;> omega
    · simp only [tileBox, hji, if_false]
      exact abs_le.1 (hoff j hji)

theorem nextFace_subset_tile (A : Nat) (hA : 1 ≤ A)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem R k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    Bset A i sigma s rem R (t + 1) ⊆
      Dset A i sigma s rem R t := by
  intro x hx
  rw [mem_Bset hsigma] at hx
  rw [mem_Dset hsigma]
  have hbase : 3 * A + 8 + 3 * A * R ≤ s := by omega
  have hwidth : width A s rem R (t + 1) ≤ longScale s rem := by
    rw [width_step]
    have hfinal := tile_budget hA hrem hbase
    have hmono : width A s rem R t ≤ width A s rem R (stepCount A) :=
      width_mono (show t ≤ stepCount A by omega)
    omega
  constructor
  · rw [hx.1, L_step]
    push_cast
    omega
  · intro j hji
    exact (hx.2 j hji).trans (by exact_mod_cast hwidth)

/-! ## One transparent exact tile -/

/-- Instantiate one orthant scheme on the literal transition `B_t -> B_(t+1)`. -/
def tileInstantiation {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A)
    (R : Nat) (hR0 : S.numbers.R0 ≤ R)
    (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    ExactTargetScheme.OrthantInstantiation S := by
  let B := faceBox A i sigma s rem R t
  let D := tileBox A i sigma s rem R t
  have hBsites : B.sites = Bset A i sigma s rem R t :=
    faceBox_sites_eq A i hsigma s rem R t
  have hDsites : D.sites = Dset A i sigma s rem R t :=
    tileBox_sites_eq A i hsigma s rem R t
  have hface : CorrMove.FaceTarget (R : Int) (Dset A i sigma s rem R t)
      (Bset A i sigma s rem R t) (Bset A i sigma s rem R (t + 1)) :=
    faceTarget_tile i hsigma hA hrem ht hscale
  let pick : ∀ v : (B.inflate R).sites,
      ExactQuarterPlanExtraction.SizedChosenTarget S.scales R
        (Dset A i sigma s rem R t) (Bset A i sigma s rem R t)
        (Bset A i sigma s rem R (t + 1)) v.1 := fun v =>
    ExactQuarterPlanExtraction.chooseSizedTarget S.scales R hlocal hface v.1 (by
      obtain ⟨b, hb, hnear⟩ :=
        ExactQuarterPlanExtraction.exists_near_of_mem_inflate B
          (faceBox_ordered A i sigma s rem R t) R v
      exact ⟨b, hBsites ▸ hb, hnear⟩)
  exact {
    sourceBox := B
    activeBox := D
    target := Bset A i sigma s rem R (t + 1)
    radius := R
    source_ordered := faceBox_ordered A i sigma s rem R t
    active_ordered := tileBox_ordered A i hsigma s rem R t
    target_nonempty := Bset_nonempty A i hsigma s rem R (t + 1)
    radius_ge := hR0
    sourcePlus_subset_active := by
      intro v hv
      let v' : (B.inflate R).sites := ⟨v, hv⟩
      have hvowner :
          v ∈ TargetAwareLattice.shiftedOwner (pick v').radius v := by
        rw [TargetAwareLattice.shiftedOwner,
          TargetAwareLattice.shiftFinset_box_eq_cube]
        exact CorrMove.centre_mem_cube (by positivity)
      rw [hDsites]
      exact (pick v').owner_subset_fresh hvowner
    target_subset_active := by
      rw [hDsites]
      exact nextFace_subset_tile A hA i hsigma hrem ht hscale
    targetRadius := fun v => (pick v).radius
    targetFace := fun v =>
      ((pick v).axis, TargetAwareLattice.qfaceUnits
        (pick v).axis (pick v).sigma (pick v).tau)
    radius_le := fun v => (pick v).radius_ge
    localRadius_le := fun v => (pick v).local_lt_radius.le
    owner_subset_active := fun v => by
      rw [hDsites]
      exact (pick v).owner_subset_fresh
    face_subset_target := fun v => (pick v).target_subset }

/-- The transparent exact target plan on one literal tile. -/
def tilePlan {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A)
    (R : Nat) (hR0 : S.numbers.R0 ≤ R)
    (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    ExactTargetPlan.Plan d :=
  let I := tileInstantiation S A hA R hR0 hlocal i hsigma hrem ht hscale
  ExactTargetPlan.buildPlan (S.params I) (S.concreteTarget I) (S.concreteHits I)

theorem tilePlan_wellFormed
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A)
    (R : Nat) (hR0 : S.numbers.R0 ≤ R)
    (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    (tilePlan S A hA R hR0 hlocal i hsigma hrem ht hscale).WellFormed := by
  let I := tileInstantiation S A hA R hR0 hlocal i hsigma hrem ht hscale
  exact ExactTargetPlan.buildPlan_wellFormed _
    (S.params_admissible hp0 hp1 he0 he1 I) _ _

theorem tilePlan_validAt
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {epsilon : Real} (he0 : 0 < epsilon) (he1 : epsilon ≤ 1)
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A)
    (R : Nat) (hR0 : S.numbers.R0 ≤ R)
    (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    (tilePlan S A hA R hR0 hlocal i hsigma hrem ht hscale).ValidAt p0 := by
  let I := tileInstantiation S A hA R hR0 hlocal i hsigma hrem ht hscale
  exact ExactTargetPlan.buildPlan_validAt _
    (S.params_admissible hp0 hp1 he0 he1 I) _ _

@[simp] theorem tilePlan_p0
    {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A) (R : Nat)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    (tilePlan S A hA R hR0 hlocal i hsigma hrem ht hscale).p0 = p0 := rfl

@[simp] theorem tilePlan_source
    {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A) (R : Nat)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    (tilePlan S A hA R hR0 hlocal i hsigma hrem ht hscale).source =
      Bset A i sigma s rem R t := by
  exact faceBox_sites_eq A i hsigma s rem R t

@[simp] theorem tilePlan_active
    {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A) (R : Nat)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    (tilePlan S A hA R hR0 hlocal i hsigma hrem ht hscale).active =
      Dset A i sigma s rem R t := by
  exact tileBox_sites_eq A i hsigma s rem R t

@[simp] theorem tilePlan_target
    {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A) (R : Nat)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    (tilePlan S A hA R hR0 hlocal i hsigma hrem ht hscale).target =
      Bset A i sigma s rem R (t + 1) := rfl

@[simp] theorem tilePlan_radius
    {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A) (R : Nat)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    (tilePlan S A hA R hR0 hlocal i hsigma hrem ht hscale).radius = R := rfl

@[simp] theorem tilePlan_epsilon
    {p0 : unitInterval} {epsilon : Real}
    (S : ExactTargetScheme.OrthantScheme d p0 epsilon)
    (A : Nat) (hA : 1 ≤ A) (R : Nat)
    (hR0 : S.numbers.R0 ≤ R) (hlocal : S.scales.localRadius < R)
    (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {s rem k n1 t : Nat} (hrem : rem ≤ 7) (ht : t < stepCount A)
    (hscale : 3 * A + 3 * A * R + k + n1 + 8 ≤ s) :
    (tilePlan S A hA R hR0 hlocal i hsigma hrem ht hscale).epsilon =
      epsilon := rfl

/-! ## A reusable extracted scheme family -/

/-- The finitely many schemes needed for an aspect-`A` chain, together with their common
radius.  The predecessor count makes the family directly consumable by
`soundPinnedChain`. -/
structure SchemeFamily (d : Nat) (p0 : unitInterval) (alpha : Real) (A : Nat) where
  transitions : Nat
  count_eq : transitions + 1 = stepCount A
  scheme : ∀ u : Fin (transitions + 1),
    ExactTargetScheme.OrthantScheme d p0 (tol A alpha (u.val + 1))
  radius : Nat
  local_lt : ∀ u, (scheme u).scales.localRadius < radius
  arithmetic_le : ∀ u, (scheme u).numbers.R0 ≤ radius

/-- Supercriticality extracts a finite variable-aspect scheme family. -/
theorem exists_schemeFamily_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (alpha : Real) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (A : Nat) (hA : 1 ≤ A) :
    Nonempty (SchemeFamily d p0 alpha A) := by
  let n := stepCount A - 1
  have hcount : n + 1 = stepCount A := by
    unfold n stepCount
    omega
  have he0 : ∀ u : Fin (n + 1), 0 < tol A alpha (u.val + 1) :=
    fun u => tol_pos A ha0 (u.val + 1)
  have he1 : ∀ u : Fin (n + 1), tol A alpha (u.val + 1) ≤ 1 :=
    fun u => tol_le_one A ha0 ha1 (u.val + 1)
  let S : ∀ u : Fin (n + 1),
      ExactTargetScheme.OrthantScheme d p0 (tol A alpha (u.val + 1)) :=
    fun u => Classical.choice
      (ExactTargetScheme.exists_orthantScheme_of_thetaSite_pos
        (d := d) p0 hp0 hp1 htheta (tol A alpha (u.val + 1))
          (he0 u) (he1 u))
  let R := (Finset.univ.sup fun u : Fin (n + 1) =>
    max (S u).scales.localRadius (S u).numbers.R0) + 1
  have hlocal : ∀ u, (S u).scales.localRadius < R := by
    intro u
    have hu := Finset.le_sup (s := (Finset.univ : Finset (Fin (n + 1))))
      (f := fun v => max (S v).scales.localRadius (S v).numbers.R0)
      (Finset.mem_univ u)
    exact lt_of_le_of_lt ((le_max_left _ _).trans hu) (Nat.lt_succ_self _)
  have harith : ∀ u, (S u).numbers.R0 ≤ R := by
    intro u
    have hu := Finset.le_sup (s := (Finset.univ : Finset (Fin (n + 1))))
      (f := fun v => max (S v).scales.localRadius (S v).numbers.R0)
      (Finset.mem_univ u)
    exact (le_max_right _ _).trans (hu.trans (Nat.le_succ _))
  exact ⟨{
    transitions := n
    count_eq := hcount
    scheme := S
    radius := R
    local_lt := hlocal
    arithmetic_le := harith }⟩

/-- For the stopped construction, aspect `2*K` has exactly `16*K-4` tile calls. -/
theorem stepCount_two_mul (K : Nat) : stepCount (2 * K) = 16 * K - 4 := by
  unfold stepCount
  omega

/-- The extracted family specialized to the manuscript's aspect-`2*K` stopped move. -/
theorem exists_stoppedSchemeFamily_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (alpha : Real) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (K : Nat) (hK : 1 ≤ K) :
    Nonempty (SchemeFamily d p0 alpha (2 * K)) := by
  apply exists_schemeFamily_of_thetaSite_pos p0 hp0 hp1 htheta alpha ha0 ha1
  omega

/-! ## Literal chain plan -/

/-- A finite exact chain filling one literal variable-aspect long box. -/
structure Plan (d : Nat) (p0 : unitInterval) (alpha : Real) (A : Nat) where
  transitions : Nat
  count_eq : transitions + 1 = stepCount A
  axis : Fin d
  sigma : Int
  rem : Nat
  radius : Nat
  macroScale : Nat
  node : Fin (transitions + 1) → ExactTargetPlan.Plan d

namespace Plan

structure WellFormed {p0 : unitInterval} {alpha : Real} {A : Nat}
    (P : Plan d p0 alpha A) : Prop where
  aspect_pos : 1 ≤ A
  sign_unit : P.sigma = 1 ∨ P.sigma = -1
  rem_le : P.rem ≤ 7
  scale_budget : 3 * A + 3 * A * P.radius + 8 ≤ P.macroScale
  node_data : ∀ u,
    (P.node u).WellFormed ∧
    (P.node u).p0 = p0 ∧
    (P.node u).source =
      Bset A P.axis P.sigma P.macroScale P.rem P.radius u.val ∧
    (P.node u).active =
      Dset A P.axis P.sigma P.macroScale P.rem P.radius u.val ∧
    (P.node u).target =
      Bset A P.axis P.sigma P.macroScale P.rem P.radius (u.val + 1) ∧
    (P.node u).radius = P.radius ∧
    (P.node u).epsilon = tol A alpha (u.val + 1)

def ValidAt {p0 : unitInterval} {alpha : Real} {A : Nat}
    (P : Plan d p0 alpha A) (q : unitInterval) : Prop :=
  ∀ u, (P.node u).ValidAt q

theorem WellFormed.node_wf {p0 : unitInterval} {alpha : Real} {A : Nat}
    {P : Plan d p0 alpha A} (hP : P.WellFormed) (u) :
    (P.node u).WellFormed := (hP.node_data u).1

theorem WellFormed.node_source {p0 : unitInterval} {alpha : Real} {A : Nat}
    {P : Plan d p0 alpha A} (hP : P.WellFormed) (u) :
    (P.node u).source =
      Bset A P.axis P.sigma P.macroScale P.rem P.radius u.val :=
  (hP.node_data u).2.2.1

theorem WellFormed.node_active {p0 : unitInterval} {alpha : Real} {A : Nat}
    {P : Plan d p0 alpha A} (hP : P.WellFormed) (u) :
    (P.node u).active =
      Dset A P.axis P.sigma P.macroScale P.rem P.radius u.val :=
  (hP.node_data u).2.2.2.1

theorem WellFormed.node_target {p0 : unitInterval} {alpha : Real} {A : Nat}
    {P : Plan d p0 alpha A} (hP : P.WellFormed) (u) :
    (P.node u).target =
      Bset A P.axis P.sigma P.macroScale P.rem P.radius (u.val + 1) :=
  (hP.node_data u).2.2.2.2.1

theorem WellFormed.node_radius {p0 : unitInterval} {alpha : Real} {A : Nat}
    {P : Plan d p0 alpha A} (hP : P.WellFormed) (u) :
    (P.node u).radius = P.radius :=
  (hP.node_data u).2.2.2.2.2.1

theorem WellFormed.node_epsilon {p0 : unitInterval} {alpha : Real} {A : Nat}
    {P : Plan d p0 alpha A} (hP : P.WellFormed) (u) :
    (P.node u).epsilon = tol A alpha (u.val + 1) :=
  (hP.node_data u).2.2.2.2.2.2

theorem final_target_subset_longFace
    {p0 : unitInterval} {alpha : Real} {A : Nat}
    (P : Plan d p0 alpha A) (hP : P.WellFormed) :
    (P.node (Fin.last P.transitions)).target ⊆
      CorrMove.longFace 0 (longScale P.macroScale P.rem : Int)
        P.axis P.sigma A := by
  have hlast : (Fin.last P.transitions).val + 1 = stepCount A := by
    simpa using P.count_eq
  rw [hP.node_target, hlast]
  have hbase : 3 * A + 8 + 3 * A * P.radius ≤ P.macroScale := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hP.scale_budget
  exact final_Bset_subset_longFace P.axis hP.sign_unit hP.aspect_pos
    hP.rem_le hbase

end Plan

/-- Instantiate an extracted family at one deterministic literal scale. -/
def SchemeFamily.planAt
    {p0 : unitInterval} {alpha : Real} {A : Nat}
    (F : SchemeFamily d p0 alpha A)
    (hA : 1 ≤ A) (axis : Fin d) (sigma : Int)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (s rem : Nat) (hrem : rem ≤ 7)
    (hscale : 3 * A + 3 * A * F.radius + 8 ≤ s) :
    Plan d p0 alpha A where
  transitions := F.transitions
  count_eq := F.count_eq
  axis := axis
  sigma := sigma
  rem := rem
  radius := F.radius
  macroScale := s
  node := fun u =>
    tilePlan (F.scheme u) A hA F.radius (F.arithmetic_le u) (F.local_lt u)
      axis hsigma (s := s) (rem := rem) (k := 0) (n1 := 0) (t := u.val) hrem
      (by
        have huLt := u.isLt
        have hcount := F.count_eq
        omega)
      (by simpa using hscale)

theorem SchemeFamily.planAt_wellFormed
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A : Nat} (F : SchemeFamily d p0 alpha A)
    (hA : 1 ≤ A) (axis : Fin d) (sigma : Int)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (s rem : Nat) (hrem : rem ≤ 7)
    (hscale : 3 * A + 3 * A * F.radius + 8 ≤ s) :
    (F.planAt hA axis sigma hsigma s rem hrem hscale).WellFormed := by
  unfold SchemeFamily.planAt
  refine {
    aspect_pos := hA
    sign_unit := hsigma
    rem_le := hrem
    scale_budget := hscale
    node_data := ?_ }
  intro u
  have hu : u.val < stepCount A := by
    have huLt : u.val < F.transitions + 1 := by simpa using u.isLt
    simpa only [F.count_eq] using huLt
  have he0 : 0 < tol A alpha (u.val + 1) := tol_pos A ha0 _
  have he1 : tol A alpha (u.val + 1) ≤ 1 := tol_le_one A ha0 ha1 _
  refine ⟨tilePlan_wellFormed hp0 hp1 he0 he1 (F.scheme u) A hA F.radius
      (F.arithmetic_le u) (F.local_lt u) axis hsigma
      (s := s) (rem := rem) (k := 0) (n1 := 0) (t := u.val)
      hrem hu (by simpa using hscale),
    rfl,
    tilePlan_source (F.scheme u) A hA F.radius (F.arithmetic_le u)
      (F.local_lt u) axis hsigma hrem hu (by simpa using hscale),
    tilePlan_active (F.scheme u) A hA F.radius (F.arithmetic_le u)
      (F.local_lt u) axis hsigma hrem hu (by simpa using hscale),
    rfl, rfl, rfl⟩

theorem SchemeFamily.planAt_validAt
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A : Nat} (F : SchemeFamily d p0 alpha A)
    (hA : 1 ≤ A) (axis : Fin d) (sigma : Int)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (s rem : Nat) (hrem : rem ≤ 7)
    (hscale : 3 * A + 3 * A * F.radius + 8 ≤ s) :
    (F.planAt hA axis sigma hsigma s rem hrem hscale).ValidAt p0 := by
  unfold SchemeFamily.planAt Plan.ValidAt
  intro u
  have hu : u.val < stepCount A := by
    have huLt : u.val < F.transitions + 1 := by simpa using u.isLt
    simpa only [F.count_eq] using huLt
  exact tilePlan_validAt hp0 hp1 (tol_pos A ha0 _) (tol_le_one A ha0 ha1 _)
    (F.scheme u) A hA F.radius (F.arithmetic_le u) (F.local_lt u)
    axis hsigma (s := s) (rem := rem) (k := 0) (n1 := 0) (t := u.val)
    hrem hu (by simpa using hscale)

@[simp] theorem SchemeFamily.planAt_radius
    {p0 : unitInterval} {alpha : Real} {A : Nat}
    (F : SchemeFamily d p0 alpha A)
    (hA : 1 ≤ A) (axis : Fin d) (sigma : Int)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (s rem : Nat) (hrem : rem ≤ 7)
    (hscale : 3 * A + 3 * A * F.radius + 8 ≤ s) :
    (F.planAt hA axis sigma hsigma s rem hrem hscale).radius = F.radius := rfl

/-! ## Exact-chain soundness -/

theorem Dset_subset_allowedRegion (A : Nat) (i : Fin d) (sigma : Int)
    (s rem R t : Nat) (ht : t < stepCount A) :
    Dset A i sigma s rem R t ⊆ allowedRegion A i sigma s rem R := by
  intro x hx
  rw [allowedRegion, Finset.mem_union]
  right
  rw [tileRegion, Finset.mem_biUnion]
  exact ⟨t, Finset.mem_range.2 ht, hx⟩

private theorem connWithinSet_mono_target {Dom X Y : Finset (Site d)} {o : Site d}
    (hXY : X ⊆ Y) :
    connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑X : Set (Site d)) ⊆
      connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o (↑Y : Set (Site d)) := by
  intro omega homega
  obtain ⟨x, hx, hox⟩ :=
    (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d)) o
      (↑X : Set (Site d)) omega).1 homega
  exact (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d)) o
    (↑Y : Set (Site d)) omega).2
      ⟨x, Finset.mem_coe.2 (hXY (Finset.mem_coe.1 hx)), hox⟩

/-- The exact `8*A-4` nodes compose under one pinned transcript. -/
theorem Plan.soundPinned
    {p0 q : unitInterval} {alpha : Real} {A : Nat}
    (P : Plan d p0 alpha A) (hP : P.WellFormed) (hvalid : P.ValidAt q)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (Rpin : Finset (Site d)) (val : Site d → Prop) (o : Site d)
    (hRactive : ∀ u, Disjoint Rpin (P.node u).active)
    (hoR : o ∈ Rpin) (hvalo : val o)
    (hbase : 1 - tol A alpha 0 <
      pinnedProb (fun _ : Site d => q) (↑Rpin : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(allowedRegion A P.axis P.sigma P.macroScale P.rem P.radius) :
            Set (Site d)) o
          (↑(Bset A P.axis P.sigma P.macroScale P.rem P.radius 0) :
            Set (Site d)))) :
    1 - alpha <
      pinnedProb (fun _ : Site d => q) (↑Rpin : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(allowedRegion A P.axis P.sigma P.macroScale P.rem P.radius) :
            Set (Site d)) o
          (↑(CorrMove.longFace 0 (longScale P.macroScale P.rem : Int)
            P.axis P.sigma A) : Set (Site d))) := by
  have hstepPos : 0 < stepCount A := by
    have := hP.aspect_pos
    unfold stepCount
    omega
  have hbase' : 1 - (P.node 0).delta <
      pinnedProb (fun _ : Site d => q) (↑Rpin : Set (Site d)) val
        (connWithinSet (zdGraph d)
          (↑(allowedRegion A P.axis P.sigma P.macroScale P.rem P.radius) :
            Set (Site d)) o
          (↑(P.node 0).source : Set (Site d))) := by
    rw [hP.node_source]
    apply lt_of_le_of_lt ?_ hbase
    have heps : (P.node 0).epsilon = tol A alpha 1 := by
      simpa using hP.node_epsilon 0
    have hrec := tol_rec A alpha hstepPos
    rw [ExactTargetPlan.Plan.delta, heps, hrec, CorrMove.f]
    nlinarith [sq_nonneg (tol A alpha 1)]
  have hchain := ExactTargetPlan.Plan.soundPinnedChain P.transitions P.node
    (fun _ => allowedRegion A P.axis P.sigma P.macroScale P.rem P.radius)
    Rpin val o
    (fun u => hP.node_wf u) hvalid
    (fun u => by
      rw [hP.node_active]
      apply Dset_subset_allowedRegion
      have huLt := u.isLt
      have hcount := P.count_eq
      omega)
    hRactive hoR hvalo hbase'
    (fun _ => Finset.Subset.rfl)
    (fun u => by
      rw [hP.node_target, hP.node_source]
      rfl)
    (fun u => by
      rw [hP.node_epsilon, ExactTargetPlan.Plan.delta, hP.node_epsilon]
      change tol A alpha (u.val + 1) ≤ tol A alpha (u.val + 2) ^ 2 / 64
      have hu : u.val + 1 < stepCount A := by
        have huLt := u.isLt
        have hcount := P.count_eq
        omega
      rw [tol_rec A alpha hu, CorrMove.f]
      nlinarith [sq_nonneg (tol A alpha (u.val + 2))])
  have hlastEps : (P.node (Fin.last P.transitions)).epsilon = alpha := by
    rw [hP.node_epsilon]
    have hv : (Fin.last P.transitions).val + 1 = stepCount A := by
      simpa using P.count_eq
    rw [hv, tol_final]
  rw [hlastEps] at hchain
  have htarget := P.final_target_subset_longFace hP
  have hevent := connWithinSet_mono_target (Dom :=
    allowedRegion A P.axis P.sigma P.macroScale P.rem P.radius) (o := o) htarget
  exact hchain.trans_le (by
    unfold pinnedProb
    exact measureReal_mono (Set.preimage_mono hevent) (measure_ne_top _ _))

/-- Canonical existence form, choosing the least convenient tile scale after extraction. -/
theorem exists_plan_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (alpha : Real) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (A : Nat) (hA : 1 ≤ A)
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1) :
    ∃ P : Plan d p0 alpha A,
      P.WellFormed ∧ P.ValidAt p0 ∧ P.radius > 0 := by
  obtain ⟨F⟩ := exists_schemeFamily_of_thetaSite_pos p0 hp0 hp1 htheta
    alpha ha0 ha1 A hA
  let s := 3 * A + 3 * A * F.radius + 8
  have hs : 3 * A + 3 * A * F.radius + 8 ≤ s := le_rfl
  let P := F.planAt hA axis sigma hsigma s 0 (by omega) hs
  refine ⟨P, F.planAt_wellFormed hp0 hp1 ha0 ha1 hA axis sigma hsigma
      s 0 (by omega) hs,
    F.planAt_validAt hp0 hp1 ha0 ha1 hA axis sigma hsigma
      s 0 (by omega) hs, ?_⟩
  change 0 < F.radius
  have hlocal := F.local_lt (0 : Fin (F.transitions + 1))
  omega

#print axioms KNAll.Site.ExactLongBoxVariablePlan.exists_schemeFamily_of_thetaSite_pos
#print axioms KNAll.Site.ExactLongBoxVariablePlan.exists_stoppedSchemeFamily_of_thetaSite_pos
#print axioms KNAll.Site.ExactLongBoxVariablePlan.SchemeFamily.planAt_wellFormed
#print axioms KNAll.Site.ExactLongBoxVariablePlan.Plan.soundPinned
#print axioms KNAll.Site.ExactLongBoxVariablePlan.exists_plan_of_thetaSite_pos

end KNAll.Site.ExactLongBoxVariablePlan

end
