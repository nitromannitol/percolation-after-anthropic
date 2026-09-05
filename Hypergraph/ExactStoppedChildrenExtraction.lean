import Hypergraph.ExactStoppedG2Geometry
import Hypergraph.ExactLongBoxHitBridge
import Hypergraph.ExactLongBoxTranslatedPlan
import Hypergraph.ExactMacroNumerics

/-!
# Exact stopped-child extraction

This module is the finite assembly seam for the `K` stopped children.  It takes a literal family
of exact target plans, together with the deterministic G2 shape equations and the two recorded
error comparisons, and constructs `ExactMacroGeometry.StoppedChildren`.  Probability validity is
kept outside the structure and transported pointwise to the assembled family.

The later concrete extractor only has to construct the rank-one aspect-`2K` plans; outgoing-region
containment and stopped-prefix freshness are discharged here by `ExactStoppedG2Geometry`.
-/

noncomputable section

namespace KNAll.Site.ExactStoppedChildrenExtraction

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open ExactTargetArithmetic
open scoped Classical

variable {d : Nat} [NeZero d]

/-- Assemble a finite stopped-child family from literal G2 plan equations.  Every hypothesis is
either a deterministic orientation/shape fact or a comparison between a plan's stored tolerance
and the macro tolerances; no probability or soundness assertion is stored here. -/
def assemble {r t s K : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    {deltaC delta2 : Real}
    (hsigma : sigma = 1 ∨ sigma = -1) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (plan : Fin K → ExactTargetPlan.Plan d)
    (hwf : ∀ a, (plan a).WellFormed)
    (hactive : ∀ a, (plan a).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val)
    (hsource : ∀ a, (plan a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)))
    (htarget : ∀ a, (plan a).target ⊆ CoreRes.target (d := d) r y)
    (hdelta : ∀ a, delta2 ≤ (plan a).delta)
    (heps : ∀ a, (plan a).epsilon ≤ deltaC) :
    ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma deltaC delta2 :=
  ExactStoppedG2.stoppedChildren hsigma hr ht hemb plan hwf hactive hsource
    htarget hdelta heps

@[simp] theorem assemble_plan {r t s K : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    {deltaC delta2 : Real}
    (hsigma : sigma = 1 ∨ sigma = -1) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (plan : Fin K → ExactTargetPlan.Plan d)
    (hwf : ∀ a, (plan a).WellFormed)
    (hactive : ∀ a, (plan a).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val)
    (hsource : ∀ a, (plan a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)))
    (htarget : ∀ a, (plan a).target ⊆ CoreRes.target (d := d) r y)
    (hdelta : ∀ a, delta2 ≤ (plan a).delta)
    (heps : ∀ a, (plan a).epsilon ≤ deltaC) (a : Fin K) :
    (assemble hsigma hr ht hemb plan hwf hactive hsource htarget hdelta heps).plan a =
      plan a := rfl

/-- Finite leaf validity is unchanged by stopped-child assembly. -/
theorem assemble_validAt {p : unitInterval}
    {r t s K : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    {deltaC delta2 : Real}
    (hsigma : sigma = 1 ∨ sigma = -1) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (plan : Fin K → ExactTargetPlan.Plan d)
    (hwf : ∀ a, (plan a).WellFormed)
    (hactive : ∀ a, (plan a).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val)
    (hsource : ∀ a, (plan a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)))
    (htarget : ∀ a, (plan a).target ⊆ CoreRes.target (d := d) r y)
    (hdelta : ∀ a, delta2 ≤ (plan a).delta)
    (heps : ∀ a, (plan a).epsilon ≤ deltaC)
    (hvalid : ∀ a, (plan a).ValidAt p) :
    ∀ a, ((assemble hsigma hr ht hemb plan hwf hactive hsource htarget hdelta heps).plan a).ValidAt p := by
  intro a
  simpa using hvalid a

/-- Existential form used by dependent finite choice over macro heads. -/
theorem exists_children_of_plans {p : unitInterval}
    {r t s K : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    {deltaC delta2 : Real}
    (hsigma : sigma = 1 ∨ sigma = -1) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (plan : Fin K → ExactTargetPlan.Plan d)
    (hwf : ∀ a, (plan a).WellFormed)
    (hactive : ∀ a, (plan a).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val)
    (hsource : ∀ a, (plan a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)))
    (htarget : ∀ a, (plan a).target ⊆ CoreRes.target (d := d) r y)
    (hdelta : ∀ a, delta2 ≤ (plan a).delta)
    (heps : ∀ a, (plan a).epsilon ≤ deltaC)
    (hvalid : ∀ a, (plan a).ValidAt p) :
    ∃ G : ExactMacroGeometry.StoppedChildren (d := d)
        r t s K z y i sigma deltaC delta2,
      (∀ a, G.plan a = plan a) ∧ ∀ a, (G.plan a).ValidAt p := by
  let G := assemble hsigma hr ht hemb plan hwf hactive hsource htarget hdelta heps
  refine ⟨G, ?_, ?_⟩
  · intro a
    rfl
  · exact assemble_validAt hsigma hr ht hemb plan hwf hactive hsource htarget hdelta heps
      hvalid

/-! ## Literal aspect-`2K` plans -/

namespace Concrete

abbrev RankInstantiation
    {p0 : unitInterval} {alpha : Real} {K R : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) (2 * K))
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    (i : Fin d) (sigma : Int) :=
  ExactLongBoxHitBridge.RankOne.Instantiation F N R i sigma

/-- The radius-`3r` recursive target lies in every stopped active box `D_j`.  The lower face of
the target is at signed coordinate `17r`, while every stopped active box starts no later than
`15r`; transversally the target has width `3r` and `D_j` has width `5r`. -/
theorem coreTarget_subset_Dbox
    {K r s j : Nat} (hs : 0 < s) (hr : r = K * s) (hj : j < K)
    {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    CoreRes.target (d := d) r y ⊆
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s j := by
  intro x hx
  have hcube : x ∈ CorrMove.cube (MacroExp.ctr d r y) (3 * (r : Int)) := by
    simpa only [CoreRes.target] using hx
  have hcy : (MacroExp.ctr d r y : Site d) =
      MacroExp.ctr d r z + Pi.single i (sigma * (20 * (r : Int))) :=
    CorrMove.ctr_add_dir r hemb
  have hi := (CorrMove.mem_cube.1 hcube) i
  rw [hcy] at hi
  simp only [Pi.add_apply, Pi.single_eq_same] at hi
  have hsigma2 : sigma * sigma = 1 := by
    rcases hsigma with rfl | rfl <;> ring
  have heq : sigma * (x i - MacroExp.ctr d r z i) - 20 * (r : Int) =
      sigma * (x i - (MacroExp.ctr d r z i + sigma * (20 * (r : Int)))) := by
    linear_combination (20 * (r : Int)) * hsigma2
  have habs :
      |sigma * (x i - MacroExp.ctr d r z i) - 20 * (r : Int)| ≤ 3 * (r : Int) := by
    rw [heq, CorrMove.abs_signed hsigma]
    exact hi
  rw [abs_le] at habs
  have htail := ExactStoppedG2.tail_le_of_lt (K := K) (s := s) hj
  have htop := ExactStoppedG2.tail_top (K := K) (r := r) (s := s) hr
  have hsplit := ExactStoppedG2.tail_split s j
  have hloNat : 5 * r + 10 * s * j + 1 ≤ 15 * r := by omega
  have hloZ : (((5 * r + 10 * s * j : Nat) : Int) + 1) ≤ 15 * (r : Int) := by
    exact_mod_cast hloNat
  rw [ExactStoppedG2.mem_Dbox hsigma]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Stopped.lam]
    exact hloZ.trans (by omega)
  · simp only [Stopped.lam]
    push_cast
    omega
  · intro k hk
    have hkx := (CorrMove.mem_cube.1 hcube) k
    rw [hcy] at hkx
    simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero] at hkx
    exact hkx.trans (by push_cast; omega)

/-- The literal G2 boxes and the radius-`3r` core form the finite geometry consumed by the
transparent rank-one constructor. -/
def instantiation
    {p0 : unitInterval} {alpha : Real} {K R r t s : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) (2 * K))
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    {z y : Site 2} (i : Fin d) (sigma : Int)
    (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s)
    (hR : 2 * R ≤ s) (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) : RankInstantiation (R := R) F N i sigma where
  sourceBox := ExactStoppedG2.faceIntBox (MacroExp.ctr d r z) i sigma r
    (10 * s * (a.val + 1))
  activeBox := ExactStoppedG2.DIntBox (MacroExp.ctr d r z) i sigma r s a.val
  target := CoreRes.target (d := d) r y
  source_ordered := ExactStoppedG2.faceIntBox_ordered _ _ _ _ _
  active_ordered := ExactStoppedG2.DIntBox_ordered _ _ hsigma hK hs hr a.isLt
  target_nonempty := by
    unfold CoreRes.target
    exact CorrMove.cube_nonempty _ (by positivity)
  target_subset_active := by
    rw [ExactStoppedG2.DIntBox_sites_eq _ _ hsigma]
    exact coreTarget_subset_Dbox hs hr a.isLt hsigma hemb
  longTarget := by
    rw [ExactStoppedG2.DIntBox_sites_eq _ _ hsigma r s a.val,
      ExactStoppedG2.faceIntBox_sites_eq _ _ hsigma r t (10 * s * (a.val + 1))]
    simpa only [ExactLongBoxHitBridge.RankOne.LongTargetAspect,
      ExactStoppedG2.LongTargetAspect, Nat.cast_mul, Nat.cast_ofNat] using
      (ExactStoppedG2.longTargetAspect_stubFace_core hsigma hK hs hr a.isLt hR hemb)

/-- A supplied aspect-`2K` scheme family gives all `K` literal stopped plans.  The only remaining
hypotheses are deterministic scale/geometry inequalities and the two numerical tolerance
comparisons recorded by `StoppedChildren`. -/
theorem exists_stoppedChildren_from_scheme
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {K R r t s : Nat} (hK : 20 ≤ K)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) (2 * K))
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    (hNR : N.R0 ≤ R)
    (hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R)
    (hs : 0 < s) (hr : r = K * s) (hR : 2 * R ≤ s) (ht : 5 * r ≤ t)
    {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    {deltaC delta2 : Real}
    (hdelta : delta2 ≤ deltaOf alpha) (hepsilon : alpha ≤ deltaC) :
    ∃ G : ExactMacroGeometry.StoppedChildren (d := d)
        r t s K z y i sigma deltaC delta2,
      (∀ a, (G.plan a).ValidAt p0) ∧
      (∀ a, (G.plan a).radius = R) ∧
      (∀ a, (G.plan a).epsilon = alpha) ∧
      (∀ a, (G.plan a).active =
        ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
      (∀ a, (G.plan a).source =
        Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
      ∀ a, (G.plan a).target = CoreRes.target (d := d) r y := by
  let I : ∀ a : Fin K, RankInstantiation (R := R) F N i sigma :=
    fun a => instantiation (R := R) (t := t) F N i sigma hK hs hr hR hsigma hemb a
  have hex : ∀ a : Fin K, ∃ C : ExactTargetPlan.Plan d,
      C.WellFormed ∧ C.ValidAt p0 ∧ C.p0 = p0 ∧ C.epsilon = alpha ∧ C.radius = R ∧
      C.sourceBox = (I a).sourceBox ∧ C.activeBox = (I a).activeBox ∧
      C.target = (I a).target ∧
      ExactLongBoxHitBridge.RankOne.LongTargetAspect (2 * K) C.radius i sigma
        C.active C.source C.target := by
    intro a
    exact ExactLongBoxHitBridge.RankOne.exists_rankOnePlan_two_mul
      hp0 hp1 ha0 ha1 K (by omega) F N i sigma hsigma hNR hlarge (I a)
  let plan : Fin K → ExactTargetPlan.Plan d := fun a => Classical.choose (hex a)
  have hspec (a : Fin K) := Classical.choose_spec (hex a)
  have hwf : ∀ a, (plan a).WellFormed := by
    intro a
    exact (hspec a).1
  have hvalid : ∀ a, (plan a).ValidAt p0 := by
    intro a
    exact (hspec a).2.1
  have hradius : ∀ a, (plan a).radius = R := by
    intro a
    exact (hspec a).2.2.2.2.1
  have heps : ∀ a, (plan a).epsilon = alpha := by
    intro a
    exact (hspec a).2.2.2.1
  have hactive : ∀ a, (plan a).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val := by
    intro a
    rw [ExactTargetPlan.Plan.active, (hspec a).2.2.2.2.2.2.1]
    exact ExactStoppedG2.DIntBox_sites_eq _ _ hsigma _ _ _
  have hsource : ∀ a, (plan a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)) := by
    intro a
    rw [ExactTargetPlan.Plan.source, (hspec a).2.2.2.2.2.1]
    exact ExactStoppedG2.faceIntBox_sites_eq _ _ hsigma _ _ _
  have htarget : ∀ a, (plan a).target = CoreRes.target (d := d) r y := by
    intro a
    exact (hspec a).2.2.2.2.2.2.2.1
  have hdeltaPlan : ∀ a, delta2 ≤ (plan a).delta := by
    intro a
    rw [ExactTargetPlan.Plan.delta, heps a]
    simpa only [deltaOf] using hdelta
  have hepsPlan : ∀ a, (plan a).epsilon ≤ deltaC := by
    intro a
    rw [heps a]
    exact hepsilon
  let G := assemble hsigma (by rw [hr]; positivity) ht hemb plan hwf hactive hsource
    (fun a => by rw [htarget a]) hdeltaPlan hepsPlan
  refine ⟨G, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact assemble_validAt hsigma (by rw [hr]; positivity) ht hemb plan hwf hactive hsource
      (fun a => by rw [htarget a]) hdeltaPlan hepsPlan hvalid
  · intro a
    change (plan a).radius = R
    exact hradius a
  · intro a
    change (plan a).epsilon = alpha
    exact heps a
  · intro a
    change (plan a).active = _
    exact hactive a
  · intro a
    change (plan a).source = _
    exact hsource a
  · intro a
    change (plan a).target = _
    exact htarget a

theorem etaOf_pos {alpha : Real} (ha : 0 < alpha) : 0 < etaOf alpha := by
  unfold etaOf deltaOf deltaCOf
  positivity

theorem etaOf_le_one {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) :
    etaOf alpha ≤ 1 := by
  unfold etaOf deltaOf deltaCOf
  have hd0 : 0 ≤ alpha ^ 2 / 64 := by positivity
  have hd1 : alpha ^ 2 / 64 ≤ 1 := by nlinarith [sq_nonneg alpha]
  have hdc0 : 0 ≤ alpha / 4 := by positivity
  have hdc1 : alpha / 4 ≤ 1 := by linarith
  have hd2 : (alpha ^ 2 / 64) ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1
  nlinarith [mul_le_mul hd2 hdc1 hdc0 (by positivity : (0 : Real) ≤ 1)]

/-! ## A canonical rank-one selector

`ExactLongBoxHitBridge.RankOne.Instantiation.choice` is an unrestricted classical choice.
That is sufficient for existence at `p0`, but it does not commute with translation: a long
target can have several lengths.  For the frozen family used below we instead choose the least
admissible natural length.  The defining predicate contains only the centre, active box and
target, so its least witness is translation-equivariant. -/

namespace CanonicalRankOne

open ExactLongBoxHitBridge.RankOne

variable {p0 : unitInterval} {alpha : Real} {A R : Nat}
  {F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A}
  {N : ExactTargetSchemeNumbers.Numbers d p0 alpha
    (ExactLongBoxHitBridge.RankOne.sourceRadius F)}
  {axis : Fin d} {sigma : Int}

/-- The entirely geometric predicate whose least witness is used by the canonical plan. -/
def AdmissibleScale
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) (n : Nat) : Prop :=
  R ≤ n ∧
  CorrMove.longBox v.1 (n : Int) axis sigma A ⊆ I.activeBox.sites ∧
  CorrMove.longFace v.1 (n : Int) axis sigma A ⊆ I.target

theorem exists_admissibleScale
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : ∃ n, AdmissibleScale I v n := by
  refine ⟨I.scale v, I.radius_le_scale v, ?_, ?_⟩
  · simpa only [I.scale_cast v] using (I.choice v).region_subset
  · simpa only [I.scale_cast v] using (I.choice v).face_subset

/-- The least admissible long-box length.  Unlike the old unrestricted choice, this value is
determined solely by a proposition on natural numbers. -/
def scale
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : Nat :=
  Nat.find (exists_admissibleScale I v)

theorem scale_spec
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : AdmissibleScale I v (scale I v) :=
  Nat.find_spec (exists_admissibleScale I v)

/-- Least admissible lengths agree whenever their defining predicates agree. -/
theorem scale_eq_of_iff
    (I J : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) (w : (J.sourceBox.inflate R).sites)
    (hiff : ∀ n, AdmissibleScale I v n ↔ AdmissibleScale J w n) :
    scale I v = scale J w := by
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_admissibleScale I v)
      ((hiff (scale J w)).2 (scale_spec J w))
  · exact Nat.find_min' (exists_admissibleScale J w)
      ((hiff (scale I v)).1 (scale_spec I v))

abbrev shiftFinset (u : Site d) (S : Finset (Site d)) : Finset (Site d) :=
  MoveWindowInput.shiftFinset u S

theorem mem_shiftFinset {u x : Site d} {S : Finset (Site d)} :
    x ∈ shiftFinset u S ↔ x - u ∈ S := by
  simp only [shiftFinset, MoveWindowInput.shiftFinset, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - u, hx, by ring⟩

theorem shiftFinset_subset_iff {u : Site d} {S T : Finset (Site d)} :
    shiftFinset u S ⊆ shiftFinset u T ↔ S ⊆ T := by
  constructor
  · intro h x hx
    have hxu : x + u ∈ shiftFinset u S := mem_shiftFinset.2 (by simpa using hx)
    have := h hxu
    simpa only [mem_shiftFinset, add_sub_cancel_right] using this
  · intro h x hx
    rw [mem_shiftFinset] at hx ⊢
    exact h hx

theorem shift_longBox (u c : Site d) {l : Int} (hl : 0 ≤ l)
    (axis : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {A : Nat} (hA : 1 ≤ A) :
    shiftFinset u (CorrMove.longBox c l axis sigma A) =
      CorrMove.longBox (c + u) l axis sigma A := by
  ext x
  rw [mem_shiftFinset]
  rw [CorrMove.mem_longBox hsigma hl (by exact_mod_cast hA),
    CorrMove.mem_longBox hsigma hl (by exact_mod_cast hA)]
  simp only [Pi.sub_apply, Pi.add_apply]
  constructor
  · rintro ⟨hi, hoff⟩
    constructor
    · convert hi using 1 <;> ring
    · intro j hji
      convert hoff j hji using 1 <;> ring
  · rintro ⟨hi, hoff⟩
    constructor
    · convert hi using 1 <;> ring
    · intro j hji
      convert hoff j hji using 1 <;> ring

theorem shift_longFace (u c : Site d) {l : Int} (hl : 0 ≤ l)
    (axis : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {A : Nat} (hA : 1 ≤ A) :
    shiftFinset u (CorrMove.longFace c l axis sigma A) =
      CorrMove.longFace (c + u) l axis sigma A := by
  ext x
  rw [mem_shiftFinset]
  rw [CorrMove.mem_longFace hsigma hl (by exact_mod_cast hA),
    CorrMove.mem_longFace hsigma hl (by exact_mod_cast hA)]
  simp only [Pi.sub_apply, Pi.add_apply]
  constructor
  · rintro ⟨hi, hoff⟩
    constructor
    · convert hi using 1 <;> ring
    · intro j hji
      convert hoff j hji using 1 <;> ring
  · rintro ⟨hi, hoff⟩
    constructor
    · convert hi using 1 <;> ring
    · intro j hji
      convert hoff j hji using 1 <;> ring

/-- The admissible-length predicate is exactly invariant under a simultaneous translation of
the relay centre, active region and target. -/
theorem admissibleScale_translate_iff
    (I J : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (u : Site d) (v : (I.sourceBox.inflate R).sites)
    (w : (J.sourceBox.inflate R).sites)
    (hpoint : w.1 = v.1 + u)
    (hactive : J.activeBox.sites = shiftFinset u I.activeBox.sites)
    (htarget : J.target = shiftFinset u I.target)
    (hsigma : sigma = 1 ∨ sigma = -1) (hA : 1 ≤ A) (n : Nat) :
    AdmissibleScale I v n ↔ AdmissibleScale J w n := by
  have hn : (0 : Int) ≤ (n : Int) := by positivity
  unfold AdmissibleScale
  rw [hpoint, hactive, htarget,
    ← shift_longBox u v.1 hn axis hsigma hA,
    ← shift_longFace u v.1 hn axis hsigma hA,
    shiftFinset_subset_iff, shiftFinset_subset_iff]

/-- Consequently the selected length itself commutes with translation. -/
theorem scale_translate
    (I J : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (u : Site d) (v : (I.sourceBox.inflate R).sites)
    (w : (J.sourceBox.inflate R).sites)
    (hpoint : w.1 = v.1 + u)
    (hactive : J.activeBox.sites = shiftFinset u I.activeBox.sites)
    (htarget : J.target = shiftFinset u I.target)
    (hsigma : sigma = 1 ∨ sigma = -1) (hA : 1 ≤ A) :
    scale J w = scale I v := by
  exact (scale_eq_of_iff I J v w fun n =>
    admissibleScale_translate_iff I J u v w hpoint hactive htarget hsigma hA n).symm

theorem region_translate
    (I J : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (u : Site d) (v : (I.sourceBox.inflate R).sites)
    (w : (J.sourceBox.inflate R).sites)
    (hpoint : w.1 = v.1 + u)
    (hactive : J.activeBox.sites = shiftFinset u I.activeBox.sites)
    (htarget : J.target = shiftFinset u I.target)
    (hsigma : sigma = 1 ∨ sigma = -1) (hA : 1 ≤ A) :
    CorrMove.longBox w.1 (scale J w : Int) axis sigma A =
      shiftFinset u (CorrMove.longBox v.1 (scale I v : Int) axis sigma A) := by
  rw [scale_translate I J u v w hpoint hactive htarget hsigma hA, hpoint,
    shift_longBox u v.1 (by positivity) axis hsigma hA]

theorem face_translate
    (I J : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (u : Site d) (v : (I.sourceBox.inflate R).sites)
    (w : (J.sourceBox.inflate R).sites)
    (hpoint : w.1 = v.1 + u)
    (hactive : J.activeBox.sites = shiftFinset u I.activeBox.sites)
    (htarget : J.target = shiftFinset u I.target)
    (hsigma : sigma = 1 ∨ sigma = -1) (hA : 1 ≤ A) :
    CorrMove.longFace w.1 (scale J w : Int) axis sigma A =
      shiftFinset u (CorrMove.longFace v.1 (scale I v : Int) axis sigma A) := by
  rw [scale_translate I J u v w hpoint hactive htarget hsigma hA, hpoint,
    shift_longFace u v.1 (by positivity) axis hsigma hA]

theorem radius_le_scale
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : R ≤ scale I v :=
  (scale_spec I v).1

def macroScale
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : Nat := scale I v / 8

def remainder
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : Nat := scale I v % 8

theorem scale_eq
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) :
    LongBoxVariable.longScale (macroScale I v) (remainder I v) = scale I v := by
  unfold macroScale remainder LongBoxVariable.longScale
  omega

theorem remainder_le
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : remainder I v ≤ 7 := by
  unfold remainder
  have := Nat.mod_lt (scale I v) (by omega : 0 < 8)
  omega

theorem source_subset_longBox
    (hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hA : 1 ≤ A)
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) :
    siteBoxAt v.1 (ExactLongBoxHitBridge.RankOne.sourceRadius F) ⊆
      CorrMove.longBox v.1 (scale I v : Int) axis sigma A := by
  intro x hx
  have hl0 : (0 : Int) ≤ (scale I v : Int) := by positivity
  have hmR : ExactLongBoxHitBridge.RankOne.sourceRadius F ≤ R := by
    unfold ExactLongBoxHitBridge.RankOne.scaleThreshold at hlarge
    omega
  have hml : (ExactLongBoxHitBridge.RankOne.sourceRadius F : Int) ≤
      (scale I v : Int) := by
    exact_mod_cast hmR.trans (radius_le_scale I v)
  rw [mem_siteBoxAt] at hx
  rw [CorrMove.mem_longBox hsigma hl0 (by exact_mod_cast hA)]
  have haxis := hx axis
  have hlA : (scale I v : Int) ≤ (A : Int) * (scale I v : Int) :=
    le_mul_of_one_le_left hl0 (by exact_mod_cast hA)
  constructor
  · rcases hsigma with rfl | rfl <;> norm_num at haxis ⊢ <;> omega
  · intro j hji
    have hj := hx j
    rw [abs_le]
    omega

/-- The canonical T4 table.  Its hit proof is the existing exact aspect-`A` chain theorem; only
the choice of its terminal length has changed. -/
def concreteHits
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    {R : Nat} (hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R)
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma) :
    ExactTargetPlan.ConcreteHits
      (ExactLongBoxHitBridge.RankOne.params F N R)
      (ExactLongBoxHitBridge.RankOne.concreteTarget hA hsigma I) where
  scale := scale I
  region := fun v => CorrMove.longBox v.1 (scale I v : Int) axis sigma A
  face := fun v => CorrMove.longFace v.1 (scale I v : Int) axis sigma A
  scale_ge := radius_le_scale I
  region_subset_active := fun v => (scale_spec I v).2.1
  face_subset_target := fun v => (scale_spec I v).2.2
  source_subset_region := source_subset_longBox hlarge hsigma hA I
  hit_valid := fun v => by
    have hbeta0 : 0 < etaOf alpha := etaOf_pos ha0
    have hbeta1 : etaOf alpha ≤ 1 := etaOf_le_one ha0 ha1
    have hmacro : ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ macroScale I v := by
      have hRs := radius_le_scale I v
      unfold macroScale
      omega
    have hhit := ExactLongBoxHitBridge.VariableBridge.translated_hit hp0 hp1 F hA
      hbeta0 hbeta1 v.1 axis sigma hsigma
      (ExactLongBoxHitBridge.RankOne.sourceRadius F) (macroScale I v) (remainder I v)
      (by unfold ExactLongBoxHitBridge.RankOne.sourceRadius; omega)
      (remainder_le I v) hmacro
    have hcast : (LongBoxVariable.longScale (macroScale I v) (remainder I v) : Int) =
        (scale I v : Int) := by rw [scale_eq]
    simpa [siteBernoulli, ExactLongBoxHitBridge.RankOne.params,
      ExactTargetPlan.ConstructorParams.eta, ExactTargetPlan.ConstructorParams.delta,
      ExactTargetPlan.ConstructorParams.deltaC, etaOf, deltaOf, deltaCOf, hcast] using hhit

/-- A transparent exact rank-one plan with a translation-equivariant T4 selector. -/
def buildPlan
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    {R : Nat} (hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R)
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma) :
    ExactTargetPlan.Plan d :=
  ExactTargetPlan.buildPlan (ExactLongBoxHitBridge.RankOne.params F N R)
    (ExactLongBoxHitBridge.RankOne.concreteTarget hA hsigma I)
    (concreteHits hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I)

theorem buildPlan_wellFormed
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    {R : Nat} (hR : N.R0 ≤ R)
    (hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R)
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).WellFormed := by
  exact ExactTargetPlan.buildPlan_wellFormed _
    (ExactLongBoxHitBridge.RankOne.params_admissible hp0 hp1 ha0 ha1 F N R hR) _ _

theorem buildPlan_validAt
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    {R : Nat} (hR : N.R0 ≤ R)
    (hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R)
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).ValidAt p0 := by
  exact ExactTargetPlan.buildPlan_validAt _
    (ExactLongBoxHitBridge.RankOne.params_admissible hp0 hp1 ha0 ha1 F N R hR) _ _

/-- Revalidate a canonical rank-one plan at a later parameter from its three kinds of literal
leaf bounds.  This is the leafwise interface used after translation: it avoids claiming equality
of the implementation-specific `Fintype.equivFin` enumerations of two translated boxes. -/
theorem buildPlan_validAt_of
    (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : ExactTargetSchemeNumbers.Numbers d p0 alpha
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    {R : Nat} (hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R)
    (I : ExactLongBoxHitBridge.RankOne.Instantiation F N R axis sigma)
    {q : unitInterval} (hq0 : 0 < (q : Real)) (hqp : (q : Real) ≤ (p0 : Real))
    (hhit : ∀ v,
      (ExactTargetPlan.hitBound
        (ExactLongBoxHitBridge.RankOne.params F N R)
        (ExactLongBoxHitBridge.RankOne.concreteTarget hA hsigma I)
        (concreteHits hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I) v).HoldsAt q)
    (hseed : (ExactTargetPlan.seedBound
      (ExactLongBoxHitBridge.RankOne.params F N R)).HoldsAt q)
    (hbarrier : (ExactTargetPlan.barrierBound
      (ExactLongBoxHitBridge.RankOne.params F N R)).HoldsAt q) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).ValidAt q := by
  let P := ExactLongBoxHitBridge.RankOne.params F N R
  let X := ExactLongBoxHitBridge.RankOne.concreteTarget hA hsigma I
  let H := concreteHits hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I
  change 0 < (q : Real) ∧ (q : Real) ≤ (p0 : Real) ∧
    ∀ l : Fin (Fintype.card ((X.sourceBox.inflate P.radius).sites) + 2),
      ((ExactTargetPlan.buildPlan P X H).leaf l).HoldsAt q
  refine ⟨hq0, hqp, ?_⟩
  intro l
  refine Fin.addCases (fun j => ?_) (fun j => ?_) l
  · let v : (X.sourceBox.inflate P.radius).sites :=
      (Fintype.equivFin ((X.sourceBox.inflate P.radius).sites)).symm j
    have hj : (ExactTargetPlan.buildPlan P X H).hitLeaf v = Fin.castAdd 2 j := by
      apply Fin.ext
      change ((Fintype.equivFin ((X.sourceBox.inflate P.radius).sites)) v).val = j.val
      simp [v]
    rw [← hj, ExactTargetPlan.buildPlan_hitLeaf]
    exact hhit v
  · fin_cases j
    · change ((ExactTargetPlan.buildPlan P X H).leaf
        (ExactTargetPlan.buildPlan P X H).seedLeaf).HoldsAt q
      rw [ExactTargetPlan.buildPlan_seedLeaf]
      exact hseed
    · change ((ExactTargetPlan.buildPlan P X H).leaf
        (ExactTargetPlan.buildPlan P X H).barrierLeaf).HoldsAt q
      rw [ExactTargetPlan.buildPlan_barrierLeaf]
      exact hbarrier

end CanonicalRankOne

/-! ## Shared frozen stopped data

The macro constructor and the uniform stability argument must use the *same* extracted object.
The transparent translated-plan input already has exactly the required fields, so this is an
abbreviation rather than a second, potentially inconsistent choice of schemes and numbers. -/

abbrev FrozenStoppedData (d : Nat) [NeZero d] (p0 : unitInterval) (K : Nat) :=
  ExactLongBoxTranslatedPlan.Inputs d p0 (ExactMacroNumerics.deltaC d) K

/-- Supercriticality freezes one concrete aspect-`2K` scheme, its canonical numerical leaves,
and their common radius. -/
theorem exists_frozenStoppedData_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (K : Nat) (hK : 1 ≤ K) : Nonempty (FrozenStoppedData d p0 K) := by
  have hdeltaC_le_one : ExactMacroNumerics.deltaC d ≤ 1 := by
    calc
      ExactMacroNumerics.deltaC d ≤ ExactMacroNumerics.rho / 2 :=
        ExactMacroNumerics.deltaC_le_rho_half d
      _ ≤ 1 := by linarith [ExactMacroNumerics.rho_le_half]
  exact ExactLongBoxTranslatedPlan.exists_inputs_of_thetaSite_pos
    p0 hp0 hp1 htheta (ExactMacroNumerics.deltaC_pos d) hdeltaC_le_one hK

namespace FrozenStoppedData

/-- One stopped child built with the least admissible long-box length at every source-plus site. -/
def plan
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) : ExactTargetPlan.Plan d :=
  CanonicalRankOne.buildPlan hp0 hp1 (ExactMacroNumerics.deltaC_pos d)
    (by linarith [ExactMacroNumerics.deltaC_le_rho_half d,
      ExactMacroNumerics.rho_le_half])
    (by omega : 1 ≤ 2 * K) D.family D.numbers i sigma hsigma D.radius_large
    (ExactLongBoxTranslatedPlan.instantiation D z y i hsigma hK hs hr hscale hemb
      a.val a.isLt)

theorem plan_wellFormed
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).WellFormed := by
  exact CanonicalRankOne.buildPlan_wellFormed hp0 hp1
    (ExactMacroNumerics.deltaC_pos d)
    (by linarith [ExactMacroNumerics.deltaC_le_rho_half d,
      ExactMacroNumerics.rho_le_half])
    (by omega : 1 ≤ 2 * K) D.family D.numbers i sigma hsigma D.radius_ge
    D.radius_large
    (ExactLongBoxTranslatedPlan.instantiation D z y i hsigma hK hs hr hscale hemb
      a.val a.isLt)

theorem plan_validAt_p0
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).ValidAt p0 := by
  exact CanonicalRankOne.buildPlan_validAt hp0 hp1
    (ExactMacroNumerics.deltaC_pos d)
    (by linarith [ExactMacroNumerics.deltaC_le_rho_half d,
      ExactMacroNumerics.rho_le_half])
    (by omega : 1 ≤ 2 * K) D.family D.numbers i sigma hsigma D.radius_ge
    D.radius_large
    (ExactLongBoxTranslatedPlan.instantiation D z y i hsigma hK hs hr hscale hemb
      a.val a.isLt)

@[simp] theorem plan_active
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).active =
      ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val := by
  exact ExactStoppedG2.DIntBox_sites_eq _ _ hsigma _ _ _

@[simp] theorem plan_source
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r t s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)) := by
  exact ExactStoppedG2.faceIntBox_sites_eq _ _ hsigma _ _ _

@[simp] theorem plan_target
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).target =
      CoreRes.target (d := d) r y := rfl

@[simp] theorem plan_radius
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).radius = D.radius := rfl

@[simp] theorem plan_epsilon
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).epsilon =
      ExactMacroNumerics.deltaC d := rfl

@[simp] theorem plan_delta
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).delta =
      deltaOf (ExactMacroNumerics.deltaC d) := rfl

/-- The literal finite family shared by macro assembly and parameter stability. -/
def planFamily
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    Fin K → ExactTargetPlan.Plan d := fun a =>
  plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a

/-- Deterministically instantiate the shared frozen data on one literal oriented stopped head. -/
def children
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r t s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (ht : 5 * r ≤ t) (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma
      (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.delta2 d) :=
  ExactStoppedG2.stoppedChildren hsigma
    (by rw [hr]; exact Nat.mul_pos (by omega) hs) ht hemb
    (planFamily hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb)
    (fun a => plan_wellFormed hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a)
    (fun a => plan_active hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a)
    (fun a => plan_source (t := t) hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a)
    (fun a => by
      change (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).target ⊆ _
      rw [plan_target hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a])
    (fun a => by
      change ExactMacroNumerics.delta2 d ≤
        (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).delta
      rw [plan_delta hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a]
      exact ExactMacroNumerics.delta2_le_targetDelta d)
    (fun a => by
      change (plan hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a).epsilon ≤ _
      rw [plan_epsilon hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a])

/-- The exact plan family seen by stability and the one stored in `children` are definitionally
the same family. -/
@[simp] theorem children_plan
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r t s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (ht : 5 * r ≤ t) (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (a : Fin K) :
    (children hp0 hp1 D hK z y i sigma hs hr hscale ht hsigma hemb).plan a =
      planFamily hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a := rfl

/-- Every leaf of the shared frozen family is valid at its extraction parameter `p0`.  No claim
at a later parameter is bundled into the data. -/
theorem children_validAt_p0
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K r t s : Nat} (D : FrozenStoppedData d p0 K) (hK : 20 ≤ K)
    (z y : Site 2) (i : Fin d) (sigma : Int)
    (hs : 0 < s) (hr : r = K * s) (hscale : 2 * D.radius ≤ s)
    (ht : 5 * r ≤ t) (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    ∀ a, ((children hp0 hp1 D hK z y i sigma hs hr hscale ht hsigma hemb).plan a).ValidAt p0 := by
  intro a
  rw [children_plan]
  exact plan_validAt_p0 hp0 hp1 D hK z y i sigma hs hr hscale hsigma hemb a

end FrozenStoppedData

/-- The finite data frozen before the macro geometry is chosen.  Keeping `F` and `N` visible is
important for the later finite-cylinder stability argument: that argument may inspect the
actual scheme and canonical seed/barrier tables, rather than reconstructing them after choosing
the smaller parameter. -/
theorem exists_frozenPlanData_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (K : Nat) (hK : 1 ≤ K) :
    ∃ F : ExactLongBoxVariablePlan.SchemeFamily d p0
        (etaOf (ExactMacroNumerics.deltaC d)) (2 * K),
      ∃ N : ExactTargetSchemeNumbers.Numbers d p0 (ExactMacroNumerics.deltaC d)
          (ExactLongBoxHitBridge.RankOne.sourceRadius F),
        ∃ R : Nat, 0 < R ∧ N.R0 ≤ R ∧
          8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R := by
  have hdeltaC_le_one : ExactMacroNumerics.deltaC d ≤ 1 := by
    calc
      ExactMacroNumerics.deltaC d ≤ ExactMacroNumerics.rho / 2 :=
        ExactMacroNumerics.deltaC_le_rho_half d
      _ ≤ 1 := by linarith [ExactMacroNumerics.rho_le_half]
  obtain ⟨F⟩ := ExactLongBoxVariablePlan.exists_stoppedSchemeFamily_of_thetaSite_pos
    (d := d) p0 hp0 hp1 htheta (etaOf (ExactMacroNumerics.deltaC d))
      (etaOf_pos (ExactMacroNumerics.deltaC_pos d))
      (etaOf_le_one (ExactMacroNumerics.deltaC_pos d) hdeltaC_le_one) K hK
  have hm : 0 < ExactLongBoxHitBridge.RankOne.sourceRadius F := by
    unfold ExactLongBoxHitBridge.RankOne.sourceRadius
    omega
  obtain ⟨N⟩ := ExactTargetSchemeNumbers.exists_numbers (d := d)
    p0 hp0 hp1 (ExactMacroNumerics.deltaC d) (ExactMacroNumerics.deltaC_pos d)
      hdeltaC_le_one (ExactLongBoxHitBridge.RankOne.sourceRadius F) hm
  let R : Nat := max N.R0 (8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F)
  have hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R :=
    le_max_right _ _
  have hthreshold : 0 < ExactLongBoxHitBridge.RankOne.scaleThreshold F := by
    unfold ExactLongBoxHitBridge.RankOne.scaleThreshold
    omega
  exact ⟨F, N, R,
    lt_of_lt_of_le (Nat.mul_pos (by omega) hthreshold) hlarge,
    le_max_left _ _, hlarge⟩

/-- Instantiate the already frozen finite tables on one literal stopped head.  The conclusion
states `ValidAt p0` and nothing about a later `q`; parameter transport remains a separate finite
stability step. -/
theorem exists_stoppedChildren_from_frozenPlanData
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {K R r t s : Nat} (hK : 20 ≤ K)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0
      (etaOf (ExactMacroNumerics.deltaC d)) (2 * K))
    (N : ExactTargetSchemeNumbers.Numbers d p0 (ExactMacroNumerics.deltaC d)
      (ExactLongBoxHitBridge.RankOne.sourceRadius F))
    (hNR : N.R0 ≤ R)
    (hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R)
    (hs : 0 < s) (hr : r = K * s) (hR : 2 * R ≤ s) (ht : 5 * r ≤ t)
    {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    ∃ G : ExactMacroGeometry.StoppedChildren (d := d)
        r t s K z y i sigma (ExactMacroNumerics.deltaC d)
          (ExactMacroNumerics.delta2 d),
      (∀ a, (G.plan a).ValidAt p0) ∧
      (∀ a, (G.plan a).radius = R) ∧
      (∀ a, (G.plan a).epsilon = ExactMacroNumerics.deltaC d) ∧
      (∀ a, (G.plan a).active =
        ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
      (∀ a, (G.plan a).source =
        Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
      ∀ a, (G.plan a).target = CoreRes.target (d := d) r y := by
  have hdeltaC_le_one : ExactMacroNumerics.deltaC d ≤ 1 := by
    calc
      ExactMacroNumerics.deltaC d ≤ ExactMacroNumerics.rho / 2 :=
        ExactMacroNumerics.deltaC_le_rho_half d
      _ ≤ 1 := by linarith [ExactMacroNumerics.rho_le_half]
  exact exists_stoppedChildren_from_scheme hp0 hp1
    (ExactMacroNumerics.deltaC_pos d) hdeltaC_le_one hK F N hNR hlarge
      hs hr hR ht hsigma hemb (ExactMacroNumerics.delta2_le_targetDelta d) le_rfl

/-- Positive percolation extracts one common rank-one radius.  At every later macro scale
satisfying the explicit G2 inequalities, and for every actual oriented head, that same radius
produces all `K` literal stopped children.  Thus the probabilistic extraction is performed once;
the remaining arguments are only deterministic arithmetic, geometry, and error comparisons. -/
theorem exists_stoppedChildren_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (alpha : Real) (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (K : Nat) (hK : 20 ≤ K) :
    ∃ R : Nat, 0 < R ∧
      ∀ {r t s : Nat}, 0 < s → r = K * s → 2 * R ≤ s → 5 * r ≤ t →
      ∀ {z y : Site 2} {i : Fin d} {sigma : Int},
        sigma = 1 ∨ sigma = -1 →
        (MacroExp.emb (y - z) : Site d) = Pi.single i sigma →
      ∀ {deltaC delta2 : Real}, delta2 ≤ deltaOf alpha → alpha ≤ deltaC →
      ∃ G : ExactMacroGeometry.StoppedChildren (d := d)
          r t s K z y i sigma deltaC delta2,
        (∀ a, (G.plan a).ValidAt p0) ∧
        (∀ a, (G.plan a).radius = R) ∧
        (∀ a, (G.plan a).epsilon = alpha) ∧
        (∀ a, (G.plan a).active =
          ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
        (∀ a, (G.plan a).source =
          Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
        ∀ a, (G.plan a).target = CoreRes.target (d := d) r y := by
  obtain ⟨F⟩ := ExactLongBoxVariablePlan.exists_stoppedSchemeFamily_of_thetaSite_pos
    (d := d) p0 hp0 hp1 htheta (etaOf alpha) (etaOf_pos ha0)
      (etaOf_le_one ha0 ha1) K (by omega)
  have hm : 0 < ExactLongBoxHitBridge.RankOne.sourceRadius F := by
    unfold ExactLongBoxHitBridge.RankOne.sourceRadius
    omega
  obtain ⟨N⟩ := ExactTargetSchemeNumbers.exists_numbers (d := d)
    p0 hp0 hp1 alpha ha0 ha1 (ExactLongBoxHitBridge.RankOne.sourceRadius F) hm
  let R : Nat := max N.R0 (8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F)
  have hNR : N.R0 ≤ R := by
    exact le_max_left _ _
  have hlarge : 8 * ExactLongBoxHitBridge.RankOne.scaleThreshold F ≤ R := by
    exact le_max_right _ _
  have hthreshold : 0 < ExactLongBoxHitBridge.RankOne.scaleThreshold F := by
    unfold ExactLongBoxHitBridge.RankOne.scaleThreshold
    omega
  have hRpos : 0 < R := by
    exact lt_of_lt_of_le (Nat.mul_pos (by omega) hthreshold) hlarge
  refine ⟨R, hRpos, ?_⟩
  intro r t s hs hr hR ht z y i sigma hsigma hemb deltaC delta2 hdelta hepsilon
  exact exists_stoppedChildren_from_scheme hp0 hp1 ha0 ha1 hK F N hNR hlarge
    hs hr hR ht hsigma hemb hdelta hepsilon

/-- The stopped extractor specialized to the numerical parameters of the v15 macro step.  The
target-plan output error is exactly `deltaC d`, and its input tolerance dominates the stopped
tower parameter `delta2 d`; hence neither comparison remains as an input. -/
theorem exists_frozen_stoppedChildren_of_thetaSite_pos
    (p0 : unitInterval) (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    (htheta : 0 < thetaSite d p0)
    (K : Nat) (hK : 20 ≤ K) :
    ∃ R : Nat, 0 < R ∧
      ∀ {r t s : Nat}, 0 < s → r = K * s → 2 * R ≤ s → 5 * r ≤ t →
      ∀ {z y : Site 2} {i : Fin d} {sigma : Int},
        sigma = 1 ∨ sigma = -1 →
        (MacroExp.emb (y - z) : Site d) = Pi.single i sigma →
      ∃ G : ExactMacroGeometry.StoppedChildren (d := d)
          r t s K z y i sigma (ExactMacroNumerics.deltaC d)
            (ExactMacroNumerics.delta2 d),
        (∀ a, (G.plan a).ValidAt p0) ∧
        (∀ a, (G.plan a).radius = R) ∧
        (∀ a, (G.plan a).epsilon = ExactMacroNumerics.deltaC d) ∧
        (∀ a, (G.plan a).active =
          ExactStoppedG2.Dbox (MacroExp.ctr d r z) i sigma r s a.val) ∧
        (∀ a, (G.plan a).source =
          Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1))) ∧
        ∀ a, (G.plan a).target = CoreRes.target (d := d) r y := by
  obtain ⟨F, N, R, hR, hNR, hlarge⟩ :=
    exists_frozenPlanData_of_thetaSite_pos p0 hp0 hp1 htheta K (by omega)
  refine ⟨R, hR, ?_⟩
  intro r t s hs hr hscale ht z y i sigma hsigma hemb
  exact exists_stoppedChildren_from_frozenPlanData hp0 hp1 hK F N hNR hlarge
    hs hr hscale ht hsigma hemb

end Concrete

#print axioms KNAll.Site.ExactStoppedChildrenExtraction.assemble
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.assemble_validAt
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.exists_children_of_plans
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.coreTarget_subset_Dbox
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.instantiation
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.CanonicalRankOne.scale
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.CanonicalRankOne.scale_translate
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.CanonicalRankOne.region_translate
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.CanonicalRankOne.face_translate
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.CanonicalRankOne.buildPlan
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.CanonicalRankOne.buildPlan_validAt
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.CanonicalRankOne.buildPlan_validAt_of
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.exists_stoppedChildren_from_scheme
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.exists_stoppedChildren_of_thetaSite_pos
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.exists_frozenStoppedData_of_thetaSite_pos
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.FrozenStoppedData.plan
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.FrozenStoppedData.planFamily
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.FrozenStoppedData.children
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.FrozenStoppedData.children_validAt_p0
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.exists_frozenPlanData_of_thetaSite_pos
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.exists_stoppedChildren_from_frozenPlanData
#print axioms KNAll.Site.ExactStoppedChildrenExtraction.Concrete.exists_frozen_stoppedChildren_of_thetaSite_pos

end KNAll.Site.ExactStoppedChildrenExtraction

end
