import Hypergraph.CoreStoppedReveal

/-!
# Explicit centre-aware direction maps

The direction of an outgoing head is intrinsically a function of the ordered pair `(z,y)`.
This module gives completely explicit total maps after fixing `z`, and proves the exact sign and
embedded-singleton statements for every actual `newHead`.

The public maps below are total functions of the ordered pair `(z,y)`.  The accepted scheduler
specializes them at its current centre before running the fixed-centre stopped interpreter.
-/

noncomputable section

namespace KNAll.Site.ExactDirectionMaps

open Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- Include one of the two planar coordinate indices into `Fin d`. -/
def planeAxis (hd : 2 ≤ d) (i : Fin 2) : Fin d :=
  ⟨i.val, i.isLt.trans_le hd⟩

/-- Explicit total axis of `y-z`: use coordinate zero if it is nonzero, and coordinate one
otherwise.  On a planar nearest-neighbour pair exactly one of these coordinates is `±1`. -/
def axisFrom (hd : 2 ≤ d) (z : Site 2) : Site 2 → Fin d := fun y =>
  if (y - z) (0 : Fin 2) ≠ 0 then planeAxis hd 0 else planeAxis hd 1

/-- Explicit total sign of `y-z`, read in the coordinate selected by `axisFrom`. -/
def signFrom (z : Site 2) : Site 2 → Int := fun y =>
  if (y - z) (0 : Fin 2) ≠ 0 then (y - z) (0 : Fin 2) else (y - z) (1 : Fin 2)

/-- Total centre-aware axis map used by the accepted exploration. -/
def axis (hd : 2 ≤ d) : Site 2 → Site 2 → Fin d := axisFrom hd

/-- Total centre-aware sign map used by the accepted exploration. -/
def sign : Site 2 → Site 2 → Int := signFrom

@[simp] theorem axis_apply (hd : 2 ≤ d) (z y : Site 2) :
    axis hd z y = axisFrom hd z y := rfl

@[simp] theorem sign_apply (z y : Site 2) : sign z y = signFrom z y := rfl

@[simp] theorem planeAxis_val (hd : 2 ≤ d) (i : Fin 2) :
    (planeAxis hd i).val = i.val := rfl

/-- Embedding a planar coordinate singleton is the same singleton at the included axis. -/
theorem emb_plane_single (hd : 2 ≤ d) (i : Fin 2) (sigma : Int) :
    (MacroExp.emb (Pi.single i sigma) : Site d) =
      Pi.single (planeAxis hd i) sigma := by
  funext j
  by_cases hj : j.val < 2
  · rw [MacroExp.emb_apply_of_lt _ hj]
    by_cases hji : (⟨j.val, hj⟩ : Fin 2) = i
    · have hjaxis : j = planeAxis hd i := by
        apply Fin.ext
        exact congrArg (fun k : Fin 2 => k.val) hji
      simp [Pi.single_apply, hji, hjaxis]
    · have hjaxis : j ≠ planeAxis hd i := by
        intro heq
        apply hji
        apply Fin.ext
        exact congrArg (fun k : Fin d => k.val) heq
      simp [Pi.single_apply, hji, hjaxis]
  · rw [MacroExp.emb_apply_of_not_lt _ hj, Pi.single_apply, if_neg]
    intro heq
    apply hj
    rw [heq]
    exact i.isLt

/-- The explicit sign is a unit sign on every macro-neighbour. -/
theorem signFrom_unit (hd : 2 ≤ d) {z y : Site 2}
    (hy : y ∈ MacroExp.nbrs z) :
    signFrom z y = 1 ∨ signFrom z y = -1 := by
  obtain ⟨i, b, rfl⟩ := MacroExp.mem_nbrs_iff.1 hy
  fin_cases i <;> cases b <;>
    simp [signFrom, MacroExp.mvUnit, Pi.single_apply]

/-- The explicit pair-dependent direction gives the literal embedded coordinate singleton. -/
theorem emb_sub_eq_single (hd : 2 ≤ d) {z y : Site 2}
    (hy : y ∈ MacroExp.nbrs z) :
    (MacroExp.emb (y - z) : Site d) =
      Pi.single (axisFrom hd z y) (signFrom z y) := by
  obtain ⟨i, b, rfl⟩ := MacroExp.mem_nbrs_iff.1 hy
  fin_cases i <;> cases b <;>
    simp [axisFrom, signFrom, planeAxis, MacroExp.mvUnit, Pi.single_apply,
      emb_plane_single hd]

/-- Every new head is a macro-neighbour of the centre that creates it. -/
theorem newHead_mem_nbrs {h : MacroExp.Tr d} {z y : Site 2}
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    y ∈ MacroExp.nbrs z :=
  ((MacroExp.mem_pending (d := d)).1
    (((CoreFrontier.mem_newHeads (d := d)).1 hy).1)).1

/-- Exact local sign clause consumed by a stopped direction at centre `z`. -/
theorem signFrom_newHead (hd : 2 ≤ d) {h : MacroExp.Tr d} {z y : Site 2}
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    signFrom z y = 1 ∨ signFrom z y = -1 :=
  signFrom_unit hd (newHead_mem_nbrs hy)

/-- Exact local embedded-direction clause consumed by a stopped direction at centre `z`. -/
theorem emb_sub_eq_single_newHead (hd : 2 ≤ d)
    {h : MacroExp.Tr d} {z y : Site 2}
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    (MacroExp.emb (y - z) : Site d) =
      Pi.single (axisFrom hd z y) (signFrom z y) :=
  emb_sub_eq_single hd (newHead_mem_nbrs hy)

/-- If the macro origin is already open, an actual new head is not the origin. -/
theorem newHead_ne_zero {h : MacroExp.Tr d} {z y : Site 2}
    (hzero : (0 : Site 2) ∈ h.openV)
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) : y ≠ 0 := by
  intro hy0
  subst y
  exact CoreFrontier.newHead_not_mem_openV (d := d) hy hzero

/-- Quantified pair of local direction clauses for all actual new heads of one centre. -/
theorem forall_newHeads (hd : 2 ≤ d) (h : MacroExp.Tr d) (z : Site 2) :
    (∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      signFrom z y = 1 ∨ signFrom z y = -1) ∧
    (∀ y ∈ CoreFrontier.newHeads (d := d) h z,
      (MacroExp.emb (y - z) : Site d) =
        Pi.single (axisFrom hd z y) (signFrom z y)) := by
  exact ⟨fun _ hy => signFrom_newHead hd hy,
    fun _ hy => emb_sub_eq_single_newHead hd hy⟩

/-- Runtime-centre spelling of the local scheduler clauses at an accepted transcript. -/
theorem forall_newHeads_at_centre (hd : 2 ≤ d)
    {r t n : Nat} {q : unitInterval} {eps : Real}
    (base : BDDom.Transcript (Site d) (Site 2))
    (_hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n)
      r t q eps base)
    (_hactive : ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n)) :
    (∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
      signFrom (CoreStoppedReveal.centre n base) y = 1 ∨
        signFrom (CoreStoppedReveal.centre n base) y = -1) ∧
    (∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
      (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
        Pi.single (axisFrom hd (CoreStoppedReveal.centre n base) y)
          (signFrom (CoreStoppedReveal.centre n base) y)) :=
  forall_newHeads hd base.base (CoreStoppedReveal.centre n base)

/-- The exact globally quantified sign premise of the accepted exploration. -/
theorem scheduler_sign (hd : 2 ≤ d)
    {r t n : Nat} {q : unitInterval} {eps : Real} :
    ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1 := by
  intro base _hadm _hactive y hy
  exact signFrom_newHead hd hy

/-- The exact globally quantified embedded-singleton premise of the accepted exploration. -/
theorem scheduler_emb (hd : 2 ≤ d)
    {r t n : Nat} {q : unitInterval} {eps : Real} :
    ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis hd (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y) := by
  intro base _hadm _hactive y hy
  exact emb_sub_eq_single_newHead hd hy

/-- Every runtime new head is nonzero under the accepted pre-reveal invariant. -/
theorem scheduler_head_ne_zero
    {r t n : Nat} {q : unitInterval} {eps : Real}
    {base : BDDom.Transcript (Site d) (Site 2)}
    (hadm : CoreAcceptedTransition.Admissible (d := d) (box 2 n)
      r t q eps base)
    {y : Site 2}
    (hy : y ∈ CoreFrontier.newHeads (d := d) base.base
      (CoreStoppedReveal.centre n base)) : y ≠ 0 :=
  newHead_ne_zero hadm.preReveal.zero_open hy

#print axioms KNAll.Site.ExactDirectionMaps.signFrom_unit
#print axioms KNAll.Site.ExactDirectionMaps.emb_sub_eq_single
#print axioms KNAll.Site.ExactDirectionMaps.forall_newHeads
#print axioms KNAll.Site.ExactDirectionMaps.forall_newHeads_at_centre
#print axioms KNAll.Site.ExactDirectionMaps.scheduler_sign
#print axioms KNAll.Site.ExactDirectionMaps.scheduler_emb
#print axioms KNAll.Site.ExactDirectionMaps.scheduler_head_ne_zero

end KNAll.Site.ExactDirectionMaps

end
