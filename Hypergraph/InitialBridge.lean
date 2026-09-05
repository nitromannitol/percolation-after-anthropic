import Hypergraph.InitialEntrance

/-!
# The recorded initial corridor is the initial-entrance corridor

`Certificate2` records the initial long-box cylinder using primitive numerical parameters, while
`InitEnt` spells its target as the innermost level box.  Well-formedness makes the two targets,
and hence the two cylinder experiments, equal.

`hinitialLongBox_holds` is the H1 input of `Assembly.site_no_percolation_at_criticality`.  Its
proof chain is

```
Certificate2.WellFormed.wideLongBox_mem
  → hwideLongBox_of_wellFormed
  → InitEnt.initial_entrance
  → hinitialLongBox_holds
```

and it mentions neither `MacroExp.src`, nor `MacroExp.Good`, nor any premise of the form
`src ∈ openSites`.  Its source is the recorded origin, its entrance is the whole face
`InitEnt.entryFace`, and the wide long-box experiment is itself the certificate entry.  Its
independence from the retired fixed-tip theorems is therefore structural: the only inputs after
fixing `d` are `3 ≤ d`, `C.WellFormed` and `C.ValidAt2 q`.

The `example` at the end of this file is the machine-checked statement that
`hinitialLongBox_holds` *is* the family `RecordedEntry.PendingOriginSourceEstimates` at the start
transcript.  It is left as an `example` on purpose: naming it would make the interface read as an
established proposition, whereas the family at an accepted transcript, which is what the
exploration consumes, is proved nowhere and is the remaining H2 obligation.
-/

noncomputable section

namespace KNAll.Site.InitBridge

set_option linter.unusedSectionVars false

open MeasureTheory Set
open Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.LeftImp2

variable {d : ℕ} [NeZero d]

/-- The primitive target recorded in `Certificate2` is the innermost level box used by
`InitEnt`.  Positivity of `levels` removes the truncated `levels - 1` edge case, and
`innerRadius_ge` makes both natural-number radius subtractions untruncated. -/
theorem initialCorridorTarget_eq_innerBox
    (C : Certificate2 d) (hwf : C.WellFormed) (y : Site 2) :
    initialCorridorTarget d C.levels C.faceTarget C.corridor C.halfWidth y =
      LongBox.innerBox C (MacroExp.ctr d C.corridor y) := by
  rw [initialCorridorTarget, Corridor.abox_eq_rbox]
  unfold LongBox.innerBox Corridor.Ibox
  congr 1
  funext j
  have hL := hwf.levels_pos
  have hr : C.levels + 2 * C.faceTarget + 1 ≤ C.corridor :=
    le_trans hwf.innerRadius_ge (min_le_left _ _)
  have ht : C.levels + 2 * C.faceTarget + 1 ≤ C.halfWidth :=
    le_trans hwf.innerRadius_ge (min_le_right _ _)
  simp only [Corridor.ρI, Corridor.ρO, Corridor.ρD, Corridor.scalesOf, MacroExp.rad]
  split <;> push_cast <;> omega

/-- The primitive-parameter cylinder stored in a certificate is exactly the downstream
`InitEnt` cylinder. -/
theorem wideLongBoxExperiment_eq
    (C : Certificate2 d) (hwf : C.WellFormed) (y : Site 2) :
    C.wideLongBoxExperiment y =
      InitEnt.wideLongBoxExperiment C C.corridor C.halfWidth y := by
  unfold Certificate2.wideLongBoxExperiment rawWideLongBoxExperiment
  unfold InitEnt.wideLongBoxExperiment
  rw [CylinderExperiment.mk.injEq]
  refine ⟨rfl, ?_⟩
  ext omega
  simp only [LeftImp2.wideLongBoxEvent, InitEnt.wideLongBoxEvent, Set.mem_setOf_eq]
  rw [initialCorridorTarget_eq_innerBox C hwf y]
  simp only [initialCorridorEntryFace, InitEnt.entryFace]

/-- `WellFormed.wideLongBox_mem`, rewritten into the spelling consumed by `InitEnt`. -/
theorem hwideLongBox_of_wellFormed :
    ∀ (C : Certificate2 d), C.WellFormed → 3 ≤ d →
      ∀ y ∈ MacroExp.nbrs (0 : Site 2),
        (InitEnt.wideLongBoxExperiment C C.corridor C.halfWidth y,
          1 - C.eps / 8) ∈ C.bounds := by
  intro C hwf hd y hy
  rw [← wideLongBoxExperiment_eq C hwf y]
  exact hwf.wideLongBox_mem hd y hy

/-- The exact initial-long-box hypothesis of the final assembly, with no probabilistic or
geometric hypothesis beyond `3 ≤ d`. -/
theorem hinitialLongBox_holds (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∀ (C : Certificate2 d) (q : unitInterval),
      C.WellFormed → C.ValidAt2 q →
      ∀ y ∈ MacroExp.pending d
          (MacroExp.start d C.corridor C.halfWidth) 0,
        1 - C.eps / 8 <
          (MacroExp.start d C.corridor C.halfWidth).prob
            (fun _ : Site d => q)
            (connWithinSet (zdGraph d)
              (↑((MacroExp.start d C.corridor C.halfWidth).inspected ∪
                MacroExp.E d C.corridor C.halfWidth 0 y) : Set (Site d))
              (MacroExp.emb 0)
              (↑(LongBox.innerBox C (MacroExp.ctr d C.corridor y)) : Set (Site d))) := by
  exact InitEnt.initial_entrance d hd fun C hwf y hy =>
    hwideLongBox_of_wellFormed C hwf hd y hy

/-- **The initial source estimate, in the named interface.**  This is `hinitialLongBox_holds`,
read as the origin-based family of `KN/SourceEstimate.lean` at the start transcript with the
innermost level boxes as targets.  The two statements are definitionally the same, so the term
below is the proof.

It is the machine-checked witness that the interface is satisfiable at a genuine corridor-crossing
target, and hence not vacuous.  It says nothing about any later transcript. -/
example (d : ℕ) [NeZero d] (hd : 3 ≤ d) (C : Certificate2 d) (q : unitInterval)
    (hwf : C.WellFormed) (hv : C.ValidAt2 q) :
    RecordedEntry.PendingOriginSourceEstimates C q C.corridor C.halfWidth
      (MacroExp.start d C.corridor C.halfWidth) 0
      (fun y => (↑(LongBox.innerBox C (MacroExp.ctr d C.corridor y)) : Set (Site d))) :=
  hinitialLongBox_holds d hd C q hwf hv

#print axioms KNAll.Site.InitBridge.hwideLongBox_of_wellFormed
#print axioms KNAll.Site.InitBridge.hinitialLongBox_holds

end KNAll.Site.InitBridge

end
