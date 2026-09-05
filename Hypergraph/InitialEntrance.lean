import Hypergraph.WideEntrance2
import Hypergraph.LongBoxHit

/-!
# The initial wide entrance

At the initial transcript the whole box `Q 0` is inspected and recorded open.  Thus the
appropriate finite experiment has a *set* of fresh sources: all sites of the new corridor which
are adjacent to `Q 0`.  Its source-open event has the exact failure probability
`(1-q)^entryFace.card`, so it has no one-site `q` cap.

Opening the entry face does not by itself cross the long corridor.  The experiment
`wideLongBoxExperiment` records precisely that remaining finite connection: some member of the
entry face connects, inside the fresh corridor, to `LongBox.innerBox`.  The theorem below shows
that listing the four canonical instances of this experiment in `Certificate2.bounds` implies the
initial entrance hypothesis used by `Assembly.site_no_percolation_at_criticality`.
-/

noncomputable section

namespace KNAll.Site.InitEnt

set_option linter.unusedSectionVars false

open MeasureTheory Set
open Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.MacroExp

variable {d : ℕ} [NeZero d]

/-- The fresh outward face of the initial box in direction `y`: all corridor sites adjacent to a
site of the completely open initial box. -/
def entryFace (d r t : ℕ) (y : Site 2) : Finset (Site d) :=
  (E d r t 0 y).filter fun g => ∃ s ∈ Q d r t 0, (zdGraph d).Adj s g

theorem entryFace_subset_E (r t : ℕ) (y : Site 2) :
    entryFace d r t y ⊆ E d r t 0 y := by
  intro g hg
  exact (Finset.mem_filter.1 hg).1

theorem entryFace_adjacent_Q {r t : ℕ} {y : Site 2} {g : Site d}
    (hg : g ∈ entryFace d r t y) :
    ∃ s ∈ Q d r t 0, (zdGraph d).Adj s g :=
  (Finset.mem_filter.1 hg).2

/-- The source-open part of the entrance really is a wide event: its failure is exactly the
probability that every site of the finite entry face is closed. -/
theorem entryFace_prob_eq (r t : ℕ) (y : Site 2) (q : unitInterval) :
    (Wide2.wideEntranceExperiment (entryFace d r t y)).prob q =
      1 - (1 - (q : ℝ)) ^ (entryFace d r t y).card :=
  Wide2.wideEntranceExperiment_prob_eq _ _

/-- In a fresh sample, some member of the wide entry face connects through the corridor to the
innermost box at its head. -/
def wideLongBoxEvent (C : LeftImp2.Certificate2 d) (r t : ℕ) (y : Site 2) :
    Set (SiteConfig (Site d)) :=
  {ω | ∃ g ∈ entryFace d r t y,
    ω ∈ connWithinSet (zdGraph d) (↑(E d r t 0 y) : Set (Site d)) g
      (↑(LongBox.innerBox C (ctr d r y)) : Set (Site d))}

theorem determinedBy_wideLongBoxEvent (C : LeftImp2.Certificate2 d)
    (r t : ℕ) (y : Site 2) :
    DeterminedBy (wideLongBoxEvent C r t y)
      (↑(E d r t 0 y) : Set (Site d)) := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  simp only [wideLongBoxEvent, Set.mem_setOf_eq]
  apply exists_congr
  intro g
  apply and_congr_right
  intro _hg
  exact (determinedBy_iff _ _).1
    (determinedBy_connWithinSet (zdGraph d)
      (↑(E d r t 0 y) : Set (Site d)) g
      (↑(LongBox.innerBox C (ctr d r y)) : Set (Site d))) ω ω' hagree

theorem measurableSet_wideLongBoxEvent (C : LeftImp2.Certificate2 d)
    (r t : ℕ) (y : Site 2) : MeasurableSet (wideLongBoxEvent C r t y) :=
  (determinedBy_wideLongBoxEvent C r t y).measurableSet_of_finset

/-- The finite cylinder which must be added to the certificate for each of the four directions.
Unlike the refuted pinned experiments, its source is the whole entry face, not one designated
fresh site. -/
def wideLongBoxExperiment (C : LeftImp2.Certificate2 d) (r t : ℕ) (y : Site 2) :
    CylinderExperiment d where
  support := E d r t 0 y
  event := wideLongBoxEvent C r t y
  determined := determinedBy_wideLongBoxEvent C r t y
  measurable' := measurableSet_wideLongBoxEvent C r t y

/-- A successful wide long-box experiment necessarily opens at least one member of the entry
face.  Together with `entryFace_prob_eq`, this displays the exact many-site entrance mechanism. -/
theorem wideLongBoxEvent_subset_wideEntranceEvent
    (C : LeftImp2.Certificate2 d) (r t : ℕ) (y : Site 2) :
    wideLongBoxEvent C r t y ⊆ Wide2.wideEntranceEvent (entryFace d r t y) := by
  rintro ω ⟨g, hg, hconn⟩
  refine ⟨g, hg, ?_⟩
  rw [mem_connWithinSet_iff] at hconn
  obtain ⟨b, _hb, hgb⟩ := hconn
  exact hgb.1.1

/-- Transfer the ordinary finite wide-source experiment to the pinned law of the start
transcript.  The proof uses exactly the two special features of `start`: `Q 0` is wholly open, and
`E 0 y` is its set-difference complement and hence fresh. -/
theorem wideLongBoxExperiment_prob_le_start
    (C : LeftImp2.Certificate2 d) (r t : ℕ) (y : Site 2) (q : unitInterval) :
    (wideLongBoxExperiment C r t y).prob q ≤
      (start d r t).prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d)
          (↑((start d r t).inspected ∪ E d r t 0 y) : Set (Site d))
          (emb 0)
          (↑(LongBox.innerBox C (ctr d r y)) : Set (Site d))) := by
  classical
  let h₀ := start d r t
  let Reg := E d r t 0 y
  let B : Set (Site d) := ↑(LongBox.innerBox C (ctr d r y))
  let A : Set (SiteConfig (Site d)) :=
    connWithinSet (zdGraph d) (↑(h₀.inspected ∪ Reg) : Set (Site d)) (emb 0) B
  rw [FRDom.Transcript.prob_eq]
  change (siteBernoulli (fun _ : Site d => q)).real (wideLongBoxEvent C r t y) ≤
    (siteBernoulli (fun _ : Site d => q)).real
      (substitute (↑h₀.inspected : Set (Site d)) h₀.state ⁻¹' A)
  apply measureReal_mono
  · intro ω hω
    change substitute (↑h₀.inspected : Set (Site d)) h₀.state ω ∈ A
    obtain ⟨g, hgFace, hgB⟩ := hω
    obtain ⟨s, hsQ, hsg⟩ := entryFace_adjacent_Q hgFace
    have hgReg : g ∈ Reg := entryFace_subset_E r t y hgFace
    let ω' : SiteConfig (Site d) :=
      substitute (↑h₀.inspected : Set (Site d)) h₀.state ω
    have hfresh : Disjoint Reg h₀.inspected := by
      change Disjoint (E d r t 0 y) (Q d r t 0)
      unfold E
      exact Finset.sdiff_disjoint
    have hagree : ω' ∩ (↑Reg : Set (Site d)) = ω ∩ (↑Reg : Set (Site d)) := by
      ext x
      simp only [Set.mem_inter_iff, Finset.mem_coe]
      by_cases hx : x ∈ Reg
      · have hxI : x ∉ h₀.inspected := fun hxI =>
          Finset.disjoint_left.1 hfresh hx hxI
        rw [mem_substitute_of_notMem h₀.state hxI]
      · simp [hx]
    have hgB' : ω' ∈ connWithinSet (zdGraph d) (↑Reg : Set (Site d)) g B := by
      exact ((determinedBy_iff _ _).1
        (determinedBy_connWithinSet (zdGraph d) (↑Reg : Set (Site d)) g B)
        ω ω' hagree.symm).1 hgB
    obtain ⟨b, hbB, hgb⟩ := (mem_connWithinSet_iff (zdGraph d)
      (↑Reg : Set (Site d)) g B ω').1 hgB'
    have hopenQ : (↑(Q d r t 0) : Set (Site d)) ⊆ ω' := by
      intro x hxQ
      rw [mem_substitute_of_mem h₀.state]
      · exact Finset.mem_coe.1 hxQ
      · exact hxQ
    have hzeroQ : emb (0 : Site 2) ∈ Q d r t 0 :=
      M_subset_Q r t 0 (emb_zero_mem_M r t)
    have hQs : ω' ∈ connWithin (zdGraph d)
        (↑(Q d r t 0) : Set (Site d)) (emb 0) s := by
      change ω' ∈ connWithin (zdGraph d)
        (↑(Corridor.rbox (ctr d r 0) (rad (5 * r) t)) : Set (Site d)) (emb 0) s
      apply Corridor.connWithin_rbox_of_allOpen hopenQ
        (Corridor.dist1 (emb 0) s) (emb 0) s hzeroQ hsQ
      exact le_rfl
    let D : Set (Site d) := ↑(h₀.inspected ∪ Reg)
    have hRegD : (↑Reg : Set (Site d)) ⊆ D := by
      exact Finset.coe_subset.2 Finset.subset_union_right
    have hQD : (↑(Q d r t 0) : Set (Site d)) ⊆ D := by
      exact Finset.coe_subset.2 Finset.subset_union_left
    have hgbD : ω' ∈ connWithin (zdGraph d) D g b :=
      connWithin_mono_set (zdGraph d) hRegD g b hgb
    have hsOpen : s ∈ ω' := hopenQ (Finset.mem_coe.2 hsQ)
    have hsD : s ∈ D := hQD (Finset.mem_coe.2 hsQ)
    have hgD : g ∈ D := hRegD (Finset.mem_coe.2 hgReg)
    have hsgb : ω' ∈ connWithin (zdGraph d) D s b :=
      TargetExt.connWithin_of_adj_of_connWithin (zdGraph d) hsg
        ⟨hsOpen, hsD⟩ ⟨hgb.1.1, hgD⟩ hgbD
    have h0sD : ω' ∈ connWithin (zdGraph d) D (emb 0) s :=
      connWithin_mono_set (zdGraph d) hQD (emb 0) s hQs
    have h0b : ω' ∈ connWithin (zdGraph d) D (emb 0) b :=
      ⟨h0sD.1, h0sD.2.trans hsgb.2⟩
    change ω' ∈ connWithinSet (zdGraph d) D (emb 0) B
    exact (mem_connWithinSet_iff (zdGraph d) D (emb 0) B ω').2 ⟨b, hbB, h0b⟩
  · exact measure_ne_top _ _

/-- **Initial entrance (H1).**  The only added input is the explicit finite certificate clause
`hwideLongBox`: for each of the four origin directions, list
`(wideLongBoxExperiment C C.corridor C.halfWidth y, 1 - C.eps / 8)` in `C.bounds`.
-/
theorem initial_entrance
    (d : ℕ) [NeZero d] (_hd : 3 ≤ d)
    (hwideLongBox : ∀ (C : LeftImp2.Certificate2 d), C.WellFormed →
      ∀ y ∈ MacroExp.nbrs (0 : Site 2),
        (wideLongBoxExperiment C C.corridor C.halfWidth y,
          1 - C.eps / 8) ∈ C.bounds) :
    ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval),
      C.WellFormed → C.ValidAt2 q →
      ∀ y ∈ pending d (start d C.corridor C.halfWidth) 0,
        1 - C.eps / 8 <
          (start d C.corridor C.halfWidth).prob
            (fun _ : Site d => q)
            (connWithinSet (zdGraph d)
              (↑((start d C.corridor C.halfWidth).inspected ∪
                E d C.corridor C.halfWidth 0 y) : Set (Site d))
              (emb 0)
              (↑(LongBox.innerBox C (ctr d C.corridor y)) : Set (Site d))) := by
  intro C q hwf hv y hy
  have hyn : y ∈ MacroExp.nbrs (0 : Site 2) := (mem_pending (d := d)).1 hy |>.1
  exact (hv.1 _ (hwideLongBox C hwf y hyn)).trans_le
    (wideLongBoxExperiment_prob_le_start C C.corridor C.halfWidth y q)

#print axioms KNAll.Site.InitEnt.entryFace_prob_eq
#print axioms KNAll.Site.InitEnt.wideLongBoxExperiment_prob_le_start
#print axioms KNAll.Site.InitEnt.initial_entrance

end KNAll.Site.InitEnt

end
