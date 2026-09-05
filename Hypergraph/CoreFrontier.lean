import Hypergraph.CoreReservation

/-!
# One-owner frontier invariant

The old macro invariant stores a reservation for every oriented edge from every open macro vertex
to every undetermined neighbour.  That is stronger than necessary and is not stable under a
stopped read: two old tails may have the same undetermined head, so their protected regions can
overlap.

This file records the replacement deterministic invariant.  Every frontier vertex has one owner,
and after a new vertex opens we probe only neighbours which were not already frontier vertices.
The elementary update theorem below shows that old owners plus reservations for precisely those
new heads restore the invariant.  A separate geometry lemma proves that an old owned corridor and
a new-head corridor are disjoint.
-/

noncomputable section

namespace KNAll.Site.CoreFrontier

open Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- An undetermined macro vertex adjacent to at least one currently open macro vertex. -/
def Frontier (h : MacroExp.Tr d) (y : Site 2) : Prop :=
  y ∉ h.openV ∪ h.closedV ∧ ∃ u ∈ h.openV, y ∈ MacroExp.nbrs u

/-- A frontier vertex has a particular open owner carrying a core reservation. -/
def HasOwner (r t : Nat) (q : unitInterval) (eps : Real) (h : MacroExp.Tr d)
    (y : Site 2) : Prop :=
  ∃ u ∈ h.openV, y ∈ MacroExp.pending d h u ∧ CoreRes.Bound r t q eps h u y

/-- The recursive probabilistic invariant: one owner is enough for each frontier vertex. -/
def Invariant (r t : Nat) (q : unitInterval) (eps : Real) (h : MacroExp.Tr d) : Prop :=
  ∀ y, Frontier h y → HasOwner r t q eps h y

/-- Neighbours of `z` which become frontier vertices for the first time if `z` is opened. -/
def newHeads (h : MacroExp.Tr d) (z : Site 2) : Finset (Site 2) := by
  classical
  exact (MacroExp.pending d h z).filter fun y => ¬ Frontier h y

theorem mem_newHeads {h : MacroExp.Tr d} {z y : Site 2} :
    y ∈ newHeads (d := d) h z ↔ y ∈ MacroExp.pending d h z ∧ ¬ Frontier h y := by
  classical
  simp [newHeads]

/-- There are at most four newly created frontier heads. -/
theorem card_newHeads_le_four (h : MacroExp.Tr d) (z : Site 2) :
    (newHeads (d := d) h z).card ≤ 4 := by
  classical
  calc
    (newHeads (d := d) h z).card ≤ (MacroExp.pending d h z).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (MacroExp.nbrs z).card := by
      apply Finset.card_le_card
      intro y hy
      exact (MacroExp.mem_pending (d := d)).1 hy |>.1
    _ ≤ (Finset.univ : Finset (Fin 2 × Bool)).card := Finset.card_image_le
    _ = 4 := by norm_num

/-- A new head cannot equal any vertex which was already on the frontier. -/
theorem newHead_ne_frontier {h : MacroExp.Tr d} {z y v : Site 2}
    (hy : y ∈ newHeads (d := d) h z) (hv : Frontier h v) : y ≠ v := by
  intro hyv
  subst v
  exact ((mem_newHeads (d := d)).1 hy).2 hv

/-- A new head is not an old open macro vertex. -/
theorem newHead_not_mem_openV {h : MacroExp.Tr d} {z y : Site 2}
    (hy : y ∈ newHeads (d := d) h z) : y ∉ h.openV := by
  have hundet := ((MacroExp.mem_pending (d := d)).1 ((mem_newHeads (d := d)).1 hy).1).2
  exact fun hopen => hundet (Finset.mem_union_left _ hopen)

/-- **Same-head repair.**  A corridor protected by an old owner is disjoint from the corridor to
a newly created head.  Distinctness of the heads follows from the definition of `newHeads`; the
reverse-edge case is impossible because a new head was not previously open. -/
theorem oldOwner_region_disjoint_newHead (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {h : MacroExp.Tr d} {u v z y : Site 2}
    (hu : u ∈ h.openV) (hv : v ∈ MacroExp.pending d h u)
    (hy : y ∈ newHeads (d := d) h z) :
    Disjoint (MacroExp.E d r t u v) (MacroExp.E d r t z y) := by
  have hvFront : Frontier h v := by
    refine ⟨((MacroExp.mem_pending (d := d)).1 hv).2, u, hu, ?_⟩
    exact ((MacroExp.mem_pending (d := d)).1 hv).1
  have hheads : v ≠ y := (newHead_ne_frontier (d := d) hy hvFront).symm
  have hrev : ¬ (u = y ∧ v = z) := by
    rintro ⟨huy, -⟩
    exact newHead_not_mem_openV (d := d) hy (huy ▸ hu)
  exact MacroExp.protectedEdges_disjoint hd r t hr
    (MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 hv).1)
    (MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1
      ((mem_newHeads (d := d)).1 hy).1).1)
    hheads hrev

/-- Opening `z` creates no frontier vertices except old frontier vertices and `newHeads h z`. -/
theorem frontier_step_true_cases {h : MacroExp.Tr d} {z y : Site 2}
    (F : Finset (Site d)) (omega : SiteConfig (Site d))
    (hy : Frontier (h.step z F true omega) y) :
    Frontier h y ∨ y ∈ newHeads (d := d) h z := by
  classical
  rcases hy with ⟨hyUndetNew, u, huOpenNew, hyNbr⟩
  have hyUndetOld : y ∉ h.openV ∪ h.closedV := by
    intro hyOld
    apply hyUndetNew
    rw [FRDom.Transcript.step_determined]
    exact Finset.mem_insert_of_mem hyOld
  rw [FRDom.Transcript.step_openV] at huOpenNew
  simp only [if_true, Finset.mem_insert] at huOpenNew
  rcases huOpenNew with rfl | huOld
  · by_cases hyFront : Frontier h y
    · exact Or.inl hyFront
    · exact Or.inr ((mem_newHeads (d := d)).2
        ⟨(MacroExp.mem_pending (d := d)).2 ⟨hyNbr, hyUndetOld⟩, hyFront⟩)
  · exact Or.inl ⟨hyUndetOld, u, huOld, hyNbr⟩

/-- **Invariant update.**  Suppose every old frontier owner persists through a stopped batch, and
every genuinely new head receives a core reservation from the newly opened vertex `z`.  Then one
owner per frontier vertex is restored after the batch. -/
theorem invariant_step_true {r t : Nat} {q : unitInterval} {eps : Real}
    {h : MacroExp.Tr d} {z : Site 2} (F : Finset (Site d)) (omega : SiteConfig (Site d))
    (hpersist : ∀ y, Frontier h y → HasOwner r t q eps (h.step z F true omega) y)
    (hnew : ∀ y ∈ newHeads (d := d) h z,
      CoreRes.Bound r t q eps (h.step z F true omega) z y) :
    Invariant r t q eps (h.step z F true omega) := by
  classical
  intro y hy
  rcases frontier_step_true_cases (d := d) F omega hy with hyOld | hyNew
  · exact hpersist y hyOld
  · refine ⟨z, ?_, ?_, hnew y hyNew⟩
    · simp
    · apply (MacroExp.mem_pending (d := d)).2
      refine ⟨((MacroExp.mem_pending (d := d)).1 ((mem_newHeads (d := d)).1 hyNew).1).1, ?_⟩
      exact hy.1

#print axioms KNAll.Site.CoreFrontier.card_newHeads_le_four
#print axioms KNAll.Site.CoreFrontier.oldOwner_region_disjoint_newHead
#print axioms KNAll.Site.CoreFrontier.frontier_step_true_cases
#print axioms KNAll.Site.CoreFrontier.invariant_step_true

end KNAll.Site.CoreFrontier

end
