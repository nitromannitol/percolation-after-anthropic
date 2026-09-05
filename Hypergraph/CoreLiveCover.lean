import Hypergraph.CoreFrontier
import Hypergraph.CoreFreshness

/-!
# Disjoint live regions for the one-owner frontier

An oriented frontier edge owns `E(w,z) \ Q(z)`.  The head box is deliberately omitted: it is
read when `z` is examined.  These elementary lemmas show that old owners, newly created heads,
and their head boxes remain separated.  They are the deterministic cover facts needed by the
bounded-damage stopped exploration.
-/

noncomputable section

namespace KNAll.Site.CoreLive

open Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- Live regions belonging to two distinct new heads have disjoint physical support. -/
theorem newHead_liveRegions_disjoint (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {h : MacroExp.Tr d} {z y₁ y₂ : Site 2}
    (hy₁ : y₁ ∈ CoreFrontier.newHeads (d := d) h z)
    (hy₂ : y₂ ∈ CoreFrontier.newHeads (d := d) h z) (hne : y₁ ≠ y₂) :
    Disjoint (CoreFresh.liveRegion d r t z y₁) (CoreFresh.liveRegion d r t z y₂) := by
  have ha₁ : (zdGraph 2).Adj z y₁ :=
    MacroExp.adj_of_mem_nbrs
      ((MacroExp.mem_pending (d := d)).1
        ((CoreFrontier.mem_newHeads (d := d)).1 hy₁).1).1
  have ha₂ : (zdGraph 2).Adj z y₂ :=
    MacroExp.adj_of_mem_nbrs
      ((MacroExp.mem_pending (d := d)).1
        ((CoreFrontier.mem_newHeads (d := d)).1 hy₂).1).1
  have hrev : ¬ (z = y₂ ∧ y₁ = z) := by
    rintro ⟨hzy₂, hy₁z⟩
    exact hne (hy₁z.trans hzy₂)
  exact (MacroExp.protectedEdges_disjoint hd r t hr ha₁ ha₂ hne hrev).mono
    Finset.sdiff_subset Finset.sdiff_subset

/-- Every new live region avoids every new head box, including its own. -/
theorem newHead_liveRegion_disjoint_headQ (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {h : MacroExp.Tr d} {z y₁ y₂ : Site 2}
    (hy₁ : y₁ ∈ CoreFrontier.newHeads (d := d) h z)
    (hy₂ : y₂ ∈ CoreFrontier.newHeads (d := d) h z) :
    Disjoint (CoreFresh.liveRegion d r t z y₁) (MacroExp.Q d r t y₂) := by
  by_cases hsame : y₁ = y₂
  · subst y₂
    exact Finset.sdiff_disjoint
  · have ha₁ : (zdGraph 2).Adj z y₁ :=
      MacroExp.adj_of_mem_nbrs
        ((MacroExp.mem_pending (d := d)).1
          ((CoreFrontier.mem_newHeads (d := d)).1 hy₁).1).1
    exact (MacroExp.protectedEdge_disjoint_Q hd r t hr ha₁ (Ne.symm hsame)).mono_left
      Finset.sdiff_subset

/-- An old owner's live region is disjoint from every newly allocated live region. -/
theorem oldOwner_liveRegion_disjoint_newHead (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {h : MacroExp.Tr d} {u v z y : Site 2}
    (hu : u ∈ h.openV) (hv : v ∈ MacroExp.pending d h u)
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    Disjoint (CoreFresh.liveRegion d r t u v) (CoreFresh.liveRegion d r t z y) := by
  exact (CoreFrontier.oldOwner_region_disjoint_newHead hd hr hu hv hy).mono
    Finset.sdiff_subset Finset.sdiff_subset

/-- An old owner's live region also avoids every newly created head box. -/
theorem oldOwner_liveRegion_disjoint_newHeadQ (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {h : MacroExp.Tr d} {u v z y : Site 2}
    (hu : u ∈ h.openV) (hv : v ∈ MacroExp.pending d h u)
    (hy : y ∈ CoreFrontier.newHeads (d := d) h z) :
    Disjoint (CoreFresh.liveRegion d r t u v) (MacroExp.Q d r t y) := by
  have hadj : (zdGraph 2).Adj u v :=
    MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 hv).1
  have hvFront : CoreFrontier.Frontier h v := by
    refine ⟨((MacroExp.mem_pending (d := d)).1 hv).2, u, hu, ?_⟩
    exact ((MacroExp.mem_pending (d := d)).1 hv).1
  have hne : v ≠ y := (CoreFrontier.newHead_ne_frontier (d := d) hy hvFront).symm
  exact (MacroExp.protectedEdge_disjoint_Q hd r t hr hadj (Ne.symm hne)).mono_left
    Finset.sdiff_subset

#print axioms KNAll.Site.CoreLive.newHead_liveRegions_disjoint
#print axioms KNAll.Site.CoreLive.newHead_liveRegion_disjoint_headQ
#print axioms KNAll.Site.CoreLive.oldOwner_liveRegion_disjoint_newHead
#print axioms KNAll.Site.CoreLive.oldOwner_liveRegion_disjoint_newHeadQ

end KNAll.Site.CoreLive

end
