import Hypergraph.CoreReservation
import Hypergraph.BoundedDamageDomination
import Hypergraph.AdmissibleBoundedDamageAdaptiveRegion
import Hypergraph.CoreTaggedCoverUpdate

/-!
# Persistence of core reservations

A core reservation is an event supported by the old inspected set together with one protected
corridor.  Reading fresh coordinates outside that corridor leaves the old pinned probability
unchanged.  The enlarged transcript only enlarges the allowed set of the connection event, so the
same strict bound persists.

This is the radius-`2r` analogue of `Acquire.reservation_step_of_disjoint`.
-/

noncomputable section

namespace KNAll.Site.CoreRes

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- A single fresh read disjoint from the protected corridor preserves a core reservation. -/
theorem bound_step_of_disjoint
    (r t : Nat) (q : unitInterval) (eps : Real) (h : MacroExp.Tr d)
    (u y v : Site 2) (F : Finset (Site d)) (b : Bool)
    (omega : SiteConfig (Site d))
    (hfresh : Disjoint F h.inspected)
    (hFE : Disjoint F (MacroExp.E d r t u y))
    (hbound : Bound (d := d) r t q eps h u y) :
    Bound (d := d) r t q eps (h.step v F b omega) u y := by
  let S : Set (Site d) := ↑(h.inspected ∪ MacroExp.E d r t u y)
  let A : Set (SiteConfig (Site d)) :=
    connWithinSet (zdGraph d) S (MacroExp.emb 0)
      (↑(target (d := d) r y) : Set (Site d))
  have hdet : DeterminedBy A S :=
    determinedBy_connWithinSet (zdGraph d) S (MacroExp.emb 0)
      (↑(target (d := d) r y) : Set (Site d))
  have hdisj : Disjoint (↑F : Set (Site d)) S := by
    rw [Set.disjoint_left]
    intro x hxF hxS
    simp only [S, Finset.mem_coe, Finset.mem_union] at hxS
    rcases hxS with hxI | hxE
    · exact Finset.disjoint_left.1 hfresh hxF hxI
    · exact Finset.disjoint_left.1 hFE hxF hxE
  have hprob :
      (h.step v F b omega).prob (fun _ : Site d => q) A =
        h.prob (fun _ : Site d => q) A :=
    ProbInv.prob_step_eq_of_disjoint h (fun _ : Site d => q) v F b omega
      hfresh hdet hdisj
  have hDom : S ⊆
      ↑((h.step v F b omega).inspected ∪ MacroExp.E d r t u y) := by
    rw [FRDom.Transcript.step_inspected]
    intro x hx
    simp only [S, Finset.mem_coe, Finset.mem_union] at hx ⊢
    rcases hx with hxI | hxE
    · exact Or.inl (Or.inl hxI)
    · exact Or.inr hxE
  have hmono : A ⊆ event (d := d) r t (h.step v F b omega) u y :=
    connWithinSet_mono_set (zdGraph d) hDom (MacroExp.emb 0)
      (↑(target (d := d) r y) : Set (Site d))
  unfold Bound at hbound ⊢
  change 1 - eps < h.prob (fun _ : Site d => q) A at hbound
  calc
    1 - eps < h.prob (fun _ : Site d => q) A := hbound
    _ = (h.step v F b omega).prob (fun _ : Site d => q) A := hprob.symm
    _ ≤ (h.step v F b omega).prob (fun _ : Site d => q)
        (event (d := d) r t (h.step v F b omega) u y) :=
      ProbInv.prob_mono _ _ hmono

/-- The same persistence statement for a bounded-damage step.  Macro-level collateral damage
does not alter the physical pinned law. -/
theorem bound_damageStep_of_disjoint
    (r t : Nat) (q : unitInterval) (eps : Real)
    (h : BDDom.Transcript (Site d) (Site 2))
    (u y v : Site 2) (F : Finset (Site d)) (damage : Finset (Site 2))
    (b : Bool) (omega : SiteConfig (Site d))
    (hfresh : Disjoint F h.inspected)
    (hFE : Disjoint F (MacroExp.E d r t u y))
    (hbound : Bound (d := d) r t q eps h.base u y) :
    Bound (d := d) r t q eps (h.step v F damage b omega).base u y := by
  let plain := h.base.step v F b omega
  let damaged := (h.step v F damage b omega).base
  have hplain : Bound (d := d) r t q eps plain u y :=
    bound_step_of_disjoint r t q eps h.base u y v F b omega hfresh hFE hbound
  have hins : damaged.inspected = plain.inspected := by
    rfl
  have hstate : ∀ x ∈ (↑damaged.inspected : Set (Site d)),
      (damaged.state x ↔ plain.state x) := by
    intro x _
    change x ∈ damaged.openSites ↔ x ∈ plain.openSites
    rfl
  have hevent : event (d := d) r t damaged u y = event (d := d) r t plain u y := by
    unfold event
    rw [hins]
  have hprob : damaged.prob (fun _ : Site d => q) (event (d := d) r t plain u y) =
      plain.prob (fun _ : Site d => q) (event (d := d) r t plain u y) := by
    rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq, hins]
    exact pinnedProb_congr_val (fun _ : Site d => q) _ hstate _
  unfold Bound at hplain ⊢
  rw [hevent, hprob]
  exact hplain

/-- A reservation persists through an entire finite reveal phase when every phase region avoids
its protected corridor.  This is the form needed for old frontier owners in the batch scheduler. -/
theorem bound_revealRun_of_disjoint
    {Admissible : BDDom.Transcript (Site d) (Site 2) → Prop}
    (R : ABDAdaptReg.RevealPhase (Site d) (Site 2) Admissible)
    (r t : Nat) (q : unitInterval) (eps : Real)
    {base k : BDDom.Transcript (Site d) (Site 2)}
    (hk : R.Phase base k) (u y : Site 2)
    (hregions : ∀ k', R.Phase base k' →
      Disjoint (R.region base k') (MacroExp.E d r t u y))
    (hbound : Bound (d := d) r t q eps k.base u y) :
    ∀ n omega,
      Bound (d := d) r t q eps (R.run base n k omega).base u y := by
  intro n
  induction n generalizing k with
  | zero =>
      intro omega
      simpa using hbound
  | succ n ih =>
      intro omega
      have hk' : R.Phase base (R.reveal base k omega) :=
        R.step_phase base k hk omega
      have hstep : Bound (d := d) r t q eps (R.reveal base k omega).base u y := by
        simpa only [ABDAdaptReg.RevealPhase.reveal] using
          bound_damageStep_of_disjoint r t q eps k u y (R.anchor base k)
            (R.region base k) ∅ true omega
            (R.region_fresh base k hk) (hregions k hk) hbound
      exact ih hk' hstep omega

/-- The final macro verdict reads no additional physical coordinate, so every reservation at the
end of the reveal phase survives the bounded-damage commit. -/
theorem bound_emptyCommit
    (r t : Nat) (q : unitInterval) (eps : Real)
    (h : BDDom.Transcript (Site d) (Site 2))
    (u y v : Site 2) (damage : Finset (Site 2)) (b : Bool)
    (omega : SiteConfig (Site d))
    (hbound : Bound (d := d) r t q eps h.base u y) :
    Bound (d := d) r t q eps (h.step v ∅ damage b omega).base u y := by
  exact bound_damageStep_of_disjoint r t q eps h u y v ∅ damage b omega
    (by simp) (by simp) hbound

/-! ## Batch geometry -/

/-- The complete physical support allocated to a new-head batch: the incoming corridor, followed
by the head-box-free regions allocated to genuinely new outgoing heads. -/
def batchReadSupport (d r t : Nat) (h : MacroExp.Tr d) (w z : Site 2) :
    Finset (Site d) :=
  MacroExp.E d r t w z ∪
    CoreTaggedCover.liveRegions d r t (CoreCoverUpdate.newEdges h z)

/-- A batch read avoids every old live reservation not aimed at the centre being examined.  The
reverse-edge case is impossible because the centre is still undetermined while every old owner is
open. -/
theorem batchReadSupport_disjoint_oldLive
    (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {q : unitInterval} {eps : Real} {h : MacroExp.Tr d}
    {w z u v : Site 2} (hw : w ∈ h.openV)
    (hz : z ∈ MacroExp.pending d h w)
    (hold : CoreTaggedCover.Live r t q eps h (u, v))
    (hvz : v ≠ z) :
    Disjoint (batchReadSupport d r t h w z) (MacroExp.E d r t u v) := by
  have hadjWZ : (zdGraph 2).Adj w z :=
    MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 hz).1
  have hadjUV : (zdGraph 2).Adj u v :=
    MacroExp.adj_of_mem_nbrs ((MacroExp.mem_pending (d := d)).1 hold.2.1).1
  have hrev : ¬ (w = v ∧ z = u) := by
    rintro ⟨-, hzu⟩
    have hzOpen : z ∈ h.openV := hzu ▸ hold.1
    exact ((MacroExp.mem_pending (d := d)).1 hz).2 (Finset.mem_union_left _ hzOpen)
  have hincoming : Disjoint (MacroExp.E d r t w z) (MacroExp.E d r t u v) :=
    MacroExp.protectedEdges_disjoint hd r t hr hadjWZ hadjUV hvz.symm hrev
  rw [Finset.disjoint_left]
  intro x hxRead hxOld
  rcases Finset.mem_union.1 hxRead with hxIncoming | hxOutgoing
  · exact Finset.disjoint_left.1 hincoming hxIncoming hxOld
  · rw [CoreTaggedCover.liveRegions, Finset.mem_biUnion] at hxOutgoing
    obtain ⟨e, heNew, hxe⟩ := hxOutgoing
    have he := (CoreCoverUpdate.mem_newEdges_iff (d := d)).1 heNew
    obtain ⟨rfl, hy⟩ := he
    have hsep := CoreFrontier.oldOwner_region_disjoint_newHead (t := t)
      hd hr hold.1 hold.2.1 hy
    exact Finset.disjoint_left.1 hsep hxOld
      (CoreCoverUpdate.liveRegion_subset_edgeRegion d r t e hxe)

/-- Every sub-read of the batch support has the same separation property. -/
theorem readSubset_disjoint_oldLive
    (hd : 2 ≤ d) {r t : Nat} (hr : 0 < r)
    {q : unitInterval} {eps : Real} {h : MacroExp.Tr d}
    {w z u v : Site 2} {F : Finset (Site d)}
    (hF : F ⊆ batchReadSupport d r t h w z)
    (hw : w ∈ h.openV) (hz : z ∈ MacroExp.pending d h w)
    (hold : CoreTaggedCover.Live r t q eps h (u, v))
    (hvz : v ≠ z) : Disjoint F (MacroExp.E d r t u v) :=
  (batchReadSupport_disjoint_oldLive hd hr hw hz hold hvz).mono_left hF

#print axioms KNAll.Site.CoreRes.bound_step_of_disjoint
#print axioms KNAll.Site.CoreRes.bound_damageStep_of_disjoint
#print axioms KNAll.Site.CoreRes.bound_revealRun_of_disjoint
#print axioms KNAll.Site.CoreRes.bound_emptyCommit
#print axioms KNAll.Site.CoreRes.batchReadSupport_disjoint_oldLive
#print axioms KNAll.Site.CoreRes.readSubset_disjoint_oldLive

end KNAll.Site.CoreRes

end
