import Hypergraph.CoreReservationPersistence

/-!
# Reservation persistence under an arbitrary transcript extension

The stepwise persistence theorem is convenient while constructing a reveal.  At a stopped
prefix, however, the final batch transcript may already contain reads made for several other
heads.  This module gives the order-free form: extending the inspected set preserves a core
reservation provided the newly pinned coordinates avoid its protected edge and the old recorded
states are unchanged.
-/

noncomputable section

namespace KNAll.Site.CoreRes

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- An arbitrary finite extension outside the protected edge preserves a core reservation. -/
theorem bound_of_transcript_extension
    (r t : Nat) (q : unitInterval) (eps : Real)
    {h k : MacroExp.Tr d} (u y : Site 2)
    (hsub : h.inspected ⊆ k.inspected)
    (hstate : ∀ x ∈ h.inspected, (k.state x ↔ h.state x))
    (hextra : Disjoint (k.inspected \ h.inspected) (MacroExp.E d r t u y))
    (hbound : Bound (d := d) r t q eps h u y) :
    Bound (d := d) r t q eps k u y := by
  let S : Set (Site d) := ↑(h.inspected ∪ MacroExp.E d r t u y)
  let A : Set (SiteConfig (Site d)) :=
    connWithinSet (zdGraph d) S (MacroExp.emb 0)
      (↑(target (d := d) r y) : Set (Site d))
  let F : Finset (Site d) := k.inspected \ h.inspected
  have hkI : k.inspected = h.inspected ∪ F := by
    dsimp only [F]
    symm
    exact Finset.union_sdiff_of_subset hsub
  have hdet : DeterminedBy A S :=
    determinedBy_connWithinSet (zdGraph d) S (MacroExp.emb 0)
      (↑(target (d := d) r y) : Set (Site d))
  have hFS : Disjoint (↑F : Set (Site d)) S := by
    rw [Set.disjoint_left]
    intro x hxF hxS
    have hxF' : x ∈ k.inspected \ h.inspected := Finset.mem_coe.1 hxF
    have hx := Finset.mem_sdiff.1 hxF'
    simp only [S, Finset.mem_coe, Finset.mem_union] at hxS
    exact hxS.elim hx.2 (fun hxE => Finset.disjoint_left.1 hextra hxF' hxE)
  have hpin :
      pinnedProb (fun _ : Site d => q) (↑k.inspected : Set (Site d)) k.state A =
        pinnedProb (fun _ : Site d => q) (↑h.inspected : Set (Site d)) k.state A := by
    rw [hkI, Finset.coe_union]
    exact pinnedProb_union_eq (fun _ : Site d => q) k.state hdet
      (hFS.mono_right Set.sdiff_subset)
  have hval :
      pinnedProb (fun _ : Site d => q) (↑h.inspected : Set (Site d)) k.state A =
        pinnedProb (fun _ : Site d => q) (↑h.inspected : Set (Site d)) h.state A :=
    pinnedProb_congr_val (fun _ : Site d => q) _
      (fun x hx => hstate x (Finset.mem_coe.1 hx)) A
  have hprob : k.prob (fun _ : Site d => q) A = h.prob (fun _ : Site d => q) A := by
    rw [FRDom.Transcript.prob_eq, FRDom.Transcript.prob_eq, hpin, hval]
  have hDom : S ⊆
      ↑(k.inspected ∪ MacroExp.E d r t u y) := by
    intro x hx
    simp only [S, Finset.mem_coe, Finset.mem_union] at hx ⊢
    exact hx.elim (fun hxI => Or.inl (hsub hxI)) Or.inr
  have hmono : A ⊆ event (d := d) r t k u y :=
    connWithinSet_mono_set (zdGraph d) hDom (MacroExp.emb 0)
      (↑(target (d := d) r y) : Set (Site d))
  unfold Bound at hbound ⊢
  change 1 - eps < h.prob (fun _ : Site d => q) A at hbound
  calc
    1 - eps < h.prob (fun _ : Site d => q) A := hbound
    _ = k.prob (fun _ : Site d => q) A := hprob.symm
    _ ≤ k.prob (fun _ : Site d => q) (event (d := d) r t k u y) :=
      ProbInv.prob_mono k (fun _ : Site d => q) hmono

/-- Bounded-damage transcripts use the same physical pinned law, so the extension theorem applies
directly to their bases. -/
theorem bound_of_damageTranscript_extension
    (r t : Nat) (q : unitInterval) (eps : Real)
    {h k : BDDom.Transcript (Site d) (Site 2)} (u y : Site 2)
    (hsub : h.inspected ⊆ k.inspected)
    (hstate : ∀ x ∈ h.inspected, (k.state x ↔ h.state x))
    (hextra : Disjoint (k.inspected \ h.inspected) (MacroExp.E d r t u y))
    (hbound : Bound (d := d) r t q eps h.base u y) :
    Bound (d := d) r t q eps k.base u y :=
  bound_of_transcript_extension r t q eps u y hsub hstate hextra hbound

/-- A good stopped level remains a reservation at any later physical transcript whose genuinely
new reads avoid the stopped head's protected edge.  This is the exact bridge needed by a
multi-head scheduler after it has stopped probing `y`. -/
theorem bound_stopLevel_of_extension
    {r t s K : Nat} {h k : MacroExp.Tr d} {z y : Site 2}
    {i : Fin d} {sigma : Int} {q : unitInterval} {eps : Real}
    {omega : SiteConfig (Site d)}
    (hsuccess : omega ∉ CoreStopped.noGoodLevel r t s h z y i sigma q eps K)
    (hsub :
      (Stopped.levelTr d r t s h z i sigma
        (CoreStopped.stopLevel r t s h z y i sigma q eps K omega) omega).inspected ⊆
          k.inspected)
    (hstate : ∀ x ∈
        (Stopped.levelTr d r t s h z i sigma
          (CoreStopped.stopLevel r t s h z y i sigma q eps K omega) omega).inspected,
      (k.state x ↔
        (Stopped.levelTr d r t s h z i sigma
          (CoreStopped.stopLevel r t s h z y i sigma q eps K omega) omega).state x))
    (hextra : Disjoint
      (k.inspected \
        (Stopped.levelTr d r t s h z i sigma
          (CoreStopped.stopLevel r t s h z y i sigma q eps K omega) omega).inspected)
      (MacroExp.E d r t z y)) :
    Bound (d := d) r t q eps k z y := by
  exact bound_of_transcript_extension r t q eps z y hsub hstate hextra
    (CoreStopped.bound_stopLevel hsuccess)

#print axioms KNAll.Site.CoreRes.bound_of_transcript_extension
#print axioms KNAll.Site.CoreRes.bound_of_damageTranscript_extension
#print axioms KNAll.Site.CoreRes.bound_stopLevel_of_extension

end KNAll.Site.CoreRes

end
