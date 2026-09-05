import Hypergraph.CorridorNarrow

/-!
# Core directional reservations

The old macro invariant reserves a connection to the anisotropic box `MacroExp.M ... y`.
For the stopped corridor construction the natural recursive target is smaller: the isotropic
core `c_y + Lambda_(3r)` used as the source of the next corridor cascade.

This file introduces that target and records the two monotonicity bridges needed by the repaired
assembly:

* a core reservation for the incoming edge is exactly the source target required by
  `CorrMove.corridorMoveNarrow` (provided its error is at most `CorrMove.beta rho d`);
* the core is contained in the old macro target, so a realized core connection is already a valid
  macro certificate.  The corridor cascade first reaches its radius-`2r` inner cube and target
  monotonicity enlarges that event to this radius-`3r` recursive core.

No endpoint is selected and no extra open-site factor is paid in either argument.
-/

noncomputable section

namespace KNAll.Site.CoreRes

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- The isotropic target naturally output by the corridor cascade. -/
def target (r : Nat) (y : Site 2) : Finset (Site d) :=
  CorrMove.cube (MacroExp.ctr d r y) (3 * (r : Int))

/-- The connection event stored for one live oriented frontier edge. -/
def event (r t : Nat) (h : MacroExp.Tr d) (z y : Site 2) : Set (SiteConfig (Site d)) :=
  connWithinSet (zdGraph d)
    (↑(h.inspected ∪ MacroExp.E d r t z y) : Set (Site d))
    (MacroExp.emb 0) (↑(target (d := d) r y) : Set (Site d))

/-- A core reservation is a strict pinned-probability bound. -/
def Bound (r t : Nat) (q : unitInterval) (eps : Real) (h : MacroExp.Tr d)
    (z y : Site 2) : Prop :=
  1 - eps < h.prob (fun _ : Site d => q) (event (d := d) r t h z y)

/-- The recursive core is the radius-`3r` cube used as the source of the corridor cascade. -/
theorem target_subset_sourceCube (r : Nat) (y : Site 2) :
    target (d := d) r y ⊆
      CorrMove.cube (MacroExp.ctr d r y) (3 * (r : Int)) := by
  intro x hx
  exact hx

/-- Under the standard scale hypothesis, the core lies in the old anisotropic macro target.
Thus changing the recursive invariant to core reservations does not weaken realized macro
certificates. -/
theorem target_subset_M {r t : Nat} (ht : 5 * r ≤ t) (y : Site 2) :
    target (d := d) r y ⊆ MacroExp.M d r t y := by
  unfold target
  apply CorrMove.cube_subset_M (d := d) (s := 3 * r) (z := y)
  · push_cast
    omega
  · have : 3 * r ≤ t := by omega
    exact_mod_cast this

/-- Event monotonicity turns an incoming core reservation into the source event required by the
narrow corridor cascade.  The new allowed set only adds the stopped stub; the target is already
the radius-`3r` source cube. -/
theorem event_subset_narrowSource {r t : Nat} (h : MacroExp.Tr d) (w z : Site 2)
    (i : Fin d) (sigma : Int) :
    event (d := d) r t h w z ⊆
      connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(CorrMove.cube (MacroExp.ctr d r z) (3 * (r : Int))) : Set (Site d)) := by
  intro omega homega
  rw [event, mem_connWithinSet_iff] at homega
  rw [mem_connWithinSet_iff]
  obtain ⟨a, ha, hconn⟩ := homega
  refine ⟨a, ?_, ?_⟩
  · exact Finset.mem_coe.2
      (target_subset_sourceCube (d := d) r z (Finset.mem_coe.1 ha))
  · exact connWithin_mono_set (zdGraph d) (x := MacroExp.emb 0) (y := a)
      (by
        intro x hx
        exact Finset.mem_coe.2
          (Finset.mem_union_left _ (Finset.mem_coe.1 hx)))
      hconn

/-- A core reservation with error at most `beta rho d` supplies exactly the `hsrc` hypothesis of
`CorrMove.corridorMoveNarrow`.  This is the formal reason the repaired invariant needs neither
`WideHead` nor a post-step origin source estimate. -/
theorem bound_implies_narrowSource {r t : Nat} {h : MacroExp.Tr d} {q : unitInterval}
    {w z : Site 2} {i : Fin d} {sigma : Int} {eps rho : Real}
    (heps : eps ≤ CorrMove.beta rho d)
    (hcore : Bound (d := d) r t q eps h w z) :
    1 - CorrMove.beta rho d < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(CorrMove.cube (MacroExp.ctr d r z) (3 * (r : Int))) : Set (Site d))) := by
  have hmono := ProbInv.prob_mono h (fun _ : Site d => q)
    (event_subset_narrowSource (d := d) (r := r) (t := t) h w z i sigma)
  unfold Bound at hcore
  exact lt_of_le_of_lt (sub_le_sub_left heps 1) (lt_of_lt_of_le hcore hmono)

/-! ## The pre-enlargement narrow corridor -/

/-- The face-extension interface used by the corridor cascade, packaged only to keep the theorem
statement readable. -/
abbrev FaceInputs (R : Nat) (h : MacroExp.Tr d) (q : unitInterval)
    (Dom : Finset (Site d)) : Prop :=
  ∀ (Sub Bset Tset : Finset (Site d)) (eps : Real), 0 < eps → eps ≤ 1 →
    Disjoint h.inspected Sub → (MacroExp.emb 0 : Site d) ∉ Sub → Sub ⊆ Dom →
    CorrMove.FaceTarget (R : Int) Sub Bset Tset →
    1 - eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Bset : Set (Site d))) →
    1 - eps < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Tset : Set (Site d)))

/-- The aspect-ratio extension interface used by the final stage of the cascade. -/
abbrev LongInputs (R : Nat) (h : MacroExp.Tr d) (q : unitInterval)
    (Dom : Finset (Site d)) (i : Fin d) (sigma : Int) : Prop :=
  ∀ (Sub Bset Tset : Finset (Site d)) (eps : Real), 0 < eps → eps ≤ 1 →
    Disjoint h.inspected Sub → (MacroExp.emb 0 : Site d) ∉ Sub → Sub ⊆ Dom →
    CorrMove.LongTarget (R : Int) i sigma Sub Bset Tset →
    1 - eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Bset : Set (Site d))) →
    1 - eps < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Tset : Set (Site d)))

/-- **The narrow corridor estimate at the recursive core.**  `CorrMove.corridorMoveCore` first
reaches the radius-`2r` inner cube at the head.  Monotonicity in the target enlarges this to the
radius-`3r` core which is the source target for the next corridor. -/
theorem corridorMoveNarrowCore (hd : 2 ≤ d) {r t R : Nat} {h : MacroExp.Tr d}
    {q : unitInterval} {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (h44 : 44 ≤ r) (hR1 : 1 ≤ R) (hscale : 100 * (d + 1) * (R + 1) < r)
    (ht : 5 * r ≤ t) (hrho0 : 0 < rho) (hrho1 : rho ≤ 1) (hwz : w ≠ z)
    (hfresh : Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y))
    (hzero : (MacroExp.emb 0 : Site d) ∉
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (hface : FaceInputs (d := d) R h q
      (h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)))
    (hlong : LongInputs (d := d) R h q
      (h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) i sigma)
    (hsrc : 1 - CorrMove.beta rho d < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(CorrMove.cube (MacroExp.ctr d r z) (3 * (r : Int))) : Set (Site d)))) :
    1 - rho / 32 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0) (↑(target (d := d) r y) : Set (Site d))) := by
  let Dom : Finset (Site d) := h.inspected ∪ MacroExp.E d r t w z ∪
    Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)
  have hcube5 : CorrMove.cube (MacroExp.ctr d r z) (5 * (r : Int)) ⊆
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y :=
    (CorrMove.cube_subset_Q (d := d) ht z).trans Finset.subset_union_left
  have hdb : CorrMove.dbox (MacroExp.ctr d r z) i sigma (-(2 * (r : Int)))
      (22 * (r : Int)) (2 * (r : Int)) ⊆
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y :=
    CorrMove.dbox_subset_Q_union_E (d := d) (by omega) ht hsigma hemb
  have hdom5 : CorrMove.cube (MacroExp.ctr d r z) (5 * (r : Int)) ⊆ Dom := by
    simpa only [Dom] using
      CorrMove.cube_subset_narrowDom hd (by omega) ht h hwz i sigma le_rfl
  have hdomD : CorrMove.dbox (MacroExp.ctr d r z) i sigma (-(2 * (r : Int)))
      (22 * (r : Int)) (2 * (r : Int)) ⊆ Dom := by
    simpa only [Dom] using CorrMove.dbox_subset_narrowDom hd (by omega) ht h hwz hsigma
  have hcore :=
    CorrMove.corridorMoveCore hsigma hemb h44 hR1 hscale hrho0 hrho1 Dom
      (hfresh.mono_right hcube5) (hfresh.mono_right hdb)
      (fun hx => hzero (hcube5 hx)) (fun hx => hzero (hdb hx))
      hdom5 hdomD hface hlong hsrc
  have hcube23 : CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int)) ⊆
      target (d := d) r y := by
    intro x hx
    rw [CorrMove.mem_cube] at hx
    rw [target, CorrMove.mem_cube]
    intro j
    exact le_trans (hx j) (by omega)
  have hevent :
      connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑(CorrMove.cube (MacroExp.ctr d r y) (2 * (r : Int))) : Set (Site d)) ⊆
        connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑(target (d := d) r y) : Set (Site d)) := by
    intro omega homega
    rw [mem_connWithinSet_iff] at homega ⊢
    obtain ⟨a, ha, hconn⟩ := homega
    exact ⟨a, Finset.mem_coe.2 (hcube23 (Finset.mem_coe.1 ha)), hconn⟩
  have hmono := ProbInv.prob_mono h (fun _ : Site d => q) hevent
  simpa only [Dom] using lt_of_lt_of_le hcore hmono

#print axioms KNAll.Site.CoreRes.target_subset_sourceCube
#print axioms KNAll.Site.CoreRes.target_subset_M
#print axioms KNAll.Site.CoreRes.event_subset_narrowSource
#print axioms KNAll.Site.CoreRes.bound_implies_narrowSource
#print axioms KNAll.Site.CoreRes.corridorMoveNarrowCore

end KNAll.Site.CoreRes

end
