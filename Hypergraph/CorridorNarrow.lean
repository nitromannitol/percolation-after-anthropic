import Hypergraph.CorridorMove
import Hypergraph.StoppedLevel

/-!
# The narrow corridor conclusion

`CorrMove.corridorMove` exports a **broad** success event: the connection is allowed to use the
whole region `E z y` and its target is the whole box `MacroExp.M ... y`.  The stopped machinery of
`KN/StoppedLevel.lean` consumes a **narrow** one: the allowed set is only
`h.inspected ∪ E w z ∪ Stopped.stub`, and the target is only `Stopped.stubTarget`.  The narrow
success event is a subset of the broad one, and that inclusion is strict for realizable corridor
configurations, so a bound on the complement of the broad event gives no bound on the complement
of the narrow one; monotonicity runs the wrong way.

This file supplies the narrow conclusion by rerunning the same `d+1` target-extension cascade in
the narrow allowed region.  It uses `CorrMove.corridorMoveCore`, which is `corridorMove` with the
allowed region abstracted: the cascade reads the region only through the head cube
`c_z + Λ_{5r}` of the `d` cross-section reductions and the long box `D'` of the final aspect-88
move, and it produces the isotropic core `c_y + Λ_{2r}`.  Neither of those two subboxes needs
`E z y`, which is why the narrow instance exists at all.

## The two containments

With `A = 17 r` the stub has longitudinal range `[5r, 22r]` and transverse radius `2r`, and its
target is the part of it at longitudinal coordinate at least `18 r`.

* `dbox_subset_cube_union_stub`: the long box `D'`, whose longitudinal range is `[-2r, 22r]`,
  splits into the head cube `c_z + Λ_{5r}` and the stub.  The head cube lies in `Q z`, hence in
  `E w z`; the rest of `D'` is exactly the isotropic corridor `H_iso` of the note, of longitudinal
  range `[5r, 22r]` and transverse radius `2r`, and that is contained in the stub because
  `2 r ≤ MacroExp.rad (2 r) t j` for every `j`.
* `cube_subset_stubTarget`: the isotropic core `c_y + Λ_{2r}` produced by the cascade has
  longitudinal coordinate in `[18r, 22r]` and transverse radius `2r`, so it lies inside
  `Stopped.stubTarget`.

Both need only the hypothesis `5 r ≤ t` already carried by `corridorMove`.

## Interface

`corridorMoveNarrow` states the bound in the form (7.1) of `math/CORRIDOR_TRANSFER.md`, with the
allowed set written out as `h.inspected ∪ E w z ∪ Stopped.stub`.  `corridorEvent_eq` identifies
that event with `Stopped.corridorEvent d r t (17*r) k z i σ` for any transcript `k` whose inspected
set is `h.inspected ∪ E w z`, which is what the incoming examination produces on every atom, and
`prob_corridorEvent_compl_le` states the same bound in the complement form the stopped theorems
take as `hcorr`.  Both are stated under the **pre-examination** law `h.prob`; no estimate is
carried across the incoming reveal.

## Hypotheses

`corridorMoveNarrow` adds no hypothesis to `corridorMove`.  It drops `hEDom : E z y ⊆ Dom` and
fixes `Dom` to the narrow region; `hface`, `hlong` and `hsrc` are the same three interfaces, read
at that smaller region.  The closing section records the regression checks of §8 of the note that
are cheap in Lean: the target is nonempty, is not a single designated site, and lies inside the
allowed region; and the side hypotheses are jointly satisfiable by an explicit witness.
-/

noncomputable section

namespace KNAll.Site.CorrMove

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

section NarrowGeometry

variable {d : ℕ} [NeZero d]

/-- **The long box splits into the head cube and the stub.**  This is `H_iso ⊆ stub_y` of (7.3)
in the form the cascade needs: the part of `D'` at signed longitudinal coordinate at most `5 r`
lies in the head cube `c_z + Λ_{5r}`, and the rest is the isotropic corridor of longitudinal
range `[5r, 22r]` and transverse radius `2 r`, which is inside the stub of height `17 r`. -/
theorem dbox_subset_cube_union_stub {r t : ℕ} (ht : 5 * r ≤ t) (z : Site 2) {i : Fin d} {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ)) ⊆
      cube (MacroExp.ctr d r z) (5 * (r : ℤ)) ∪
        Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) := by
  classical
  have ht' : 5 * (r : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
  intro x hx
  rw [mem_dbox hσ] at hx
  obtain ⟨⟨hlo, hhi⟩, htrans⟩ := hx
  by_cases hnear : σ * (x i - MacroExp.ctr d r z i) ≤ 5 * (r : ℤ)
  · refine Finset.mem_union_left _ ?_
    rw [mem_cube]
    intro j
    rcases eq_or_ne j i with rfl | hj
    · have habs : |x j - MacroExp.ctr d r z j|
          = |σ * (x j - MacroExp.ctr d r z j)| :=
        (abs_signed (σ := σ) (a := x j - MacroExp.ctr d r z j) hσ).symm
      rw [habs, abs_le]
      omega
    · exact le_trans (htrans j hj) (by omega)
  · push_neg at hnear
    refine Finset.mem_union_right _ ?_
    rw [Stopped.mem_stub hσ]
    simp only [Stopped.lam]
    refine ⟨by omega, ?_, ?_⟩
    · have hcast : ((5 * r + 17 * r : ℕ) : ℤ) = 22 * (r : ℤ) := by push_cast; ring
      rw [hcast]
      exact hhi
    · intro j hj
      have hj' := htrans j hj
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hj'

/-- **The isotropic core at `y` lies in the stopped target.**  This is `c_y + Λ_{2r} ⊆
stubTarget_y` of (7.3): relative to `c_z` the core has longitudinal coordinate in `[18r, 22r]`,
which is inside the stub of height `17 r` and beyond the threshold `18 r` of its target. -/
theorem cube_subset_stubTarget {r t : ℕ} (ht : 5 * r ≤ t) {z y : Site 2} {i : Fin d} {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) :
    cube (MacroExp.ctr d r y) (2 * (r : ℤ)) ⊆
      Stopped.stubTarget (MacroExp.ctr d r z) i σ r t (17 * r) := by
  classical
  have ht' : 5 * (r : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
  have hr0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
  have hcy : (MacroExp.ctr d r y : Site d)
      = MacroExp.ctr d r z + Pi.single i (σ * (20 * (r : ℤ))) := ctr_add_dir r hemb
  intro x hx
  rw [mem_cube] at hx
  -- the longitudinal coordinate
  have hi := hx i
  rw [hcy] at hi
  simp only [Pi.add_apply, Pi.single_eq_same] at hi
  have heq : σ * (x i - MacroExp.ctr d r z i) - 20 * (r : ℤ)
      = σ * (x i - (MacroExp.ctr d r z i + σ * (20 * (r : ℤ)))) := by
    linear_combination (20 * (r : ℤ)) * hσ2
  have habs : |σ * (x i - MacroExp.ctr d r z i) - 20 * (r : ℤ)| ≤ 2 * (r : ℤ) := by
    rw [heq, abs_signed hσ]
    exact hi
  rw [abs_le] at habs
  -- the transverse coordinates
  have htr : ∀ j, j ≠ i → |x j - MacroExp.ctr d r z j| ≤ 2 * (r : ℤ) := by
    intro j hj
    have hj' := hx j
    rw [hcy] at hj'
    simpa only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero] using hj'
  rw [Stopped.stubTarget, Finset.mem_filter, Stopped.mem_stub hσ]
  simp only [Stopped.lam]
  refine ⟨⟨by omega, ?_, ?_⟩, by push_cast; omega⟩
  · have hcast : ((5 * r + 17 * r : ℕ) : ℤ) = 22 * (r : ℤ) := by push_cast; ring
    rw [hcast]
    omega
  · intro j hj
    have hj' := htr j hj
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hj'

end NarrowGeometry

section Narrow

variable {d : ℕ} [NeZero d]

/-- Every set the narrow interfaces mention lies inside the narrow allowed region.  This is the
first half: the incoming edge region carries the whole central cube `c_z + Λ_{5r}`, hence both the
subbox `Sub` of the `d` cross-section reductions and the target `c_z + Λ_{3r}` of the incoming
reservation `hsrc`. -/
theorem cube_subset_narrowDom (hd : 2 ≤ d) {r t : ℕ} (hr : 0 < r) (ht : 5 * r ≤ t)
    (h : MacroExp.Tr d) {w z : Site 2} (hwz : w ≠ z) (i : Fin d) (σ : ℤ) {s : ℤ}
    (hs : s ≤ 5 * (r : ℤ)) :
    cube (MacroExp.ctr d r z) s ⊆
      h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) := by
  refine le_trans (ibox_mono fun _ => hs) ?_
  exact le_trans (le_trans (cube_subset_Q ht z) (Q_subset_E hd r t hr hwz))
    (le_trans Finset.subset_union_right Finset.subset_union_left)

/-- The second half: the long box of the final move splits between the incoming edge region and
the stub. -/
theorem dbox_subset_narrowDom (hd : 2 ≤ d) {r t : ℕ} (hr : 0 < r) (ht : 5 * r ≤ t)
    (h : MacroExp.Tr d) {w z : Site 2} (hwz : w ≠ z) {i : Fin d} {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ)) ⊆
      h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) :=
  le_trans (dbox_subset_cube_union_stub ht z hσ)
    (Finset.union_subset (cube_subset_narrowDom hd hr ht h hwz i σ le_rfl)
      Finset.subset_union_right)

/-- **(7.1).  The corridor move with the narrow allowed set and the narrow target.**

Same hypotheses as `corridorMove`, except that the allowed region is fixed to the narrow set
`I ∪ E w z ∪ stub_y` of (7.4) and the containment `E z y ⊆ Dom` is dropped; `hface`, `hlong` and
`hsrc` are the same three interfaces of manuscript Lemma 7.3, read at that smaller region.

The conclusion is the pre-examination estimate the finite-atom tower of §5 of
`math/CORRIDOR_TRANSFER.md` consumes: the origin reaches `Stopped.stubTarget` inside
`h.inspected ∪ E w z ∪ Stopped.stub` with probability more than `1 - ρ/32`.  The tolerance scheme
is unchanged: `α = ρ/32`, `J = d+1`, `f a = a²/96`, and the input reservation to the isotropic
core `c_z + Λ_{3r}` is at error `beta ρ d = (ρ/32)^(2^(d+1)) / 96^(2^(d+1)-1)`. -/
theorem corridorMoveNarrow (hd : 2 ≤ d) {r t R : ℕ} {h : MacroExp.Tr d} {q : unitInterval}
    {w z y : Site 2} {i : Fin d} {σ : ℤ} {ρ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ)
    (h44 : 44 ≤ r) (hR1 : 1 ≤ R) (hscale : 100 * (d + 1) * (R + 1) < r) (ht : 5 * r ≤ t)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hwz : w ≠ z)
    (hfresh : Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y))
    (hzero : (MacroExp.emb 0 : Site d) ∉ MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (hface : ∀ (Sub Bset Tset : Finset (Site d)) (ε : ℝ), 0 < ε → ε ≤ 1 →
      Disjoint h.inspected Sub → (MacroExp.emb 0 : Site d) ∉ Sub →
      Sub ⊆ h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) →
      FaceTarget (R : ℤ) Sub Bset Tset →
      1 - ε / 8 < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d)
          (↑(h.inspected ∪ MacroExp.E d r t w z ∪
            Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
          (MacroExp.emb 0) (↑Bset : Set (Site d))) →
      1 - ε < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d)
          (↑(h.inspected ∪ MacroExp.E d r t w z ∪
            Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
          (MacroExp.emb 0) (↑Tset : Set (Site d))))
    (hlong : ∀ (Sub Bset Tset : Finset (Site d)) (ε : ℝ), 0 < ε → ε ≤ 1 →
      Disjoint h.inspected Sub → (MacroExp.emb 0 : Site d) ∉ Sub →
      Sub ⊆ h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) →
      LongTarget (R : ℤ) i σ Sub Bset Tset →
      1 - ε / 8 < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d)
          (↑(h.inspected ∪ MacroExp.E d r t w z ∪
            Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
          (MacroExp.emb 0) (↑Bset : Set (Site d))) →
      1 - ε < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d)
          (↑(h.inspected ∪ MacroExp.E d r t w z ∪
            Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
          (MacroExp.emb 0) (↑Tset : Set (Site d))))
    (hsrc : 1 - beta ρ d < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(cube (MacroExp.ctr d r z) (3 * (r : ℤ))) : Set (Site d)))) :
    1 - ρ / 32 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))) := by
  classical
  set Dnar : Finset (Site d) := h.inspected ∪ MacroExp.E d r t w z ∪
    Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) with hDnar
  -- the head cube lies in `Q z`, hence in `E w z`, hence in the narrow region
  have hcube5Q : cube (MacroExp.ctr d r z) (5 * (r : ℤ)) ⊆ MacroExp.Q d r t z :=
    cube_subset_Q ht z
  have hQEwz : MacroExp.Q d r t z ⊆ MacroExp.E d r t w z :=
    Q_subset_E hd r t (by omega) hwz
  have hEDnar : MacroExp.E d r t w z ⊆ Dnar :=
    le_trans Finset.subset_union_right Finset.subset_union_left
  have hstubDnar : Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) ⊆ Dnar :=
    Finset.subset_union_right
  have hdom5 : cube (MacroExp.ctr d r z) (5 * (r : ℤ)) ⊆ Dnar :=
    cube_subset_narrowDom hd (by omega) ht h hwz i σ le_rfl
  have hdomD : dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ)) ⊆
      Dnar :=
    dbox_subset_narrowDom hd (by omega) ht h hwz hσ
  -- freshness and origin exclusion, exactly as in `corridorMove`
  have hcube5 : cube (MacroExp.ctr d r z) (5 * (r : ℤ)) ⊆
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y :=
    le_trans hcube5Q Finset.subset_union_left
  have hdb : dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ)) ⊆
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y :=
    dbox_subset_Q_union_E (by omega) ht hσ hemb
  have hfin := corridorMoveCore hσ hemb h44 hR1 hscale hρ0 hρ1 Dnar
    (hfresh.mono_right hcube5) (hfresh.mono_right hdb)
    (fun hcon => hzero (hcube5 hcon)) (fun hcon => hzero (hdb hcon))
    hdom5 hdomD hface hlong hsrc
  -- from the isotropic core at `y` to the stopped target
  refine lt_of_lt_of_le hfin (ProbInv.prob_mono h _ ?_)
  intro ω hω
  rw [mem_connWithinSet_iff] at hω ⊢
  obtain ⟨b, hb, hconn⟩ := hω
  exact ⟨b, Finset.mem_coe.2 (cube_subset_stubTarget ht hσ hemb (Finset.mem_coe.1 hb)), hconn⟩

/-- The narrow event of `corridorMoveNarrow` **is** `Stopped.corridorEvent` at any transcript whose
inspected set is the pre-examination one together with the incoming region.  That is the inspected
set of every atom `h.step z (E w z) true ω` of the incoming examination, by
`FRDom.Transcript.step_inspected`. -/
theorem corridorEvent_eq {r t : ℕ} (h k : MacroExp.Tr d) (z : Site 2) (i : Fin d) (σ : ℤ)
    (w : Site 2) (hk : k.inspected = h.inspected ∪ MacroExp.E d r t w z) :
    Stopped.corridorEvent d r t (17 * r) k z i σ =
      connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d)) := by
  rw [Stopped.corridorEvent, hk]

/-- **(7.1) in the complement form the stopped theorems take as `hcorr`.**  The estimate is stated
under the pre-examination law `h.prob`, while the event is the corridor event of the
post-examination transcript `k`; by (5.8) that event does not depend on which incoming pattern `k`
records, only on `k.inspected`. -/
theorem prob_corridorEvent_compl_le {r t : ℕ} {h k : MacroExp.Tr d} {q : unitInterval}
    {w z : Site 2} {i : Fin d} {σ : ℤ} {ρ : ℝ}
    (hk : k.inspected = h.inspected ∪ MacroExp.E d r t w z)
    (hnar : 1 - ρ / 32 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d)))) :
    h.prob (fun _ : Site d => q)
      (Stopped.corridorEvent d r t (17 * r) k z i σ)ᶜ ≤ ρ / 32 := by
  have hm : MeasurableSet
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(Stopped.stubTarget (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))) :=
    measurableSet_connWithinSet _ _ _ _
  rw [corridorEvent_eq h k z i σ w hk, FRDom.Transcript.prob_eq, pinnedProb_compl _ _ _ hm,
    ← FRDom.Transcript.prob_eq]
  linarith

end Narrow

/-! ## §8.  The four regression checks -/

section Regression

variable {d : ℕ} [NeZero d]

/-- **§8.2.  The narrow target is not empty.**  Its axial site at longitudinal coordinate `20 r`
is the centre of the target box of `y`. -/
theorem stubTarget_nonempty' {r t : ℕ} (z : Site 2) (i : Fin d) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    (Stopped.stubTarget (MacroExp.ctr d r z) i σ r t (17 * r)).Nonempty :=
  Stopped.stubTarget_nonempty _ i hσ (by omega)

/-- **§8.2.  The narrow target lies inside the narrow allowed region**, so the success event is not
empty for the trivial reason that no allowed path can end in it. -/
theorem stubTarget_subset_narrowDom {r t : ℕ} (h : MacroExp.Tr d) (w z : Site 2) (i : Fin d)
    (σ : ℤ) :
    Stopped.stubTarget (MacroExp.ctr d r z) i σ r t (17 * r) ⊆
      h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) :=
  le_trans (Finset.filter_subset _ _) Finset.subset_union_right

/-- **§8.1.  The narrow target is not a designated single site.**  It contains the whole isotropic
core `c_y + Λ_{2r}`, hence at least two sites, so the success probability of the narrow event is
not capped by a single-site factor `q`. -/
theorem one_lt_card_stubTarget {r t : ℕ} (hr : 0 < r) (ht : 5 * r ≤ t) {z y : Site 2} {i : Fin d}
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) :
    1 < (Stopped.stubTarget (MacroExp.ctr d r z) i σ r t (17 * r)).card := by
  classical
  have hr0 : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hsub := cube_subset_stubTarget (d := d) ht hσ hemb
  have h1 : (MacroExp.ctr d r y : Site d) ∈ cube (MacroExp.ctr d r y) (2 * (r : ℤ)) :=
    centre_mem_cube (by omega)
  have h2 : (MacroExp.ctr d r y + Pi.single i (1 : ℤ) : Site d) ∈
      cube (MacroExp.ctr d r y) (2 * (r : ℤ)) := by
    rw [mem_cube]
    intro j
    rcases eq_or_ne j i with rfl | hj
    · simp only [Pi.add_apply, Pi.single_eq_same, add_sub_cancel_left]
      rw [abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 1)]
      omega
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero, sub_self, abs_zero]
      omega
  refine Finset.one_lt_card.2 ⟨_, hsub h1, _, hsub h2, ?_⟩
  intro hcon
  have hco := congrFun hcon i
  simp only [Pi.add_apply, Pi.single_eq_same] at hco
  omega

/-- **§8.2.  `hsrc` forces the origin into the narrow allowed region.**  If the incoming
reservation holds at the narrow region, its success event is not empty, and every configuration in
it has `MacroExp.emb 0` inside that region.  So the narrow interfaces do not silently ask for a
connection whose source lies outside the allowed set, and the requirement is compatible with
`hzero` and `hfresh`: `narrow_side_hypotheses_satisfiable` exhibits a transcript satisfying all
three at once. -/
theorem zero_mem_narrowDom_of_src {r t : ℕ} {h : MacroExp.Tr d} {q : unitInterval} {w z : Site 2}
    {i : Fin d} {σ : ℤ} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsrc : 1 - beta ρ d < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑(h.inspected ∪ MacroExp.E d r t w z ∪
          Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
        (MacroExp.emb 0)
        (↑(cube (MacroExp.ctr d r z) (3 * (r : ℤ))) : Set (Site d)))) :
    (MacroExp.emb 0 : Site d) ∈ h.inspected ∪ MacroExp.E d r t w z ∪
      Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r) := by
  by_contra hcon
  have hempty : connWithinSet (zdGraph d)
      (↑(h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i σ r t (17 * r)) : Set (Site d))
      (MacroExp.emb 0)
      (↑(cube (MacroExp.ctr d r z) (3 * (r : ℤ))) : Set (Site d)) = ∅ := by
    ext ω
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hω
    rw [mem_connWithinSet_iff] at hω
    obtain ⟨a, -, ha⟩ := hω
    exact hcon (Finset.mem_coe.1 ha.1.2)
  have hb : beta ρ d ≤ ρ / 32 := beta_le hρ0 hρ1 d
  rw [hempty, FRDom.Transcript.prob_eq, pinnedProb_emptyEvent] at hsrc
  linarith

/-- **§8.4.  The side hypotheses of `corridorMoveNarrow` are jointly satisfiable.**

The witness is `d = 2`, `R = 1`, any `601 ≤ r`, any `t ≥ 5 r`, `ρ = 1`, the collinear macro triple
`w = (4,0)`, `z = (5,0)`, `y = (6,0)` in the direction `(0, 1)`, and the transcript that has read
only the origin and found it open.  The last two clauses are the ones that matter: the origin is
inside the narrow allowed region, and simultaneously outside the fresh subbox `Q z ∪ E z y`, so
`hzero` and `hfresh` do not conflict with the narrow region containing the source of the
connection.  The analytic hypotheses `hface`, `hlong` and `hsrc` are not part of this claim; they
are the same three target-extension interfaces as in `corridorMove`, read at the narrow region. -/
theorem narrow_side_hypotheses_satisfiable {r t : ℕ} (hr : 601 ≤ r) (ht : 5 * r ≤ t) :
    ∃ (h : MacroExp.Tr 2) (w z y : Site 2) (i : Fin 2) (σ : ℤ),
      (σ = 1 ∨ σ = -1) ∧
      (MacroExp.emb (y - z) : Site 2) = Pi.single i σ ∧
      44 ≤ r ∧ 1 ≤ 1 ∧ 100 * (2 + 1) * (1 + 1) < r ∧ 5 * r ≤ t ∧
      (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ w ≠ z ∧
      Disjoint h.inspected (MacroExp.Q 2 r t z ∪ MacroExp.E 2 r t z y) ∧
      (MacroExp.emb 0 : Site 2) ∉ MacroExp.Q 2 r t z ∪ MacroExp.E 2 r t z y ∧
      (MacroExp.emb 0 : Site 2) ∈ h.inspected ∪ MacroExp.E 2 r t w z ∪
        Stopped.stub (MacroExp.ctr 2 r z) i σ r t (17 * r) := by
  classical
  have hlt : ((0 : Fin 2) : ℕ) < 2 := by norm_num
  have hctrz : MacroExp.ctr 2 r (![5, 0] : Site 2) 0 = 100 * (r : ℤ) := by
    rw [MacroExp.ctr_apply_of_lt r _ hlt]
    norm_num
    ring
  have hctry : MacroExp.ctr 2 r (![6, 0] : Site 2) 0 = 120 * (r : ℤ) := by
    rw [MacroExp.ctr_apply_of_lt r _ hlt]
    norm_num
    ring
  have hrad : MacroExp.rad (5 * r) t (0 : Fin 2) = ((5 * r : ℕ) : ℤ) := by
    rw [MacroExp.rad, if_pos hlt]
  have hout : (MacroExp.emb 0 : Site 2) ∉
      MacroExp.Q 2 r t (![5, 0] : Site 2) ∪ MacroExp.E 2 r t (![5, 0] : Site 2)
        (![6, 0] : Site 2) := by
    intro hcon
    have hzero0 : (MacroExp.emb (0 : Site 2) : Site 2) 0 = 0 := by
      rw [MacroExp.emb_zero]; rfl
    rcases Finset.mem_union.1 hcon with hQ | hE
    · rw [MacroExp.Q, MacroExp.mem_abox] at hQ
      have hq := (hQ 0).1
      rw [hctrz, hrad, hzero0] at hq
      push_cast at hq
      omega
    · rw [MacroExp.E, Finset.mem_sdiff, MacroExp.mem_hbox] at hE
      have hq := (hE.1 0).1
      rw [hctrz, hctry, hrad, hzero0] at hq
      push_cast at hq
      omega
  refine ⟨⟨{0}, {0}, by simp, ∅, ∅⟩, ![4, 0], ![5, 0], ![6, 0], 0, 1, Or.inl rfl, ?_, by omega,
    le_rfl, by omega, ht, by norm_num, le_rfl, ?_, ?_, hout, ?_⟩
  · funext j
    fin_cases j <;> simp [MacroExp.emb]
  · intro hcon
    have hc := congrFun hcon 0
    norm_num at hc
  · rw [Finset.disjoint_left]
    intro a ha hb
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    exact hout (by simpa [MacroExp.emb_zero] using hb)
  · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    rw [Finset.mem_singleton, MacroExp.emb_zero]

end Regression

#print axioms KNAll.Site.CorrMove.corridorMoveNarrow
#print axioms KNAll.Site.CorrMove.zero_mem_narrowDom_of_src
#print axioms KNAll.Site.CorrMove.narrow_side_hypotheses_satisfiable
#print axioms KNAll.Site.CorrMove.one_lt_card_stubTarget
#print axioms KNAll.Site.CorrMove.prob_corridorEvent_compl_le
#print axioms KNAll.Site.CorrMove.corridorEvent_eq
#print axioms KNAll.Site.CorrMove.cube_subset_stubTarget
#print axioms KNAll.Site.CorrMove.dbox_subset_cube_union_stub

end KNAll.Site.CorrMove

end
