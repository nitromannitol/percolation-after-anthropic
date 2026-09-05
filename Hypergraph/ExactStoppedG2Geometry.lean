import Hypergraph.ExactMacroGeometry
import Hypergraph.ExactLongBoxVariablePlan

/-!
# The literal v15 stopped-target geometry (G2)

This module formalizes clause (G2) of the manuscript lemma *Initial and stopped-target geometry*
(v15, lines 3138--3225) for the corrected isotropic stopped stub, and packages the finite shapes
that `ExactMacroGeometry.StoppedChildren` and `ExactLongBoxVariablePlan` consume.

Throughout `K ≥ 20`, `0 < s`, `r = K * s`, `2 * R ≤ s` and `j < K`, and the oriented macro edge
`z → y` has centre displacement `c_y - c_z = 20 r σ e_i`, recorded as
`MacroExp.emb (y - z) = Pi.single i σ`.

## The (G2) data

* `axial r s j = a_j = 5 r + 10 s (j+1)` — the signed axial coordinate of the level-`j` face.
* `Dbox c i σ r s j = D_j` — signed axial interval `[5 r + 10 s j + 1, 25 r]`, transverse
  half-width `5 r`.  This is `CorrMove.dbox`, so it is isotropic in every transverse coordinate.
* `B_j = Stopped.stubFace (MacroExp.ctr d r z) i σ r t (10 * s * (j+1))` — the corrected
  isotropic outgoing face `F^{j+1}_{z,y}`, of transverse half-width `2 r`.
* `ell K r s j = ℓ_j = ⌊(20 r - a_j) / (2 K)⌋`.
* the aspect is `2 * K`; `LongTargetAspect` is the aspect-`A` analogue of `CorrMove.LongTarget`,
  which is hard-coded to the corridor aspect `88`.

## What is proved

* `radius_le_ell` : `R ≤ ℓ_j`, together with the manuscript's companion bounds
  `two_s_le_ell` (`2 s ≤ ℓ_j`), `two_ell_le` (`2 ℓ_j ≤ 15 s`) and `ell_add_le`
  (`ℓ_j + R ≤ 8 s`), which are (eq:stopped-ell-bounds).
* `longBox_subset_Dbox` : for every source-plus point `v` the aspect-`2K` long box
  `CorrMove.longBox v ℓ_j i σ (2K)` — the shape `LongBoxVariable` fills — lies in `D_j`.
* `longFace_subset_cube`, `longTargetAspect_of_face` : its far face lies in the isotropic cube of
  radius `ρ` about `c_y` whenever the deterministic inequalities
  `w + R + ℓ_j ≤ ρ` and `2 K + R ≤ ρ + 1` hold.
* `longTargetAspect_stubFace_M` : the literal v15 conclusion, `T_j = M_y`, at the actual face
  half-width `2 r`.
* `longTargetAspect_stubFace_core` : the same conclusion with `T_j = CoreRes.target r y`, the
  radius-`3r` isotropic core the exact interpreter stores as its recursive reservation target.
  `sharp_face_radius` records that the reachable isotropic radius from the `2r`-wide face is
  exactly `2 r + ℓ_j + R`; by `ell_pos` this exceeds `2 r`, so the `3 r` core radius is what makes
  the stopped child's `target_subset` field attainable by the long move alone.
* `Dbox_subset_E` : `D_j ⊆ MacroExp.E d r t z y`.
* `stub_disjoint_Dbox` : the prefix `H^j_{z,y}` already revealed at level `j` is disjoint from
  `D_j`; the gap is the single lattice step `5 r + 10 s j + 1`.
* `DIntBox_sites_eq`, `faceIntBox_sites_eq` : `D_j` and `B_j` as `ExactTargetPlan.IntBox`es.
* `stoppedChildren` : the finite constructor of `ExactMacroGeometry.StoppedChildren` whose
  geometric fields are exactly the theorems above.
* `longScale_eq`, `longRem_le`, `scale_budget`, `allowedRegion_subset_longBox_ell` : the aspect,
  tile scale and budget needed to instantiate `ExactLongBoxVariablePlan.SchemeFamily.planAt` at
  scale `ℓ_j`.

Only deterministic finite geometry and integer arithmetic occur here.  There are no probability
hypotheses, no theorem-valued fields, and every parameter is an explicit numerical inequality.
-/

noncomputable section

namespace KNAll.Site.ExactStoppedG2

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## §1.  The literal (G2) integers -/

section Arithmetic

/-- `a_j = 5 r + 10 s (j+1)`, the signed axial coordinate of the level-`j` outgoing face. -/
def axial (r s j : Nat) : Nat := 5 * r + 10 * s * (j + 1)

/-- `20 r - a_j`, the residual axial distance from the level-`j` face to `c_y`. -/
def gap (r s j : Nat) : Nat := 20 * r - axial r s j

/-- `ℓ_j = ⌊(20 r - a_j) / (2 K)⌋`, the scale of the aspect-`2K` stopped long move. -/
def ell (K r s j : Nat) : Nat := gap r s j / (2 * K)

/-- The aspect of the stopped long move. -/
def aspect (K : Nat) : Nat := 2 * K

theorem tail_split (s j : Nat) : 10 * s * (j + 1) = 10 * s * j + 10 * s := by ring

theorem tail_le_of_lt {K s j : Nat} (hj : j < K) : 10 * s * (j + 1) ≤ 10 * s * K :=
  Nat.mul_le_mul (le_refl (10 * s)) (show j + 1 ≤ K by omega)

theorem tail_top {K r s : Nat} (hr : r = K * s) : 10 * s * K = 10 * r := by
  subst hr; ring

/-- `a_j ≤ 15 r`: the last face is at `15 r`, five macro radii short of `c_y`. -/
theorem axial_add_five_le {K r s j : Nat} (hr : r = K * s) (hj : j < K) :
    axial r s j + 5 * r ≤ 20 * r := by
  have h1 := tail_le_of_lt (K := K) (s := s) hj
  have h2 := tail_top (K := K) (r := r) (s := s) hr
  unfold axial
  omega

theorem gap_add_axial {K r s j : Nat} (hr : r = K * s) (hj : j < K) :
    gap r s j + axial r s j = 20 * r := by
  have h := axial_add_five_le (K := K) hr hj
  unfold gap
  omega

/-- `5 r ≤ 20 r - a_j`, the first half of the manuscript's `5r ≤ 20r - a_j ≤ 15r - 10s`. -/
theorem five_r_le_gap {K r s j : Nat} (hr : r = K * s) (hj : j < K) :
    5 * r ≤ gap r s j := by
  have h1 := gap_add_axial (K := K) hr hj
  have h2 := axial_add_five_le (K := K) hr hj
  omega

/-- `20 r - a_j ≤ 15 r - 10 s`, the second half. -/
theorem gap_add_ten_le {K r s j : Nat} (hr : r = K * s) (hj : j < K) :
    gap r s j + 10 * s ≤ 15 * r := by
  have h1 := gap_add_axial (K := K) hr hj
  have h2 := tail_split s j
  unfold axial at h1
  omega

theorem ell_le_gap {K r s j : Nat} (hK : 0 < K) :
    2 * K * ell K r s j ≤ gap r s j := by
  have h := Nat.div_add_mod (gap r s j) (2 * K)
  have hmod : gap r s j % (2 * K) < 2 * K := Nat.mod_lt _ (by omega)
  unfold ell
  omega

theorem gap_lt_ell {K r s j : Nat} (hK : 0 < K) :
    gap r s j < 2 * K * ell K r s j + 2 * K := by
  have h := Nat.div_add_mod (gap r s j) (2 * K)
  have hmod : gap r s j % (2 * K) < 2 * K := Nat.mod_lt _ (by omega)
  unfold ell
  omega

/-- `2 s ≤ ℓ_j`, the manuscript's `⌊5s/2⌋ ≥ 2s`. -/
theorem two_s_le_ell {K r s j : Nat} (hK : 20 ≤ K) (hr : r = K * s) (hj : j < K) :
    2 * s ≤ ell K r s j := by
  have h5 := five_r_le_gap (K := K) hr hj
  have hmul : 2 * s * (2 * K) = 4 * r := by subst hr; ring
  unfold ell
  rw [Nat.le_div_iff_mul_le (show 0 < 2 * K by omega)]
  omega

/-- `ℓ_j ≤ 15 s / 2`. -/
theorem two_ell_le {K r s j : Nat} (hK : 20 ≤ K) (hr : r = K * s) (hj : j < K) :
    2 * ell K r s j ≤ 15 * s := by
  have h1 := ell_le_gap (K := K) (r := r) (s := s) (j := j) (show 0 < K by omega)
  have h2 := gap_add_ten_le (K := K) hr hj
  have h3 : 2 * K * ell K r s j = K * (2 * ell K r s j) := by ring
  have h4 : 15 * r = K * (15 * s) := by subst hr; ring
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < K by omega)
  omega

/-- `ℓ_j + R ≤ 8 s`, the last of (eq:stopped-ell-bounds). -/
theorem ell_add_le {K r s j R : Nat} (hK : 20 ≤ K) (hr : r = K * s) (hj : j < K)
    (hR : 2 * R ≤ s) : ell K r s j + R ≤ 8 * s := by
  have h := two_ell_le (K := K) hK hr hj
  omega

/-- **`R ≤ ℓ_j`.**  The stopped long move is never asked for a scale below the extraction
radius. -/
theorem radius_le_ell {K r s j R : Nat} (hK : 20 ≤ K) (hr : r = K * s) (hj : j < K)
    (hR : 2 * R ≤ s) : R ≤ ell K r s j := by
  have h := two_s_le_ell (K := K) hK hr hj
  omega

theorem ell_pos {K r s j : Nat} (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hj : j < K) :
    0 < ell K r s j := by
  have h := two_s_le_ell (K := K) hK hr hj
  omega

theorem eight_s_le_r {K r s : Nat} (hK : 20 ≤ K) (hr : r = K * s) : 8 * s ≤ r := by
  have h : 20 * s ≤ K * s := Nat.mul_le_mul hK (le_refl s)
  omega

/-- The far face of the stopped long move overshoots `c_y` axially by at most `2 K + R - 1`,
which the radius-`2r` core already absorbs. -/
theorem two_K_add_le {K r s R : Nat} (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s)
    (hR : 2 * R ≤ s) : 2 * K + R ≤ 2 * r + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  subst hr
  have hm : m ≤ K * m := Nat.le_mul_of_pos_left m (by omega)
  have hks : K * (m + 1) = K * m + K := by ring
  omega

/-- The lower endpoint of `D_j` is below its upper endpoint. -/
theorem Dbox_ordered_nat {K r s j : Nat} (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s)
    (hj : j < K) : 5 * r + 10 * s * j + 1 ≤ 25 * r := by
  have h1 := tail_le_of_lt (K := K) (s := s) hj
  have h2 := tail_top (K := K) (r := r) (s := s) hr
  have h3 := tail_split s j
  have h4 : 20 * s ≤ K * s := Nat.mul_le_mul hK (le_refl s)
  omega

end Arithmetic

/-! ## §2.  The literal boxes -/

section Boxes

variable {d : Nat}

/-- **`D_j`.**  Signed axial interval `[5 r + 10 s j + 1, 25 r]`, transverse half-width `5 r`. -/
def Dbox (c : Site d) (i : Fin d) (sigma : Int) (r s j : Nat) : Finset (Site d) :=
  CorrMove.dbox c i sigma (((5 * r + 10 * s * j : Nat) : Int) + 1)
    ((25 * r : Nat) : Int) ((5 * r : Nat) : Int)

theorem mem_Dbox {c x : Site d} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {r s j : Nat} :
    x ∈ Dbox c i sigma r s j ↔
      ((((5 * r + 10 * s * j : Nat) : Int) + 1 ≤ Stopped.lam c i sigma x ∧
          Stopped.lam c i sigma x ≤ ((25 * r : Nat) : Int)) ∧
        ∀ k, k ≠ i → |x k - c k| ≤ ((5 * r : Nat) : Int)) := by
  rw [Dbox, CorrMove.mem_dbox hsigma]
  simp only [Stopped.lam]

/-- **The prefix gap.**  The stub already revealed at level `j` stops at `5 r + 10 s j`, one
lattice step before `D_j` begins. -/
theorem stub_disjoint_Dbox {c : Site d} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (r t s j : Nat) :
    Disjoint (Stopped.stub c i sigma r t (10 * s * j)) (Dbox c i sigma r s j) := by
  rw [Finset.disjoint_left]
  intro x hxstub hxD
  rw [Stopped.mem_stub hsigma] at hxstub
  rw [mem_Dbox hsigma] at hxD
  have h1 := hxstub.2.1
  have h2 := hxD.1.1
  omega

/-- **`D_j ⊆ E(z,y)`.**  Everything beyond the outgoing face of `Q z` and before `25 r` lies in
the outgoing edge region of the pending direction. -/
theorem Dbox_subset_E {r t s j : Nat} (hr : 0 < r) (ht : 5 * r ≤ t)
    {z y : Site 2} {i : Fin d} {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    Dbox (MacroExp.ctr d r z) i sigma r s j ⊆ MacroExp.E d r t z y := by
  intro x hx
  rw [mem_Dbox hsigma] at hx
  obtain ⟨⟨hlo, hhi⟩, htr⟩ := hx
  have hiplanar : i.val < 2 := Stopped.dir_planar hsigma hemb
  have hradi : MacroExp.rad (5 * r) t i = 5 * (r : Int) := by
    unfold MacroExp.rad
    rw [if_pos hiplanar]
    push_cast
    ring
  have hnn : (0 : Int) ≤ 10 * (s : Int) * (j : Int) := by positivity
  have hrnn : (0 : Int) ≤ 20 * (r : Int) := by positivity
  have hlo' : 5 * (r : Int) < Stopped.lam (MacroExp.ctr d r z) i sigma x := by
    push_cast at hlo
    linarith
  have hhi' : Stopped.lam (MacroExp.ctr d r z) i sigma x ≤ 25 * (r : Int) := by
    push_cast at hhi
    linarith
  rw [MacroExp.E, Finset.mem_sdiff]
  constructor
  · rw [MacroExp.mem_hbox]
    intro k
    have hctr := Stopped.ctr_sub_apply (d := d) r y z k
    by_cases hki : k = i
    · subst hki
      rw [hemb, Pi.single_eq_same] at hctr
      rw [hradi]
      rcases hsigma with rfl | rfl
      · have hcy : MacroExp.ctr d r y k = MacroExp.ctr d r z k + 20 * (r : Int) := by
          linear_combination hctr
        have hlam : Stopped.lam (MacroExp.ctr d r z) k 1 x
            = x k - MacroExp.ctr d r z k := by
          simp only [Stopped.lam, one_mul]
        rw [hlam] at hlo' hhi'
        rw [hcy, min_eq_left (by linarith), max_eq_right (by linarith)]
        constructor <;> linarith
      · have hcy : MacroExp.ctr d r y k = MacroExp.ctr d r z k - 20 * (r : Int) := by
          linear_combination hctr
        have hlam : Stopped.lam (MacroExp.ctr d r z) k (-1) x
            = MacroExp.ctr d r z k - x k := by
          simp only [Stopped.lam, neg_one_mul]
          ring
        rw [hlam] at hlo' hhi'
        rw [hcy, min_eq_right (by linarith), max_eq_left (by linarith)]
        constructor <;> linarith
    · rw [hemb, Pi.single_eq_of_ne hki] at hctr
      have hcy : MacroExp.ctr d r y k = MacroExp.ctr d r z k := by linear_combination hctr
      have hb := htr k hki
      have hrad : ((5 * r : Nat) : Int) ≤ MacroExp.rad (5 * r) t k := by
        unfold MacroExp.rad
        split_ifs <;> push_cast <;> omega
      rw [abs_le] at hb
      rw [hcy, min_self, max_self]
      constructor <;> linarith
  · intro hQ
    rw [MacroExp.Q, MacroExp.mem_abox] at hQ
    have hQi := hQ i
    rw [hradi] at hQi
    have habs : |x i - MacroExp.ctr d r z i| ≤ 5 * (r : Int) := by
      rw [abs_le]
      constructor <;> linarith [hQi.1, hQi.2]
    rw [← Stopped.lam_abs hsigma (MacroExp.ctr d r z) i x] at habs
    have := (le_abs_self (Stopped.lam (MacroExp.ctr d r z) i sigma x)).trans habs
    linarith

end Boxes

/-! ## §3.  The aspect-`2K` long move -/

section LongMove

variable {d : Nat}

/-- The aspect-`A` analogue of `CorrMove.LongTarget`, which is hard-coded to the corridor
aspect `88`.  `Tset` is a long target for `Bset` inside `Sub` in the direction `(i, σ)` at aspect
`A` when every site within `R` of `Bset` carries an aspect-`A` long box of scale at least `R`,
contained in `Sub`, whose far face lies in `Tset`. -/
def LongTargetAspect (A R : Int) (i : Fin d) (sigma : Int)
    (Sub Bset Tset : Finset (Site d)) : Prop :=
  ∀ v : Site d, (∃ b ∈ Bset, ∀ k, |v k - b k| ≤ R) →
    ∃ l : Int, R ≤ l ∧ CorrMove.longBox v l i sigma A ⊆ Sub ∧
      CorrMove.longFace v l i sigma A ⊆ Tset

theorem LongTargetAspect.mono_target {A R : Int} {i : Fin d} {sigma : Int}
    {Sub Bset T T' : Finset (Site d)}
    (h : LongTargetAspect A R i sigma Sub Bset T) (hT : T ⊆ T') :
    LongTargetAspect A R i sigma Sub Bset T' := by
  intro v hv
  obtain ⟨l, hl, hbox, hface⟩ := h v hv
  exact ⟨l, hl, hbox, hface.trans hT⟩

/-- **(G2), containment.**  For every source-plus point `v` the aspect-`2K` long box of scale
`ℓ_j` based at `v` lies in `D_j`.  The rear endpoint clears `5 r + 10 s j` because
`ℓ_j + R ≤ 8 s < 10 s`, the forward endpoint stops at `20 r + R < 25 r`, and transversally
`w + ℓ_j ≤ 5 r`. -/
theorem longBox_subset_Dbox {c v : Site d} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    {K r s j R : Nat} {w : Int} (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hj : j < K)
    (hR : 2 * R ≤ s) (hwidth : w + ((ell K r s j : Nat) : Int) ≤ 5 * (r : Int))
    (hvlong : |Stopped.lam c i sigma v - ((axial r s j : Nat) : Int)| ≤ (R : Int))
    (hvtrans : ∀ k, k ≠ i → |v k - c k| ≤ w) :
    CorrMove.longBox v ((ell K r s j : Nat) : Int) i sigma (2 * (K : Int)) ⊆
      Dbox c i sigma r s j := by
  have hKZ : (1 : Int) ≤ 2 * (K : Int) := by
    have hKz : (20 : Int) ≤ (K : Int) := by exact_mod_cast hK
    linarith
  have hellZ : (0 : Int) ≤ ((ell K r s j : Nat) : Int) := by positivity
  have hgapax : ((gap r s j : Nat) : Int) + ((axial r s j : Nat) : Int) = 20 * (r : Int) := by
    exact_mod_cast gap_add_axial (K := K) hr hj
  have hax : ((axial r s j : Nat) : Int)
      = 5 * (r : Int) + ((10 * s * j : Nat) : Int) + 10 * (s : Int) := by
    unfold axial
    push_cast
    ring
  have hmul : 2 * (K : Int) * ((ell K r s j : Nat) : Int) ≤ ((gap r s j : Nat) : Int) := by
    exact_mod_cast ell_le_gap (K := K) (r := r) (s := s) (j := j) (show 0 < K by omega)
  have hsum : ((ell K r s j : Nat) : Int) + (R : Int) ≤ 8 * (s : Int) := by
    exact_mod_cast ell_add_le (K := K) hK hr hj hR
  have hRs : 2 * (R : Int) ≤ (s : Int) := by exact_mod_cast hR
  have hsr : 8 * (s : Int) ≤ (r : Int) := by exact_mod_cast eight_s_le_r (K := K) hK hr
  have hs1 : (1 : Int) ≤ (s : Int) := by exact_mod_cast hs
  have hnn : (0 : Int) ≤ ((10 * s * j : Nat) : Int) := by positivity
  intro x hx
  rw [CorrMove.mem_longBox hsigma hellZ hKZ] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  rw [abs_le] at hvlong
  have hsplit : Stopped.lam c i sigma x
      = sigma * (x i - v i) + Stopped.lam c i sigma v := by
    simp only [Stopped.lam]
    ring
  rw [mem_Dbox hsigma]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · push_cast
    rw [hsplit]
    push_cast at hax hnn
    linarith [hvlong.1]
  · push_cast
    rw [hsplit]
    linarith [hvlong.2]
  · intro k hk
    have hb := h3 k hk
    have hc := hvtrans k hk
    rw [abs_le] at hb hc ⊢
    push_cast
    constructor <;> linarith [hb.1, hb.2, hc.1, hc.2]

/-- **(G2), far face.**  The far face of the aspect-`2K` long box lies in the isotropic cube of
radius `ρ` about `c_y = c + 20 r σ e_i`, whenever `w + ℓ_j ≤ ρ` transversally and
`2 K + R ≤ ρ + 1` axially.  The axial bound is the manuscript's floor identity
`20 r - R - (2K-1) ≤ v_i + 2 K ℓ_j ≤ 20 r + R`. -/
theorem longFace_subset_cube {c v : Site d} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    {K r s j R : Nat} {w rho : Int} (hK : 20 ≤ K) (hr : r = K * s) (hj : j < K)
    (hwidth : w + ((ell K r s j : Nat) : Int) ≤ rho)
    (hfit : 2 * (K : Int) + (R : Int) ≤ rho + 1)
    (hvlong : |Stopped.lam c i sigma v - ((axial r s j : Nat) : Int)| ≤ (R : Int))
    (hvtrans : ∀ k, k ≠ i → |v k - c k| ≤ w) :
    CorrMove.longFace v ((ell K r s j : Nat) : Int) i sigma (2 * (K : Int)) ⊆
      CorrMove.cube (c + Pi.single i (sigma * (20 * (r : Int)))) rho := by
  have hKZ : (1 : Int) ≤ 2 * (K : Int) := by
    have hKz : (20 : Int) ≤ (K : Int) := by exact_mod_cast hK
    linarith
  have hKz : (20 : Int) ≤ (K : Int) := by exact_mod_cast hK
  have hellZ : (0 : Int) ≤ ((ell K r s j : Nat) : Int) := by positivity
  have hRz : (0 : Int) ≤ (R : Int) := by positivity
  have hsigma2 : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
  have hgapax : ((gap r s j : Nat) : Int) + ((axial r s j : Nat) : Int) = 20 * (r : Int) := by
    exact_mod_cast gap_add_axial (K := K) hr hj
  have hmul : 2 * (K : Int) * ((ell K r s j : Nat) : Int) ≤ ((gap r s j : Nat) : Int) := by
    exact_mod_cast ell_le_gap (K := K) (r := r) (s := s) (j := j) (show 0 < K by omega)
  have hmul2 : ((gap r s j : Nat) : Int)
      < 2 * (K : Int) * ((ell K r s j : Nat) : Int) + 2 * (K : Int) := by
    exact_mod_cast gap_lt_ell (K := K) (r := r) (s := s) (j := j) (show 0 < K by omega)
  intro x hx
  rw [CorrMove.mem_longFace hsigma hellZ hKZ] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [abs_le] at hvlong
  have hsplit : Stopped.lam c i sigma x
      = sigma * (x i - v i) + Stopped.lam c i sigma v := by
    simp only [Stopped.lam]
    ring
  rw [h1] at hsplit
  rw [CorrMove.mem_cube]
  intro k
  by_cases hki : k = i
  · subst hki
    simp only [Pi.add_apply, Pi.single_eq_same]
    have hdiff : x k - (c k + sigma * (20 * (r : Int)))
        = sigma * (Stopped.lam c k sigma x - 20 * (r : Int)) := by
      simp only [Stopped.lam]
      have hxc : sigma * (sigma * (x k - c k)) = x k - c k := by
        calc sigma * (sigma * (x k - c k)) = (sigma * sigma) * (x k - c k) := by ring
          _ = x k - c k := by rw [hsigma2]; ring
      linear_combination -hxc
    rw [hdiff, CorrMove.abs_signed hsigma, abs_le]
    constructor <;> linarith [hvlong.1, hvlong.2]
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hki, add_zero]
    have hb := h2 k hki
    have hc := hvtrans k hki
    rw [abs_le] at hb hc ⊢
    constructor <;> linarith [hb.1, hb.2, hc.1, hc.2]

/-- **(G2), packaged.**  Any face `Bset` sitting at signed axial coordinate `a_j` with transverse
half-width `w0` is an aspect-`2K` long source for the cube of radius `ρ` about `c + 20 r σ e_i`,
inside `D_j`, at extraction radius `R`. -/
theorem longTargetAspect_of_face {c : Site d} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1)
    {K r s j R : Nat} {w0 rho : Int} (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hj : j < K)
    (hR : 2 * R ≤ s)
    (hD : w0 + (R : Int) + ((ell K r s j : Nat) : Int) ≤ 5 * (r : Int))
    (hT : w0 + (R : Int) + ((ell K r s j : Nat) : Int) ≤ rho)
    (hfit : 2 * (K : Int) + (R : Int) ≤ rho + 1)
    {Bset : Finset (Site d)}
    (hBlong : ∀ b ∈ Bset, Stopped.lam c i sigma b = ((axial r s j : Nat) : Int))
    (hBtrans : ∀ b ∈ Bset, ∀ k, k ≠ i → |b k - c k| ≤ w0) :
    LongTargetAspect (2 * (K : Int)) (R : Int) i sigma (Dbox c i sigma r s j) Bset
      (CorrMove.cube (c + Pi.single i (sigma * (20 * (r : Int)))) rho) := by
  intro v hv
  obtain ⟨b, hb, hvb⟩ := hv
  have hvlong : |Stopped.lam c i sigma v - ((axial r s j : Nat) : Int)| ≤ (R : Int) := by
    have hsub : Stopped.lam c i sigma v - ((axial r s j : Nat) : Int)
        = sigma * (v i - b i) := by
      rw [← hBlong b hb]
      simp only [Stopped.lam]
      ring
    rw [hsub, CorrMove.abs_signed hsigma]
    exact hvb i
  have hvtrans : ∀ k, k ≠ i → |v k - c k| ≤ w0 + (R : Int) := by
    intro k hk
    have h1 := hBtrans b hb k hk
    have h2 := hvb k
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨((ell K r s j : Nat) : Int), ?_, ?_, ?_⟩
  · exact_mod_cast radius_le_ell (K := K) (r := r) (s := s) (j := j) hK hr hj hR
  · exact longBox_subset_Dbox hsigma hK hs hr hj hR (by linarith) hvlong hvtrans
  · exact longFace_subset_cube hsigma hK hr hj (by linarith) hfit hvlong hvtrans

end LongMove

/-! ## §4.  The literal v15 instance at the corrected stub face -/

section Instance

variable {d : Nat} [NeZero d]

omit [NeZero d] in
/-- The v15 face `F^{j+1}_{z,y}` sits at signed axial coordinate `a_j`. -/
theorem stubFace_lam {c : Site d} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {r t s j : Nat} :
    ∀ b ∈ Stopped.stubFace c i sigma r t (10 * s * (j + 1)),
      Stopped.lam c i sigma b = ((axial r s j : Nat) : Int) := by
  intro b hb
  rw [Stopped.mem_stubFace hsigma] at hb
  exact hb.1

omit [NeZero d] in
/-- Its transverse half-width is exactly `2 r`: the corrected isotropic stub. -/
theorem stubFace_trans {c : Site d} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {r t a : Nat} :
    ∀ b ∈ Stopped.stubFace c i sigma r t a,
      ∀ k, k ≠ i → |b k - c k| ≤ ((2 * r : Nat) : Int) := by
  intro b hb
  rw [Stopped.mem_stubFace hsigma] at hb
  exact hb.2

/-- **(G2) at the corrected stub face, sharp radius.**  From the `2r`-wide face `F^{j+1}` the
aspect-`2K` long move lands in the isotropic cube of radius `2 r + ℓ_j + R` about `c_y`.  This is
sharp: the far face has transverse half-width exactly `ℓ_j` about a point that may sit `2 r + R`
off axis. -/
theorem sharp_face_radius {r t s j K R : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hj : j < K)
    (hR : 2 * R ≤ s)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    LongTargetAspect (2 * (K : Int)) (R : Int) i sigma
      (Dbox (MacroExp.ctr d r z) i sigma r s j)
      (Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)))
      (CorrMove.cube (MacroExp.ctr d r y)
        (2 * (r : Int) + ((ell K r s j : Nat) : Int) + (R : Int))) := by
  have hsum : ((ell K r s j : Nat) : Int) + (R : Int) ≤ 8 * (s : Int) := by
    exact_mod_cast ell_add_le (K := K) hK hr hj hR
  have hsr : 8 * (s : Int) ≤ (r : Int) := by exact_mod_cast eight_s_le_r (K := K) hK hr
  have hfitNat : 2 * K + R ≤ 2 * r + 1 := two_K_add_le (K := K) hK hs hr hR
  have hfit : 2 * (K : Int) + (R : Int) ≤ 2 * (r : Int) + 1 := by exact_mod_cast hfitNat
  have hellZ : (0 : Int) ≤ ((ell K r s j : Nat) : Int) := by positivity
  have hRz : (0 : Int) ≤ (R : Int) := by positivity
  rw [CorrMove.ctr_add_dir r hemb]
  refine longTargetAspect_of_face (w0 := ((2 * r : Nat) : Int)) hsigma hK hs hr hj hR
    ?_ ?_ ?_ (stubFace_lam hsigma) (stubFace_trans hsigma)
  · push_cast
    linarith
  · push_cast
    linarith
  · linarith

/-- **(G2) exactly as stated in v15: `T_j = M_y`.**  The far face of the aspect-`2K` long move
lands in the target box `M_y`, of planar half-width `3 r`, because `2 r + ℓ_j + R ≤ 2 r + 8 s`
and `8 s ≤ r`. -/
theorem longTargetAspect_stubFace_M {r t s j K R : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hj : j < K)
    (hR : 2 * R ≤ s) (ht : 5 * r ≤ t)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    LongTargetAspect (2 * (K : Int)) (R : Int) i sigma
      (Dbox (MacroExp.ctr d r z) i sigma r s j)
      (Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)))
      (MacroExp.M d r t y) := by
  have hsum : ((ell K r s j : Nat) : Int) + (R : Int) ≤ 8 * (s : Int) := by
    exact_mod_cast ell_add_le (K := K) hK hr hj hR
  have hsr : 8 * (s : Int) ≤ (r : Int) := by exact_mod_cast eight_s_le_r (K := K) hK hr
  have htz : 5 * (r : Int) ≤ (t : Int) := by exact_mod_cast ht
  have hrz : (0 : Int) ≤ (r : Int) := by positivity
  refine (sharp_face_radius hsigma hK hs hr hj hR hemb).mono_target ?_
  have hcube : CorrMove.cube (MacroExp.ctr d r y)
      (2 * (r : Int) + ((ell K r s j : Nat) : Int) + (R : Int)) ⊆
      CorrMove.cube (MacroExp.ctr d r y) ((3 * r : Nat) : Int) := by
    apply CorrMove.ibox_mono
    intro k
    push_cast
    linarith
  refine hcube.trans (CorrMove.cube_subset_M ?_ ?_ y)
  · push_cast
    linarith
  · push_cast
    linarith

/-- **(G2) with `T_j = CoreRes.target r y`.**  The far face of the aspect-`2K` stopped long move
lands in the radius-`3r` isotropic core that the exact interpreter stores as its recursive
reservation target.  Transversally `2 r + ℓ_j + R ≤ 2 r + 8 s ≤ 3 r`, and axially the floor
identity keeps the face within `2 K + R - 1 ≤ 2 r` of `c_y`.

This is the sharp statement: `sharp_face_radius` shows the reachable isotropic radius is exactly
`2 r + ℓ_j + R`, which by `ell_pos` is strictly larger than `2 r`.  A radius-`2r` recursive core
would therefore *not* be reachable from the full `2r`-wide face `F^{j+1}` by the long move
alone. -/
theorem longTargetAspect_stubFace_core {r t s j K R : Nat} {z y : Site 2} {i : Fin d}
    {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hj : j < K)
    (hR : 2 * R ≤ s)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    LongTargetAspect (2 * (K : Int)) (R : Int) i sigma
      (Dbox (MacroExp.ctr d r z) i sigma r s j)
      (Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)))
      (CoreRes.target (d := d) r y) := by
  have hsum : ((ell K r s j : Nat) : Int) + (R : Int) ≤ 8 * (s : Int) := by
    exact_mod_cast ell_add_le (K := K) hK hr hj hR
  have hsr : 8 * (s : Int) ≤ (r : Int) := by exact_mod_cast eight_s_le_r (K := K) hK hr
  have hfitNat : 2 * K + R ≤ 2 * r + 1 := two_K_add_le (K := K) hK hs hr hR
  have hfit : 2 * (K : Int) + (R : Int) ≤ 2 * (r : Int) + 1 := by exact_mod_cast hfitNat
  have hrz : (0 : Int) ≤ (r : Int) := by positivity
  have hgoal : CoreRes.target (d := d) r y
      = CorrMove.cube (MacroExp.ctr d r z + Pi.single i (sigma * (20 * (r : Int))))
        (3 * (r : Int)) := by
    rw [CoreRes.target, CorrMove.ctr_add_dir r hemb]
  rw [hgoal]
  refine longTargetAspect_of_face (w0 := ((2 * r : Nat) : Int)) hsigma hK hs hr hj hR
    ?_ ?_ ?_ (stubFace_lam hsigma) (stubFace_trans hsigma)
  · push_cast
    linarith
  · push_cast
    linarith
  · linarith

end Instance

/-! ## §5.  The exact integer boxes -/

section IntBoxes

variable {d : Nat}

/-- `D_j` as an exact-plan integer box. -/
def DIntBox (c : Site d) (i : Fin d) (sigma : Int) (r s j : Nat) :
    ExactTargetPlan.IntBox d where
  lower k :=
    if k = i then
      (if sigma = 1 then c k + (((5 * r + 10 * s * j : Nat) : Int) + 1)
        else c k - ((25 * r : Nat) : Int))
    else c k - ((5 * r : Nat) : Int)
  upper k :=
    if k = i then
      (if sigma = 1 then c k + ((25 * r : Nat) : Int)
        else c k - (((5 * r + 10 * s * j : Nat) : Int) + 1))
    else c k + ((5 * r : Nat) : Int)

/-- `B_j = F^{j+1}_{z,y}` as an exact-plan integer box: a degenerate slab in the direction `i`. -/
def faceIntBox (c : Site d) (i : Fin d) (sigma : Int) (r a : Nat) :
    ExactTargetPlan.IntBox d where
  lower k :=
    if k = i then c k + sigma * ((5 * r + a : Nat) : Int) else c k - ((2 * r : Nat) : Int)
  upper k :=
    if k = i then c k + sigma * ((5 * r + a : Nat) : Int) else c k + ((2 * r : Nat) : Int)

/-! ### Coordinate values of the two boxes -/

theorem faceIntBox_lower_self (c : Site d) (i : Fin d) (sigma : Int) (r a : Nat) :
    (faceIntBox c i sigma r a).lower i = c i + sigma * ((5 * r + a : Nat) : Int) := by
  simp [faceIntBox]

theorem faceIntBox_upper_self (c : Site d) (i : Fin d) (sigma : Int) (r a : Nat) :
    (faceIntBox c i sigma r a).upper i = c i + sigma * ((5 * r + a : Nat) : Int) := by
  simp [faceIntBox]

theorem faceIntBox_lower_of_ne (c : Site d) (i : Fin d) (sigma : Int) (r a : Nat)
    {k : Fin d} (hk : k ≠ i) :
    (faceIntBox c i sigma r a).lower k = c k - ((2 * r : Nat) : Int) := by
  simp [faceIntBox, hk]

theorem faceIntBox_upper_of_ne (c : Site d) (i : Fin d) (sigma : Int) (r a : Nat)
    {k : Fin d} (hk : k ≠ i) :
    (faceIntBox c i sigma r a).upper k = c k + ((2 * r : Nat) : Int) := by
  simp [faceIntBox, hk]

theorem DIntBox_lower_self_pos (c : Site d) (i : Fin d) (r s j : Nat) :
    (DIntBox c i 1 r s j).lower i = c i + (((5 * r + 10 * s * j : Nat) : Int) + 1) := by
  simp [DIntBox]

theorem DIntBox_upper_self_pos (c : Site d) (i : Fin d) (r s j : Nat) :
    (DIntBox c i 1 r s j).upper i = c i + ((25 * r : Nat) : Int) := by
  simp [DIntBox]

theorem DIntBox_lower_self_neg (c : Site d) (i : Fin d) (r s j : Nat) :
    (DIntBox c i (-1) r s j).lower i = c i - ((25 * r : Nat) : Int) := by
  simp [DIntBox]

theorem DIntBox_upper_self_neg (c : Site d) (i : Fin d) (r s j : Nat) :
    (DIntBox c i (-1) r s j).upper i = c i - (((5 * r + 10 * s * j : Nat) : Int) + 1) := by
  simp [DIntBox]

theorem DIntBox_lower_of_ne (c : Site d) (i : Fin d) (sigma : Int) (r s j : Nat)
    {k : Fin d} (hk : k ≠ i) :
    (DIntBox c i sigma r s j).lower k = c k - ((5 * r : Nat) : Int) := by
  simp [DIntBox, hk]

theorem DIntBox_upper_of_ne (c : Site d) (i : Fin d) (sigma : Int) (r s j : Nat)
    {k : Fin d} (hk : k ≠ i) :
    (DIntBox c i sigma r s j).upper k = c k + ((5 * r : Nat) : Int) := by
  simp [DIntBox, hk]

/-! ### Orderedness and the exact `Finset` identities -/

theorem faceIntBox_ordered (c : Site d) (i : Fin d) (sigma : Int) (r a : Nat) :
    (faceIntBox c i sigma r a).Ordered := by
  intro k
  by_cases hki : k = i
  · subst hki
    rw [faceIntBox_lower_self, faceIntBox_upper_self]
  · rw [faceIntBox_lower_of_ne _ _ _ _ _ hki, faceIntBox_upper_of_ne _ _ _ _ _ hki]
    have h2 : (0 : Int) ≤ ((2 * r : Nat) : Int) := by positivity
    omega

theorem DIntBox_ordered (c : Site d) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {K r s j : Nat}
    (hK : 20 ≤ K) (hs : 0 < s) (hr : r = K * s) (hj : j < K) :
    (DIntBox c i sigma r s j).Ordered := by
  have hboundZ : ((5 * r + 10 * s * j : Nat) : Int) + 1 ≤ ((25 * r : Nat) : Int) := by
    exact_mod_cast Dbox_ordered_nat hK hs hr hj
  intro k
  by_cases hki : k = i
  · subst hki
    rcases hsigma with rfl | rfl
    · rw [DIntBox_lower_self_pos, DIntBox_upper_self_pos]
      omega
    · rw [DIntBox_lower_self_neg, DIntBox_upper_self_neg]
      omega
  · rw [DIntBox_lower_of_ne _ _ _ _ _ _ hki, DIntBox_upper_of_ne _ _ _ _ _ _ hki]
    have h5 : (0 : Int) ≤ ((5 * r : Nat) : Int) := by positivity
    omega

/-- **`B_j` as an integer box.**  Its site set is literally the corrected isotropic stub face. -/
theorem faceIntBox_sites_eq (c : Site d) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (r t a : Nat) :
    (faceIntBox c i sigma r a).sites = Stopped.stubFace c i sigma r t a := by
  have hsigma2 : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> ring
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, Stopped.mem_stubFace hsigma]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have hi := hx i
      rw [faceIntBox_lower_self, faceIntBox_upper_self] at hi
      have hxi : x i - c i = sigma * ((5 * r + a : Nat) : Int) := by omega
      show sigma * (x i - c i) = ((5 * r + a : Nat) : Int)
      rw [hxi]
      calc sigma * (sigma * ((5 * r + a : Nat) : Int))
          = (sigma * sigma) * ((5 * r + a : Nat) : Int) := by ring
        _ = ((5 * r + a : Nat) : Int) := by rw [hsigma2]; ring
    · intro k hk
      have hb := hx k
      rw [faceIntBox_lower_of_ne _ _ _ _ _ hk, faceIntBox_upper_of_ne _ _ _ _ _ hk] at hb
      exact abs_le.2 ⟨by omega, by omega⟩
  · rintro ⟨hi, hoff⟩ k
    by_cases hki : k = i
    · subst hki
      rw [faceIntBox_lower_self, faceIntBox_upper_self]
      have hlam : sigma * (x k - c k) = ((5 * r + a : Nat) : Int) := hi
      have hxc : x k - c k = sigma * ((5 * r + a : Nat) : Int) := by
        calc x k - c k = (sigma * sigma) * (x k - c k) := by rw [hsigma2]; ring
          _ = sigma * (sigma * (x k - c k)) := by ring
          _ = sigma * ((5 * r + a : Nat) : Int) := by rw [hlam]
      omega
    · rw [faceIntBox_lower_of_ne _ _ _ _ _ hki, faceIntBox_upper_of_ne _ _ _ _ _ hki]
      have hb := abs_le.1 (hoff k hki)
      omega

/-- **`D_j` as an integer box.**  Its site set is literally `Dbox`. -/
theorem DIntBox_sites_eq (c : Site d) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (r s j : Nat) :
    (DIntBox c i sigma r s j).sites = Dbox c i sigma r s j := by
  ext x
  rw [ExactTargetPlan.IntBox.mem_sites, mem_Dbox hsigma]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have hi := hx i
      simp only [Stopped.lam]
      rcases hsigma with rfl | rfl
      · rw [DIntBox_lower_self_pos, DIntBox_upper_self_pos] at hi
        omega
      · rw [DIntBox_lower_self_neg, DIntBox_upper_self_neg] at hi
        omega
    · intro k hk
      have hb := hx k
      rw [DIntBox_lower_of_ne _ _ _ _ _ _ hk, DIntBox_upper_of_ne _ _ _ _ _ _ hk] at hb
      exact abs_le.2 ⟨by omega, by omega⟩
  · rintro ⟨hi, hoff⟩ k
    simp only [Stopped.lam] at hi
    by_cases hki : k = i
    · subst hki
      rcases hsigma with rfl | rfl
      · rw [DIntBox_lower_self_pos, DIntBox_upper_self_pos]
        omega
      · rw [DIntBox_lower_self_neg, DIntBox_upper_self_neg]
        omega
    · rw [DIntBox_lower_of_ne _ _ _ _ _ _ hki, DIntBox_upper_of_ne _ _ _ _ _ _ hki]
      have hb := abs_le.1 (hoff k hki)
      omega

end IntBoxes

/-! ## §6.  Instantiating `ExactMacroGeometry.StoppedChildren` -/

section Children

variable {d : Nat} [NeZero d]

/-- **The finite stopped-child constructor.**  Supplied `K` exact target plans whose active box is
literally `D_j` and whose source is literally the corrected stub face `F^{j+1}`, the two geometric
fields of `ExactMacroGeometry.StoppedChildren` are the theorems of §2.  No probability hypothesis
occurs: `htarget`, `hdelta` and `heps` are the plans' own recorded data. -/
def stoppedChildren {r t s K : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    {deltaC delta2 : Real}
    (hsigma : sigma = 1 ∨ sigma = -1) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (plan : Fin K → ExactTargetPlan.Plan d)
    (hwf : ∀ a, (plan a).WellFormed)
    (hactive : ∀ a, (plan a).active = Dbox (MacroExp.ctr d r z) i sigma r s a.val)
    (hsource : ∀ a, (plan a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)))
    (htarget : ∀ a, (plan a).target ⊆ CoreRes.target (d := d) r y)
    (hdelta : ∀ a, delta2 ≤ (plan a).delta)
    (heps : ∀ a, (plan a).epsilon ≤ deltaC) :
    ExactMacroGeometry.StoppedChildren (d := d) r t s K z y i sigma deltaC delta2 where
  plan := plan
  wellFormed := hwf
  active_subset_outgoing := fun a => by
    rw [hactive a]
    exact Dbox_subset_E hr ht hsigma hemb
  prefix_disjoint_active := fun a => by
    rw [hactive a]
    exact stub_disjoint_Dbox hsigma r t s a.val
  source_eq := hsource
  target_subset := htarget
  input_tolerance := hdelta
  output_error := heps

omit [NeZero d] in
@[simp] theorem stoppedChildren_plan {r t s K : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    {deltaC delta2 : Real}
    (hsigma : sigma = 1 ∨ sigma = -1) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (plan : Fin K → ExactTargetPlan.Plan d)
    (hwf : ∀ a, (plan a).WellFormed)
    (hactive : ∀ a, (plan a).active = Dbox (MacroExp.ctr d r z) i sigma r s a.val)
    (hsource : ∀ a, (plan a).source =
      Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (a.val + 1)))
    (htarget : ∀ a, (plan a).target ⊆ CoreRes.target (d := d) r y)
    (hdelta : ∀ a, delta2 ≤ (plan a).delta)
    (heps : ∀ a, (plan a).epsilon ≤ deltaC) (a : Fin K) :
    (stoppedChildren hsigma hr ht hemb plan hwf hactive hsource htarget hdelta heps).plan a
      = plan a := rfl

omit [NeZero d] in
/-- The two `StoppedChildren` shape fields are exactly the geometry of §2, restated in the form a
plan constructor consumes: the active `IntBox` is `DIntBox` and the source `IntBox` is
`faceIntBox`. -/
theorem stoppedChildren_boxes {r t s j : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    (DIntBox (MacroExp.ctr d r z) i sigma r s j).sites ⊆ MacroExp.E d r t z y ∧
      Disjoint (Stopped.stub (MacroExp.ctr d r z) i sigma r t (10 * s * j))
        (DIntBox (MacroExp.ctr d r z) i sigma r s j).sites ∧
      (faceIntBox (MacroExp.ctr d r z) i sigma r (10 * s * (j + 1))).sites =
        Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1)) := by
  refine ⟨?_, ?_, faceIntBox_sites_eq _ i hsigma r t _⟩
  · rw [DIntBox_sites_eq _ i hsigma]
    exact Dbox_subset_E hr ht hsigma hemb
  · rw [DIntBox_sites_eq _ i hsigma]
    exact stub_disjoint_Dbox hsigma r t s j

end Children

/-! ## §7.  Instantiating `ExactLongBoxVariablePlan` at the stopped scale -/

section VariablePlan

variable {d : Nat}

/-- The tile scale of the aspect-`2K` chain filling the stopped long box: `ℓ_j = 8 s' + rem`. -/
def longMacroScale (K r s j : Nat) : Nat := ell K r s j / 8

/-- The tile remainder of the stopped long box. -/
def longRem (K r s j : Nat) : Nat := ell K r s j % 8

theorem longRem_le (K r s j : Nat) : longRem K r s j ≤ 7 := by
  unfold longRem
  omega

theorem longScale_eq (K r s j : Nat) :
    LongBoxVariable.longScale (longMacroScale K r s j) (longRem K r s j) = ell K r s j := by
  unfold LongBoxVariable.longScale longMacroScale longRem
  omega

theorem one_le_aspect {K : Nat} (hK : 20 ≤ K) : 1 ≤ aspect K := by
  unfold aspect
  omega

theorem stepCount_aspect (K : Nat) : LongBoxVariable.stepCount (aspect K) = 16 * K - 4 := by
  unfold aspect LongBoxVariable.stepCount
  omega

/-- The deterministic tile budget of `ExactLongBoxVariablePlan.SchemeFamily.planAt` at aspect
`2 K` and radius `R`, discharged from a single explicit inequality on the level spacing `s`. -/
theorem scale_budget {K r s j R : Nat} (hK : 20 ≤ K) (hr : r = K * s) (hj : j < K)
    (hbudget : 48 * K + 48 * K * R + 64 ≤ 2 * s) :
    3 * aspect K + 3 * aspect K * R + 8 ≤ longMacroScale K r s j := by
  have hell := two_s_le_ell (K := K) hK hr hj
  have hlink : 48 * K * R = 8 * (6 * K * R) := by ring
  have hlink2 : 3 * aspect K * R = 6 * K * R := by unfold aspect; ring
  have hlink3 : 3 * aspect K = 6 * K := by unfold aspect; ring
  have hdiv : 6 * K + 6 * K * R + 8 ≤ ell K r s j / 8 := by
    rw [Nat.le_div_iff_mul_le (show 0 < 8 by omega)]
    omega
  unfold longMacroScale
  omega

/-- The finite region of the aspect-`2K` chain at tile scale `ℓ_j` sits inside the aspect-`2K`
long box of scale `ℓ_j` based at the origin.  Translating this region to a source-plus point `v`
and combining with `longBox_subset_Dbox` is what places the chain inside `D_j`. -/
theorem allowedRegion_subset_longBox_ell {K r s j R : Nat} (hK : 20 ≤ K) (hr : r = K * s)
    (hj : j < K) (i : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (hbudget : 48 * K + 48 * K * R + 64 ≤ 2 * s) :
    LongBoxVariable.allowedRegion (aspect K) i sigma (longMacroScale K r s j)
        (longRem K r s j) R ⊆
      CorrMove.longBox 0 ((ell K r s j : Nat) : Int) i sigma ((aspect K : Nat) : Int) := by
  have hbase : 3 * aspect K + 8 + 3 * aspect K * R ≤ longMacroScale K r s j := by
    have h := scale_budget (K := K) (r := r) (s := s) (j := j) (R := R) hK hr hj hbudget
    omega
  have h := LongBoxVariable.allowedRegion_subset_longBox (K := aspect K) i hsigma
    (one_le_aspect hK) (longRem_le K r s j) hbase
  rw [longScale_eq] at h
  exact h

end VariablePlan

#print axioms KNAll.Site.ExactStoppedG2.radius_le_ell
#print axioms KNAll.Site.ExactStoppedG2.longBox_subset_Dbox
#print axioms KNAll.Site.ExactStoppedG2.longFace_subset_cube
#print axioms KNAll.Site.ExactStoppedG2.longTargetAspect_stubFace_M
#print axioms KNAll.Site.ExactStoppedG2.longTargetAspect_stubFace_core
#print axioms KNAll.Site.ExactStoppedG2.Dbox_subset_E
#print axioms KNAll.Site.ExactStoppedG2.stub_disjoint_Dbox
#print axioms KNAll.Site.ExactStoppedG2.DIntBox_sites_eq
#print axioms KNAll.Site.ExactStoppedG2.faceIntBox_sites_eq
#print axioms KNAll.Site.ExactStoppedG2.stoppedChildren
#print axioms KNAll.Site.ExactStoppedG2.scale_budget

end KNAll.Site.ExactStoppedG2

end
