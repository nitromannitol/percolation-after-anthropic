import Hypergraph.CorridorMove

/-!
# The numerical spine of the 700-step aspect-88 construction

The aspect-88 input is obtained from `8 * 88 - 4 = 700` target-extension steps.  This module
isolates the exact backwards tolerance cascade and the integer inequalities for the 700 tiles.
It deliberately does not assert the missing finite-window estimates: those remain explicit inputs
to the eventual geometric/probabilistic induction.
-/

noncomputable section

namespace KNAll.Site.LongBox700

set_option maxRecDepth 4096

open KNAll.Site
open Percolation.Literature.LatticeModels

def aspect : Nat := 88

def stepCount : Nat := 8 * aspect - 4

theorem stepCount_eq : stepCount = 700 := by decide

/-- `b_t` from (6.2), written with the existing corridor cascade. -/
def tol (chi : Real) (t : Nat) : Real := CorrMove.casc chi (stepCount - t)

/-- The common component tolerance `xi = b_0^2 / 4`. -/
def componentTol (chi : Real) : Real := (tol chi 0) ^ 2 / 4

@[simp] theorem tol_zero (chi : Real) : tol chi 0 = CorrMove.casc chi 700 := by
  rw [tol, stepCount_eq, Nat.sub_zero]

@[simp] theorem tol_final (chi : Real) : tol chi stepCount = chi := by
  simp [tol]

theorem tol_rec (chi : Real) {t : Nat} (ht : t < stepCount) :
    tol chi t = CorrMove.f (tol chi (t + 1)) := by
  exact CorrMove.casc_rec chi stepCount ht

theorem tol_closed_form (chi : Real) {t : Nat} (ht : t ≤ stepCount) :
    tol chi t = chi ^ (2 ^ (stepCount - t)) / 96 ^ (2 ^ (stepCount - t) - 1) := by
  exact CorrMove.casc_closed_form chi (stepCount - t)

/-- Increasing the cascade depth can only decrease the tolerance while the starting tolerance is
in `(0,1]`. -/
theorem casc_succ_le {a : Real} (ha0 : 0 < a) (ha1 : a ≤ 1) (n : Nat) :
    CorrMove.casc a (n + 1) ≤ CorrMove.casc a n := by
  rw [CorrMove.casc_succ, CorrMove.f]
  have hp := CorrMove.casc_pos ha0 n
  have h1 := CorrMove.casc_le_one ha0 ha1 n
  nlinarith [sq_nonneg (CorrMove.casc a n)]

theorem casc_antitone {a : Real} (ha0 : 0 < a) (ha1 : a ≤ 1)
    {m n : Nat} (hmn : m ≤ n) : CorrMove.casc a n ≤ CorrMove.casc a m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simp
  | succ k ih =>
      exact (casc_succ_le ha0 ha1 (m + k)).trans (by simpa [Nat.add_assoc] using ih)

theorem tol_pos {chi : Real} (hchi : 0 < chi) (t : Nat) : 0 < tol chi t :=
  CorrMove.casc_pos hchi _

theorem tol_le_one {chi : Real} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1) (t : Nat) :
    tol chi t ≤ 1 := CorrMove.casc_le_one hchi0 hchi1 _

/-- Earlier inputs are no larger than later outputs. -/
theorem tol_mono {chi : Real} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1)
    {u v : Nat} (huv : u ≤ v) (hv : v ≤ stepCount) : tol chi u ≤ tol chi v := by
  apply casc_antitone hchi0 hchi1
  omega

theorem componentTol_pos {chi : Real} (hchi : 0 < chi) : 0 < componentTol chi := by
  unfold componentTol
  positivity [tol_pos hchi 0]

/-- The common component tolerance is strictly below the first input tolerance. -/
theorem componentTol_lt_tol_zero {chi : Real} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1) :
    componentTol chi < tol chi 0 := by
  have hb0 := tol_pos hchi0 0
  have hb1 := tol_le_one hchi0 hchi1 0
  unfold componentTol
  nlinarith [sq_nonneg (tol chi 0)]

/-- Equation (6.5): three component losses fit strictly inside the local window budget at every
one of the 700 steps. -/
theorem three_componentTol_lt {chi : Real} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1)
    {t : Nat} (ht : t < stepCount) :
    3 * componentTol chi < 3 * (tol chi t) ^ 2 := by
  have hmono : tol chi 0 ≤ tol chi t :=
    tol_mono hchi0 hchi1 (Nat.zero_le t) ht.le
  have hb0 := tol_pos hchi0 0
  have hbt := tol_pos hchi0 t
  unfold componentTol
  nlinarith [sq_nonneg (tol chi 0), sq_nonneg (tol chi t)]

/-- The 700-fold error induction, separated from its geometric step. -/
theorem cascade
    {chi : Real} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1) {P : Nat → Real}
    (hsrc : 1 - tol chi 0 < P 0)
    (hstep : ∀ t, t < stepCount →
      1 - tol chi (t + 1) / 8 < P t → 1 - tol chi (t + 1) < P (t + 1)) :
    1 - chi < P stepCount := by
  have hb : ∀ t, t ≤ stepCount → 0 ≤ tol chi t ∧ tol chi t ≤ 1 := by
    intro t ht
    exact ⟨(tol_pos hchi0 t).le, tol_le_one hchi0 hchi1 t⟩
  have hrec : ∀ t, t < stepCount → tol chi t = CorrMove.f (tol chi (t + 1)) :=
    fun t ht => tol_rec chi ht
  have h := CorrMove.cascade_of_step (J := stepCount) (a := tol chi) (P := P)
    hb hrec hsrc hstep
  simpa using h

/-! ## Integer arithmetic for the 700 tiles -/

def longScale (s q : Nat) : Nat := 8 * s + q

def L0 (s q : Nat) : Nat := 4 * s + aspect * q

def L (s q t : Nat) : Nat := L0 s q + t * s

def width (s q R t : Nat) : Nat := L0 s q + t * R

theorem L_final (s q : Nat) : L s q stepCount = aspect * longScale s q := by
  simp [L, L0, longScale, aspect, stepCount]
  omega

/-- The scale hypothesis (6.7), slightly weakened to exactly the two terms used by the displayed
containment arithmetic.  The manuscript's `3K₀ + 3K₀R_* + k + n₁ + 8` implies it. -/
theorem tile_budget {s q R : Nat} (hq : q ≤ 7)
    (hs : 272 + 264 * R ≤ s) :
    width s q R stepCount + s + 2 * R ≤ longScale s q := by
  simp only [width, L0, longScale, aspect, stepCount]
  omega

theorem width_final_le {s q R : Nat} (hq : q ≤ 7)
    (hs : 272 + 264 * R ≤ s) : width s q R stepCount ≤ longScale s q := by
  have h := tile_budget hq hs
  omega

theorem L0_le_longScale {s q R : Nat} (hq : q ≤ 7)
    (hs : 272 + 264 * R ≤ s) : L0 s q ≤ longScale s q := by
  have h := tile_budget hq hs
  simp only [width, stepCount] at h
  omega

/-- The initial tile starts beyond the wired source scale. -/
theorem source_before_L0 {s q k n1 R : Nat}
    (hs : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    k < L0 s q - 2 * s := by
  simp only [aspect, L0] at hs ⊢
  omega

theorem initial_radius_le_L0 {s q n1 R k : Nat}
    (hs : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    n1 ≤ L0 s q := by
  simp only [aspect, L0] at hs ⊢
  omega

/-! ## The actual tile faces -/

/-- The hyperplane patch `B_t` from (6.8). -/
def Bset {d : Nat} (i : Fin d) (sigma : Int) (s q R t : Nat) : Finset (Site d) :=
  CorrMove.dbox 0 i sigma (L s q t : Int) (L s q t : Int) (width s q R t : Int)

/-- The rectangular site subbox `D_t` from (6.8). -/
def Dset {d : Nat} (i : Fin d) (sigma : Int) (s q R t : Nat) : Finset (Site d) :=
  CorrMove.dbox 0 i sigma ((L s q t : Int) - 2 * (s : Int))
    ((L s q t : Int) + (s : Int)) (longScale s q : Int)

theorem mem_Bset {d : Nat} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R t : Nat} {x : Site d} :
    x ∈ Bset i sigma s q R t ↔
      sigma * x i = (L s q t : Int) ∧
        ∀ j, j ≠ i → |x j| ≤ (width s q R t : Int) := by
  rw [Bset, CorrMove.mem_dbox hsigma]
  simp only [Pi.zero_apply, sub_zero, le_antisymm_iff]
  tauto

theorem mem_Dset {d : Nat} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R t : Nat} {x : Site d} :
    x ∈ Dset i sigma s q R t ↔
      ((L s q t : Int) - 2 * (s : Int) ≤ sigma * x i ∧
        sigma * x i ≤ (L s q t : Int) + (s : Int)) ∧
        ∀ j, j ≠ i → |x j| ≤ (longScale s q : Int) := by
  rw [Dset, CorrMove.mem_dbox hsigma]
  simp only [Pi.zero_apply, sub_zero]

/-- Every intermediate face is genuinely nonempty.  This rules out a vacuous use of
`faceTarget_tile` caused by an empty source patch. -/
theorem Bset_nonempty {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s q R t : Nat) :
    (Bset i sigma s q R t).Nonempty := by
  classical
  let x : Site d := fun j => if j = i then sigma * (L s q t : Int) else 0
  refine ⟨x, (mem_Bset hsigma).2 ?_⟩
  have hsigmaSq : sigma * sigma = 1 := by
    rcases hsigma with rfl | rfl <;> norm_num
  constructor
  · dsimp [x]
    rw [if_pos rfl]
    calc
      sigma * (sigma * (L s q t : Int)) = (sigma * sigma) * (L s q t : Int) := by ring
      _ = (L s q t : Int) := by rw [hsigmaSq, one_mul]
  · intro j hji
    simp [x, hji]

/-- The first face is a patch of the boundary of the initial cube `Lambda_(L_0)`. -/
theorem Bset_zero_subset_initialCube {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s q R : Nat) :
    Bset i sigma s q R 0 ⊆ CorrMove.cube 0 (L0 s q : Int) := by
  intro x hx
  rw [mem_Bset hsigma] at hx
  simp only [L, Nat.zero_mul, Nat.add_zero] at hx
  rw [CorrMove.mem_cube]
  simp only [Pi.zero_apply, sub_zero]
  intro j
  by_cases hji : j = i
  · subst j
    calc
      |x i| = |sigma * x i| := (CorrMove.abs_signed hsigma).symm
      _ = |(L0 s q : Int)| := congrArg (fun z : Int => |z|) hx.1
      _ = (L0 s q : Int) := abs_of_nonneg (by positivity)
      _ ≤ (L0 s q : Int) := le_rfl
  · simpa [width] using hx.2 j hji

theorem width_mono {s q R u v : Nat} (huv : u ≤ v) : width s q R u ≤ width s q R v := by
  simp only [width]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right R huv) _

theorem width_step (s q R t : Nat) : width s q R (t + 1) = width s q R t + R := by
  simp [width, Nat.add_mul]
  omega

theorem L_step (s q t : Nat) : L s q (t + 1) = L s q t + s := by
  simp [L, Nat.add_mul]
  omega

/-- Each of the 700 boxes has exactly the quarter-face target relation used by one application of
target extension.  The orthant signs are chosen towards the coordinate hyperplanes. -/
theorem faceTarget_tile {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R k n1 t : Nat}
    (hq : q ≤ 7) (ht : t < stepCount)
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    CorrMove.FaceTarget (R : Int) (Dset i sigma s q R t)
      (Bset i sigma s q R t) (Bset i sigma s q R (t + 1)) := by
  classical
  have hbase : 272 + 264 * R ≤ s := by
    simp only [aspect] at hscale
    omega
  have hR2s : 2 * R ≤ s := by omega
  have hswidth : s ≤ width s q R t := by
    simp only [width, L0, aspect]
    omega
  have htfinal : t ≤ stepCount := ht.le
  have hwidthFinal : width s q R t ≤ width s q R stepCount :=
    width_mono htfinal
  have htransNat : width s q R t + s + 2 * R ≤ longScale s q :=
    le_trans (by omega) (tile_budget hq hbase)
  rintro v ⟨b, hb, hvb⟩
  rw [mem_Bset hsigma] at hb
  let a : Int := sigma * v i
  have havi : |a - (L s q t : Int)| ≤ (R : Int) := by
    rw [← hb.1, ← mul_sub, CorrMove.abs_signed hsigma]
    simpa [a] using hvb i
  have haBounds := abs_le.1 havi
  let ell : Int := (L s q t : Int) + (s : Int) - a
  have hellLower : (s : Int) - (R : Int) ≤ ell := by
    dsimp [ell]
    linarith
  have hellUpper : ell ≤ (s : Int) + (R : Int) := by
    dsimp [ell]
    linarith
  have hRell : (R : Int) ≤ ell := by
    have hR2s' : 2 * (R : Int) ≤ (s : Int) := by exact_mod_cast hR2s
    linarith
  let tau : Fin d → Int := fun j => if v j ≤ 0 then 1 else -1
  refine ⟨ell, i, sigma, tau, hRell, hsigma, ?_, ?_⟩
  · intro x hx
    rw [CorrMove.mem_cube] at hx
    rw [mem_Dset hsigma]
    have hxi := hx i
    have hsigned : |sigma * (x i - v i)| ≤ ell := by
      rw [CorrMove.abs_signed hsigma]
      exact hxi
    have hsignedBounds := abs_le.1 hsigned
    have hsplit : sigma * x i = sigma * (x i - v i) + a := by
      dsimp [a]
      ring
    constructor
    · constructor
      · have hR2s' : 2 * (R : Int) ≤ (s : Int) := by exact_mod_cast hR2s
        dsimp [ell] at hsignedBounds
        linarith
      · dsimp [ell] at hsignedBounds
        linarith
    · intro j hji
      have hxj := hx j
      have hvj : |v j| ≤ (width s q R t : Int) + (R : Int) := by
        have hbj := hb.2 j hji
        have hvbj := hvb j
        rw [abs_le] at hbj hvbj ⊢
        omega
      have htrans : (width s q R t : Int) + (s : Int) + 2 * (R : Int) ≤
          (longScale s q : Int) := by exact_mod_cast htransNat
      rw [abs_le] at hxj hvj ⊢
      constructor <;> linarith [hellUpper]
  · intro x hx
    rw [CorrMove.mem_qface] at hx
    obtain ⟨hxcube, hxnormal, hxorth⟩ := hx
    rw [mem_Bset hsigma]
    have hlong : sigma * x i = (L s q (t + 1) : Int) := by
      have hsplit : sigma * x i = sigma * (x i - v i) + a := by
        dsimp [a]
        ring
      rw [hsplit, hxnormal]
      dsimp [ell]
      rw [L_step]
      push_cast
      ring
    refine ⟨hlong, ?_⟩
    intro j hji
    have hbj := hb.2 j hji
    have hvbj := hvb j
    have hvj : |v j| ≤ (width s q R t : Int) + (R : Int) := by
      rw [abs_le] at hbj hvbj ⊢
      omega
    have hellWidth : ell ≤ (width s q R t : Int) + (R : Int) := by
      have hswidth' : (s : Int) ≤ (width s q R t : Int) := by exact_mod_cast hswidth
      linarith
    have hdisp := hxcube j
    have horth := hxorth j hji
    have hwidthStep : (width s q R (t + 1) : Int) =
        (width s q R t : Int) + (R : Int) := by
      exact_mod_cast width_step s q R t
    rw [hwidthStep, abs_le]
    by_cases hvneg : v j ≤ 0
    · have hnonneg : 0 ≤ x j - v j := by
        simpa only [tau, if_pos hvneg, one_mul] using horth
      rw [abs_le] at hdisp hvj
      constructor <;> linarith
    · have hnonpos : x j - v j ≤ 0 := by
        have h := horth
        simp only [tau, if_neg hvneg] at h
        linarith
      rw [abs_le] at hdisp hvj
      constructor <;> linarith

/-! ## Containment in the aspect-88 box

The preceding theorem checks the geometry one tile at a time.  The following statements close the
purely deterministic part of (6.11)--(6.12): the initial cube and all 700 site subboxes lie in one
aspect-88 long box, while the last hyperplane patch lies in its far face. -/

/-- Every tile used before step `700` is contained in the aspect-88 long box of scale
`R_long = 8s+q`.  No scale hypothesis is needed for this containment: its longitudinal upper edge
is `L_(t+1)`, hence is at most `L_700 = 88 R_long`, and its lower edge is nonnegative. -/
theorem Dset_subset_longBox {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R t : Nat} (ht : t < stepCount) :
    Dset i sigma s q R t ⊆
      CorrMove.longBox 0 (longScale s q : Int) i sigma 88 := by
  intro x hx
  rw [mem_Dset hsigma] at hx
  rw [CorrMove.mem_longBox hsigma (by positivity) (by norm_num)]
  simp only [Pi.zero_apply, sub_zero]
  have hlowNat : 2 * s ≤ L s q t := by
    simp only [L, L0, aspect]
    omega
  have hlow : (2 * s : Int) ≤ (L s q t : Int) := by exact_mod_cast hlowNat
  have huppNat : L s q t + s ≤ L s q stepCount := by
    have hts : (t + 1) * s ≤ stepCount * s :=
      Nat.mul_le_mul_right s (by omega)
    simpa [L, Nat.add_mul, Nat.add_assoc] using
      Nat.add_le_add_left hts (L0 s q)
  have hupp : (L s q t : Int) + (s : Int) ≤ (L s q stepCount : Int) := by
    exact_mod_cast huppNat
  have hfinal : (L s q stepCount : Int) = 88 * (longScale s q : Int) := by
    have h := congrArg (fun n : Nat => (n : Int)) (L_final s q)
    simpa [aspect] using h
  constructor
  · constructor
    · have hlongNonneg : 0 ≤ (longScale s q : Int) := by positivity
      linarith [hx.1.1]
    · rw [← hfinal]
      exact hx.1.2.trans hupp
  · exact hx.2

/-- The initial cube `Lambda_(L_0)` lies in the same aspect-88 long box.  The only nontrivial
inequality is `L_0 ≤ R_long`, which is a consequence of (6.7) and `q ≤ 7`. -/
theorem initialCube_subset_longBox {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R : Nat}
    (hq : q ≤ 7) (hbase : 272 + 264 * R ≤ s) :
    CorrMove.cube 0 (L0 s q : Int) ⊆
      CorrMove.longBox 0 (longScale s q : Int) i sigma 88 := by
  intro x hx
  rw [CorrMove.mem_cube] at hx
  rw [CorrMove.mem_longBox hsigma (by positivity) (by norm_num)]
  simp only [Pi.zero_apply, sub_zero] at hx ⊢
  have hLNat : L0 s q ≤ longScale s q := L0_le_longScale hq hbase
  have hL : (L0 s q : Int) ≤ (longScale s q : Int) := by exact_mod_cast hLNat
  have hlongNonneg : 0 ≤ (longScale s q : Int) := by positivity
  have hi : |sigma * x i| ≤ (L0 s q : Int) := by
    rw [CorrMove.abs_signed hsigma]
    exact hx i
  rw [abs_le] at hi
  constructor
  · constructor
    · linarith
    · nlinarith
  · intro j hji
    exact (hx j).trans hL

/-- The terminal patch is a subset of the far face of the enclosing aspect-88 box. -/
theorem final_Bset_subset_longFace {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R : Nat}
    (hq : q ≤ 7) (hbase : 272 + 264 * R ≤ s) :
    Bset i sigma s q R stepCount ⊆
      CorrMove.longFace 0 (longScale s q : Int) i sigma 88 := by
  intro x hx
  rw [mem_Bset hsigma] at hx
  rw [CorrMove.mem_longFace hsigma (by positivity) (by norm_num)]
  simp only [Pi.zero_apply, sub_zero]
  have hfinal : (L s q stepCount : Int) = 88 * (longScale s q : Int) := by
    have h := congrArg (fun n : Nat => (n : Int)) (L_final s q)
    simpa [aspect] using h
  have hwNat : width s q R stepCount ≤ longScale s q := width_final_le hq hbase
  have hw : (width s q R stepCount : Int) ≤ (longScale s q : Int) := by
    exact_mod_cast hwNat
  refine ⟨hx.1.trans hfinal, ?_⟩
  intro j hji
  exact (hx.2 j hji).trans hw

/-- The union of all 700 tile subboxes. -/
def tileRegion {d : Nat} (i : Fin d) (sigma : Int) (s q R : Nat) : Finset (Site d) :=
  (Finset.range stepCount).biUnion fun t => Dset i sigma s q R t

/-- The allowed set `A_700` of (6.11a). -/
def allowedRegion {d : Nat} (i : Fin d) (sigma : Int) (s q R : Nat) : Finset (Site d) :=
  CorrMove.cube 0 (L0 s q : Int) ∪ tileRegion i sigma s q R

theorem tileRegion_subset_longBox {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R : Nat} :
    tileRegion i sigma s q R ⊆
      CorrMove.longBox 0 (longScale s q : Int) i sigma 88 := by
  intro x hx
  rw [tileRegion, Finset.mem_biUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact Dset_subset_longBox i hsigma (Finset.mem_range.1 ht) hxt

/-- The complete allowed region of the 700-step induction lies in the intended finite long box. -/
theorem allowedRegion_subset_longBox {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R : Nat}
    (hq : q ≤ 7) (hbase : 272 + 264 * R ≤ s) :
    allowedRegion i sigma s q R ⊆
      CorrMove.longBox 0 (longScale s q : Int) i sigma 88 := by
  intro x hx
  rw [allowedRegion, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact initialCube_subset_longBox i hsigma hq hbase hx
  · exact tileRegion_subset_longBox (s := s) (q := q) (R := R) i hsigma hx

/-- The wired source cube is contained in the initial cube. -/
theorem sourceCube_subset_initialCube {d : Nat} {s q k n1 R : Nat}
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    CorrMove.cube (0 : Site d) (k : Int) ⊆ CorrMove.cube 0 (L0 s q : Int) := by
  apply CorrMove.ibox_mono
  intro j
  have hk : k ≤ L0 s q := by
    have := source_before_L0 (s := s) (q := q) (k := k) (n1 := n1) (R := R) hscale
    omega
  exact_mod_cast hk

/-- The wired source is outside every new tile, as required by target extension. -/
theorem sourceCube_disjoint_Dset {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R k n1 t : Nat}
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    Disjoint (CorrMove.cube (0 : Site d) (k : Int)) (Dset i sigma s q R t) := by
  rw [Finset.disjoint_left]
  intro x hxSource hxTile
  rw [CorrMove.mem_cube] at hxSource
  simp only [Pi.zero_apply, sub_zero] at hxSource
  rw [mem_Dset hsigma] at hxTile
  have hkNat : k + 2 * s < L s q t := by
    simp only [aspect, L, L0] at hscale ⊢
    omega
  have hk : (k : Int) < (L s q t : Int) - 2 * (s : Int) := by
    have hk' : (k : Int) + 2 * (s : Int) < (L s q t : Int) := by
      exact_mod_cast hkNat
    linarith
  have hxi : sigma * x i ≤ (k : Int) := by
    have hi := hxSource i
    rw [← CorrMove.abs_signed (a := x i) hsigma, abs_le] at hi
    exact hi.2
  linarith [hxTile.1.1]

theorem sourceCube_subset_allowedRegion {d : Nat} (i : Fin d) (sigma : Int)
    {s q R k n1 : Nat}
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    CorrMove.cube (0 : Site d) (k : Int) ⊆ allowedRegion i sigma s q R := by
  intro x hx
  rw [allowedRegion, Finset.mem_union]
  exact Or.inl (sourceCube_subset_initialCube hscale hx)

theorem sourceCube_disjoint_tileRegion {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R k n1 : Nat}
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    Disjoint (CorrMove.cube (0 : Site d) (k : Int)) (tileRegion i sigma s q R) := by
  rw [Finset.disjoint_left]
  intro x hxSource hxTiles
  rw [tileRegion, Finset.mem_biUnion] at hxTiles
  obtain ⟨t, -, hxTile⟩ := hxTiles
  exact Finset.disjoint_left.1 (sourceCube_disjoint_Dset i hsigma hscale) hxSource hxTile

/-- The complete deterministic statement of §6.2 under exactly the manuscript's scale
hypotheses.  This is the convenient interface for the eventual 700-step probability induction. -/
theorem geometry_700 {d : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s q R k n1 : Nat}
    (hq : q ≤ 7)
    (hscale : 3 * aspect + 3 * aspect * R + k + n1 + 8 ≤ s) :
    (Bset i sigma s q R 0).Nonempty ∧
      Bset i sigma s q R 0 ⊆ CorrMove.cube 0 (L0 s q : Int) ∧
      (∀ t, t < stepCount →
        CorrMove.FaceTarget (R : Int) (Dset i sigma s q R t)
          (Bset i sigma s q R t) (Bset i sigma s q R (t + 1))) ∧
      allowedRegion i sigma s q R ⊆
        CorrMove.longBox 0 (longScale s q : Int) i sigma 88 ∧
      Bset i sigma s q R stepCount ⊆
        CorrMove.longFace 0 (longScale s q : Int) i sigma 88 ∧
      CorrMove.cube (0 : Site d) (k : Int) ⊆ allowedRegion i sigma s q R ∧
      Disjoint (CorrMove.cube (0 : Site d) (k : Int)) (tileRegion i sigma s q R) := by
  have hbase : 272 + 264 * R ≤ s := by
    simp only [aspect] at hscale
    omega
  refine ⟨Bset_nonempty i hsigma s q R 0, Bset_zero_subset_initialCube i hsigma s q R,
    ?_, allowedRegion_subset_longBox i hsigma hq hbase,
    final_Bset_subset_longFace i hsigma hq hbase,
    sourceCube_subset_allowedRegion i sigma hscale,
    sourceCube_disjoint_tileRegion i hsigma hscale⟩
  intro t ht
  exact faceTarget_tile i hsigma hq ht hscale

#print axioms KNAll.Site.LongBox700.cascade
#print axioms KNAll.Site.LongBox700.tile_budget
#print axioms KNAll.Site.LongBox700.L_final
#print axioms KNAll.Site.LongBox700.faceTarget_tile
#print axioms KNAll.Site.LongBox700.Bset_nonempty
#print axioms KNAll.Site.LongBox700.Bset_zero_subset_initialCube
#print axioms KNAll.Site.LongBox700.Dset_subset_longBox
#print axioms KNAll.Site.LongBox700.final_Bset_subset_longFace
#print axioms KNAll.Site.LongBox700.allowedRegion_subset_longBox
#print axioms KNAll.Site.LongBox700.sourceCube_disjoint_Dset
#print axioms KNAll.Site.LongBox700.sourceCube_disjoint_tileRegion
#print axioms KNAll.Site.LongBox700.geometry_700

end KNAll.Site.LongBox700

end
