import Hypergraph.CorridorMove

/-!
# Variable-aspect long-box geometry

This is the `8 * K - 4` version of `LongBox700`.  It is kept in a separate
namespace so the already checked aspect-88 implementation remains unchanged.
-/

noncomputable section

namespace KNAll.Site.LongBoxVariable

set_option maxRecDepth 4096

open KNAll.Site
open Percolation.Literature.LatticeModels

def stepCount (K : Nat) : Nat := 8 * K - 4

def tol (K : Nat) (chi : Real) (t : Nat) : Real :=
  CorrMove.casc chi (stepCount K - t)

def componentTol (K : Nat) (chi : Real) : Real := (tol K chi 0) ^ 2 / 4

@[simp] theorem tol_final (K : Nat) (chi : Real) : tol K chi (stepCount K) = chi := by
  simp [tol]

theorem tol_rec (K : Nat) (chi : Real) {t : Nat} (ht : t < stepCount K) :
    tol K chi t = CorrMove.f (tol K chi (t + 1)) := by
  exact CorrMove.casc_rec chi (stepCount K) ht

theorem tol_closed_form (K : Nat) (chi : Real) {t : Nat} (ht : t ≤ stepCount K) :
    tol K chi t = chi ^ (2 ^ (stepCount K - t)) /
      96 ^ (2 ^ (stepCount K - t) - 1) := by
  exact CorrMove.casc_closed_form chi (stepCount K - t)

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

theorem tol_pos (K : Nat) {chi : Real} (hchi : 0 < chi) (t : Nat) : 0 < tol K chi t :=
  CorrMove.casc_pos hchi _

theorem tol_le_one (K : Nat) {chi : Real} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1)
    (t : Nat) : tol K chi t ≤ 1 :=
  CorrMove.casc_le_one hchi0 hchi1 _

theorem tol_mono (K : Nat) {chi : Real} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1)
    {u v : Nat} (huv : u ≤ v) (hv : v ≤ stepCount K) : tol K chi u ≤ tol K chi v := by
  apply casc_antitone hchi0 hchi1
  omega

theorem componentTol_pos (K : Nat) {chi : Real} (hchi : 0 < chi) :
    0 < componentTol K chi := by
  unfold componentTol
  positivity [tol_pos K hchi 0]

theorem componentTol_lt_tol_zero (K : Nat) {chi : Real}
    (hchi0 : 0 < chi) (hchi1 : chi ≤ 1) : componentTol K chi < tol K chi 0 := by
  have hb0 := tol_pos K hchi0 0
  have hb1 := tol_le_one K hchi0 hchi1 0
  unfold componentTol
  nlinarith [sq_nonneg (tol K chi 0)]

theorem cascade (K : Nat)
    {chi : Real} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1) {P : Nat → Real}
    (hsrc : 1 - tol K chi 0 < P 0)
    (hstep : ∀ t, t < stepCount K →
      1 - tol K chi (t + 1) / 8 < P t →
      1 - tol K chi (t + 1) < P (t + 1)) :
    1 - chi < P (stepCount K) := by
  have hb : ∀ t, t ≤ stepCount K → 0 ≤ tol K chi t ∧ tol K chi t ≤ 1 := by
    intro t ht
    exact ⟨(tol_pos K hchi0 t).le, tol_le_one K hchi0 hchi1 t⟩
  have hrec : ∀ t, t < stepCount K →
      tol K chi t = CorrMove.f (tol K chi (t + 1)) :=
    fun t ht => tol_rec K chi ht
  have h := CorrMove.cascade_of_step (J := stepCount K) (a := tol K chi) (P := P)
    hb hrec hsrc hstep
  simpa using h

def longScale (s rem : Nat) : Nat := 8 * s + rem

def L0 (K s rem : Nat) : Nat := 4 * s + K * rem

def L (K s rem t : Nat) : Nat := L0 K s rem + t * s

def width (K s rem R t : Nat) : Nat := L0 K s rem + t * R

theorem L_final {K : Nat} (hK : 1 ≤ K) (s rem : Nat) :
    L K s rem (stepCount K) = K * longScale s rem := by
  have hcount : stepCount K + 4 = 8 * K := by
    unfold stepCount
    omega
  have hprod := congrArg (fun n : Nat => n * s) hcount
  simp only [Nat.add_mul] at hprod
  unfold L L0
  calc
    4 * s + K * rem + stepCount K * s =
        K * rem + (stepCount K * s + 4 * s) := by ac_rfl
    _ = K * rem + 8 * K * s := by rw [hprod]
    _ = K * longScale s rem := by unfold longScale; ring

theorem tile_budget {K s rem R : Nat} (hK : 1 ≤ K) (hrem : rem ≤ 7)
    (hs : 3 * K + 8 + 3 * K * R ≤ s) :
    width K s rem R (stepCount K) + s + 2 * R ≤ longScale s rem := by
  have hcount : stepCount K + 2 ≤ 8 * K := by
    unfold stepCount
    omega
  have hcountR := Nat.mul_le_mul_right R hcount
  simp only [Nat.add_mul] at hcountR
  have hremK := Nat.mul_le_mul_left K hrem
  have hscale3 : 7 * K + 8 * K * R ≤ 3 * s := by
    have haux : 7 * K + 8 * K * R ≤ 3 * (3 * K + 8 + 3 * K * R) := by
      nlinarith
    exact haux.trans (Nat.mul_le_mul_left 3 hs)
  have hextra : K * rem + stepCount K * R + 2 * R ≤ 3 * s := by
    nlinarith
  simp only [width, L0, longScale]
  omega

theorem width_final_le {K s rem R : Nat} (hK : 1 ≤ K) (hrem : rem ≤ 7)
    (hs : 3 * K + 8 + 3 * K * R ≤ s) :
    width K s rem R (stepCount K) ≤ longScale s rem := by
  have h := tile_budget hK hrem hs
  omega

theorem L0_le_longScale {K s rem R : Nat} (hK : 1 ≤ K) (hrem : rem ≤ 7)
    (hs : 3 * K + 8 + 3 * K * R ≤ s) : L0 K s rem ≤ longScale s rem := by
  have h := tile_budget hK hrem hs
  simp only [width] at h
  omega

theorem source_before_L0 {K s rem k n1 R : Nat} (hK : 1 ≤ K)
    (hs : 3 * K + 3 * K * R + k + n1 + 8 ≤ s) :
    k < L0 K s rem - 2 * s := by
  simp only [L0] at hs ⊢
  omega

def Bset {d : Nat} (K : Nat) (i : Fin d) (sigma : Int)
    (s rem R t : Nat) : Finset (Site d) :=
  CorrMove.dbox 0 i sigma (L K s rem t : Int) (L K s rem t : Int)
    (width K s rem R t : Int)

def Dset {d : Nat} (K : Nat) (i : Fin d) (sigma : Int)
    (s rem R t : Nat) : Finset (Site d) :=
  CorrMove.dbox 0 i sigma ((L K s rem t : Int) - 2 * (s : Int))
    ((L K s rem t : Int) + (s : Int)) (longScale s rem : Int)

theorem mem_Bset {d : Nat} {K : Nat} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s rem R t : Nat} {x : Site d} :
    x ∈ Bset K i sigma s rem R t ↔
      sigma * x i = (L K s rem t : Int) ∧
        ∀ j, j ≠ i → |x j| ≤ (width K s rem R t : Int) := by
  rw [Bset, CorrMove.mem_dbox hsigma]
  simp only [Pi.zero_apply, sub_zero, le_antisymm_iff]
  tauto

theorem mem_Dset {d : Nat} {K : Nat} {i : Fin d} {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s rem R t : Nat} {x : Site d} :
    x ∈ Dset K i sigma s rem R t ↔
      ((L K s rem t : Int) - 2 * (s : Int) ≤ sigma * x i ∧
        sigma * x i ≤ (L K s rem t : Int) + (s : Int)) ∧
        ∀ j, j ≠ i → |x j| ≤ (longScale s rem : Int) := by
  rw [Dset, CorrMove.mem_dbox hsigma]
  simp only [Pi.zero_apply, sub_zero]

theorem Bset_nonempty {d : Nat} (K : Nat) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s rem R t : Nat) :
    (Bset K i sigma s rem R t).Nonempty := by
  classical
  let x : Site d := fun j => if j = i then sigma * (L K s rem t : Int) else 0
  refine ⟨x, (mem_Bset hsigma).2 ?_⟩
  have hsigmaSq : sigma * sigma = 1 := by
    rcases hsigma with rfl | rfl <;> norm_num
  constructor
  · dsimp [x]
    rw [if_pos rfl]
    calc
      sigma * (sigma * (L K s rem t : Int)) =
          (sigma * sigma) * (L K s rem t : Int) := by ring
      _ = (L K s rem t : Int) := by rw [hsigmaSq, one_mul]
  · intro j hji
    simp [x, hji]

theorem Bset_zero_subset_initialCube {d : Nat} (K : Nat) (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (s rem R : Nat) :
    Bset K i sigma s rem R 0 ⊆ CorrMove.cube 0 (L0 K s rem : Int) := by
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
      _ = |(L0 K s rem : Int)| := congrArg (fun z : Int => |z|) hx.1
      _ = (L0 K s rem : Int) := abs_of_nonneg (by positivity)
      _ ≤ (L0 K s rem : Int) := le_rfl
  · simpa [width] using hx.2 j hji

theorem width_mono {K s rem R u v : Nat} (huv : u ≤ v) :
    width K s rem R u ≤ width K s rem R v := by
  simp only [width]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right R huv) _

theorem width_step (K s rem R t : Nat) :
    width K s rem R (t + 1) = width K s rem R t + R := by
  simp [width, Nat.add_mul]
  omega

theorem L_step (K s rem t : Nat) : L K s rem (t + 1) = L K s rem t + s := by
  simp [L, Nat.add_mul]
  omega

theorem faceTarget_tile {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) {s rem R k n1 t : Nat}
    (hK : 1 ≤ K) (hrem : rem ≤ 7) (ht : t < stepCount K)
    (hscale : 3 * K + 3 * K * R + k + n1 + 8 ≤ s) :
    CorrMove.FaceTarget (R : Int) (Dset K i sigma s rem R t)
      (Bset K i sigma s rem R t) (Bset K i sigma s rem R (t + 1)) := by
  classical
  have hbase : 3 * K + 8 + 3 * K * R ≤ s := by omega
  have hR2s : 2 * R ≤ s := by nlinarith
  have hswidth : s ≤ width K s rem R t := by
    simp only [width, L0]
    omega
  have hwidthFinal : width K s rem R t ≤ width K s rem R (stepCount K) :=
    width_mono ht.le
  have htransNat : width K s rem R t + s + 2 * R ≤ longScale s rem :=
    le_trans (by omega) (tile_budget hK hrem hbase)
  rintro v ⟨b, hb, hvb⟩
  rw [mem_Bset hsigma] at hb
  let a : Int := sigma * v i
  have havi : |a - (L K s rem t : Int)| ≤ (R : Int) := by
    rw [← hb.1, ← mul_sub, CorrMove.abs_signed hsigma]
    simpa [a] using hvb i
  have haBounds := abs_le.1 havi
  let ell : Int := (L K s rem t : Int) + (s : Int) - a
  have hellLower : (s : Int) - (R : Int) ≤ ell := by dsimp [ell]; linarith
  have hellUpper : ell ≤ (s : Int) + (R : Int) := by dsimp [ell]; linarith
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
    have hsplit : sigma * x i = sigma * (x i - v i) + a := by dsimp [a]; ring
    constructor
    · constructor
      · have hR2s' : 2 * (R : Int) ≤ (s : Int) := by exact_mod_cast hR2s
        dsimp [ell] at hsignedBounds
        linarith
      · dsimp [ell] at hsignedBounds
        linarith
    · intro j hji
      have hxj := hx j
      have hvj : |v j| ≤ (width K s rem R t : Int) + (R : Int) := by
        have hbj := hb.2 j hji
        have hvbj := hvb j
        rw [abs_le] at hbj hvbj ⊢
        omega
      have htrans : (width K s rem R t : Int) + (s : Int) + 2 * (R : Int) ≤
          (longScale s rem : Int) := by exact_mod_cast htransNat
      rw [abs_le] at hxj hvj ⊢
      constructor <;> linarith [hellUpper]
  · intro x hx
    rw [CorrMove.mem_qface] at hx
    obtain ⟨hxcube, hxnormal, hxorth⟩ := hx
    rw [mem_Bset hsigma]
    have hlong : sigma * x i = (L K s rem (t + 1) : Int) := by
      have hsplit : sigma * x i = sigma * (x i - v i) + a := by dsimp [a]; ring
      rw [hsplit, hxnormal]
      dsimp [ell]
      rw [L_step]
      push_cast
      ring
    refine ⟨hlong, ?_⟩
    intro j hji
    have hbj := hb.2 j hji
    have hvbj := hvb j
    have hvj : |v j| ≤ (width K s rem R t : Int) + (R : Int) := by
      rw [abs_le] at hbj hvbj ⊢
      omega
    have hellWidth : ell ≤ (width K s rem R t : Int) + (R : Int) := by
      have hswidth' : (s : Int) ≤ (width K s rem R t : Int) := by exact_mod_cast hswidth
      linarith
    have hdisp := hxcube j
    have horth := hxorth j hji
    have hwidthStep : (width K s rem R (t + 1) : Int) =
        (width K s rem R t : Int) + (R : Int) := by
      exact_mod_cast width_step K s rem R t
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

theorem Dset_subset_longBox {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 1 ≤ K) {s rem R t : Nat}
    (ht : t < stepCount K) :
    Dset K i sigma s rem R t ⊆
      CorrMove.longBox 0 (longScale s rem : Int) i sigma K := by
  intro x hx
  rw [mem_Dset hsigma] at hx
  rw [CorrMove.mem_longBox hsigma (by positivity) (by exact_mod_cast hK)]
  simp only [Pi.zero_apply, sub_zero]
  have hlowNat : 2 * s ≤ L K s rem t := by simp only [L, L0]; omega
  have hlow : (2 * s : Int) ≤ (L K s rem t : Int) := by exact_mod_cast hlowNat
  have huppNat : L K s rem t + s ≤ L K s rem (stepCount K) := by
    have hts : (t + 1) * s ≤ stepCount K * s :=
      Nat.mul_le_mul_right s (by omega)
    simpa [L, Nat.add_mul, Nat.add_assoc] using
      Nat.add_le_add_left hts (L0 K s rem)
  have hupp : (L K s rem t : Int) + (s : Int) ≤
      (L K s rem (stepCount K) : Int) := by exact_mod_cast huppNat
  have hfinal : (L K s rem (stepCount K) : Int) =
      (K : Int) * (longScale s rem : Int) := by
    exact_mod_cast L_final hK s rem
  constructor
  · constructor
    · have hlongNonneg : 0 ≤ (longScale s rem : Int) := by positivity
      linarith [hx.1.1]
    · rw [← hfinal]
      exact hx.1.2.trans hupp
  · exact hx.2

theorem initialCube_subset_longBox {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 1 ≤ K) {s rem R : Nat}
    (hrem : rem ≤ 7) (hbase : 3 * K + 8 + 3 * K * R ≤ s) :
    CorrMove.cube 0 (L0 K s rem : Int) ⊆
      CorrMove.longBox 0 (longScale s rem : Int) i sigma K := by
  intro x hx
  rw [CorrMove.mem_cube] at hx
  rw [CorrMove.mem_longBox hsigma (by positivity) (by exact_mod_cast hK)]
  simp only [Pi.zero_apply, sub_zero] at hx ⊢
  have hLNat : L0 K s rem ≤ longScale s rem := L0_le_longScale hK hrem hbase
  have hL : (L0 K s rem : Int) ≤ (longScale s rem : Int) := by exact_mod_cast hLNat
  have hlongNonneg : 0 ≤ (longScale s rem : Int) := by positivity
  have hi : |sigma * x i| ≤ (L0 K s rem : Int) := by
    rw [CorrMove.abs_signed hsigma]
    exact hx i
  rw [abs_le] at hi
  constructor
  · constructor
    · linarith
    · have hKInt : (1 : Int) ≤ (K : Int) := by exact_mod_cast hK
      nlinarith
  · intro j hji
    exact (hx j).trans hL

theorem final_Bset_subset_longFace {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 1 ≤ K) {s rem R : Nat}
    (hrem : rem ≤ 7) (hbase : 3 * K + 8 + 3 * K * R ≤ s) :
    Bset K i sigma s rem R (stepCount K) ⊆
      CorrMove.longFace 0 (longScale s rem : Int) i sigma K := by
  intro x hx
  rw [mem_Bset hsigma] at hx
  rw [CorrMove.mem_longFace hsigma (by positivity) (by exact_mod_cast hK)]
  simp only [Pi.zero_apply, sub_zero]
  have hfinal : (L K s rem (stepCount K) : Int) =
      (K : Int) * (longScale s rem : Int) := by
    exact_mod_cast L_final hK s rem
  have hwNat : width K s rem R (stepCount K) ≤ longScale s rem :=
    width_final_le hK hrem hbase
  have hw : (width K s rem R (stepCount K) : Int) ≤ (longScale s rem : Int) := by
    exact_mod_cast hwNat
  refine ⟨hx.1.trans hfinal, ?_⟩
  intro j hji
  exact (hx.2 j hji).trans hw

def tileRegion {d : Nat} (K : Nat) (i : Fin d) (sigma : Int)
    (s rem R : Nat) : Finset (Site d) :=
  (Finset.range (stepCount K)).biUnion fun t => Dset K i sigma s rem R t

def allowedRegion {d : Nat} (K : Nat) (i : Fin d) (sigma : Int)
    (s rem R : Nat) : Finset (Site d) :=
  CorrMove.cube 0 (L0 K s rem : Int) ∪ tileRegion K i sigma s rem R

theorem tileRegion_subset_longBox {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 1 ≤ K) {s rem R : Nat} :
    tileRegion K i sigma s rem R ⊆
      CorrMove.longBox 0 (longScale s rem : Int) i sigma K := by
  intro x hx
  rw [tileRegion, Finset.mem_biUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact Dset_subset_longBox i hsigma hK (Finset.mem_range.1 ht) hxt

theorem allowedRegion_subset_longBox {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 1 ≤ K) {s rem R : Nat}
    (hrem : rem ≤ 7) (hbase : 3 * K + 8 + 3 * K * R ≤ s) :
    allowedRegion K i sigma s rem R ⊆
      CorrMove.longBox 0 (longScale s rem : Int) i sigma K := by
  intro x hx
  rw [allowedRegion, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact initialCube_subset_longBox i hsigma hK hrem hbase hx
  · exact tileRegion_subset_longBox i hsigma hK hx

theorem sourceCube_subset_initialCube {d : Nat} {K s rem k n1 R : Nat}
    (hK : 1 ≤ K) (hscale : 3 * K + 3 * K * R + k + n1 + 8 ≤ s) :
    CorrMove.cube (0 : Site d) (k : Int) ⊆ CorrMove.cube 0 (L0 K s rem : Int) := by
  apply CorrMove.ibox_mono
  intro j
  have hk : k ≤ L0 K s rem := by
    have := source_before_L0 (rem := rem) hK hscale
    omega
  exact_mod_cast hk

theorem sourceCube_disjoint_Dset {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 1 ≤ K) {s rem R k n1 t : Nat}
    (hscale : 3 * K + 3 * K * R + k + n1 + 8 ≤ s) :
    Disjoint (CorrMove.cube (0 : Site d) (k : Int)) (Dset K i sigma s rem R t) := by
  rw [Finset.disjoint_left]
  intro x hxSource hxTile
  rw [CorrMove.mem_cube] at hxSource
  simp only [Pi.zero_apply, sub_zero] at hxSource
  rw [mem_Dset hsigma] at hxTile
  have hkNat : k + 2 * s < L K s rem t := by
    simp only [L, L0] at hscale ⊢
    omega
  have hk : (k : Int) < (L K s rem t : Int) - 2 * (s : Int) := by
    have hk' : (k : Int) + 2 * (s : Int) < (L K s rem t : Int) := by exact_mod_cast hkNat
    linarith
  have hxi : sigma * x i ≤ (k : Int) := by
    have hi := hxSource i
    rw [← CorrMove.abs_signed (a := x i) hsigma, abs_le] at hi
    exact hi.2
  linarith [hxTile.1.1]

theorem sourceCube_subset_allowedRegion {d : Nat} {K : Nat} (i : Fin d) (sigma : Int)
    (hK : 1 ≤ K) {s rem R k n1 : Nat}
    (hscale : 3 * K + 3 * K * R + k + n1 + 8 ≤ s) :
    CorrMove.cube (0 : Site d) (k : Int) ⊆ allowedRegion K i sigma s rem R := by
  intro x hx
  rw [allowedRegion, Finset.mem_union]
  exact Or.inl (sourceCube_subset_initialCube hK hscale hx)

theorem sourceCube_disjoint_tileRegion {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 1 ≤ K) {s rem R k n1 : Nat}
    (hscale : 3 * K + 3 * K * R + k + n1 + 8 ≤ s) :
    Disjoint (CorrMove.cube (0 : Site d) (k : Int)) (tileRegion K i sigma s rem R) := by
  rw [Finset.disjoint_left]
  intro x hxSource hxTiles
  rw [tileRegion, Finset.mem_biUnion] at hxTiles
  obtain ⟨t, -, hxTile⟩ := hxTiles
  exact Finset.disjoint_left.1 (sourceCube_disjoint_Dset i hsigma hK hscale) hxSource hxTile

theorem geometry {d : Nat} {K : Nat} (i : Fin d) {sigma : Int}
    (hsigma : sigma = 1 ∨ sigma = -1) (hK : 1 ≤ K) {s rem R k n1 : Nat}
    (hrem : rem ≤ 7)
    (hscale : 3 * K + 3 * K * R + k + n1 + 8 ≤ s) :
    (Bset K i sigma s rem R 0).Nonempty ∧
      Bset K i sigma s rem R 0 ⊆ CorrMove.cube 0 (L0 K s rem : Int) ∧
      (∀ t, t < stepCount K →
        CorrMove.FaceTarget (R : Int) (Dset K i sigma s rem R t)
          (Bset K i sigma s rem R t) (Bset K i sigma s rem R (t + 1))) ∧
      allowedRegion K i sigma s rem R ⊆
        CorrMove.longBox 0 (longScale s rem : Int) i sigma K ∧
      Bset K i sigma s rem R (stepCount K) ⊆
        CorrMove.longFace 0 (longScale s rem : Int) i sigma K ∧
      CorrMove.cube (0 : Site d) (k : Int) ⊆ allowedRegion K i sigma s rem R ∧
      Disjoint (CorrMove.cube (0 : Site d) (k : Int))
        (tileRegion K i sigma s rem R) := by
  have hbase : 3 * K + 8 + 3 * K * R ≤ s := by omega
  refine ⟨Bset_nonempty K i hsigma s rem R 0,
    Bset_zero_subset_initialCube K i hsigma s rem R, ?_,
    allowedRegion_subset_longBox i hsigma hK hrem hbase,
    final_Bset_subset_longFace i hsigma hK hrem hbase,
    sourceCube_subset_allowedRegion i sigma hK hscale,
    sourceCube_disjoint_tileRegion i hsigma hK hscale⟩
  intro t ht
  exact faceTarget_tile i hsigma hK hrem ht hscale

#print axioms KNAll.Site.LongBoxVariable.L_final
#print axioms KNAll.Site.LongBoxVariable.tile_budget
#print axioms KNAll.Site.LongBoxVariable.faceTarget_tile
#print axioms KNAll.Site.LongBoxVariable.geometry

end KNAll.Site.LongBoxVariable

end
