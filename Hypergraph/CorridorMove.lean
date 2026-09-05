import Hypergraph.MacroExploration
import Hypergraph.StubBudget

/-!
# The corrected corridor move

This module formalises `math/CORRIDOR_MOVE.md`.

## The point

The corridor move as usually stated is **false** when only the outgoing corridor is assumed fresh.
`naive_corridorMove_false` is the machine-checked refutation: it exhibits a transcript whose
inspected set misses the outgoing corridor `E z y` entirely, whose pinned probability of reaching
the incoming target `M z` through `E w z` is exactly `1`, and whose pinned probability of reaching
`M y` through `E w z ∪ E z y` is exactly `0`.  The obstruction is a recorded **closed wall inside
the incoming corridor**, at transverse level `5 r`; freshness of `E z y` says nothing about it.

Consequently every statement below carries the corrected hypotheses of the note:

* the whole site subbox of the move, `Q z ∪ E z y` -- *including the current central box* -- is
  fresh (`hfresh`), not just the outgoing corridor;
* the input error is the tolerance `beta`, the `d+1`-fold iterate (0.1) of the manuscript source
  map `a ↦ a²/96` applied to `ρ/32`, not `ρ/4`;
* the scale is large: `44 ≤ r` and `100 (d+1) (R+1) < r` (0.3).

## Contents

* `casc`, `beta`, `casc_closed_form`, `cascade_of_step`: the tolerance cascade of §0 and §3, with
  the explicit constant `beta ρ d = (ρ/32)^(2^(d+1)) / 96^(2^(d+1)-1)` and the induction (3.7).
* `ibox`, `cube`, `qface`, `longBox`, `longFace`, `FaceTarget`, `LongTarget`: the finite geometry
  of §7 and the two target relations it verifies.
* `faceTarget_ibox`, `faceTarget_step`, `longTarget_cube`: the deterministic content of §7.1 and
  §7.2 -- the cross-section reduction and the aspect-88 long move.
* `inspected_disjoint_pending_out_E`: freshness of the **outgoing** corridor at a good
  transcript with a nonempty frontier, the sibling of `MacroExp.inspected_disjoint_pending_E`.
* `Q_subset_E` and `fresh_subbox`: §7.3 item 4, `Q z ⊆ E w z`, and the assembled freshness of the
  whole site subbox `Q z ∪ E z y`.
* `corridorMoveCore`: the same `d+1` cascade with the allowed region abstracted, which is what
  makes a second, narrow instance possible; `corridorMove` is its broad instance.
* `corridorMove`: the corrected move (0.4)/(0.8).
* `KN/CorridorNarrow.lean` carries the narrow instance `corridorMoveNarrow`, whose allowed set
  is `h.inspected ∪ E w z ∪ Stopped.stub` and whose target is `Stopped.stubTarget`.  It lives in
  a separate module because `KN.StoppedLevel` already depends on this one.
* `qface_nonempty`, `longFace_nonempty`, `Bx_nonempty`, `prob_move_step_eq_of_disjoint`: the §10
  regression checks against the three failed design patterns.
* `prob_eq_product`, `prob_of_targetExtension`: the pinned law is a product law, and the reduction
  of `hface`/`hlong` to a `TargetExt.LevelGeometry` family, which is the new certificate clause.

## What is assumed, and where it must come from

The `d+1` target-extension calls of §7 are the hypotheses `hface` and `hlong` of `corridorMove`.
They are manuscript Lemma 7.3 restricted to the fresh site subbox of the move.  In the Lean tree
that lemma is `TargetExt.targetExtension_eps`, whose `LevelGeometry.Gx` fields are exactly the
`MoveWindow` cylinders that §8.4 tells the certificate to record; `prob_of_targetExtension` is the
bridge, and the closing section of this file lists the clauses verbatim.

This module imports only `KN.MacroExploration` and `KN.StubBudget`, neither of which depends on
`KN.Certificate2`; every declaration below is therefore checked against source that builds, not
against a stale object file of a module under edit.
-/

noncomputable section

namespace KNAll.Site.CorrMove

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## §0, §3.  The tolerance cascade -/

section Cascade

/-- The source-error map of the manuscript target extension (3.1): for output error `a`, the
required input error is `δ_a = a c_a / 12 = a² / 96`. -/
def f (a : ℝ) : ℝ := a ^ 2 / 96

/-- The cascade `a_J, a_{J-1}, …` of (0.1), indexed by the number of remaining stages. -/
def casc (α : ℝ) : ℕ → ℝ
  | 0 => α
  | n + 1 => f (casc α n)

@[simp] theorem casc_zero (α : ℝ) : casc α 0 = α := rfl

@[simp] theorem casc_succ (α : ℝ) (n : ℕ) : casc α (n + 1) = f (casc α n) := rfl

/-- **The corridor-move input tolerance (0.1)**, `β = (ρ/32)^{2^{d+1}} / 96^{2^{d+1}-1}`. -/
def beta (ρ : ℝ) (d : ℕ) : ℝ := casc (ρ / 32) (d + 1)

theorem casc_pos {α : ℝ} (hα : 0 < α) : ∀ n, 0 < casc α n := by
  intro n
  induction n with
  | zero => simpa using hα
  | succ n ih => rw [casc_succ, f]; positivity

theorem casc_le_self {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) : ∀ n, casc α n ≤ α := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := casc_pos hα0 n
      rw [casc_succ, f]
      nlinarith

theorem casc_le_one {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) : casc α n ≤ 1 :=
  le_trans (casc_le_self hα0 hα1 n) hα1

/-- **The closed form (0.1).** -/
theorem casc_closed_form (α : ℝ) : ∀ n, casc α n = α ^ (2 ^ n) / 96 ^ (2 ^ n - 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hsucc : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + (2 ^ n - 1) + 1 := by
        have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
        omega
      have hexp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      rw [casc_succ, f, ih, hsucc, hexp]
      rw [div_pow, pow_add, pow_add, ← pow_mul]
      rw [pow_succ, pow_add]
      have h96 : ((96 : ℝ) ^ (2 ^ n - 1)) ≠ 0 := by positivity
      field_simp
      ring

/-- **(0.1) spelled out.** -/
theorem beta_closed_form (ρ : ℝ) (d : ℕ) :
    beta ρ d = (ρ / 32) ^ (2 ^ (d + 1)) / 96 ^ (2 ^ (d + 1) - 1) :=
  casc_closed_form _ _

theorem beta_pos {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) : 0 < beta ρ d :=
  casc_pos (by linarith) _

theorem beta_le {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℕ) : beta ρ d ≤ ρ / 32 :=
  casc_le_self (by linarith) (by linarith) _

/-- The manuscript source tolerance is stronger than the input tolerance `ε/8` of the Lean
`TargetExt.targetExtension_eps`: `a²/96 ≤ a/8` for `0 ≤ a ≤ 12`. -/
theorem f_le_div_eight {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : f a ≤ a / 8 := by
  rw [f]; nlinarith

/-- **The cascade induction (3.7)–(3.8).**  A chain of `J` target-extension steps, the `j`-th with
output error `a (j+1)` and hence input error `a j = f (a (j+1))`, carries an input estimate at
error `a 0` to an output estimate at error `a J`. -/
theorem cascade_of_step {J : ℕ} {a P : ℕ → ℝ}
    (hb : ∀ j, j ≤ J → 0 ≤ a j ∧ a j ≤ 1)
    (hrec : ∀ j, j < J → a j = f (a (j + 1)))
    (hsrc : 1 - a 0 < P 0)
    (hstep : ∀ j, j < J → 1 - a (j + 1) / 8 < P j → 1 - a (j + 1) < P (j + 1)) :
    1 - a J < P J := by
  have key : ∀ j, j ≤ J → 1 - a j < P j := by
    intro j
    induction j with
    | zero => intro _; exact hsrc
    | succ j ih =>
        intro hj
        have hjJ : j < J := by omega
        have hprev := ih (by omega)
        have hle : a j ≤ a (j + 1) / 8 := by
          rw [hrec j hjJ]
          exact f_le_div_eight (hb (j + 1) (by omega)).1 (hb (j + 1) (by omega)).2
        exact hstep j hjJ (by linarith)
  exact key J le_rfl

/-- The cascade `a j = casc α (J - j)` satisfies the recursion of `cascade_of_step`, with
`a 0 = casc α J` and `a J = α`. -/
theorem casc_rec (α : ℝ) (J : ℕ) {j : ℕ} (hj : j < J) :
    casc α (J - j) = f (casc α (J - (j + 1))) := by
  have h : J - j = (J - (j + 1)) + 1 := by omega
  rw [h, casc_succ]

end Cascade

/-! ## §7.  The finite geometry of the move

Sections 1--7 of the note use the **isotropic** manuscript sets, not the anisotropic
`MacroExp.abox`.  All of them are `ibox`es. -/

section Geometry

variable {d : ℕ}

/-- The box of radii `rho` about `c`. -/
def ibox (c : Site d) (rho : Fin d → ℤ) : Finset (Site d) :=
  Fintype.piFinset fun j => Finset.Icc (c j - rho j) (c j + rho j)

theorem mem_ibox {c x : Site d} {rho : Fin d → ℤ} :
    x ∈ ibox c rho ↔ ∀ j, c j - rho j ≤ x j ∧ x j ≤ c j + rho j := by
  simp [ibox, Fintype.mem_piFinset]

theorem mem_ibox_abs {c x : Site d} {rho : Fin d → ℤ} :
    x ∈ ibox c rho ↔ ∀ j, |x j - c j| ≤ rho j := by
  rw [mem_ibox]
  refine forall_congr' fun j => ?_
  rw [abs_le]
  omega

theorem ibox_mono {c : Site d} {rho rho' : Fin d → ℤ} (h : ∀ j, rho j ≤ rho' j) :
    ibox c rho ⊆ ibox c rho' := by
  intro x hx
  rw [mem_ibox_abs] at hx ⊢
  exact fun j => le_trans (hx j) (h j)

theorem centre_mem_ibox {c : Site d} {rho : Fin d → ℤ} (h : ∀ j, 0 ≤ rho j) : c ∈ ibox c rho := by
  rw [mem_ibox_abs]; simpa using h

/-- `c + Λ_s`, the isotropic cube of radius `s`. -/
def cube (c : Site d) (s : ℤ) : Finset (Site d) := ibox c fun _ => s

theorem mem_cube {c x : Site d} {s : ℤ} : x ∈ cube c s ↔ ∀ j, |x j - c j| ≤ s := mem_ibox_abs

theorem centre_mem_cube {c : Site d} {s : ℤ} (hs : 0 ≤ s) : c ∈ cube c s :=
  centre_mem_ibox fun _ => hs

/-- **No target is empty** (§10.2): every cube of nonnegative radius contains its centre, so is
nonempty. -/
theorem cube_nonempty (c : Site d) {s : ℤ} (hs : 0 ≤ s) : (cube c s).Nonempty :=
  ⟨c, centre_mem_cube hs⟩

/-- The orthant quarter-face of `cube v l`: the face with outward normal `σ` in the coordinate
`i`, restricted to the orthant of transverse signs `τ`. -/
def qface (v : Site d) (l : ℤ) (i : Fin d) (σ : ℤ) (τ : Fin d → ℤ) : Finset (Site d) :=
  (cube v l).filter fun x => σ * (x i - v i) = l ∧ ∀ j, j ≠ i → 0 ≤ τ j * (x j - v j)

theorem mem_qface {v x : Site d} {l : ℤ} {i : Fin d} {σ : ℤ} {τ : Fin d → ℤ} :
    x ∈ qface v l i σ τ ↔
      (∀ j, |x j - v j| ≤ l) ∧ σ * (x i - v i) = l ∧ ∀ j, j ≠ i → 0 ≤ τ j * (x j - v j) := by
  classical
  simp only [qface, Finset.mem_filter, mem_cube]

/-- **§7.1, (7.2)–(7.4).  The target relation of a quarter-face call.**  `Tset` is a quarter-face
target for `Bset` inside `Sub` at inflation radius `R` when every site within `R` of `Bset`
carries a cube of scale at least `R`, contained in `Sub`, one of whose orthant quarter-faces lies
in `Tset`.  This is the hypothesis "`B^{+R} ⊆ D` and `T` is a target for `B`" of §3, spelled out
for the geometry §7.1 uses. -/
def FaceTarget (R : ℤ) (Sub Bset Tset : Finset (Site d)) : Prop :=
  ∀ v : Site d, (∃ b ∈ Bset, ∀ j, |v j - b j| ≤ R) →
    ∃ (l : ℤ) (i : Fin d) (σ : ℤ) (τ : Fin d → ℤ),
      R ≤ l ∧ (σ = 1 ∨ σ = -1) ∧ cube v l ⊆ Sub ∧ qface v l i σ τ ⊆ Tset

/-- The aspect-`K` long box based at `v` in the direction `(i, σ)` at scale `l`: it extends back
by `l` and forward by `K l`, with transverse half-width `l`. -/
def longBox (v : Site d) (l : ℤ) (i : Fin d) (σ : ℤ) (K : ℤ) : Finset (Site d) :=
  (Fintype.piFinset fun j => Finset.Icc (v j - l - K * l) (v j + l + K * l)).filter
    fun x => (-l ≤ σ * (x i - v i) ∧ σ * (x i - v i) ≤ K * l) ∧ ∀ j, j ≠ i → |x j - v j| ≤ l

theorem abs_signed {σ a : ℤ} (hσ : σ = 1 ∨ σ = -1) : |σ * a| = |a| := by
  rcases hσ with rfl | rfl <;> simp

theorem mem_longBox {v x : Site d} {l : ℤ} {i : Fin d} {σ : ℤ} {K : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hl : 0 ≤ l) (hK : 1 ≤ K) :
    x ∈ longBox v l i σ K ↔
      ((-l ≤ σ * (x i - v i) ∧ σ * (x i - v i) ≤ K * l) ∧ ∀ j, j ≠ i → |x j - v j| ≤ l) := by
  classical
  rw [longBox, Finset.mem_filter, and_iff_right_iff_imp]
  rintro ⟨⟨h1, h2⟩, h3⟩
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  intro j
  have hKl : l ≤ K * l := le_mul_of_one_le_left hl hK
  by_cases hj : j = i
  · subst hj
    have habs : |x j - v j| ≤ K * l := by
      rw [← abs_signed (a := x j - v j) hσ, abs_le]
      constructor <;> linarith
    rw [abs_le] at habs
    constructor <;> linarith [habs.1, habs.2]
  · have habs := h3 j hj
    rw [abs_le] at habs
    constructor <;> linarith [habs.1, habs.2]

/-- The far face of the aspect-`K` long box. -/
def longFace (v : Site d) (l : ℤ) (i : Fin d) (σ : ℤ) (K : ℤ) : Finset (Site d) :=
  (longBox v l i σ K).filter fun x => σ * (x i - v i) = K * l

theorem mem_longFace {v x : Site d} {l : ℤ} {i : Fin d} {σ : ℤ} {K : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hl : 0 ≤ l) (hK : 1 ≤ K) :
    x ∈ longFace v l i σ K ↔
      (σ * (x i - v i) = K * l ∧ ∀ j, j ≠ i → |x j - v j| ≤ l) := by
  classical
  rw [longFace, Finset.mem_filter, mem_longBox hσ hl hK]
  have hKl : l ≤ K * l := le_mul_of_one_le_left hl hK
  constructor
  · rintro ⟨⟨-, h3⟩, h⟩; exact ⟨h, h3⟩
  · rintro ⟨h, h3⟩; exact ⟨⟨⟨by linarith, by linarith⟩, h3⟩, h⟩

/-- **§6, §7.2.  The target relation of the aspect-88 long call.**  `Tset` is a long target for
`Bset` inside `Sub` in the direction `(i, σ)` when every site within `R` of `Bset` carries an
aspect-88 long box of scale at least `R`, contained in `Sub`, whose far face lies in `Tset`.
The number `88` is the manuscript aspect `K₀` whose hitting estimate §6 builds from exactly
`8 K₀ - 4 = 700` nested quarter-face steps. -/
def LongTarget (R : ℤ) (i : Fin d) (σ : ℤ) (Sub Bset Tset : Finset (Site d)) : Prop :=
  ∀ v : Site d, (∃ b ∈ Bset, ∀ j, |v j - b j| ≤ R) →
    ∃ l : ℤ, R ≤ l ∧ longBox v l i σ 88 ⊆ Sub ∧ longFace v l i σ 88 ⊆ Tset


/-! ### §7.1.  The cross-section reduction -/

/-- **§7.1, (7.2)–(7.4).  The cross-section reduction, abstract form.**  One coordinate `q` has its
radius reduced from `rho q` to `rho' q` while every other radius grows by the inflation radius `R`.
The local scale is `ℓ(v) = R + max{0, |v_q - c_q| - rho' q}` of (7.2), and the quarter-face is the
one pointing towards `c` in every coordinate.  The three inequalities are exactly the containments
(7.3) and the displayed bounds after it.  No probability appears: this is deterministic. -/
theorem faceTarget_ibox (c : Site d) (R M : ℤ) (hR : 0 ≤ R) (q : Fin d)
    (rho rho' : Fin d → ℤ)
    (hRq : R ≤ rho' q) (hq' : rho' q ≤ rho q)
    (hoff : ∀ k, k ≠ q → rho k + R ≤ rho' k)
    (hell : ∀ k, k ≠ q → 2 * R + rho q - rho' q ≤ rho' k)
    (hM : ∀ k, rho k + 3 * R + rho q - rho' q ≤ M) :
    FaceTarget R (cube c M) (ibox c rho) (ibox c rho') := by
  classical
  rintro v ⟨b, hb, hvb⟩
  have hbc : ∀ j, |b j - c j| ≤ rho j := mem_ibox_abs.1 hb
  have hv : ∀ j, |v j - c j| ≤ rho j + R := by
    intro j
    have h1 := hbc j
    have h2 := hvb j
    rw [abs_le] at h1 h2 ⊢
    omega
  set l : ℤ := R + max 0 (|v q - c q| - rho' q) with hldef
  have hl1 : R ≤ l := by
    have : (0 : ℤ) ≤ max 0 (|v q - c q| - rho' q) := le_max_left _ _
    omega
  have hvq := hv q
  have hkey : (l = R ∧ |v q - c q| ≤ rho' q) ∨
      (l = R + |v q - c q| - rho' q ∧ rho' q ≤ |v q - c q|) := by
    rcases max_cases (0 : ℤ) (|v q - c q| - rho' q) with ⟨h, hle⟩ | ⟨h, hlt⟩
    · exact Or.inl ⟨by rw [hldef, h]; ring, by omega⟩
    · exact Or.inr ⟨by rw [hldef, h]; ring, by omega⟩
  have hl2 : l ≤ 2 * R + rho q - rho' q := by
    rcases hkey with ⟨h, hb⟩ | ⟨h, hb⟩
    · linarith
    · linarith [hvq]
  refine ⟨l, q, if v q ≤ c q then 1 else -1, (fun j => if v j ≤ c j then 1 else -1),
    hl1, ?_, ?_, ?_⟩
  · split_ifs <;> simp
  · -- the local cube lies in the declared subbox
    intro x hx
    rw [mem_cube] at hx
    rw [mem_cube]
    intro k
    have h1 := hx k
    have h2 := hv k
    have h3 := hM k
    rw [abs_le] at h1 h2 ⊢
    omega
  · -- the quarter-face lies in the reduced box
    intro x hx
    rw [mem_qface] at hx
    obtain ⟨hcube, hnorm, horth⟩ := hx
    rw [mem_ibox_abs]
    intro k
    by_cases hk : k = q
    · subst hk
      by_cases hvc : v k ≤ c k
      · rw [if_pos hvc, one_mul] at hnorm
        have habs : |v k - c k| = c k - v k := by
          rw [abs_of_nonpos (by omega)]; ring
        rw [habs] at hkey
        rw [abs_le]
        rcases hkey with ⟨hl, hb⟩ | ⟨hl, hb⟩ <;> omega
      · rw [if_neg hvc] at hnorm
        have hnorm' : x k - v k = -l := by linarith [hnorm]
        have habs : |v k - c k| = v k - c k := abs_of_nonneg (by omega)
        rw [habs] at hkey
        rw [abs_le]
        rcases hkey with ⟨hl, hb⟩ | ⟨hl, hb⟩ <;> omega
    · have horthk := horth k hk
      have hcubek := hcube k
      have hoffk := hoff k hk
      have hellk := hell k hk
      have hvk := hv k
      rw [abs_le] at hcubek hvk ⊢
      by_cases hvc : v k ≤ c k
      · rw [if_pos hvc, one_mul] at horthk
        omega
      · rw [if_neg hvc] at horthk
        have : x k - v k ≤ 0 := by linarith [horthk]
        omega


/-! ### §7.2.  The long move -/

/-- A longitudinal slab about `c` in the direction `(i, σ)`: signed longitudinal coordinate in
`[lo, hi]` and transverse half-width `w`.  The narrow corridor `H` of (1.1) and the box `D'` of
(7.6) are the two instances used below. -/
def dbox (c : Site d) (i : Fin d) (σ : ℤ) (lo hi w : ℤ) : Finset (Site d) :=
  (cube c (|lo| + |hi| + |w|)).filter fun x =>
    (lo ≤ σ * (x i - c i) ∧ σ * (x i - c i) ≤ hi) ∧ ∀ j, j ≠ i → |x j - c j| ≤ w

theorem mem_dbox {c x : Site d} {i : Fin d} {σ lo hi w : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    x ∈ dbox c i σ lo hi w ↔
      ((lo ≤ σ * (x i - c i) ∧ σ * (x i - c i) ≤ hi) ∧ ∀ j, j ≠ i → |x j - c j| ≤ w) := by
  classical
  rw [dbox, Finset.mem_filter, and_iff_right_iff_imp]
  rintro ⟨⟨h1, h2⟩, h3⟩
  rw [mem_cube]
  intro j
  by_cases hj : j = i
  · subst hj
    have := abs_signed (σ := σ) (a := x j - c j) hσ
    rw [← this, abs_le]
    constructor
    · have := abs_nonneg hi
      have := abs_nonneg w
      have := neg_abs_le lo
      linarith
    · have := abs_nonneg lo
      have := abs_nonneg w
      have := le_abs_self hi
      linarith
  · have h := h3 j hj
    have := le_abs_self w
    have := abs_nonneg lo
    have := abs_nonneg hi
    linarith

theorem dbox_mono {c : Site d} {i : Fin d} {σ lo hi w lo' hi' w' : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (hw : w ≤ w') :
    dbox c i σ lo hi w ⊆ dbox c i σ lo' hi' w' := by
  intro x hx
  rw [mem_dbox hσ] at hx ⊢
  exact ⟨⟨le_trans hlo hx.1.1, le_trans hx.1.2 hhi⟩, fun j hj => le_trans (hx.2 j hj) hw⟩

/-- **§7.2, (7.8)–(7.12).  The final long move.**  From a cube of radius `H` about `c`, the
aspect-88 long box of scale `ℓ(v) = ⌊(20 r - a)/88⌋` based at `v`, where `a` is the signed
longitudinal coordinate of `v`, stays inside `D'` and its far face lands in the cube of radius
`2 r` about the neighbouring centre `c + σ 20 r e_i`.  The single numerical hypothesis is
`89 (H + R) ≤ 156 r`, which is (7.9); the note derives it from `44 ≤ r` and
`100 (d+1) (R+1) < r`. -/
theorem longTarget_cube (c : Site d) (i : Fin d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (R H rr : ℤ) (hR : 1 ≤ R) (hrr : 44 ≤ rr)
    (h89 : 89 * (H + R) ≤ 156 * rr) (hRr : 88 * R + 88 ≤ 20 * rr - (H + R)) :
    LongTarget R i σ (dbox c i σ (-(2 * rr)) (22 * rr) (2 * rr)) (cube c H)
      (cube (c + Pi.single i (σ * (20 * rr))) (2 * rr)) := by
  classical
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
  rintro v ⟨b, hb, hvb⟩
  have hbc : ∀ j, |b j - c j| ≤ H := mem_cube.1 hb
  have hv : ∀ j, |v j - c j| ≤ H + R := by
    intro j
    have h1 := hbc j
    have h2 := hvb j
    rw [abs_le] at h1 h2 ⊢
    omega
  obtain ⟨A, hA⟩ : ∃ A : ℤ, σ * (v i - c i) = A := ⟨_, rfl⟩
  have hae : |A| ≤ H + R := by rw [← hA, abs_signed hσ]; exact hv i
  have haabs := abs_le.1 hae
  obtain ⟨l, hfl, hfu⟩ : ∃ l : ℤ, 88 * l ≤ 20 * rr - A ∧ 20 * rr - A < 88 * l + 88 :=
    ⟨(20 * rr - A) / 88, by omega, by omega⟩
  have hRl : R ≤ l := by linarith
  have hl0 : 0 ≤ l := le_trans (by linarith) hRl
  have htr : l + (H + R) ≤ 2 * rr := by linarith
  refine ⟨l, hRl, ?_, ?_⟩
  · -- the long box stays inside `D'`
    intro x hx
    rw [mem_longBox hσ hl0 (by norm_num)] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have hsplit : σ * (x i - c i) = σ * (x i - v i) + A := by rw [← hA]; ring
    rw [mem_dbox hσ]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hsplit]; linarith
    · rw [hsplit]; linarith
    · intro j hj
      have h4 := h3 j hj
      have h5 := hv j
      rw [abs_le] at h4 h5 ⊢
      omega
  · -- the far face lands in the neighbouring core cube
    intro x hx
    rw [mem_longFace hσ hl0 (by norm_num)] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [mem_cube]
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.single_eq_same]
      have hsplit : σ * (x j - c j) = 88 * l + A := by
        have hexp : σ * (x j - c j) = σ * (x j - v j) + σ * (v j - c j) := by ring
        rw [hexp, h1, hA]
      have hxc : x j - c j = σ * (88 * l + A) := by
        rw [← hsplit, ← mul_assoc, hσ2, one_mul]
      have hdiff : x j - (c j + σ * (20 * rr)) = σ * (88 * l + A - 20 * rr) := by
        have : x j - (c j + σ * (20 * rr)) = (x j - c j) - σ * (20 * rr) := by ring
        rw [this, hxc]; ring
      rw [hdiff, abs_signed hσ, abs_le]
      constructor <;> linarith
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hj, add_zero]
      have h4 := h2 j hj
      have h5 := hv j
      rw [abs_le] at h4 h5 ⊢
      omega

end Geometry

/-! ## §2.  The counterexample: freshness of the outgoing corridor is not enough

Take `w = 0`, `z = e₁`, `y = e₁ + e₂`.  A transcript may record a straight open segment from the
origin to the centre of `M z`, together with a **closed wall inside the incoming corridor** at
transverse level `5 r`.  Nothing of this touches the outgoing corridor `E z y`, whose sites all
have transverse coordinate strictly above `5 r`.  So the freshness hypothesis holds, the incoming
reservation holds with probability exactly one, and the outgoing connection is impossible. -/

section Counterexample

variable {d : ℕ} [NeZero d]

/-- The first entry of an open confined walk into a region: an open edge from outside `D` into
`D`, both endpoints inside the confining set. -/
private theorem firstEntry_walk {V : Type*} {G : SimpleGraph V} {W D : Set V} :
    ∀ {o b : V}, (openSiteGraph G W).Walk o b → o ∉ D → b ∈ D →
      ∃ u v : V, G.Adj u v ∧ u ∉ D ∧ v ∈ D ∧ u ∈ W ∧ v ∈ W := by
  intro o b p
  induction p with
  | nil => intro ho hb; exact absurd hb ho
  | @cons a m b hadj q ih =>
      intro ha hb
      have hadj' := (openSiteGraph_adj_iff' G W a m).1 hadj
      by_cases hm : m ∈ D
      · exact ⟨a, m, hadj'.1, ha, hm, hadj'.2.1, hadj'.2.2⟩
      · exact ih hm hb

theorem exists_firstEntry {V : Type*} {G : SimpleGraph V} {S D : Set V} {o b : V}
    {ω : SiteConfig V} (ho : o ∉ D) (hb : b ∈ D) (hconn : ω ∈ connWithin G S o b) :
    ∃ u v : V, G.Adj u v ∧ u ∉ D ∧ v ∈ D ∧ v ∈ ω ∩ S := by
  obtain ⟨-, hreach⟩ := hconn
  obtain ⟨p⟩ := hreach
  obtain ⟨u, v, huv, hu, hv, -, hvW⟩ := firstEntry_walk (G := G) (D := D) p ho hb
  exact ⟨u, v, huv, hu, hv, hvW⟩

/-- The macro-neighbour `e₁` of the origin. -/
def zdir : Site 2 := MacroExp.mvUnit 0 true

/-- The macro-neighbour `e₁ + e₂` of `zdir`. -/
def ydir : Site 2 := zdir + MacroExp.mvUnit 1 true

theorem val_zero_lt (d : ℕ) [NeZero d] : (0 : Fin d).val < 2 := by
  rw [Fin.val_zero]; omega

theorem val_one_eq (hd : 2 ≤ d) : (1 : Fin d).val = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]

theorem zero_ne_one_fin (hd : 2 ≤ d) : (0 : Fin d) ≠ (1 : Fin d) := by
  intro hc
  have := congrArg Fin.val hc
  rw [Fin.val_zero, val_one_eq hd] at this
  omega

theorem emb_zdir_zero : (MacroExp.emb zdir : Site d) (0 : Fin d) = 1 := by
  rw [MacroExp.emb_apply_of_lt zdir (val_zero_lt d)]
  have : (⟨(0 : Fin d).val, val_zero_lt d⟩ : Fin 2) = (0 : Fin 2) := by
    apply Fin.ext; simp
  rw [this]
  simp [zdir, MacroExp.mvUnit]

theorem emb_zdir_one (hd : 2 ≤ d) : (MacroExp.emb zdir : Site d) (1 : Fin d) = 0 := by
  have hlt : (1 : Fin d).val < 2 := by rw [val_one_eq hd]; omega
  rw [MacroExp.emb_apply_of_lt zdir hlt]
  have : (⟨(1 : Fin d).val, hlt⟩ : Fin 2) = (1 : Fin 2) := by
    apply Fin.ext; rw [val_one_eq hd]; rfl
  rw [this]
  simp [zdir, MacroExp.mvUnit]

theorem emb_ydir_one (hd : 2 ≤ d) : (MacroExp.emb ydir : Site d) (1 : Fin d) = 1 := by
  have hlt : (1 : Fin d).val < 2 := by rw [val_one_eq hd]; omega
  rw [MacroExp.emb_apply_of_lt ydir hlt]
  have : (⟨(1 : Fin d).val, hlt⟩ : Fin 2) = (1 : Fin 2) := by
    apply Fin.ext; rw [val_one_eq hd]; rfl
  rw [this]
  simp [ydir, zdir, MacroExp.mvUnit]

theorem emb_ydir_of_ne_one (hd : 2 ≤ d) {j : Fin d} (hj : j ≠ (1 : Fin d)) :
    (MacroExp.emb ydir : Site d) j = (MacroExp.emb zdir : Site d) j := by
  by_cases hlt : j.val < 2
  · rw [MacroExp.emb_apply_of_lt ydir hlt, MacroExp.emb_apply_of_lt zdir hlt]
    have hne : (⟨j.val, hlt⟩ : Fin 2) ≠ (1 : Fin 2) := by
      intro hc
      apply hj
      apply Fin.ext
      have := congrArg Fin.val hc
      rw [val_one_eq hd]
      simpa using this
    simp [ydir, MacroExp.mvUnit, hne]
  · rw [MacroExp.emb_apply_of_not_lt ydir hlt, MacroExp.emb_apply_of_not_lt zdir hlt]

theorem ctr_zdir_one (hd : 2 ≤ d) (r : ℕ) : MacroExp.ctr d r zdir (1 : Fin d) = 0 := by
  simp [MacroExp.ctr, emb_zdir_one hd]

theorem ctr_ydir_one (hd : 2 ≤ d) (r : ℕ) :
    MacroExp.ctr d r ydir (1 : Fin d) = 20 * (r : ℤ) := by
  simp [MacroExp.ctr, emb_ydir_one hd]

theorem ctr_ydir_of_ne_one (hd : 2 ≤ d) (r : ℕ) {j : Fin d} (hj : j ≠ (1 : Fin d)) :
    MacroExp.ctr d r ydir j = MacroExp.ctr d r zdir j := by
  simp [MacroExp.ctr, emb_ydir_of_ne_one hd hj]

theorem rad_one (hd : 2 ≤ d) (R t : ℕ) : MacroExp.rad R t (1 : Fin d) = (R : ℤ) := by
  unfold MacroExp.rad
  rw [if_pos (by rw [val_one_eq hd]; omega)]


/-- **(2.2).  The outgoing corridor lies strictly above the wall.**  Every site of `E z y` has
transverse coordinate larger than `5 r`. -/
theorem lt_coord_one_of_mem_E_out (hd : 2 ≤ d) {r t : ℕ} {x : Site d}
    (hx : x ∈ MacroExp.E d r t zdir ydir) : 5 * (r : ℤ) < x (1 : Fin d) := by
  classical
  rw [MacroExp.E, Finset.mem_sdiff, MacroExp.mem_hbox] at hx
  obtain ⟨hhull, hQ⟩ := hx
  by_contra hcon
  push Not at hcon
  apply hQ
  rw [MacroExp.Q, MacroExp.mem_abox]
  intro j
  by_cases hj : j = (1 : Fin d)
  · subst hj
    have h1 := hhull (1 : Fin d)
    rw [ctr_zdir_one hd, ctr_ydir_one hd, rad_one hd] at h1
    rw [ctr_zdir_one hd, rad_one hd]
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
    have hmin : min (0 : ℤ) (20 * (r : ℤ)) = 0 := min_eq_left (by omega)
    rw [hmin] at h1
    omega
  · have h1 := hhull j
    rw [ctr_ydir_of_ne_one hd r hj] at h1
    simpa using h1

/-- The incoming corridor stays within transverse distance `5 r` of the axis. -/
theorem abs_coord_one_of_mem_E_in (hd : 2 ≤ d) {r t : ℕ} {x : Site d}
    (hx : x ∈ MacroExp.E d r t 0 zdir) : |x (1 : Fin d)| ≤ 5 * (r : ℤ) := by
  classical
  rw [MacroExp.E, Finset.mem_sdiff, MacroExp.mem_hbox] at hx
  have h1 := hx.1 (1 : Fin d)
  rw [ctr_zdir_one hd, rad_one hd] at h1
  have hz : MacroExp.ctr d r (0 : Site 2) (1 : Fin d) = 0 := by
    simp [MacroExp.ctr]
  rw [hz] at h1
  simp only [min_self, max_self] at h1
  rw [abs_le]
  push_cast at h1 ⊢
  omega

/-- The straight open segment from the origin to the centre of `M z`. -/
def lineL (d r : ℕ) [NeZero d] : Finset (Site d) :=
  (Finset.range (20 * r + 1)).image fun k : ℕ => (Pi.single (0 : Fin d) (k : ℤ) : Site d)

theorem mem_lineL {r : ℕ} {x : Site d} :
    x ∈ lineL d r ↔ ∃ k : ℕ, k ≤ 20 * r ∧ x = Pi.single (0 : Fin d) (k : ℤ) := by
  classical
  simp only [lineL, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩

theorem coord_one_lineL (hd : 2 ≤ d) {r : ℕ} {x : Site d} (hx : x ∈ lineL d r) :
    x (1 : Fin d) = 0 := by
  obtain ⟨k, -, rfl⟩ := mem_lineL.1 hx
  have hne : (1 : Fin d) ≠ (0 : Fin d) := (zero_ne_one_fin hd).symm
  simp [hne]

/-- **The recorded closed wall (2.1).**  The cross-section of the *incoming* corridor at
transverse level `5 r`.  It is disjoint from the outgoing corridor. -/
def blockN (d r t : ℕ) [NeZero d] : Finset (Site d) :=
  (MacroExp.E d r t 0 zdir).filter fun x => x (1 : Fin d) = 5 * (r : ℤ)

theorem mem_blockN {r t : ℕ} {x : Site d} :
    x ∈ blockN d r t ↔ x ∈ MacroExp.E d r t 0 zdir ∧ x (1 : Fin d) = 5 * (r : ℤ) := by
  classical
  simp [blockN]

/-- **(2.2).  The recorded set misses the outgoing corridor entirely.** -/
theorem inspected_disjoint_E_out (hd : 2 ≤ d) {r t : ℕ} (hr : 0 < r) :
    Disjoint (lineL d r ∪ blockN d r t) (MacroExp.E d r t zdir ydir) := by
  rw [Finset.disjoint_left]
  intro x hx hxE
  have hlow := lt_coord_one_of_mem_E_out hd hxE
  have hr' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  rcases Finset.mem_union.1 hx with hx | hx
  · rw [coord_one_lineL hd hx] at hlow; omega
  · rw [(mem_blockN.1 hx).2] at hlow; omega

/-- **The counterexample transcript.**  Recorded open: the segment `lineL`.  Recorded closed: the
wall `blockN`.  Nothing else is inspected. -/
def badTr (d r t : ℕ) [NeZero d] : MacroExp.Tr d where
  inspected := lineL d r ∪ blockN d r t
  openSites := lineL d r
  openSites_subset := Finset.subset_union_left
  openV := {0}
  closedV := ∅

@[simp] theorem badTr_inspected (r t : ℕ) :
    (badTr d r t).inspected = lineL d r ∪ blockN d r t := rfl

@[simp] theorem badTr_openSites (r t : ℕ) : (badTr d r t).openSites = lineL d r := rfl

theorem badTr_state (r t : ℕ) (x : Site d) :
    (badTr d r t).state x ↔ x ∈ lineL d r := Iff.rfl


theorem emb_zdir_of_ne_zero (hd : 2 ≤ d) {j : Fin d} (hj : j ≠ (0 : Fin d)) :
    (MacroExp.emb zdir : Site d) j = 0 := by
  by_cases hlt : j.val < 2
  · have hj1 : j = (1 : Fin d) := by
      apply Fin.ext
      rw [val_one_eq hd]
      have : j.val ≠ 0 := fun hc => hj (Fin.ext (by rw [hc, Fin.val_zero]))
      omega
    rw [hj1, emb_zdir_one hd]
  · rw [MacroExp.emb_apply_of_not_lt zdir hlt]

theorem ctr_zdir_eq (hd : 2 ≤ d) (r : ℕ) :
    (MacroExp.ctr d r zdir : Site d) = Pi.single (0 : Fin d) (20 * (r : ℤ)) := by
  funext j
  by_cases hj : j = (0 : Fin d)
  · subst hj
    simp [MacroExp.ctr, emb_zdir_zero]
  · rw [MacroExp.ctr]
    simp [emb_zdir_of_ne_zero hd hj, hj]

/-- Consecutive sites of the segment are lattice-adjacent. -/
theorem adj_line (k : ℕ) :
    (zdGraph d).Adj (Pi.single (0 : Fin d) (k : ℤ)) (Pi.single (0 : Fin d) ((k : ℤ) + 1)) := by
  rw [zdGraph_adj_iff]
  refine ⟨(0 : Fin d), Or.inl ?_⟩
  funext j
  by_cases hj : j = (0 : Fin d)
  · subst hj; simp
  · simp [hj]

/-- The pinned configuration contains every recorded-open site of the segment. -/
theorem lineL_subset_substitute (r t : ℕ) (ω : SiteConfig (Site d)) :
    (↑(lineL d r) : Set (Site d)) ⊆
      substitute (↑(badTr d r t).inspected : Set (Site d)) (badTr d r t).state ω := by
  intro x hx
  have hxI : x ∈ (↑(badTr d r t).inspected : Set (Site d)) := by
    rw [badTr_inspected, Finset.coe_union]
    exact Or.inl hx
  rw [mem_substitute_of_mem _ hxI]
  exact Finset.mem_coe.1 hx

/-- **(2.3).  The incoming reservation holds with probability exactly one.**  The segment is
recorded open, so *every* configuration joins the origin to the centre of `M z`. -/
theorem prob_incoming_eq_one (hd : 2 ≤ d) (r t : ℕ) (q : unitInterval) :
    (badTr d r t).prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑((badTr d r t).inspected ∪ MacroExp.E d r t 0 zdir) : Set (Site d))
        (MacroExp.emb 0) (↑(MacroExp.M d r t zdir) : Set (Site d))) = 1 := by
  classical
  rw [FRDom.Transcript.prob_eq, pinnedProb]
  have huniv : substitute (↑(badTr d r t).inspected : Set (Site d)) (badTr d r t).state ⁻¹'
      connWithinSet (zdGraph d)
        (↑((badTr d r t).inspected ∪ MacroExp.E d r t 0 zdir) : Set (Site d))
        (MacroExp.emb 0) (↑(MacroExp.M d r t zdir) : Set (Site d)) = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true, Set.mem_preimage]
    set ω' := substitute (↑(badTr d r t).inspected : Set (Site d)) (badTr d r t).state ω with hω'
    have hline : (↑(lineL d r) : Set (Site d)) ⊆ ω' := lineL_subset_substitute r t ω
    set S : Set (Site d) :=
      (↑((badTr d r t).inspected ∪ MacroExp.E d r t 0 zdir) : Set (Site d)) with hS
    have hlineS : (↑(lineL d r) : Set (Site d)) ⊆ S := by
      rw [hS, badTr_inspected, Finset.coe_union, Finset.coe_union]
      intro x hx
      exact Or.inl (Or.inl hx)
    have hmem : ∀ k : ℕ, k ≤ 20 * r →
        (Pi.single (0 : Fin d) (k : ℤ) : Site d) ∈ ω' ∩ S := by
      intro k hk
      have hL : (Pi.single (0 : Fin d) (k : ℤ) : Site d) ∈ (↑(lineL d r) : Set (Site d)) :=
        Finset.mem_coe.2 (mem_lineL.2 ⟨k, hk, rfl⟩)
      exact ⟨hline hL, hlineS hL⟩
    have hreach : ∀ k : ℕ, k ≤ 20 * r →
        (openSiteGraph (zdGraph d) (ω' ∩ S)).Reachable
          (Pi.single (0 : Fin d) ((0 : ℕ) : ℤ)) (Pi.single (0 : Fin d) (k : ℤ)) := by
      intro k
      induction k with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ k ih =>
          intro hk
          have hstep : (openSiteGraph (zdGraph d) (ω' ∩ S)).Adj
              (Pi.single (0 : Fin d) (k : ℤ)) (Pi.single (0 : Fin d) ((k : ℤ) + 1)) := by
            rw [openSiteGraph_adj_iff']
            exact ⟨adj_line k, hmem k (by omega), hmem (k + 1) (by omega) |>.imp id id⟩
          have hcast : (Pi.single (0 : Fin d) (((k + 1 : ℕ)) : ℤ) : Site d)
              = Pi.single (0 : Fin d) ((k : ℤ) + 1) := by push_cast; rfl
          rw [hcast]
          exact (ih (by omega)).trans hstep.reachable
    have hzero : (MacroExp.emb (0 : Site 2) : Site d) = Pi.single (0 : Fin d) ((0 : ℕ) : ℤ) := by
      rw [MacroExp.emb_zero]
      funext j; simp
    rw [mem_connWithinSet_iff]
    refine ⟨MacroExp.ctr d r zdir, Finset.mem_coe.2 (MacroExp.ctr_mem_M r t zdir), ?_, ?_⟩
    · rw [hzero]; exact hmem 0 (by omega)
    · rw [hzero, ctr_zdir_eq hd]
      have h20 : (20 * (r : ℤ)) = ((20 * r : ℕ) : ℤ) := by push_cast; ring
      rw [h20]
      exact hreach (20 * r) le_rfl
  rw [huniv]
  exact probReal_univ

/-- **(2.4)–(2.5).  The outgoing connection is impossible.**  Every lattice path from the origin
to `M y` meets transverse level `5 r`; there the only allowed sites are the recorded-closed wall,
so no configuration realises the connection. -/
theorem prob_outgoing_eq_zero (hd : 2 ≤ d) {r t : ℕ} (hr : 0 < r) (q : unitInterval) :
    (badTr d r t).prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑((badTr d r t).inspected ∪ MacroExp.E d r t 0 zdir ∪ MacroExp.E d r t zdir ydir) :
          Set (Site d))
        (MacroExp.emb 0) (↑(MacroExp.M d r t ydir) : Set (Site d))) = 0 := by
  classical
  have hr' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  rw [FRDom.Transcript.prob_eq, pinnedProb]
  have hempty : substitute (↑(badTr d r t).inspected : Set (Site d)) (badTr d r t).state ⁻¹'
      connWithinSet (zdGraph d)
        (↑((badTr d r t).inspected ∪ MacroExp.E d r t 0 zdir ∪ MacroExp.E d r t zdir ydir) :
          Set (Site d))
        (MacroExp.emb 0) (↑(MacroExp.M d r t ydir) : Set (Site d)) = ∅ := by
    ext ω
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_preimage]
    intro hconn
    rw [mem_connWithinSet_iff] at hconn
    obtain ⟨b, hb, hconn⟩ := hconn
    -- the target is above transverse level `17 r`
    have hbD : 5 * (r : ℤ) ≤ b (1 : Fin d) := by
      have := (MacroExp.mem_abox.1 (Finset.mem_coe.1 hb)) (1 : Fin d)
      rw [ctr_ydir_one hd, rad_one hd] at this
      push_cast at this
      omega
    have hoD : (MacroExp.emb (0 : Site 2) : Site d) ∉ {x : Site d | 5 * (r : ℤ) ≤ x (1 : Fin d)} := by
      rw [MacroExp.emb_zero]
      simp only [Set.mem_setOf_eq]
      intro hc
      simp only [Pi.zero_apply] at hc
      omega
    obtain ⟨u, v, huv, hu, hv, hvS⟩ := exists_firstEntry hoD hbD hconn
    -- the crossing site sits exactly at level `5 r`
    have hstep : |v (1 : Fin d) - u (1 : Fin d)| ≤ 1 := by
      obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff u v).1 huv
      · rw [hi]
        by_cases hij : i = (1 : Fin d) <;> simp [hij]
      · rw [hi]
        by_cases hij : i = (1 : Fin d) <;> simp [hij]
    simp only [Set.mem_setOf_eq, not_le] at hu
    simp only [Set.mem_setOf_eq] at hv
    rw [abs_le] at hstep
    have hv5 : v (1 : Fin d) = 5 * (r : ℤ) := by omega
    -- the crossing site is recorded, hence recorded closed
    have hvI : v ∈ (↑(badTr d r t).inspected : Set (Site d)) := by
      have hvmem := hvS.2
      rw [Finset.coe_union, Finset.coe_union] at hvmem
      rcases hvmem with (hvm | hvm) | hvm
      · exact hvm
      · rw [badTr_inspected, Finset.coe_union]
        exact Or.inr (Finset.mem_coe.2 (mem_blockN.2 ⟨Finset.mem_coe.1 hvm, hv5⟩))
      · exact absurd (lt_coord_one_of_mem_E_out hd (Finset.mem_coe.1 hvm)) (by omega)
    have hvopen := hvS.1
    rw [mem_substitute_of_mem _ hvI] at hvopen
    have : v (1 : Fin d) = 0 := coord_one_lineL hd hvopen
    omega
  rw [hempty]
  exact measureReal_empty

/-- **§2.  The naive corridor move is false.**  There is a transcript whose inspected set is
disjoint from the outgoing corridor, whose incoming reservation to `M z` through the incoming
corridor holds with probability `1`, and whose outgoing connection to `M y` through both corridors
has probability `0`.  No tolerance repairs this: the hypothesis holds at every `ε > 0` and the
conclusion fails at every `ρ ≤ 1`. -/
theorem naive_corridorMove_false (hd : 2 ≤ d) {r t : ℕ} (hr : 0 < r) (q : unitInterval)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : ρ ≤ 1) :
    ∃ h : MacroExp.Tr d,
      Disjoint h.inspected (MacroExp.E d r t zdir ydir) ∧
      1 - ε < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d)
          (↑(h.inspected ∪ MacroExp.E d r t 0 zdir) : Set (Site d))
          (MacroExp.emb 0) (↑(MacroExp.M d r t zdir) : Set (Site d))) ∧
      ¬ 1 - ρ < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d)
          (↑(h.inspected ∪ MacroExp.E d r t 0 zdir ∪ MacroExp.E d r t zdir ydir) : Set (Site d))
          (MacroExp.emb 0) (↑(MacroExp.M d r t ydir) : Set (Site d))) := by
  refine ⟨badTr d r t, ?_, ?_, ?_⟩
  · rw [badTr_inspected]; exact inspected_disjoint_E_out hd hr
  · rw [prob_incoming_eq_one hd r t q]; linarith
  · rw [prob_outgoing_eq_zero hd hr q]
    intro hc
    linarith

end Counterexample

/-! ## §7.3.  Freshness, and the manuscript sets inside the macro geometry -/

section Fresh

variable {d : ℕ} [NeZero d]

/-- **§7.3 item 4.  `Q z ⊆ E w z`.**  The edge region subtracts only the *tail* cube `Q w`, and the
two central boxes of distinct macro-vertices are disjoint because their centres are `20 r` apart
while each has planar radius `5 r`. -/
theorem Q_subset_E (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r) {w z : Site 2} (hwz : w ≠ z) :
    MacroExp.Q d r t z ⊆ MacroExp.E d r t w z := by
  intro x hx
  rw [MacroExp.Q, MacroExp.mem_abox] at hx
  rw [MacroExp.E, Finset.mem_sdiff, MacroExp.mem_hbox, MacroExp.Q, MacroExp.mem_abox]
  refine ⟨fun j => ?_, fun hQ => ?_⟩
  · have h := hx j
    have h1 := min_le_right (MacroExp.ctr d r w j) (MacroExp.ctr d r z j)
    have h2 := le_max_right (MacroExp.ctr d r w j) (MacroExp.ctr d r z j)
    omega
  · obtain ⟨i, hi⟩ : ∃ i : Fin 2, w i ≠ z i := by
      by_contra hc
      push Not at hc
      exact hwz (funext hc)
    have hid : i.val < d := lt_of_lt_of_le i.isLt hd
    have h1 := hx ⟨i.val, hid⟩
    have h2 := hQ ⟨i.val, hid⟩
    have hjlt : (⟨i.val, hid⟩ : Fin d).val < 2 := i.isLt
    rw [MacroExp.ctr_apply_of_lt r z hjlt] at h1
    rw [MacroExp.ctr_apply_of_lt r w hjlt] at h2
    unfold MacroExp.rad at h1 h2
    rw [if_pos hjlt] at h1 h2
    have hr' : (0 : ℤ) ≤ 20 * (r : ℤ) := by positivity
    have hr1 : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    rcases lt_or_gt_of_ne hi with hlt | hlt
    · have hle : w i + 1 ≤ z i := hlt
      have := mul_le_mul_of_nonneg_left hle hr'
      push_cast at h1 h2
      nlinarith
    · have hle : z i + 1 ≤ w i := hlt
      have := mul_le_mul_of_nonneg_left hle hr'
      push_cast at h1 h2
      nlinarith

/-- **§7.3 item 2 for the outgoing corridor.**  At a good non-terminal transcript the whole edge
region of a *pending* direction of the vertex about to be examined is unread.  This is the sibling
of `MacroExp.inspected_disjoint_pending_E`: the tail of the outgoing edge is the undetermined
vertex `pendZ`, so the edge is neither a cover edge nor the reverse of one.

The frontier hypothesis is stated as nonemptiness of the boundary; at a non-terminal transcript
`MacroExp.boundary_nonempty_of_not_terminal` supplies it. -/
theorem inspected_disjoint_pending_out_E (d : ℕ) [NeZero d] (r t n : ℕ) {q : unitInterval}
    {δ : ℝ} {h : MacroExp.Tr d} (hd : 2 ≤ d) (hr : 0 < r) (hg : MacroExp.Good d r t h q δ)
    (hne : (h.boundary (zdGraph 2) (box 2 n) 0).Nonempty)
    {y : Site 2} (hy : y ∈ MacroExp.pending d h (MacroExp.pendZ d n h)) :
    Disjoint h.inspected (MacroExp.E d r t (MacroExp.pendZ d n h) y) := by
  classical
  obtain ⟨edges, hedges, hcover⟩ := hg.cover
  obtain ⟨-, hzo, hzc, -⟩ := MacroExp.pendZ_mem d n hne
  have hpzUndet : MacroExp.pendZ d n h ∉ h.openV ∪ h.closedV := by
    intro hpz
    rcases Finset.mem_union.1 hpz with hpz | hpz
    · exact hzo hpz
    · exact hzc hpz
  obtain ⟨hynbr, hyUndet⟩ := (MacroExp.mem_pending d).1 hy
  have hadj : (zdGraph 2).Adj (MacroExp.pendZ d n h) y := MacroExp.adj_of_mem_nbrs hynbr
  have hy0 : (0 : Site 2) ≠ y := by
    intro hc
    exact hyUndet (by rw [← hc]; exact Finset.mem_union_left _ hg.zero_mem)
  rw [Finset.disjoint_left]
  intro x hxI hxNew
  rcases hcover (Finset.mem_coe.2 hxI) with hxQ | hxEdges
  · exact Finset.disjoint_left.1 (MacroExp.protectedEdge_disjoint_Q hd r t hr hadj hy0)
      hxNew (Finset.mem_coe.1 hxQ)
  · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxEdges
    obtain ⟨heOpen, heDet, heAdj⟩ := hedges e (Finset.mem_coe.1 he)
    have hheads : e.2 ≠ y := fun hc => hyUndet (hc ▸ heDet)
    have hreverse : ¬ (e.1 = y ∧ e.2 = MacroExp.pendZ d n h) := by
      rintro ⟨-, heq⟩
      exact hpzUndet (heq ▸ heDet)
    exact Finset.disjoint_left.1
      (MacroExp.protectedEdges_disjoint hd r t hr heAdj hadj hheads hreverse)
      (Finset.mem_coe.1 hxe) hxNew

end Fresh

/-! ## §0.6–0.7.  The manuscript sets inside the anisotropic macro geometry

`MacroExp.M` and `MacroExp.Q` have planar radius `3 r`, `5 r` but transverse half-width `t`, so
they are *not* the manuscript cubes.  Every statement below therefore carries the explicit clause
`5 * r ≤ t` of §8.3 option 1, and uses the isotropic core `c_z + Λ_{3r}` as the reservation
target. -/

section Isotropic

variable {d : ℕ} [NeZero d]

theorem emb_sub (y z : Site 2) (j : Fin d) :
    (MacroExp.emb (y - z) : Site d) j = MacroExp.emb y j - MacroExp.emb z j := by
  by_cases hj : j.val < 2
  · rw [MacroExp.emb_apply_of_lt _ hj, MacroExp.emb_apply_of_lt _ hj,
      MacroExp.emb_apply_of_lt _ hj]
    rfl
  · rw [MacroExp.emb_apply_of_not_lt _ hj, MacroExp.emb_apply_of_not_lt _ hj,
      MacroExp.emb_apply_of_not_lt _ hj]
    ring

/-- The direction of a macro-edge is planar. -/
theorem planar_of_emb {y z : Site 2} {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) : i.val < 2 := by
  by_contra hi
  have h := congrFun hemb i
  rw [MacroExp.emb_apply_of_not_lt _ hi, Pi.single_eq_same] at h
  rcases hσ with rfl | rfl <;> norm_num at h

theorem rad_planar {R t : ℕ} {i : Fin d} (hi : i.val < 2) : MacroExp.rad R t i = (R : ℤ) := by
  unfold MacroExp.rad; rw [if_pos hi]

/-- **(0.7).  The neighbouring centre.** -/
theorem ctr_add_dir (r : ℕ) {y z : Site 2} {i : Fin d} {σ : ℤ}
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) :
    (MacroExp.ctr d r y : Site d) = MacroExp.ctr d r z + Pi.single i (σ * (20 * (r : ℤ))) := by
  funext j
  have h := congrFun hemb j
  rw [emb_sub] at h
  simp only [Pi.add_apply, MacroExp.ctr]
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same] at h ⊢
    have : MacroExp.emb y j - MacroExp.emb z j = σ := h
    have hy : (MacroExp.emb y : Site d) j = MacroExp.emb z j + σ := by omega
    rw [hy]; ring
  · rw [Pi.single_eq_of_ne hj] at h ⊢
    have : MacroExp.emb y j - MacroExp.emb z j = 0 := h
    have hy : (MacroExp.emb y : Site d) j = MacroExp.emb z j := by omega
    rw [hy]; ring

theorem cube_subset_Q {r t : ℕ} (ht : 5 * r ≤ t) (z : Site 2) :
    cube (MacroExp.ctr d r z) (5 * (r : ℤ)) ⊆ MacroExp.Q d r t z := by
  intro x hx
  rw [mem_cube] at hx
  rw [MacroExp.Q, MacroExp.mem_abox]
  intro j
  have h := hx j
  rw [abs_le] at h
  have ht' : 5 * (r : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
  unfold MacroExp.rad
  split_ifs <;> push_cast <;> omega

theorem cube_subset_M {r t s : ℕ} (hs : (s : ℤ) ≤ 3 * (r : ℤ)) (ht : (s : ℤ) ≤ (t : ℤ))
    (z : Site 2) : cube (MacroExp.ctr d r z) (s : ℤ) ⊆ MacroExp.M d r t z := by
  intro x hx
  rw [mem_cube] at hx
  rw [MacroExp.M, MacroExp.mem_abox]
  intro j
  have h := hx j
  rw [abs_le] at h
  unfold MacroExp.rad
  split_ifs <;> push_cast <;> omega

/-- **(7.7).  `D' ⊆ Q z ∪ E z y`.**  The part of the long box at signed coordinate at most `5 r`
lies in the head cube of the incoming edge, the rest in the outgoing edge region. -/
theorem dbox_subset_Q_union_E {r t : ℕ} (hr : 0 < r) (ht : 5 * r ≤ t) {z y : Site 2}
    {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ) :
    dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ)) ⊆
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y := by
  classical
  have hi := planar_of_emb hσ hemb
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
  have hr' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have ht' : 5 * (r : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
  have hcy := ctr_add_dir (d := d) r hemb
  intro x hx
  rw [mem_dbox hσ] at hx
  obtain ⟨⟨hlo, hhi⟩, htrans⟩ := hx
  have habsi : |x i - MacroExp.ctr d r z i| = |σ * (x i - MacroExp.ctr d r z i)| :=
    (abs_signed hσ).symm
  by_cases hnear : σ * (x i - MacroExp.ctr d r z i) ≤ 5 * (r : ℤ)
  · refine Finset.mem_union_left _ ?_
    rw [MacroExp.Q, MacroExp.mem_abox]
    intro j
    by_cases hj : j = i
    · subst hj
      have : |x j - MacroExp.ctr d r z j| ≤ 5 * (r : ℤ) := by
        rw [habsi, abs_le]; omega
      rw [abs_le] at this
      rw [rad_planar hi]
      omega
    · have h := htrans j hj
      rw [abs_le] at h
      unfold MacroExp.rad
      split_ifs <;> push_cast <;> omega
  · push Not at hnear
    refine Finset.mem_union_right _ ?_
    rw [MacroExp.E, Finset.mem_sdiff, MacroExp.mem_hbox]
    constructor
    · intro j
      by_cases hj : j = i
      · subst hj
        have hcyj : MacroExp.ctr d r y j = MacroExp.ctr d r z j + σ * (20 * (r : ℤ)) := by
          rw [hcy]; simp
        rw [hcyj, rad_planar hi]
        rcases hσ with rfl | rfl
        · simp only [one_mul] at hlo hhi hnear
          rw [min_eq_left (by omega), max_eq_right (by omega)]
          push_cast
          omega
        · have he1 : (-1 : ℤ) * (x j - MacroExp.ctr d r z j) = -(x j - MacroExp.ctr d r z j) := by
            ring
          rw [he1] at hlo hhi hnear
          rw [min_eq_right (by omega), max_eq_left (by omega)]
          push_cast
          omega
      · have hcyj : MacroExp.ctr d r y j = MacroExp.ctr d r z j := by
          rw [hcy]; simp [Pi.single_eq_of_ne hj]
        have h := htrans j hj
        rw [abs_le] at h
        rw [hcyj, min_self, max_self]
        unfold MacroExp.rad
        split_ifs <;> push_cast <;> omega
    · intro hQ
      rw [MacroExp.Q, MacroExp.mem_abox] at hQ
      have h := hQ i
      rw [rad_planar hi] at h
      have habs : |x i - MacroExp.ctr d r z i| ≤ 5 * (r : ℤ) := by rw [abs_le]; omega
      rw [habsi, abs_le] at habs
      omega

end Isotropic

/-! ## §7.1.  The `d` cross-section reductions -/

section CrossSection

variable {d : ℕ}

/-- The box `B_j` of §7.1: the first `j` coordinate half-widths are `hwv + j R`, the rest
`3 rv + j R`.  The `A` argument is the accumulated inflation `j R`, kept abstract so that all the
arithmetic below is linear. -/
def Bx (c : Site d) (hwv rv A : ℤ) (j : ℕ) : Finset (Site d) :=
  ibox c fun k => (if k.val < j then hwv else 3 * rv) + A

@[simp] theorem Bx_zero (c : Site d) (hwv rv A : ℤ) :
    Bx c hwv rv A 0 = cube c (3 * rv + A) := by
  ext x
  rw [Bx, mem_ibox_abs, mem_cube]
  exact forall_congr' fun k => by rw [if_neg (Nat.not_lt_zero _)]

theorem Bx_dim (c : Site d) (hwv rv A : ℤ) : Bx c hwv rv A d = cube c (hwv + A) := by
  ext x
  rw [Bx, mem_ibox_abs, mem_cube]
  exact forall_congr' fun k => by rw [if_pos k.isLt]

/-- **§7.1, (7.2)–(7.4).  One cross-section reduction is a quarter-face target.**  The `j+1`-st
coordinate is reduced from `3 rv + A` to `hwv + A + R`; every other half-width grows by the
inflation radius `R`.  All local cubes stay inside the central cube of radius `5 rv`. -/
theorem faceTarget_step (c : Site d) (hwv rv R A : ℤ) (j : ℕ) (q : Fin d) (hqj : q.val = j)
    (hR0 : 0 ≤ R) (hA0 : 0 ≤ A) (hA : A + 2 * R ≤ hwv - rv)
    (h2hw : 3 * rv ≤ 2 * hwv) (hwr : hwv + R ≤ 3 * rv) :
    FaceTarget R (cube c (5 * rv)) (Bx c hwv rv A j) (Bx c hwv rv (A + R) (j + 1)) := by
  classical
  show FaceTarget R (cube c (5 * rv))
    (ibox c fun k => (if k.val < j then hwv else 3 * rv) + A)
    (ibox c fun k => (if k.val < j + 1 then hwv else 3 * rv) + (A + R))
  refine faceTarget_ibox c R (5 * rv) hR0 q _ _ ?_ ?_ ?_ ?_ ?_
  · simp only [hqj]; split_ifs <;> omega
  · simp only [hqj]; split_ifs <;> omega
  · intro k hk
    have hkj : k.val ≠ j := fun hc => hk (Fin.ext (by rw [hqj]; exact hc))
    split_ifs <;> omega
  · intro k hk
    have hkj : k.val ≠ j := fun hc => hk (Fin.ext (by rw [hqj]; exact hc))
    simp only [hqj]; split_ifs <;> omega
  · intro k
    simp only [hqj]; split_ifs <;> omega

end CrossSection

/-! ## §7.  The corrected corridor move -/

section Move

variable {d : ℕ} [NeZero d]

/-- `h_r = r + ⌈r/2⌉` of §7.1. -/
def hw (r : ℕ) : ℕ := r + (r + 1) / 2

theorem three_mul_le_two_mul_hw (r : ℕ) : 3 * r ≤ 2 * hw r := by unfold hw; omega

theorem two_mul_hw_le (r : ℕ) : 2 * hw r ≤ 3 * r + 1 := by unfold hw; omega

/-- `100 (d+1) R < r` follows from the scale condition (0.3). -/
theorem scale_mul (d R r : ℕ) (hscale : 100 * (d + 1) * (R + 1) < r) :
    100 * ((d + 1) * R) < r := by
  calc 100 * ((d + 1) * R) = 100 * (d + 1) * R := by ring
    _ ≤ 100 * (d + 1) * (R + 1) := Nat.mul_le_mul_left _ (by omega)
    _ < r := hscale

/-- Every box of the cross-section chain lies in the central cube. -/
theorem Bx_subset_cube (c : Site d) {hwv rv A M : ℤ} (j : ℕ)
    (h1 : hwv + A ≤ M) (h2 : 3 * rv + A ≤ M) : Bx c hwv rv A j ⊆ cube c M := by
  intro x hx
  rw [Bx, mem_ibox_abs] at hx
  rw [mem_cube]
  intro k
  have h := hx k
  by_cases hlt : k.val < j
  · rw [if_pos hlt] at h; omega
  · rw [if_neg hlt] at h; omega

/-- The last box of the chain lies in the long box `D'`. -/
theorem cube_subset_dbox (c : Site d) {i : Fin d} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {s rv : ℤ}
    (h1 : s ≤ 2 * rv) : cube c s ⊆ dbox c i σ (-(2 * rv)) (22 * rv) (2 * rv) := by
  intro x hx
  rw [mem_cube] at hx
  rw [mem_dbox hσ]
  have hi := hx i
  have habs : |σ * (x i - c i)| ≤ s := by rw [abs_signed hσ]; exact hi
  rw [abs_le] at habs
  refine ⟨⟨by omega, by omega⟩, fun j _ => le_trans (hx j) (by omega)⟩

/-- **The `d+1` target-extension cascade of §7, run in an arbitrary allowed region.**

The corridor move touches the allowed region `Dom` only through the two site subboxes it actually
reads -- the head cube `c_z + Λ_{5r}` of the `d` cross-section reductions of §7.1 and the long box
`D'` of the final aspect-88 move of §7.2 -- and it produces the **isotropic core** `c_y + Λ_{2r}`
of the neighbouring macro-vertex.  Nothing else about `Dom` enters the cascade, so the six
geometric facts about `Dom` are hypotheses here rather than consequences of a containment
`E z y ⊆ Dom`.

`corridorMove` is the instance where `E w z ∪ E z y ⊆ Dom` supplies those six facts and the target
is then enlarged to `MacroExp.M ... y`.  `CorrMove.corridorMoveNarrow`, in `KN/CorridorNarrow.lean`,
is the instance `Dom = h.inspected ∪ E w z ∪ Stopped.stub ...` with the target shrunk to
`Stopped.stubTarget`; that instance is available precisely because the cascade never uses
`E z y ⊆ Dom`. -/
theorem corridorMoveCore {r R : ℕ} {h : MacroExp.Tr d} {q : unitInterval}
    {z y : Site 2} {i : Fin d} {σ : ℤ} {ρ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ)
    (h44 : 44 ≤ r) (hR1 : 1 ≤ R) (hscale : 100 * (d + 1) * (R + 1) < r)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (Dom : Finset (Site d))
    (hfresh5 : Disjoint h.inspected (cube (MacroExp.ctr d r z) (5 * (r : ℤ))))
    (hfreshD : Disjoint h.inspected
      (dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ))))
    (hzero5 : (MacroExp.emb 0 : Site d) ∉ cube (MacroExp.ctr d r z) (5 * (r : ℤ)))
    (hzeroD : (MacroExp.emb 0 : Site d) ∉
      dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ)))
    (hdom5 : cube (MacroExp.ctr d r z) (5 * (r : ℤ)) ⊆ Dom)
    (hdomD : dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ)) ⊆ Dom)
    (hface : ∀ (Sub Bset Tset : Finset (Site d)) (ε : ℝ), 0 < ε → ε ≤ 1 →
      Disjoint h.inspected Sub → (MacroExp.emb 0 : Site d) ∉ Sub → Sub ⊆ Dom →
      FaceTarget (R : ℤ) Sub Bset Tset →
      1 - ε / 8 < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑Bset : Set (Site d))) →
      1 - ε < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑Tset : Set (Site d))))
    (hlong : ∀ (Sub Bset Tset : Finset (Site d)) (ε : ℝ), 0 < ε → ε ≤ 1 →
      Disjoint h.inspected Sub → (MacroExp.emb 0 : Site d) ∉ Sub → Sub ⊆ Dom →
      LongTarget (R : ℤ) i σ Sub Bset Tset →
      1 - ε / 8 < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑Bset : Set (Site d))) →
      1 - ε < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑Tset : Set (Site d))))
    (hsrc : 1 - beta ρ d < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
        (↑(cube (MacroExp.ctr d r z) (3 * (r : ℤ))) : Set (Site d)))) :
    1 - ρ / 32 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
        (↑(cube (MacroExp.ctr d r y) (2 * (r : ℤ))) : Set (Site d))) := by
  classical
  set c : Site d := MacroExp.ctr d r z with hc
  set rv : ℤ := (r : ℤ) with hrv
  set hwv : ℤ := (hw r : ℤ) with hhwv
  set Rv : ℤ := (R : ℤ) with hRv
  set P : ℤ := (((d + 1) * R : ℕ) : ℤ) with hPdef
  -- numerical facts (0.3)
  have hPn : 100 * ((d + 1) * R) < r := scale_mul d R r hscale
  have hP : 100 * P < rv := by rw [hPdef, hrv]; exact_mod_cast hPn
  have hP0 : (0 : ℤ) ≤ P := by rw [hPdef]; positivity
  have hRP : Rv ≤ P := by
    rw [hRv, hPdef]
    exact_mod_cast Nat.le_mul_of_pos_left R (by omega)
  have hr44 : (44 : ℤ) ≤ rv := by rw [hrv]; exact_mod_cast h44
  have hR1' : (1 : ℤ) ≤ Rv := by rw [hRv]; exact_mod_cast hR1
  have hhw1 : 3 * rv ≤ 2 * hwv := by
    rw [hrv, hhwv]; exact_mod_cast three_mul_le_two_mul_hw r
  have hhw2 : 2 * hwv ≤ 3 * rv + 1 := by
    rw [hrv, hhwv]; exact_mod_cast two_mul_hw_le r
  have hwr : hwv + Rv ≤ 3 * rv := by omega
  set cy : Site d := c + Pi.single i (σ * (20 * rv)) with hcy
  set Tg : ℕ → Finset (Site d) := fun j =>
    if j ≤ d then Bx c hwv rv ((j : ℤ) * Rv) j else cube cy (2 * rv) with hTg
  have hα0 : 0 < ρ / 32 := by linarith
  have hα1 : ρ / 32 ≤ 1 := by linarith
  -- the cascade
  have hbnd : ∀ j, j ≤ d + 1 →
      0 ≤ casc (ρ / 32) (d + 1 - j) ∧ casc (ρ / 32) (d + 1 - j) ≤ 1 := fun j _ =>
    ⟨(casc_pos hα0 _).le, casc_le_one hα0 hα1 _⟩
  have hrec : ∀ j, j < d + 1 →
      casc (ρ / 32) (d + 1 - j) = f (casc (ρ / 32) (d + 1 - (j + 1))) := fun j hj =>
    casc_rec (ρ / 32) (d + 1) hj
  have hsrc' : 1 - casc (ρ / 32) (d + 1 - 0) < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) (↑(Tg 0) : Set (Site d))) := by
    have hT0 : Tg 0 = cube c (3 * rv) := by
      simp only [hTg, if_pos (Nat.zero_le d), Nat.cast_zero, zero_mul, Bx_zero, add_zero]
    rw [hT0, Nat.sub_zero]
    rw [hc, hrv]
    exact hsrc
  have hstep : ∀ j, j < d + 1 →
      1 - casc (ρ / 32) (d + 1 - (j + 1)) / 8 < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑(Tg j) : Set (Site d))) →
      1 - casc (ρ / 32) (d + 1 - (j + 1)) < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑(Tg (j + 1)) : Set (Site d))) := by
    intro j hj hin
    have hε0 : 0 < casc (ρ / 32) (d + 1 - (j + 1)) := casc_pos hα0 _
    have hε1 : casc (ρ / 32) (d + 1 - (j + 1)) ≤ 1 := casc_le_one hα0 hα1 _
    rcases Nat.lt_or_ge j d with hjd | hjd
    · -- one of the `d` cross-section reductions (§7.1)
      have hcast : ((j + 1 : ℕ) : ℤ) * Rv = (j : ℤ) * Rv + Rv := by push_cast; ring
      have hTj1 : Tg (j + 1) = Bx c hwv rv ((j : ℤ) * Rv + Rv) (j + 1) := by
        simp only [hTg, if_pos (by omega : j + 1 ≤ d), hcast]
      have hA0 : (0 : ℤ) ≤ (j : ℤ) * Rv := by rw [hRv]; positivity
      have hjP : (j : ℤ) * Rv + 2 * Rv ≤ P := by
        rw [hPdef, hRv]
        have hmul : (j + 2) * R ≤ (d + 1) * R := Nat.mul_le_mul_right R (by omega)
        have hcast2 : ((j : ℤ)) * (R : ℤ) + 2 * (R : ℤ) = (((j + 2) * R : ℕ) : ℤ) := by
          push_cast; ring
        rw [hcast2]
        exact_mod_cast hmul
      have hft := faceTarget_step c hwv rv Rv ((j : ℤ) * Rv) j ⟨j, hjd⟩ rfl
        (by omega) hA0 (by omega) hhw1 hwr
      rw [hTj1]
      refine hface (cube c (5 * rv)) _ _ _ hε0 hε1 hfresh5 hzero5 hdom5 hft ?_
      have hTj : Tg j = Bx c hwv rv ((j : ℤ) * Rv) j := by
        simp only [hTg, if_pos (by omega : j ≤ d)]
      rw [← hTj]
      exact hin
    · -- the final aspect-88 long move (§7.2)
      have hjd' : j = d := by omega
      have hTj : Tg j = cube c (hwv + (d : ℤ) * Rv) := by
        simp only [hTg, if_pos (by omega : j ≤ d)]
        rw [hjd', Bx_dim]
      have hTj1 : Tg (j + 1) = cube cy (2 * rv) := by
        simp only [hTg, if_neg (by omega : ¬ j + 1 ≤ d)]
      have hjP : (d : ℤ) * Rv + Rv ≤ P := by
        rw [hPdef, hRv]
        exact le_of_eq (by push_cast; ring)
      have hdR0 : (0 : ℤ) ≤ (d : ℤ) * Rv := by rw [hRv]; positivity
      have h89 : 89 * ((hwv + (d : ℤ) * Rv) + Rv) ≤ 156 * rv := by omega
      have hRr : 88 * Rv + 88 ≤ 20 * rv - ((hwv + (d : ℤ) * Rv) + Rv) := by omega
      have hlt := longTarget_cube c i σ hσ Rv (hwv + (d : ℤ) * Rv) rv hR1' hr44 h89 hRr
      rw [hTj1]
      refine hlong (dbox c i σ (-(2 * rv)) (22 * rv) (2 * rv)) _ _ _ hε0 hε1
        hfreshD hzeroD hdomD hlt ?_
      rw [← hTj]
      exact hin
  have hfin := cascade_of_step (J := d + 1) (a := fun j => casc (ρ / 32) (d + 1 - j))
    (P := fun j => h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
        (↑(Tg j) : Set (Site d))))
    hbnd hrec hsrc' hstep
  simp only [Nat.sub_self, casc_zero] at hfin
  have hTend : Tg (d + 1) = cube cy (2 * rv) := by
    simp only [hTg, if_neg (by omega : ¬ d + 1 ≤ d)]
  rw [hTend] at hfin
  -- the isotropic core at `y` is the centred cube of the neighbouring macro-vertex
  have hcyeq : cy = MacroExp.ctr d r y := by
    rw [hcy, hc, hrv]
    exact (ctr_add_dir r hemb).symm
  rw [hcyeq] at hfin
  exact hfin

/-- **The corrected corridor move (0.4)/(0.8).**

Hypotheses, exactly those of §0 and §7.3.

* the direction `(i, σ)` is the macro-edge `z → y`, and `w ≠ z` is the incoming predecessor;
* the scale is large: `44 ≤ r`, `1 ≤ R` and `100 (d+1) (R+1) < r` (0.3);
* the slab is thick enough for the isotropic manuscript cubes: `5 r ≤ t` (§8.3);
* **the whole site subbox of the move is fresh**: `h.inspected` misses `Q z ∪ E z y`, so the
  *current central box*, not only the outgoing corridor, carries the unconditioned parameter.
  This is what the counterexample `naive_corridorMove_false` shows cannot be dropped;
* the origin lies outside that subbox;
* `hface` and `hlong` are the `d+1` calls of manuscript Lemma 7.3, restricted to a fresh subbox
  inside the allowed region and to the two target relations §7.1 and §7.2 verify;
* the incoming reservation is at the corrected error `beta ρ d` of (0.1), and its target is the
  **isotropic core** `c_z + Λ_{3r}`.

Conclusion: the outgoing connection to `M y` inside the allowed region fails with probability at
most `ρ/32`. -/
theorem corridorMove (hd : 2 ≤ d) {r t R : ℕ} {h : MacroExp.Tr d} {q : unitInterval}
    {w z y : Site 2} {i : Fin d} {σ : ℤ} {ρ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i σ)
    (h44 : 44 ≤ r) (hR1 : 1 ≤ R) (hscale : 100 * (d + 1) * (R + 1) < r) (ht : 5 * r ≤ t)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hwz : w ≠ z)
    (hfresh : Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y))
    (hzero : (MacroExp.emb 0 : Site d) ∉ MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (Dom : Finset (Site d))
    (hQDom : MacroExp.E d r t w z ⊆ Dom) (hEDom : MacroExp.E d r t z y ⊆ Dom)
    (hface : ∀ (Sub Bset Tset : Finset (Site d)) (ε : ℝ), 0 < ε → ε ≤ 1 →
      Disjoint h.inspected Sub → (MacroExp.emb 0 : Site d) ∉ Sub → Sub ⊆ Dom →
      FaceTarget (R : ℤ) Sub Bset Tset →
      1 - ε / 8 < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑Bset : Set (Site d))) →
      1 - ε < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑Tset : Set (Site d))))
    (hlong : ∀ (Sub Bset Tset : Finset (Site d)) (ε : ℝ), 0 < ε → ε ≤ 1 →
      Disjoint h.inspected Sub → (MacroExp.emb 0 : Site d) ∉ Sub → Sub ⊆ Dom →
      LongTarget (R : ℤ) i σ Sub Bset Tset →
      1 - ε / 8 < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑Bset : Set (Site d))) →
      1 - ε < h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
          (↑Tset : Set (Site d))))
    (hsrc : 1 - beta ρ d < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
        (↑(cube (MacroExp.ctr d r z) (3 * (r : ℤ))) : Set (Site d)))) :
    1 - ρ / 32 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0)
        (↑(MacroExp.M d r t y) : Set (Site d))) := by
  classical
  -- the two site subboxes of the move lie in the fresh subbox `Q z ∪ E z y`
  have hcube5 : cube (MacroExp.ctr d r z) (5 * (r : ℤ)) ⊆
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y :=
    le_trans (cube_subset_Q ht z) Finset.subset_union_left
  have hdb : dbox (MacroExp.ctr d r z) i σ (-(2 * (r : ℤ))) (22 * (r : ℤ)) (2 * (r : ℤ)) ⊆
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y :=
    dbox_subset_Q_union_E (by omega) ht hσ hemb
  have hQE : MacroExp.Q d r t z ∪ MacroExp.E d r t z y ⊆ Dom :=
    Finset.union_subset (le_trans (Q_subset_E hd r t (by omega) hwz) hQDom) hEDom
  have hfin := corridorMoveCore hσ hemb h44 hR1 hscale hρ0 hρ1 Dom
    (hfresh.mono_right hcube5) (hfresh.mono_right hdb)
    (fun hcon => hzero (hcube5 hcon)) (fun hcon => hzero (hdb hcon))
    (le_trans hcube5 hQE) (le_trans hdb hQE) hface hlong hsrc
  -- from the isotropic core at `y` to the anisotropic target box
  have h5t : 5 * (r : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
  have hrv0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
  have hsub : (↑(cube (MacroExp.ctr d r y) (2 * (r : ℤ))) : Set (Site d)) ⊆
      (↑(MacroExp.M d r t y) : Set (Site d)) := by
    intro x hx
    rw [Finset.mem_coe, mem_cube] at hx
    rw [Finset.mem_coe, MacroExp.M, MacroExp.mem_abox]
    intro j
    have hj := hx j
    rw [abs_le] at hj
    unfold MacroExp.rad
    split_ifs <;> push_cast <;> omega
  refine lt_of_lt_of_le hfin (ProbInv.prob_mono h _ ?_)
  intro ω hω
  rw [mem_connWithinSet_iff] at hω ⊢
  obtain ⟨b, hb, hconn⟩ := hω
  exact ⟨b, hsub hb, hconn⟩

end Move

/-! ## §10.  The three failed design patterns, checked against the corrected move -/

section Regression

variable {d : ℕ}

/-- **§10.1–10.2.  No target is a designated site and none is empty.**  A quarter-face contains the
axial site of its cube, so the relay is chosen from a whole face, never from one predesignated
unread vertex. -/
theorem qface_nonempty (v : Site d) {l : ℤ} (hl : 0 ≤ l) (i : Fin d) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (τ : Fin d → ℤ) : (qface v l i σ τ).Nonempty := by
  refine ⟨v + Pi.single i (σ * l), ?_⟩
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
  rw [mem_qface]
  refine ⟨fun j => ?_, ?_, fun j hj => ?_⟩
  · by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.single_eq_same, add_sub_cancel_left]
      rw [abs_signed hσ, abs_of_nonneg hl]
    · simp [Pi.single_eq_of_ne hj, hl]
  · simp only [Pi.add_apply, Pi.single_eq_same, add_sub_cancel_left]
    rw [← mul_assoc, hσ2, one_mul]
  · simp [Pi.single_eq_of_ne hj]

/-- **§10.2.  The far face of a long box is not empty.** -/
theorem longFace_nonempty (v : Site d) {l : ℤ} (hl : 0 ≤ l) (i : Fin d) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) : (longFace v l i σ 88).Nonempty := by
  refine ⟨v + Pi.single i (σ * (88 * l)), ?_⟩
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> ring
  rw [mem_longFace hσ hl (by norm_num)]
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [Pi.add_apply, Pi.single_eq_same, add_sub_cancel_left]
    rw [← mul_assoc, hσ2, one_mul]
  · simp [Pi.single_eq_of_ne hj, hl]

/-- **§10.2.  Every box of the cross-section chain contains its centre.** -/
theorem Bx_nonempty (c : Site d) {hwv rv A : ℤ} (j : ℕ) (h1 : 0 ≤ hwv + A) (h2 : 0 ≤ 3 * rv + A) :
    (Bx c hwv rv A j).Nonempty := by
  refine ⟨c, ?_⟩
  rw [Bx, mem_ibox_abs]
  intro k
  by_cases hlt : k.val < j
  · rw [if_pos hlt]; simpa using h1
  · rw [if_neg hlt]; simpa using h2

/-- **§10.3.  The corridor-move estimate does not go stale.**  It is a cylinder on the allowed
region, so a later examination whose fresh set is disjoint from that region leaves it unchanged.
The disjointness is a hypothesis, never an appeal to monotonicity. -/
theorem prob_move_step_eq_of_disjoint [NeZero d] (h : MacroExp.Tr d) (q : unitInterval)
    (Dom : Finset (Site d)) (T : Set (Site d)) (zv : Site 2) (F : Finset (Site d)) (b : Bool)
    (ω : SiteConfig (Site d)) (hfresh : Disjoint F h.inspected)
    (hdisj : Disjoint (↑F : Set (Site d)) (↑Dom : Set (Site d))) :
    (h.step zv F b ω).prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) T)
      = h.prob (fun _ : Site d => q)
        (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) T) :=
  ProbInv.prob_step_eq_of_disjoint h _ zv F b ω hfresh
    (determinedBy_connWithinSet (zdGraph d) (↑Dom : Set (Site d)) (MacroExp.emb 0) T) hdisj

end Regression

/-! ## §8.  What the certificate must record, and how it discharges `hface` and `hlong`

The hypotheses `hface` and `hlong` of `corridorMove` are manuscript Lemma 7.3 in the fresh site
subbox of the move.  In the Lean tree that lemma is `TargetExt.targetExtension_eps`, which consumes
a family `lv : ℕ → TargetExt.LevelGeometry (zdGraph d) Dom o T` whose `Gx` fields are the derived
shell-window events (4.1) and whose `prob` clause is (8.6).  `prob_of_targetExtension` below is the
reduction: **given** such a family for the boxes of §7, the pinned-law implication follows.  Its
`hG` hypothesis is exactly the family of new certificate clauses (8.4).  Nothing in this module
constructs those events; §8.1 shows the recorded FACE and COALESCENCE cylinders do not imply them,
and `ShellWindowBuild.candidate_contains_no_open_relay` machine-checks that obstruction. -/

section Pinned

variable {ι : Type*}

/-- A cylinder is the intersection of an all-open event and an all-closed event. -/
theorem cyl_eq_inter (F : Finset ι) (ξ : Set ι) [DecidablePred (· ∈ ξ)] :
    localCylinder (↑F : Set ι) ξ =
      {ω : Set ι | (↑(F.filter (· ∈ ξ)) : Set ι) ⊆ ω} ∩
        {ω : Set ι | ∀ i ∈ F.filter (fun i => i ∉ ξ), i ∉ ω} := by
  ext ω
  simp only [localCylinder, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.coe_filter,
    Set.subset_def, Finset.mem_filter, Finset.mem_coe]
  constructor
  · intro h
    exact ⟨fun i hi => (h i (Finset.mem_coe.2 hi.1)).2 hi.2,
      fun i hi hiω => hi.2 ((h i (Finset.mem_coe.2 hi.1)).1 hiω)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases hiξ : i ∈ ξ
    · exact ⟨fun _ => hiξ, fun _ => h1 i ⟨hi, hiξ⟩⟩
    · exact ⟨fun hiω => absurd hiω (h2 i ⟨hi, hiξ⟩), fun hc => absurd hc hiξ⟩

/-- The all-closed event is determined by its finite set of coordinates. -/
theorem determinedBy_allClosed (N : Finset ι) :
    DeterminedBy {ω : Set ι | ∀ i ∈ N, i ∉ ω} (↑N : Set ι) := by
  rw [determinedBy_iff]
  intro ω ω' hagree
  have h := TargetExt.forall_iff_of_inter_eq hagree
  simp only [Set.mem_setOf_eq]
  exact forall₂_congr fun i hi => not_congr (h i (Finset.mem_coe.2 hi))

/-- **Every pattern of a finite set has positive probability** strictly inside the unit interval. -/
theorem pos_real_cyl (q : unitInterval) (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (F : Finset ι) (ξ : Set ι) :
    0 < (prodBernoulli (fun _ : ι => q)).real (localCylinder (↑F : Set ι) ξ) := by
  classical
  have hdisj : Disjoint (F.filter (· ∈ ξ)) (F.filter (fun i => i ∉ ξ)) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    exact (Finset.mem_filter.1 hi').2 (Finset.mem_filter.1 hi).2
  have hAm : MeasurableSet {ω : Set ι | (↑(F.filter (· ∈ ξ)) : Set ι) ⊆ ω} :=
    (KNAll.Site.determinedBy_allOpen (↑(F.filter (· ∈ ξ)) : Set ι)).measurableSet_of_finset
  have hBm : MeasurableSet {ω : Set ι | ∀ i ∈ F.filter (fun i => i ∉ ξ), i ∉ ω} :=
    (determinedBy_allClosed (F.filter (fun i => i ∉ ξ))).measurableSet_of_finset
  rw [cyl_eq_inter F ξ,
    prodBernoulli_real_inter_of_determinedBy_disjoint _ hdisj
      (KNAll.Site.determinedBy_allOpen _) (determinedBy_allClosed _) hAm hBm,
    prodBernoulli_real_subset, prodBernoulli_real_forall_notMem]
  have h1 : 0 < ∏ _i ∈ F.filter (· ∈ ξ), (q : ℝ) := by
    rw [Finset.prod_const]; positivity
  have h2 : 0 < ∏ _i ∈ F.filter (fun i => i ∉ ξ), (1 - (q : ℝ)) := by
    rw [Finset.prod_const]
    exact pow_pos (by linarith) _
  exact mul_pos h1 h2

/-- **Pinning is a product law.** -/
theorem pinnedProb_eq_product (w : ι → unitInterval) (F : Finset ι) (ξ : Set ι)
    {A : Set (Set ι)} (hA : MeasurableSet A)
    (hpos : 0 < (prodBernoulli w).real (localCylinder (↑F : Set ι) ξ)) :
    pinnedProb w (↑F : Set ι) (fun i => i ∈ ξ) A
      = (prodBernoulli (pinW w (↑F : Set ι) ξ)).real A := by
  have h1 := TargetExt.real_inter_localCylinder_eq_mul_pinnedProb w F ξ hA
  have h2 := prodBernoulli_real_inter_localCylinder w F ξ hA
  rw [h1] at h2
  exact mul_left_cancel₀ (ne_of_gt hpos) h2

variable {κ V : Type*}

/-- The pinned law of a transcript at a constant parameter strictly inside the unit interval is the
product law with the recorded sites forced to their recorded states. -/
theorem prob_eq_product (h : FRDom.Transcript κ V) (q : unitInterval) (hq0 : 0 < (q : ℝ))
    (hq1 : (q : ℝ) < 1) {A : Set (Set κ)} (hA : MeasurableSet A) :
    h.prob (fun _ : κ => q) A
      = (prodBernoulli (pinW (fun _ : κ => q) (↑h.inspected : Set κ)
          (↑h.openSites : Set κ))).real A := by
  rw [FRDom.Transcript.prob_eq]
  have hval : pinnedProb (fun _ : κ => q) (↑h.inspected : Set κ) h.state A
      = pinnedProb (fun _ : κ => q) (↑h.inspected : Set κ)
          (fun i => i ∈ (↑h.openSites : Set κ)) A :=
    pinnedProb_congr_val _ _ (fun i _ => Iff.rfl) A
  rw [hval]
  exact pinnedProb_eq_product _ _ _ hA (pos_real_cyl q hq0 hq1 _ _)

end Pinned

section Bridge

variable {d : ℕ} [NeZero d]

/-- **The reduction of `hface`/`hlong` to the new certificate clauses.**  Given, for one call of the
corridor move, a level family whose boxes lie in the fresh site subbox `Sub`, `TargetExt`'s
`ε`–`ε/8` theorem holds verbatim under the pinned law of the transcript.  The freshness hypothesis
is used exactly once, to see that the pinned weights are the unconditioned parameter `q` on every
level box; the weights elsewhere are arbitrary, as §1 says.

`hG` is the clause family (8.4): for every level `i` and every contact `x` on the outer boundary of
the level box, the derived shell-window event `Gx i x` of (4.1) has probability at least
`1 - 3 (ε/8)²` at the extraction parameter.  With the corridor tolerances of §0 this is
`1 - 3 β²` at every stage, since `β ≤ a_j` for every `j`. -/
theorem prob_of_targetExtension {h : MacroExp.Tr d} {q : unitInterval}
    (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (Dom Sub : Finset (Site d)) (o : Site d) (T B : Set (Site d))
    (hfresh : Disjoint h.inspected Sub)
    {Δ : ℕ} (hdeg : ∀ x, (Dom.filter ((zdGraph d).Adj x)).card ≤ Δ)
    {L : ℕ} (hL : 0 < L)
    (lv : ℕ → TargetExt.LevelGeometry (zdGraph d) Dom o T)
    (hDsub : ∀ i, i < L → (lv i).D ⊆ Sub)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgate : ∀ i, i + 1 < L → ∀ x ∉ (lv i).D, ∀ y ∈ (lv i).D, (zdGraph d).Adj x y →
      y ∉ (lv (i + 1)).D)
    (hB : ∀ i < L, B ⊆ ↑(lv i).D) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ TargetExt.outerBoundary (zdGraph d) Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (lv i).D, ((lv i).J x).card ≤ s)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hLδ : 1 ≤ (L : ℝ) * (ε / 8) * (1 - (q : ℝ)) ^ (Δ * N))
    (hk : (1 - (q : ℝ) ^ s) ^ k ≤ ε / 8)
    (hG : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (lv i).D,
      1 - 3 * (ε / 8) ^ 2 ≤ (siteBernoulli (fun _ : Site d => q)).real ((lv i).Gx x))
    (hsrc : 1 - ε / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o B)) :
    1 - ε < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d)) o T) := by
  rw [prob_eq_product h q hq0 hq1 (measurableSet_connWithinSet (zdGraph d) Dom o T)]
  rw [prob_eq_product h q hq0 hq1 (measurableSet_connWithinSet (zdGraph d) Dom o B)] at hsrc
  refine TargetExt.targetExtension_eps (zdGraph d) Dom o T (Δ := Δ) ?_ hL lv hnest hgate hB q hq1
    _ ?_ N k s hsel_card hs hε0 hε1 hLδ hk hG hsrc
  · intro x
    rw [Finset.filter_congr_decidable]
    exact hdeg x
  · intro i hi y hy
    have hyI : y ∉ (↑h.inspected : Set (Site d)) := fun hc =>
      Finset.disjoint_left.1 hfresh (Finset.mem_coe.1 hc) (hDsub i hi hy)
    exact pinW_apply_of_not_mem _ _ hyI

end Bridge

/-! ## The call site -/

section CallSite

variable {d : ℕ} [NeZero d]

/-- **§7.3 item 2, assembled.**  The site subbox of the move, `Q z ∪ E z y`, is fresh as soon as
both corridors are.  At a good non-terminal transcript the incoming half is
`MacroExp.inspected_disjoint_pending_E` and the outgoing half is
`inspected_disjoint_pending_out_E`; `Q_subset_E` turns the first into freshness of the current
central box, which is the hypothesis `naive_corridorMove_false` shows cannot be dropped. -/
theorem fresh_subbox (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r) {h : MacroExp.Tr d} {w z y : Site 2}
    (hwz : w ≠ z) (hin : Disjoint h.inspected (MacroExp.E d r t w z))
    (hout : Disjoint h.inspected (MacroExp.E d r t z y)) :
    Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y) :=
  Finset.disjoint_union_right.2 ⟨hin.mono_right (Q_subset_E hd r t hr hwz), hout⟩

/-- **§0.  The retained invariant error must be far below `ρ/4`.**  The corridor move starts from
`beta ρ d`, which is at most `ρ/32`; a reservation kept only at error `ρ/4` cannot start the
cascade (3.8). -/
theorem beta_lt_quarter {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℕ) : beta ρ d < ρ / 4 :=
  lt_of_le_of_lt (beta_le hρ0 hρ1 d) (by linarith)

end CallSite

/-!
## The exact new certificate clauses (§8)

`corridorMove` is unconditional in the sense of `acceptance.py`: it takes no open proposition and
no `Nonempty` as a hypothesis.  What it does take, as the two explicitly written hypotheses
`hface` and `hlong`, is manuscript Lemma 7.3 in the fresh site subbox of the move.  Those are not
consequences of the certificate as it stands.  `prob_of_targetExtension` shows precisely what has
to be added, and `KN/Certificate2.lean` must record it.  **This module does not edit that file.**

Write `ρ = 1 - C.density`, `α = ρ/32`, `β = CorrMove.beta ρ d`, `χ = β²/4`.

1. `beta : ℝ` and `beta_eq : C.beta = (ρ/32)^(2^(d+1)) / 96^(2^(d+1)-1)`, together with
   `eps_le_beta : C.eps ≤ C.beta`.  The exploration must be run at `MacroExp.Good … C.beta`, not
   at `(1 - density)/4`; `beta_lt_quarter` is the gap.
2. `halfWidth_ge_five_corridor : 5 * C.corridor ≤ C.halfWidth`.  Without it the isotropic cubes
   `c_z + Λ_{3r}` and `c_z + Λ_{5r}` of (0.6) are not inside `MacroExp.M` and `MacroExp.Q`, whose
   transverse half-width is `t`, not `3r` and `5r`.  This is §8.3 option 1; the reservation target
   becomes the isotropic core `c_z + Λ_{3r}`, which is what `corridorMove` consumes.
3. `moveLocalRadius : ℕ` (the inflation radius `R` of §3), with `moveLocalRadius_ge : 1 ≤ R` and
   the scale clause `100 * (d+1) * (R+1) < C.corridor` of (0.3).
4. `moveLevelCount : ℕ`, `moveContacts`, `moveSeedSize`, `moveSeedCount` rebuilt at tolerance `β`
   by (3.6):  `(1 - q^{s})^{k} ≤ β/8` and `1 ≤ L * (β/8) * (1 - q)^{Δ N}`.
5. **The new cylinder family (8.4).**  For each of the four planar orientations `ν`, each of the
   `J = d+1` calls `j`, each level `ℓ < L_j` and each contact `x` on the outer vertex boundary of
   `D^{level}_{ν,j,ℓ} = (B^{src}_{ν,j})^{+(2M_j+2+ℓ)}`, a `CylinderExperiment` whose support is
   `S_{ν,j,ℓ,x} = (v + Λ_{M_j}) ∪ Q_γ(λ, v)` of (8.2) and whose event is the derived shell window
   `G = G^{coal} ∩ G^{face} ∩ G^{target}` of (4.1), recorded with threshold `1 - 3 β²`.
   In Lean these are the `Gx` fields of the `TargetExt.LevelGeometry` family that
   `prob_of_targetExtension` consumes, and its `hG` hypothesis is their probability clause.
   The `LevelGeometry.hrelay` field is the deterministic relay assertion of §4; the existing FACE
   and COALESCENCE entries do not imply it (`ShellWindowBuild.candidate_contains_no_open_relay`),
   so these are genuinely new entries and not a numerical strengthening of old ones.
6. Stability: extend `Certificate2.stable` by `|p - q| < 9 β² / (8 S_max)` of (8.9), where
   `S_max` is the largest support in item 5.
7. The 700 internal steps of §6 are used to prove item 5's threshold at extraction time; they are
   not separate entries.

Two further points recorded here rather than silently patched.

* The note's `P_h(0 ↔ M_y in I ∪ E_{w,z} ∪ E_{z,y})` is `MacroExp.reservationEvent` evaluated at
  the *accepted* transcript, whose inspected set is `h.inspected ∪ E w z`.  `corridorMove` proves
  the bound at the **pre-examination** transcript for the allowed set `Dom ⊇ E w z ∪ E z y`.
  Transporting it across the examination reads coordinates of `E w z`, which lie in the support of
  the estimate, so `ProbInv.prob_step_eq_of_disjoint` does **not** apply there; §9's interface
  qualification is real and the assembly must use the stopped filtration.
  `prob_move_step_eq_of_disjoint` is the case that does transfer.
* §1 recommends keeping `0 ∉ D` as an explicit hypothesis rather than deriving it, and
  `corridorMove` does so (`hzero`).  In the exploration it follows from `z ≠ 0` and `y ≠ 0`.

## Steps of the note not formalised here, and why

Three constructions of the note are extraction-time inputs, not parts of the move, and none of
them is used by `corridorMove`.  They are what item 5 above asks the certificate to record, and
they are stated here so that no reader takes them for proved.

* §5, the quarter-face hitting estimate.  Its proof is the square-root trick for the `d 2^d`
  orthant faces under Harris' inequality for decreasing events.  It is an unconditioned
  finite-cylinder statement about `siteBernoulli`, not about a transcript.
* §4, the derived shell window `G_x = G^{coal} ∩ G^{face} ∩ G^{target}` and its deterministic
  relay assertion.  In Lean this is the pair of fields `LevelGeometry.hrelay` and
  `LevelGeometry.hGdet`; `prob_of_targetExtension` consumes them and proves nothing about them.
* §6, the aspect-88 long-box hitting estimate built from exactly `8 * 88 - 4 = 700` nested
  quarter-face steps with the tolerances `b_t` of (6.2) and `ξ` of (6.4).  What is formalised is
  only the *geometry* of the final long move (`longTarget_cube`, which verifies (7.8)-(7.12)),
  never the estimate.

One interface mismatch, recorded rather than patched.  `Stopped.prob_directionEvent_compl_le`
in `KN/StoppedLevel.lean` consumes
`h.prob q (Stopped.corridorEvent d r t A h z i σ)ᶜ ≤ ρ/32`, whose allowed set is
`h.inspected ∪ Stopped.stub …` and whose transcript has already read `Q z`.  At that transcript
the corrected hypothesis `Disjoint h.inspected (Q z ∪ E z y)` is false, so `corridorMove` cannot be
applied there.  `corridorMove` proves the bound at the **pre-examination** transcript, for the
larger allowed set `Dom ⊇ E w z ∪ E z y`.  Passing from the one to the other shrinks the event and
changes the measure, and neither step is monotonicity: this is exactly the interface qualification
of §9, and it is the assembly's obligation, not the corridor move's.
-/

end KNAll.Site.CorrMove

end
