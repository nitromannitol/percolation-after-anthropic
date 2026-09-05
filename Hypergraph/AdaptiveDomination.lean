import Mathlib.Data.List.Forall2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Adaptive exploration dominates independent Bernoulli trials

An adaptive exploration reveals one Boolean outcome at a time.  The history revealed so far is a
list of Booleans, read left to right in the order the outcomes were revealed, and after a history
`g` the next outcome is `true` with probability `q g`.  The single hypothesis on the exploration is
a uniform lower bound `a ≤ q g`, holding for every history: the conditional success probability is
never worse than `a`, however the exploration chooses to branch.

The main theorem `walkProb_const_le` says that under that hypothesis the exploration is at least as
likely to land in any upward-closed event as the constant process `q ≡ a`, which is an independent
sequence of Bernoulli(`a`) trials.

The proof is a double induction.  The auxiliary theorem `walkProb_const_mono` states that the
constant process is monotone in its history, and it is available at the constant parameter only:
for a general `q` the two continuations after `h ++ [false]` and `h ++ [true]` are driven by
unrelated values of `q`, so no such monotonicity holds.  That is why the induction step of the main
theorem first raises the branching weight from `a` to `q h`, using monotonicity of the constant
process to know the sign of the bracket it multiplies, and only afterwards compares the two
processes branch by branch.

## Main statements

* `walkProb`, the probability that a length-`n` continuation of a history lands in the event;
* `MonoWord`, upward closure of an event of Boolean words;
* `walkProb_nonneg` and `walkProb_le_one`, the elementary bounds;
* `walkProb_const_mono`, monotonicity of the constant process in its history;
* `walkProb_const_le`, the domination statement.
-/

namespace KN

open Classical in
/-- `walkProb q A n h` is the probability that the length-`n` continuation of the history `h`
lands in `A`, when after any history `g` the next outcome is `true` with probability `q g`. -/
noncomputable def walkProb (q : List Bool → ℝ) (A : List Bool → Prop) :
    ℕ → List Bool → ℝ
  | 0,     h => if A h then 1 else 0
  | n + 1, h => q h * walkProb q A n (h ++ [true]) + (1 - q h) * walkProb q A n (h ++ [false])

open Classical in
@[simp] theorem walkProb_zero (q : List Bool → ℝ) (A : List Bool → Prop) (h : List Bool) :
    walkProb q A 0 h = if A h then 1 else 0 := by
  simp only [walkProb]

theorem walkProb_succ (q : List Bool → ℝ) (A : List Bool → Prop) (n : ℕ) (h : List Bool) :
    walkProb q A (n + 1) h =
      q h * walkProb q A n (h ++ [true]) + (1 - q h) * walkProb q A n (h ++ [false]) := by
  simp only [walkProb]

/-- Upward closure: replacing `false` by `true` anywhere cannot leave `A`. -/
def MonoWord (A : List Bool → Prop) : Prop :=
  ∀ u v : List Bool, u.length = v.length →
    (∀ i, ∀ hu : i < u.length, ∀ hv : i < v.length, u.get ⟨i, hu⟩ = true → v.get ⟨i, hv⟩ = true) →
    A u → A v

/-- The coordinatewise order on Boolean words: `u` and `v` have the same length, and at every
position a `true` of `u` is matched by a `true` of `v`.  This is exactly the hypothesis of
`MonoWord`, packaged as a `List.Forall₂`, which is the form that behaves well under appending. -/
def WordLE (u v : List Bool) : Prop :=
  List.Forall₂ (fun x y => x = true → y = true) u v

theorem WordLE.refl (u : List Bool) : WordLE u u :=
  List.forall₂_same.2 fun _ _ hx => hx

theorem WordLE.append {u v s t : List Bool} (h₁ : WordLE u v) (h₂ : WordLE s t) :
    WordLE (u ++ s) (v ++ t) :=
  List.rel_append h₁ h₂

/-- Appending the same outcome to both words preserves the coordinatewise order. -/
theorem WordLE.snoc {u v : List Bool} (h : WordLE u v) (b : Bool) :
    WordLE (u ++ [b]) (v ++ [b]) :=
  h.append (WordLE.refl [b])

/-- Turning the last outcome from `false` into `true` moves up in the coordinatewise order. -/
theorem WordLE.snoc_false_true (u : List Bool) : WordLE (u ++ [false]) (u ++ [true]) := by
  refine (WordLE.refl u).append ?_
  exact List.Forall₂.cons (fun _ => rfl) List.Forall₂.nil

/-- `MonoWord` restated against `WordLE`.  The two hypotheses say the same thing:
`List.forall₂_iff_get` splits a `List.Forall₂` into the equality of lengths and the pointwise
condition that `MonoWord` asks for. -/
theorem MonoWord.of_wordLE {A : List Bool → Prop} (hA : MonoWord A) {u v : List Bool}
    (huv : WordLE u v) (hu : A u) : A v := by
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 huv
  exact hA u v hlen hget hu

/-- The walk probability is a probability. -/
theorem walkProb_mem_unitInterval (q : List Bool → ℝ) (hq0 : ∀ g, 0 ≤ q g) (hq1 : ∀ g, q g ≤ 1)
    (A : List Bool → Prop) (n : ℕ) (h : List Bool) :
    0 ≤ walkProb q A n h ∧ walkProb q A n h ≤ 1 := by
  induction n generalizing h with
  | zero =>
    rw [walkProb_zero]
    split_ifs with _hAh
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨le_rfl, zero_le_one⟩
  | succ n ih =>
    rw [walkProb_succ]
    obtain ⟨ht0, ht1⟩ := ih (h ++ [true])
    obtain ⟨hf0, hf1⟩ := ih (h ++ [false])
    have hq0h : 0 ≤ q h := hq0 h
    have hq1h : (0 : ℝ) ≤ 1 - q h := by linarith [hq1 h]
    have hp0 : 0 ≤ q h * walkProb q A n (h ++ [true]) := mul_nonneg hq0h ht0
    have hp1 : 0 ≤ (1 - q h) * walkProb q A n (h ++ [false]) := mul_nonneg hq1h hf0
    have hp2 : q h * walkProb q A n (h ++ [true]) ≤ q h * 1 :=
      mul_le_mul_of_nonneg_left ht1 hq0h
    have hp3 : (1 - q h) * walkProb q A n (h ++ [false]) ≤ (1 - q h) * 1 :=
      mul_le_mul_of_nonneg_left hf1 hq1h
    constructor
    · linarith
    · linarith

theorem walkProb_nonneg (q : List Bool → ℝ) (hq0 : ∀ g, 0 ≤ q g) (hq1 : ∀ g, q g ≤ 1)
    (A : List Bool → Prop) (n : ℕ) (h : List Bool) : 0 ≤ walkProb q A n h :=
  (walkProb_mem_unitInterval q hq0 hq1 A n h).1

theorem walkProb_le_one (q : List Bool → ℝ) (hq0 : ∀ g, 0 ≤ q g) (hq1 : ∀ g, q g ≤ 1)
    (A : List Bool → Prop) (n : ℕ) (h : List Bool) : walkProb q A n h ≤ 1 :=
  (walkProb_mem_unitInterval q hq0 hq1 A n h).2

/-- The constant process is monotone in its history: raising the revealed outcomes coordinatewise
can only raise the chance of landing in an upward-closed event.  The continuation law of the
constant process does not depend on the history, which is what lets this induction close, and the
same statement for a general `q` is false. -/
theorem walkProb_const_mono (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (A : List Bool → Prop) (hA : MonoWord A) (n : ℕ) :
    ∀ u v : List Bool, WordLE u v →
      walkProb (fun _ => a) A n u ≤ walkProb (fun _ => a) A n v := by
  induction n with
  | zero =>
    intro u v huv
    rw [walkProb_zero, walkProb_zero]
    split_ifs with hu hv hv
    · exact le_rfl
    · exact absurd (hA.of_wordLE huv hu) hv
    · exact zero_le_one
    · exact le_rfl
  | succ n ih =>
    intro u v huv
    simp only [walkProb_succ]
    have ht := ih (u ++ [true]) (v ++ [true]) (huv.snoc true)
    have hf := ih (u ++ [false]) (v ++ [false]) (huv.snoc false)
    have h1 : a * walkProb (fun _ => a) A n (u ++ [true])
        ≤ a * walkProb (fun _ => a) A n (v ++ [true]) := mul_le_mul_of_nonneg_left ht ha0
    have h2 : (1 - a) * walkProb (fun _ => a) A n (u ++ [false])
        ≤ (1 - a) * walkProb (fun _ => a) A n (v ++ [false]) :=
      mul_le_mul_of_nonneg_left hf (by linarith)
    linarith

/-- An adaptive exploration whose conditional success probability is everywhere at least `a`
dominates the independent Bernoulli(`a`) sequence on every upward-closed event. -/
theorem walkProb_const_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (q : List Bool → ℝ) (hqa : ∀ g, a ≤ q g) (hq1 : ∀ g, q g ≤ 1)
    (A : List Bool → Prop) (hA : MonoWord A) (n : ℕ) (h : List Bool) :
    walkProb (fun _ => a) A n h ≤ walkProb q A n h := by
  induction n generalizing h with
  | zero => rw [walkProb_zero, walkProb_zero]
  | succ n ih =>
    simp only [walkProb_succ]
    -- The bracket `W_a(h ++ [true]) - W_a(h ++ [false])` is nonnegative, so raising the weight it
    -- carries from `a` to `q h` can only help.
    have hbracket : walkProb (fun _ => a) A n (h ++ [false])
        ≤ walkProb (fun _ => a) A n (h ++ [true]) :=
      walkProb_const_mono a ha0 ha1 A hA n _ _ (WordLE.snoc_false_true h)
    have hq0h : 0 ≤ q h := le_trans ha0 (hqa h)
    have hq1h : (0 : ℝ) ≤ 1 - q h := by linarith [hq1 h]
    have hstep : a * (walkProb (fun _ => a) A n (h ++ [true])
          - walkProb (fun _ => a) A n (h ++ [false]))
        ≤ q h * (walkProb (fun _ => a) A n (h ++ [true])
          - walkProb (fun _ => a) A n (h ++ [false])) :=
      mul_le_mul_of_nonneg_right (hqa h) (by linarith)
    -- Now compare the two processes on each branch separately.
    have ht : q h * walkProb (fun _ => a) A n (h ++ [true])
        ≤ q h * walkProb q A n (h ++ [true]) :=
      mul_le_mul_of_nonneg_left (ih (h ++ [true])) hq0h
    have hf : (1 - q h) * walkProb (fun _ => a) A n (h ++ [false])
        ≤ (1 - q h) * walkProb q A n (h ++ [false]) :=
      mul_le_mul_of_nonneg_left (ih (h ++ [false])) hq1h
    linarith

end KN
