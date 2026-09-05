import Hypergraph.AdaptiveDomination

/-!
# Reaching a target: the interface an adaptive exploration hands to the geometry

`KN.walkProb_const_le` compares two laws on Boolean words: an adaptive one, in which the next
outcome is `true` with a history-dependent probability `q g`, and the constant one `q ≡ a`, which
is a sequence of independent Bernoulli(`a`) trials.  Under the single hypothesis `a ≤ q g`, valid
after every history, the adaptive law is at least as likely to land in an upward-closed event.

This file turns that comparison into the shape the percolation argument uses.  An exploration of a
finite graph examines one vertex at a time; which vertex is examined next may depend on everything
revealed so far, so a run of the exploration is exactly a word in `List Bool`, read left to right
in the order of examination.  The event "the explored cluster reaches the target" is then a
predicate on runs, and the only property of it that the comparison needs is upward closure:
turning a closed vertex into an open one cannot destroy a connection.  That is `MonoWord`.

Everything here stays at the level of words.  No graph, no lattice and no exploration order is
constructed: fixing an examination order is a separate step, and the point of this file is that the
domination does not depend on how that step is carried out.

## Main statements

* `walkProb_mono_event`, monotonicity of `walkProb` in the event, for any law with values in `[0,1]`;
* `walkProb_const_mono_param`, monotonicity of the constant law in its parameter;
* `walkProb_const_le_event`, the two comparisons combined;
* `reach_le_of_succ_ge`, `walkProb_const_le` read at the empty history;
* `Exploration`, an adaptive exploration with a uniform lower bound on its success probability;
* `Exploration.bernoulliReachProb_le`, the domination in that language;
* `Exploration.le_reachProb_of_le_bernoulli`, the corollary that transfers a bound valid for the
  Bernoulli law, uniformly in the number of steps, to the exploration.
-/

namespace KN

/-! ### Monotonicity in the event -/

/-- Enlarging the event can only raise the probability of landing in it.  Unlike the comparison of
two laws, this needs nothing of the event beyond the implication, and nothing of the law beyond its
values lying in `[0,1]`. -/
theorem walkProb_mono_event (q : List Bool → ℝ) (hq0 : ∀ g, 0 ≤ q g) (hq1 : ∀ g, q g ≤ 1)
    (A B : List Bool → Prop) (hAB : ∀ w, A w → B w) (n : ℕ) (h : List Bool) :
    walkProb q A n h ≤ walkProb q B n h := by
  induction n generalizing h with
  | zero =>
    rw [walkProb_zero, walkProb_zero]
    split_ifs with hAh hBh hBh
    · exact le_rfl
    · exact absurd (hAB h hAh) hBh
    · exact zero_le_one
    · exact le_rfl
  | succ n ih =>
    simp only [walkProb_succ]
    have hq0h : 0 ≤ q h := hq0 h
    have hq1h : (0 : ℝ) ≤ 1 - q h := by linarith [hq1 h]
    have ht := mul_le_mul_of_nonneg_left (ih (h ++ [true])) hq0h
    have hf := mul_le_mul_of_nonneg_left (ih (h ++ [false])) hq1h
    linarith

/-! ### Monotonicity in the parameter -/

/-- Raising the success probability of the constant law raises the probability of an upward-closed
event.  This is `walkProb_const_le` applied to the constant law of parameter `b`. -/
theorem walkProb_const_mono_param {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (A : List Bool → Prop) (hA : MonoWord A) (n : ℕ) (h : List Bool) :
    walkProb (fun _ => a) A n h ≤ walkProb (fun _ => b) A n h :=
  walkProb_const_le a ha0 (hab.trans hb1) (fun _ => b) (fun _ => hab) (fun _ => hb1) A hA n h

/-- The two comparisons at once: a smaller event under the constant law is beaten by a larger,
upward-closed event under any law that succeeds with probability at least `a`.  Only the larger
event has to be upward closed. -/
theorem walkProb_const_le_event (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (q : List Bool → ℝ) (hqa : ∀ g, a ≤ q g) (hq1 : ∀ g, q g ≤ 1)
    (A B : List Bool → Prop) (hAB : ∀ w, A w → B w) (hB : MonoWord B) (n : ℕ) (h : List Bool) :
    walkProb (fun _ => a) A n h ≤ walkProb q B n h :=
  (walkProb_mono_event (fun _ => a) (fun _ => ha0) (fun _ => ha1) A B hAB n h).trans
    (walkProb_const_le a ha0 ha1 q hqa hq1 B hB n h)

/-- The domination read at the empty history: the run of an exploration that starts knowing nothing
reaches an upward-closed target at least as often as a Bernoulli(`a`) sequence does. -/
theorem reach_le_of_succ_ge (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (q : List Bool → ℝ) (hqa : ∀ g, a ≤ q g) (hq1 : ∀ g, q g ≤ 1)
    (reaches : List Bool → Prop) (hmono : MonoWord reaches) (n : ℕ) :
    walkProb (fun _ => a) reaches n [] ≤ walkProb q reaches n [] :=
  walkProb_const_le a ha0 ha1 q hqa hq1 reaches hmono n []

/-! ### Building upward-closed events -/

theorem MonoWord.and {A B : List Bool → Prop} (hA : MonoWord A) (hB : MonoWord B) :
    MonoWord fun w => A w ∧ B w :=
  fun u v hlen hget hu => ⟨hA u v hlen hget hu.1, hB u v hlen hget hu.2⟩

theorem MonoWord.or {A B : List Bool → Prop} (hA : MonoWord A) (hB : MonoWord B) :
    MonoWord fun w => A w ∨ B w :=
  fun u v hlen hget hu => hu.imp (hA u v hlen hget) (hB u v hlen hget)

/-! ### The Bernoulli benchmark -/

/-- The probability that `n` independent Bernoulli(`a`) trials, read as a word, land in `reaches`.
This is the quantity a percolation estimate is expected to bound from below. -/
noncomputable def bernoulliReachProb (a : ℝ) (reaches : List Bool → Prop) (n : ℕ) : ℝ :=
  walkProb (fun _ => a) reaches n []

theorem bernoulliReachProb_mono {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (A : List Bool → Prop) (hA : MonoWord A) (n : ℕ) :
    bernoulliReachProb a A n ≤ bernoulliReachProb b A n :=
  walkProb_const_mono_param ha0 hab hb1 A hA n []

theorem bernoulliReachProb_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (A : List Bool → Prop)
    (n : ℕ) : 0 ≤ bernoulliReachProb a A n :=
  walkProb_nonneg _ (fun _ => ha0) (fun _ => ha1) A n []

theorem bernoulliReachProb_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (A : List Bool → Prop)
    (n : ℕ) : bernoulliReachProb a A n ≤ 1 :=
  walkProb_le_one _ (fun _ => ha0) (fun _ => ha1) A n []

/-! ### Adaptive explorations -/

/-- An adaptive exploration of a vertex set `V` whose conditional success probability is at least
`a` after every history.

`nextVertex g` is the vertex examined after the history `g`, and `succProb g` is the conditional
probability that this vertex is open given `g`.  Nothing constrains `nextVertex`; in particular the
domination below never reads it.  It is carried because a run of the exploration is a mere word in
`List Bool` only once the examination order has been fixed, and `nextVertex` is that order. -/
structure Exploration (V : Type*) (a : ℝ) where
  /-- The vertex examined after a given history. -/
  nextVertex : List Bool → V
  /-- The conditional probability that the examined vertex is open. -/
  succProb : List Bool → ℝ
  /-- The guaranteed success probability is a probability. -/
  a_nonneg : 0 ≤ a
  /-- The uniform lower bound, the only hypothesis the domination uses. -/
  le_succProb : ∀ g, a ≤ succProb g
  /-- The conditional success probabilities are probabilities. -/
  succProb_le_one : ∀ g, succProb g ≤ 1

namespace Exploration

variable {V : Type*} {a : ℝ}

theorem a_le_one (E : Exploration V a) : a ≤ 1 :=
  (E.le_succProb []).trans (E.succProb_le_one [])

theorem succProb_nonneg (E : Exploration V a) (g : List Bool) : 0 ≤ E.succProb g :=
  E.a_nonneg.trans (E.le_succProb g)

/-- The vertices examined along the run `w`, in the order they are examined: after the first `i`
outcomes the exploration examines `E.nextVertex (w.take i)`. -/
def trace (E : Exploration V a) (w : List Bool) : List V :=
  (List.range w.length).map fun i => E.nextVertex (w.take i)

@[simp] theorem length_trace (E : Exploration V a) (w : List Bool) :
    (E.trace w).length = w.length := by
  simp [trace]

/-- One further outcome examines one further vertex, and does not disturb the vertices already
examined: the exploration order is prefix-consistent. -/
theorem trace_append_singleton (E : Exploration V a) (w : List Bool) (b : Bool) :
    E.trace (w ++ [b]) = E.trace w ++ [E.nextVertex w] := by
  have key : (List.range w.length).map (fun i => E.nextVertex ((w ++ [b]).take i))
      = (List.range w.length).map (fun i => E.nextVertex (w.take i)) := by
    refine List.map_congr_left ?_
    intro i hi
    simp only [List.take_append_of_le_length (le_of_lt (List.mem_range.1 hi))]
  have hlen : (w ++ [b]).length = w.length + 1 := by simp
  unfold trace
  rw [hlen, List.range_succ, List.map_append, key]
  simp

/-- The probability that a run of `n` steps, started from the empty history, lands in `reaches`. -/
noncomputable def reachProb (E : Exploration V a) (reaches : List Bool → Prop) (n : ℕ) : ℝ :=
  walkProb E.succProb reaches n []

theorem reachProb_nonneg (E : Exploration V a) (reaches : List Bool → Prop) (n : ℕ) :
    0 ≤ E.reachProb reaches n :=
  walkProb_nonneg _ E.succProb_nonneg E.succProb_le_one reaches n []

theorem reachProb_le_one (E : Exploration V a) (reaches : List Bool → Prop) (n : ℕ) :
    E.reachProb reaches n ≤ 1 :=
  walkProb_le_one _ E.succProb_nonneg E.succProb_le_one reaches n []

theorem reachProb_mono_event (E : Exploration V a) (A B : List Bool → Prop)
    (hAB : ∀ w, A w → B w) (n : ℕ) : E.reachProb A n ≤ E.reachProb B n :=
  walkProb_mono_event E.succProb E.succProb_nonneg E.succProb_le_one A B hAB n []

/-- **The domination, in the language of explorations.**  If every examined vertex is open with
conditional probability at least `a`, whatever has been revealed before, and if the target
predicate is upward closed, then the exploration reaches the target at least as often as `n`
independent Bernoulli(`a`) trials do. -/
theorem bernoulliReachProb_le (E : Exploration V a) (reaches : List Bool → Prop)
    (hreaches : MonoWord reaches) (n : ℕ) :
    bernoulliReachProb a reaches n ≤ E.reachProb reaches n :=
  walkProb_const_le a E.a_nonneg E.a_le_one E.succProb E.le_succProb E.succProb_le_one
    reaches hreaches n []

/-- **The corollary the geometry uses.**  A lower bound `c` on the Bernoulli(`a`) probability of
reaching the target, valid for every number of steps, is inherited by the exploration. -/
theorem le_reachProb_of_le_bernoulli {c : ℝ} (E : Exploration V a) (reaches : List Bool → Prop)
    (hreaches : MonoWord reaches) (hc : ∀ n, c ≤ bernoulliReachProb a reaches n) (n : ℕ) :
    c ≤ E.reachProb reaches n :=
  (hc n).trans (E.bernoulliReachProb_le reaches hreaches n)

/-- An exploration guaranteeing success probability `b` also guarantees any smaller `a`. -/
def weaken {b : ℝ} (E : Exploration V b) (ha0 : 0 ≤ a) (hab : a ≤ b) : Exploration V a where
  nextVertex := E.nextVertex
  succProb := E.succProb
  a_nonneg := ha0
  le_succProb g := hab.trans (E.le_succProb g)
  succProb_le_one := E.succProb_le_one

@[simp] theorem reachProb_weaken {b : ℝ} (E : Exploration V b) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (reaches : List Bool → Prop) (n : ℕ) :
    (E.weaken ha0 hab).reachProb reaches n = E.reachProb reaches n := rfl

/-- The Bernoulli comparison at any parameter below the guarantee. -/
theorem bernoulliReachProb_le_of_le {b : ℝ} (E : Exploration V b) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (reaches : List Bool → Prop) (hreaches : MonoWord reaches) (n : ℕ) :
    bernoulliReachProb a reaches n ≤ E.reachProb reaches n :=
  (E.weaken ha0 hab).bernoulliReachProb_le reaches hreaches n

end Exploration

end KN
