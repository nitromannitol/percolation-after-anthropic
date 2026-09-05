import Hypergraph.HyperImplA
import Hypergraph.HyperImplB

/-!
# Phase 1, target 5, and the Lipschitz estimate in the parameters

* `clusterFactorization` — the event that the cluster of `S` is exactly `K` is independent of
  every event determined by the labels avoiding `K`, and on the second factor the hypergraph with
  the labels meeting `K` closed gives the same probability.  The labels meeting `K` form a finite
  set because `E` is finite, so this is the independence of an event determined by a finite set of
  coordinates and an event determined by its complement, followed by the deletion lemma.
* `prodBernoulli_real_lipschitz` — for an event determined by a finite set `F` of coordinates the
  probability moves by at most `∑_{i ∈ F} |p i - q i|` when the parameters move from `p` to `q`.
  The proof changes one coordinate at a time.  For a single coordinate `a` the probability is
  affine in the parameter: splitting on the state of `a` writes it as
  `p a * P(B) + (1 - p a) * P(C)` with `B`, `C` determined by the other coordinates, so the two
  probabilities differ by `(p a - q a) (P(B) - P(C))`, which is at most `|p a - q a|` in absolute
  value.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Target 5: the cluster factorization -/

/-- **Target 5, the cluster factorization.**  The event that the cluster of `S` is exactly `K` is
independent of every event determined by the labels avoiding `K`, and on the second factor the
deleted hypergraph gives the same probability. -/
theorem clusterFactorization {V E : Type*} [Fintype E] (H : Hypergraph V E) (S K : Set V)
    {A : Set (Set E)} (hA : DeterminedBy A (labelsMeeting H K)ᶜ) (hAm : MeasurableSet A) :
    (prodBernoulli H.prob).real (clusterEvent H S K ∩ A) =
      (prodBernoulli H.prob).real (clusterEvent H S K) *
        (prodBernoulli (deleteHyper H K).prob).real A := by
  classical
  have hfin : (labelsMeeting H K).Finite := Set.toFinite _
  have hcoe : (↑hfin.toFinset : Set E) = labelsMeeting H K := hfin.coe_toFinset
  have hdet : DeterminedBy (clusterEvent H S K) (↑hfin.toFinset : Set E) := by
    rw [hcoe]; exact determinedBy_clusterEvent H S K
  have hAdet : DeterminedBy A (↑hfin.toFinset : Set E)ᶜ := by
    rw [hcoe]; exact hA
  rw [prodBernoulli_real_inter_of_determinedBy H.prob hfin.toFinset hdet hAdet
      (measurableSet_clusterEvent H S K) hAm,
    prodBernoulli_deleteHyper_real_eq H K hA]

/-! ## The Lipschitz estimate in the parameters -/

/-- **One coordinate.**  If `p` and `q` agree off the coordinate `a`, the probability of any
measurable event moves by at most `|p a - q a|`: splitting on the state of `a` shows that the
probability is affine in `p a` with slope of absolute value at most one. -/
private theorem prodBernoulli_real_abs_sub_le_single {ι : Type*} (p q : ι → unitInterval) (a : ι)
    (hpq : ∀ i, i ≠ a → p i = q i) {A : Set (Set ι)} (hAm : MeasurableSet A) :
    |(prodBernoulli p).real A - (prodBernoulli q).real A| ≤ |(p a : ℝ) - (q a : ℝ)| := by
  classical
  -- the two maps that read the event off a configuration with the state of `a` prescribed
  have hins : Measurable fun ω : Set ι => insert a ω := by
    rw [measurable_set_iff]
    intro i
    by_cases hi : i = a
    · subst hi
      have h : (fun ω : Set ι => i ∈ insert i ω) = fun _ => True := by
        funext ω; simp
      rw [h]; exact measurable_const
    · have h : (fun ω : Set ι => i ∈ insert a ω) = fun ω => i ∈ ω := by
        funext ω; simp [Set.mem_insert_iff, hi]
      rw [h]; exact measurable_set_mem i
  have hsd : Measurable fun ω : Set ι => ω \ {a} := by
    rw [measurable_set_iff]
    intro i
    by_cases hi : i = a
    · subst hi
      have h : (fun ω : Set ι => i ∈ ω \ {i}) = fun _ => False := by
        funext ω; simp
      rw [h]; exact measurable_const
    · have h : (fun ω : Set ι => i ∈ ω \ {a}) = fun ω => i ∈ ω := by
        funext ω; simp [hi]
      rw [h]; exact measurable_set_mem i
  obtain ⟨B, hB⟩ : ∃ B : Set (Set ι), B = {ω : Set ι | insert a ω ∈ A} := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Set (Set ι), C = {ω : Set ι | ω \ {a} ∈ A} := ⟨_, rfl⟩
  have hBm : MeasurableSet B := by rw [hB]; exact hins hAm
  have hCm : MeasurableSet C := by rw [hC]; exact hsd hAm
  -- the four events and the coordinate sets that determine them
  have hBdet : DeterminedBy B (↑({a} : Finset ι) : Set ι)ᶜ := by
    rw [Finset.coe_singleton, determinedBy_iff]
    intro ω ω' hω
    have key : ∀ i, i ≠ a → (i ∈ ω ↔ i ∈ ω') := by
      intro i hi
      have h := Set.ext_iff.1 hω i
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff] at h
      exact ⟨fun hiω => (h.1 ⟨hiω, hi⟩).1, fun hiω' => (h.2 ⟨hiω', hi⟩).1⟩
    have hins' : insert a ω = insert a ω' := by
      ext i
      by_cases hi : i = a
      · subst hi; simp
      · simp only [Set.mem_insert_iff, hi, false_or]
        exact key i hi
    simp only [hB, Set.mem_setOf_eq, hins']
  have hCdet : DeterminedBy C (↑({a} : Finset ι) : Set ι)ᶜ := by
    rw [Finset.coe_singleton, determinedBy_iff]
    intro ω ω' hω
    have h : ω \ {a} = ω' \ {a} := by
      rw [Set.sdiff_eq, Set.sdiff_eq]; exact hω
    simp only [hC, Set.mem_setOf_eq, h]
  have hmemdet : DeterminedBy {ω : Set ι | a ∈ ω} (↑({a} : Finset ι) : Set ι) := by
    rw [Finset.coe_singleton, determinedBy_iff]
    intro ω ω' hω
    constructor
    · intro h
      have hmem : a ∈ ω ∩ ({a} : Set ι) := ⟨h, rfl⟩
      rw [hω] at hmem
      exact hmem.1
    · intro h
      have hmem : a ∈ ω' ∩ ({a} : Set ι) := ⟨h, rfl⟩
      rw [← hω] at hmem
      exact hmem.1
  have hnotmemdet : DeterminedBy {ω : Set ι | a ∉ ω} (↑({a} : Finset ι) : Set ι) := by
    rw [Finset.coe_singleton, determinedBy_iff]
    intro ω ω' hω
    constructor
    · intro h h'
      exact h (by
        have hmem : a ∈ ω' ∩ ({a} : Set ι) := ⟨h', rfl⟩
        rw [← hω] at hmem
        exact hmem.1)
    · intro h h'
      exact h (by
        have hmem : a ∈ ω ∩ ({a} : Set ι) := ⟨h', rfl⟩
        rw [hω] at hmem
        exact hmem.1)
  -- the probability of `A` is affine in the parameter at `a`
  have hsplit : ∀ r : ι → unitInterval,
      (prodBernoulli r).real A
        = (r a : ℝ) * (prodBernoulli r).real B + (1 - (r a : ℝ)) * (prodBernoulli r).real C := by
    intro r
    have hAeq : A = ({ω : Set ι | a ∈ ω} ∩ B) ∪ ({ω : Set ι | a ∉ ω} ∩ C) := by
      ext ω
      by_cases h : a ∈ ω
      · simp [hB, hC, h, Set.insert_eq_self.2 h]
      · simp [hB, hC, h, Set.sdiff_singleton_eq_self h]
    have hdisj : Disjoint ({ω : Set ι | a ∈ ω} ∩ B) ({ω : Set ι | a ∉ ω} ∩ C) :=
      Set.disjoint_left.2 fun ω hω hω' => hω'.1 hω.1
    rw [hAeq, measureReal_union hdisj ((measurableSet_notMem a).inter hCm)
        (measure_ne_top _ _) (measure_ne_top _ _),
      prodBernoulli_real_inter_of_determinedBy r {a} hmemdet hBdet (measurableSet_mem a) hBm,
      prodBernoulli_real_inter_of_determinedBy r {a} hnotmemdet hCdet (measurableSet_notMem a) hCm,
      prodBernoulli_real_setOf_mem, prodBernoulli_real_setOf_notMem]
  -- the two conditional probabilities do not depend on the parameter at `a`
  have hoff : ∀ i ∈ (↑({a} : Finset ι) : Set ι)ᶜ, p i = q i := by
    intro i hi
    exact hpq i (by simpa using hi)
  have hBpq : (prodBernoulli p).real B = (prodBernoulli q).real B :=
    prodBernoulli_real_eq_of_determinedBy p q hoff hBdet hBm
  have hCpq : (prodBernoulli p).real C = (prodBernoulli q).real C :=
    prodBernoulli_real_eq_of_determinedBy p q hoff hCdet hCm
  rw [hsplit p, hsplit q, hBpq, hCpq]
  have hexp : (p a : ℝ) * (prodBernoulli q).real B + (1 - (p a : ℝ)) * (prodBernoulli q).real C
      - ((q a : ℝ) * (prodBernoulli q).real B + (1 - (q a : ℝ)) * (prodBernoulli q).real C)
      = ((p a : ℝ) - (q a : ℝ))
          * ((prodBernoulli q).real B - (prodBernoulli q).real C) := by ring
  rw [hexp, abs_mul]
  have hB0 : 0 ≤ (prodBernoulli q).real B := measureReal_nonneg
  have hB1 : (prodBernoulli q).real B ≤ 1 := measureReal_le_one
  have hC0 : 0 ≤ (prodBernoulli q).real C := measureReal_nonneg
  have hC1 : (prodBernoulli q).real C ≤ 1 := measureReal_le_one
  have hle : |(prodBernoulli q).real B - (prodBernoulli q).real C| ≤ 1 :=
    abs_le.2 ⟨by linarith, by linarith⟩
  calc |(p a : ℝ) - (q a : ℝ)| * |(prodBernoulli q).real B - (prodBernoulli q).real C|
      ≤ |(p a : ℝ) - (q a : ℝ)| * 1 := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ = |(p a : ℝ) - (q a : ℝ)| := mul_one _

/-- **The hybrid argument.**  If `p` and `q` agree off the finite set `G`, the probability of any
measurable event moves by at most `∑_{i ∈ G} |p i - q i|`: change the parameters at the coordinates
of `G` one at a time. -/
private theorem prodBernoulli_real_abs_sub_le_sum {ι : Type*} {A : Set (Set ι)}
    (hAm : MeasurableSet A) (G : Finset ι) :
    ∀ p q : ι → unitInterval, (∀ i, i ∉ G → p i = q i) →
      |(prodBernoulli p).real A - (prodBernoulli q).real A|
        ≤ ∑ i ∈ G, |(p i : ℝ) - (q i : ℝ)| := by
  classical
  induction G using Finset.induction_on with
  | empty =>
    intro p q h
    have hpq : p = q := funext fun i => h i (by simp)
    subst hpq
    simp
  | insert a s ha ih =>
    intro p q h
    obtain ⟨r, hr⟩ : ∃ r : ι → unitInterval, ∀ i, r i = if i = a then q a else p i :=
      ⟨_, fun _ => rfl⟩
    have hra : r a = q a := by rw [hr]; simp
    have hrne : ∀ i, i ≠ a → r i = p i := by
      intro i hi; rw [hr]; simp [hi]
    have h1 : |(prodBernoulli p).real A - (prodBernoulli r).real A| ≤ |(p a : ℝ) - (r a : ℝ)| :=
      prodBernoulli_real_abs_sub_le_single p r a (fun i hi => (hrne i hi).symm) hAm
    rw [hra] at h1
    have h2 : |(prodBernoulli r).real A - (prodBernoulli q).real A|
        ≤ ∑ i ∈ s, |(r i : ℝ) - (q i : ℝ)| := by
      refine ih r q fun i hi => ?_
      by_cases hia : i = a
      · subst hia; exact hra
      · rw [hrne i hia]
        exact h i (by simp [Finset.mem_insert, hia, hi])
    have hsum : ∑ i ∈ s, |(r i : ℝ) - (q i : ℝ)| = ∑ i ∈ s, |(p i : ℝ) - (q i : ℝ)| :=
      Finset.sum_congr rfl fun i hi => by
        rw [hrne i (by rintro rfl; exact ha hi)]
    rw [hsum] at h2
    calc |(prodBernoulli p).real A - (prodBernoulli q).real A|
        ≤ |(prodBernoulli p).real A - (prodBernoulli r).real A|
            + |(prodBernoulli r).real A - (prodBernoulli q).real A| := abs_sub_le _ _ _
      _ ≤ |(p a : ℝ) - (q a : ℝ)| + ∑ i ∈ s, |(p i : ℝ) - (q i : ℝ)| := add_le_add h1 h2
      _ = ∑ i ∈ insert a s, |(p i : ℝ) - (q i : ℝ)| :=
            (Finset.sum_insert (f := fun i => |(p i : ℝ) - (q i : ℝ)|) ha).symm

/-- **The Lipschitz estimate.**  An event determined by the finite set `F` of coordinates has
probabilities differing by at most `∑_{i ∈ F} |p i - q i|` under the two parameter families:
the coordinates outside `F` do not move the probability at all, and the coordinates of `F` are
changed one at a time. -/
theorem prodBernoulli_real_lipschitz {ι : Type*} (p q : ι → unitInterval) (F : Finset ι)
    {A : Set (Set ι)} (hA : DeterminedBy A (↑F : Set ι)) (hAm : MeasurableSet A) :
    |(prodBernoulli p).real A - (prodBernoulli q).real A| ≤ ∑ i ∈ F, |(p i : ℝ) - (q i : ℝ)| := by
  classical
  obtain ⟨p', hp'⟩ : ∃ p' : ι → unitInterval, ∀ i, p' i = if i ∈ F then p i else q i :=
    ⟨_, fun _ => rfl⟩
  have hpp' : (prodBernoulli p).real A = (prodBernoulli p').real A :=
    prodBernoulli_real_eq_of_determinedBy p p'
      (fun i hi => by rw [hp']; simp [Finset.mem_coe.1 hi]) hA hAm
  rw [hpp']
  refine le_trans (prodBernoulli_real_abs_sub_le_sum hAm F p' q fun i hi => ?_) (le_of_eq ?_)
  · rw [hp']; simp [hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [show p' i = p i by rw [hp']; simp [hi]]

end KNAll.Site

end
