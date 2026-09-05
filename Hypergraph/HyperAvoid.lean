import Hypergraph.HyperUpper
import Percolation.Literature.ConditionalPositiveAssociationProofs

/-!
# The avoidance functional

The correlation inequalities behind the gluing theorem are stated in terms of the expectation of a
function of the cluster of a source, restricted to the event that the cluster avoids a set of
vertices.  This module introduces that functional and proves the elementary facts every later
inequality uses.

* `avoidEvent` — the event that the cluster of `S` avoids `X`;
* `isLowerSet_avoidEvent` — opening more labels only grows the cluster, so avoidance is decreasing;
* `avoidEvent_antitone` — avoiding a larger set is harder;
* `measurableSet_avoidEvent` — over a finite label type every event is measurable, being determined
  by the finite set of all labels;
* `avoidIntegral` — the expectation of `f` at the cluster on the avoidance event;
* `avoidIntegral_mono`, `avoidIntegral_one` — its monotonicity in the integrand, and its value at
  the constant one.

The last section proves the disjoint case of the one-cluster inequality: for increasing nonnegative
`f` and `g`,

  `avoidIntegral X f · avoidIntegral Y g ≤ avoidIntegral ∅ (f · g) · P(avoidEvent (X ∪ Y))`.

This is the case `X ∩ Y = ∅` of van den Berg–Häggström–Kahn's Theorem 1.1, which those authors
dispose of by "two applications of the Harris–FKG inequality" (their display (4)), and the proof
here is exactly that: Harris for an increasing function against a decreasing indicator bounds each
factor on the left by `E[f(C)] P(avoid X)` and `E[g(C)] P(avoid Y)`, Harris for two increasing
functions turns `E[f(C)] E[g(C)]` into `E[f(C) g(C)]`, and Harris for two decreasing functions
turns `P(avoid X) P(avoid Y)` into `P(avoid X ∪ Y)`.  Disjointness of `X` and `Y` is not used.

The finite-sum apparatus is the one built for that theorem in
`Percolation/Literature/ConditionalPositiveAssociationProofs.lean`: `BHK2006.weight`, the three
Harris inequalities `BHK2006.harris`, `BHK2006.harris_mono_anti`, `BHK2006.harris_anti_anti`, and
the identification `BHK2006.integral_prodBernoulli_eq_sum` of an integral against `prodBernoulli`
over a finite label type with the finite weighted sum.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006), Thm. 1.1.
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## The avoidance event -/

/-- The event that the cluster of `S` avoids `X`. -/
def avoidEvent (H : Hypergraph V E) (S X : Set V) : Set (Set E) :=
  {ω | Disjoint (hyperClusterSet H ω S) X}

/-- The expectation of `f` at the cluster of `S`, on the event that the cluster avoids `X`. -/
noncomputable def avoidIntegral (H : Hypergraph V E) (S X : Set V) (f : Set V → ℝ) : ℝ :=
  ∫ ω in avoidEvent H S X, f (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)

@[simp] theorem mem_avoidEvent (H : Hypergraph V E) (S X : Set V) (ω : Set E) :
    ω ∈ avoidEvent H S X ↔ Disjoint (hyperClusterSet H ω S) X := Iff.rfl

/-- **Target 1.**  Opening more labels only grows the cluster, so the avoidance event is a lower set
in the configuration order. -/
theorem isLowerSet_avoidEvent (H : Hypergraph V E) (S X : Set V) :
    IsLowerSet (avoidEvent H S X) := fun _ _ hsub hω =>
  Set.disjoint_of_subset_left (hyperClusterSet_mono H S hsub) hω

/-- **Target 2.**  Avoiding a larger set is harder. -/
theorem avoidEvent_antitone (H : Hypergraph V E) (S : Set V) :
    Antitone (avoidEvent H S) := fun _ _ hXY _ hω =>
  Set.disjoint_of_subset_right hXY hω

/-- Avoiding nothing is no condition. -/
theorem avoidEvent_empty (H : Hypergraph V E) (S : Set V) :
    avoidEvent H S ∅ = Set.univ :=
  Set.eq_univ_of_forall fun ω => Set.disjoint_empty (hyperClusterSet H ω S)

/-- Avoiding a union is avoiding each of the two sets. -/
theorem avoidEvent_union (H : Hypergraph V E) (S X Y : Set V) :
    avoidEvent H S (X ∪ Y) = avoidEvent H S X ∩ avoidEvent H S Y := by
  ext ω
  simp only [mem_avoidEvent, Set.mem_inter_iff, Set.disjoint_union_right]

/-! ## Measurability over a finite label type -/

/-- Over a finite label type every event is determined by the finite set of all labels, hence
measurable.  This is the route of `measurableSet_hyperConn`, isolated. -/
theorem measurableSet_of_fintype [Fintype E] (A : Set (Set E)) : MeasurableSet A := by
  classical
  have h : DeterminedBy A (↑(Finset.univ : Finset E)) := by
    rw [determinedBy_iff]
    intro ω ω' hω
    have hωω : ω = ω' := by simpa using hω
    rw [hωω]
  exact h.measurableSet_of_finset

/-- **Target 3.**  The avoidance event is measurable over a finite label type. -/
theorem measurableSet_avoidEvent [Fintype E] (H : Hypergraph V E) (S X : Set V) :
    MeasurableSet (avoidEvent H S X) :=
  measurableSet_of_fintype _

/-- Over a finite label type every real function of the configuration is integrable against a finite
measure: it is measurable because every set is, and bounded because there are finitely many
configurations. -/
theorem integrable_of_fintype [Fintype E] {μ : Measure (Set E)} [IsFiniteMeasure μ]
    (g : Set E → ℝ) : Integrable g μ := by
  have hmeas : Measurable g := fun _ _ => measurableSet_of_fintype _
  obtain ⟨C, hC⟩ := (Set.finite_range fun ω => ‖g ω‖).bddAbove
  exact Integrable.mono' (integrable_const C) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hC (Set.mem_range_self ω))

/-- The integrand of `avoidIntegral` is integrable, by finiteness of the label type. -/
theorem integrable_avoidIntegrand [Fintype E] (H : Hypergraph V E) (S X : Set V) (f : Set V → ℝ) :
    Integrable (fun ω => f (hyperClusterSet H ω S))
      ((prodBernoulli H.prob).restrict (avoidEvent H S X)) :=
  integrable_of_fintype _

/-! ## Elementary behaviour of the functional -/

/-- **Target 4.**  The functional is monotone in its integrand. -/
theorem avoidIntegral_mono (H : Hypergraph V E) [Fintype E] (S X : Set V) {f g : Set V → ℝ}
    (hfg : ∀ K, f K ≤ g K) : avoidIntegral H S X f ≤ avoidIntegral H S X g :=
  integral_mono (integrable_avoidIntegrand H S X f) (integrable_avoidIntegrand H S X g)
    fun _ => hfg _

/-- **Target 5.**  At the constant one the functional is the probability of the avoidance event. -/
theorem avoidIntegral_one (H : Hypergraph V E) [Fintype E] (S X : Set V) :
    avoidIntegral H S X (fun _ => 1)
      = (prodBernoulli H.prob).real (avoidEvent H S X) := by
  have h : avoidIntegral H S X (fun _ => 1)
      = ∫ _ω in avoidEvent H S X, (1 : ℝ) ∂(prodBernoulli H.prob) := rfl
  rw [h, setIntegral_const, smul_eq_mul, mul_one]

/-! ## The finite-sum form

Over a finite label type `prodBernoulli` is a finite weighted sum, and the three Harris inequalities
of `BHK2006` are available in that form.  These four lemmas translate the objects of this file into
it.
-/

/-- The total mass of the product weights is one. -/
theorem sum_weight_eq_one [Fintype E] (p : E → unitInterval) :
    ∑ ω : Set E, BHK2006.weight (fun e => (p e : ℝ)) ω = 1 := by
  have h := BHK2006.integral_prodBernoulli_eq_sum p fun _ => (1 : ℝ)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  exact h.symm

/-- The probability of an event as a finite weighted sum of its indicator. -/
theorem prodBernoulli_real_eq_sum [Fintype E] (p : E → unitInterval) (A : Set (Set E)) :
    (prodBernoulli p).real A
      = ∑ ω : Set E, BHK2006.weight (fun e => (p e : ℝ)) ω * DecisionTree.ind A ω := by
  rw [← integral_indicator_one (measurableSet_of_fintype A),
    BHK2006.integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [DecisionTree.indicator_eq_mul_ind]
  simp

/-- The avoidance functional as a finite weighted sum. -/
theorem avoidIntegral_eq_sum [Fintype E] (H : Hypergraph V E) (S X : Set V) (f : Set V → ℝ) :
    avoidIntegral H S X f
      = ∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
          (f (hyperClusterSet H ω S) * DecisionTree.ind (avoidEvent H S X) ω) := by
  have h : avoidIntegral H S X f
      = ∫ ω in avoidEvent H S X, f (hyperClusterSet H ω S) ∂(prodBernoulli H.prob) := rfl
  rw [h, ← integral_indicator (measurableSet_avoidEvent H S X),
    BHK2006.integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [DecisionTree.indicator_eq_mul_ind]

/-- The unrestricted expectation as a finite weighted sum. -/
theorem avoidIntegral_empty_eq_sum [Fintype E] (H : Hypergraph V E) (S : Set V) (f : Set V → ℝ) :
    avoidIntegral H S ∅ f
      = ∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
          f (hyperClusterSet H ω S) := by
  rw [avoidIntegral_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hmem : ω ∈ avoidEvent H S ∅ := Set.disjoint_empty (hyperClusterSet H ω S)
  rw [DecisionTree.ind_of_mem hmem, mul_one]

/-- The probability of avoiding a union as a finite weighted sum of the product of the two
indicators. -/
theorem real_avoidEvent_union_eq_sum [Fintype E] (H : Hypergraph V E) (S X Y : Set V) :
    (prodBernoulli H.prob).real (avoidEvent H S (X ∪ Y))
      = ∑ ω : Set E, BHK2006.weight (fun e => (H.prob e : ℝ)) ω *
          (DecisionTree.ind (avoidEvent H S X) ω * DecisionTree.ind (avoidEvent H S Y) ω) := by
  rw [prodBernoulli_real_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [avoidEvent_union H S X Y, BHK2006.ind_inter]

/-! ## The disjoint case of the one-cluster inequality -/

/-- The indicator of a decreasing event is a decreasing function. -/
theorem antitone_ind_of_isLowerSet {ι : Type*} {A : Set (Set ι)} (hA : IsLowerSet A) :
    Antitone fun ω : Set ι => DecisionTree.ind A ω := by
  intro a b hab
  show DecisionTree.ind A b ≤ DecisionTree.ind A a
  by_cases hb : b ∈ A
  · rw [DecisionTree.ind_of_mem hb, DecisionTree.ind_of_mem (hA hab hb)]
  · rw [DecisionTree.ind_of_not_mem hb]
    exact DecisionTree.ind_nonneg _ _

/-- **The two-Harris estimate.**  For increasing nonnegative `F, G` and decreasing events `A, B`
under a product weight,

  `E[F 1_A] E[G 1_B] ≤ E[F G] E[1_A 1_B]`.

Each factor on the left is bounded by `E[F] P(A)` resp. `E[G] P(B)` by Harris for an increasing
function against a decreasing one; then `E[F] E[G] ≤ E[F G]` by Harris for two increasing functions
and `P(A) P(B) ≤ E[1_A 1_B]` by Harris for two decreasing ones.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1, display (4)] -/
theorem sum_mul_le_of_harris {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω : Set ι, BHK2006.weight w ω = 1) {F G : Set ι → ℝ}
    (hF : Monotone F) (hG : Monotone G) (hF0 : ∀ ω, 0 ≤ F ω) (hG0 : ∀ ω, 0 ≤ G ω)
    {A B : Set (Set ι)} (hA : IsLowerSet A) (hB : IsLowerSet B) :
    (∑ ω : Set ι, BHK2006.weight w ω * (F ω * DecisionTree.ind A ω)) *
        ∑ ω : Set ι, BHK2006.weight w ω * (G ω * DecisionTree.ind B ω)
      ≤ (∑ ω : Set ι, BHK2006.weight w ω * (F ω * G ω)) *
          ∑ ω : Set ι, BHK2006.weight w ω *
            (DecisionTree.ind A ω * DecisionTree.ind B ω) := by
  have hantiA := antitone_ind_of_isLowerSet hA
  have hantiB := antitone_ind_of_isLowerSet hB
  have hFA := BHK2006.harris_mono_anti hw0 hw1 hm hF0 hF hantiA (BHK2006.ind_le_one A)
  have hGB := BHK2006.harris_mono_anti hw0 hw1 hm hG0 hG hantiB (BHK2006.ind_le_one B)
  have hFG := BHK2006.harris hw0 hw1 hF0 hG0 hF hG
  rw [hm, one_mul] at hFG
  have hAB := BHK2006.harris_anti_anti hw0 hw1 hm hantiA hantiB (BHK2006.ind_le_one A)
    (BHK2006.ind_le_one B)
  have nB : 0 ≤ ∑ ω : Set ι, BHK2006.weight w ω * (G ω * DecisionTree.ind B ω) :=
    BHK2006.sum_ind_nonneg hw0 hw1 hG0 B
  have nF : 0 ≤ ∑ ω : Set ι, BHK2006.weight w ω * F ω :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (BHK2006.weight_nonneg hw0 hw1 ω) (hF0 ω)
  have nIA : 0 ≤ ∑ ω : Set ι, BHK2006.weight w ω * DecisionTree.ind A ω :=
    Finset.sum_nonneg fun ω _ =>
      mul_nonneg (BHK2006.weight_nonneg hw0 hw1 ω) (DecisionTree.ind_nonneg A ω)
  have nIB : 0 ≤ ∑ ω : Set ι, BHK2006.weight w ω * DecisionTree.ind B ω :=
    Finset.sum_nonneg fun ω _ =>
      mul_nonneg (BHK2006.weight_nonneg hw0 hw1 ω) (DecisionTree.ind_nonneg B ω)
  have nFG : 0 ≤ ∑ ω : Set ι, BHK2006.weight w ω * (F ω * G ω) :=
    Finset.sum_nonneg fun ω _ =>
      mul_nonneg (BHK2006.weight_nonneg hw0 hw1 ω) (mul_nonneg (hF0 ω) (hG0 ω))
  calc (∑ ω : Set ι, BHK2006.weight w ω * (F ω * DecisionTree.ind A ω)) *
        ∑ ω : Set ι, BHK2006.weight w ω * (G ω * DecisionTree.ind B ω)
      ≤ ((∑ ω : Set ι, BHK2006.weight w ω * F ω) *
            ∑ ω : Set ι, BHK2006.weight w ω * DecisionTree.ind A ω) *
          ((∑ ω : Set ι, BHK2006.weight w ω * G ω) *
            ∑ ω : Set ι, BHK2006.weight w ω * DecisionTree.ind B ω) :=
        mul_le_mul hFA hGB nB (mul_nonneg nF nIA)
    _ = ((∑ ω : Set ι, BHK2006.weight w ω * F ω) *
            ∑ ω : Set ι, BHK2006.weight w ω * G ω) *
          ((∑ ω : Set ι, BHK2006.weight w ω * DecisionTree.ind A ω) *
            ∑ ω : Set ι, BHK2006.weight w ω * DecisionTree.ind B ω) := by ring
    _ ≤ (∑ ω : Set ι, BHK2006.weight w ω * (F ω * G ω)) *
          ∑ ω : Set ι, BHK2006.weight w ω *
            (DecisionTree.ind A ω * DecisionTree.ind B ω) :=
        mul_le_mul hFG hAB (mul_nonneg nIA nIB) nFG

/-- **The one-cluster inequality, disjoint case.**  For increasing nonnegative `f` and `g`,

  `avoidIntegral X f · avoidIntegral Y g ≤ avoidIntegral ∅ (f · g) · P(avoidEvent (X ∪ Y))`.

Disjointness of `X` and `Y` plays no role; what is used is that avoiding `X ∪ Y` is avoiding both.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1, display (4)] -/
theorem avoidIntegral_mul_le [Fintype E] (H : Hypergraph V E) (S X Y : Set V) {f g : Set V → ℝ}
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) :
    avoidIntegral H S X f * avoidIntegral H S Y g
      ≤ avoidIntegral H S ∅ (fun K => f K * g K) *
          (prodBernoulli H.prob).real (avoidEvent H S (X ∪ Y)) := by
  rw [avoidIntegral_eq_sum H S X f, avoidIntegral_eq_sum H S Y g,
    avoidIntegral_empty_eq_sum H S fun K => f K * g K, real_avoidEvent_union_eq_sum H S X Y]
  exact sum_mul_le_of_harris (w := fun e => (H.prob e : ℝ))
    (F := fun ω => f (hyperClusterSet H ω S)) (G := fun ω => g (hyperClusterSet H ω S))
    (A := avoidEvent H S X) (B := avoidEvent H S Y)
    (fun e => unitInterval.nonneg (H.prob e)) (fun e => unitInterval.le_one (H.prob e))
    (sum_weight_eq_one H.prob)
    (fun _ _ hab => hf (hyperClusterSet_mono H S hab))
    (fun _ _ hab => hg (hyperClusterSet_mono H S hab))
    (fun _ => hf0 _) (fun _ => hg0 _)
    (isLowerSet_avoidEvent H S X) (isLowerSet_avoidEvent H S Y)

/-- **Target 6**, as stated: the one-cluster inequality for disjoint `X` and `Y`.  The hypothesis
`Disjoint X Y` is carried because the statement asked for it; the inequality holds without it. -/
theorem avoidIntegral_mul_le_of_disjoint [Fintype E] (H : Hypergraph V E) (S X Y : Set V)
    (_hXY : Disjoint X Y) {f g : Set V → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) :
    avoidIntegral H S X f * avoidIntegral H S Y g
      ≤ avoidIntegral H S ∅ (fun K => f K * g K) *
          (prodBernoulli H.prob).real (avoidEvent H S (X ∪ Y)) :=
  avoidIntegral_mul_le H S X Y hf hg hf0 hg0

end KNAll.Site

end
