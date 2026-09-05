import Hypergraph.SiteIntrinsicInputs
import Hypergraph.ReachCoupling
import Hypergraph.SiteFiniteEnergy
import Hypergraph.SiteSlabGeometry
import Hypergraph.SiteGluingSet

/-!
# Target extension without a gluing inequality

The gluing inequality `P(o ↔ b) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)` of Kozma and Nitzan is used in
the target-extension argument of the manuscript to pass from "the source reaches some reliable
relay" to "the source reaches the target".  This module proves the argument with the gluing
inequality replaced by a statement that holds for every product measure and needs no monotonicity:
if the events `I u` are all determined by one set of coordinates and the events `E u` by a disjoint
set, then

  `μ(⋃ u, I u ∩ E u) ≥ μ(⋃ u, I u) · min_u μ(E u)`.

The point is that the connection from the source to a relay `u` in the shell is decided by the
coordinates outside the interior box once the shell is pinned, and the connection from `u` to the
target inside the box `O` is decided by the interior coordinates; the two are supported on disjoint
coordinate sets, so the statement above applies and no monotone-event argument is needed.
-/

noncomputable section

namespace KNAll.Site.TargetExt

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## The decisive lemma -/

section Decisive

variable {ι κ : Type*}

/-- **The decisive lemma, abstract form.**  Let `μ` be a finite measure on configurations and let
the events `I u` (`u ∈ s`) all be determined by the coordinates in `R`.  Suppose every `E u` is
independent of every measurable event determined by `R`.  Then

`μ(⋃ u ∈ s, I u) · m ≤ μ(⋃ u ∈ s, I u ∩ E u)` whenever `m ≤ μ(E u)` for all `u ∈ s`.

Proof: peel one index at a time.  With `J = ⋃_{u ∈ s} I u`, the set `I a \ J` is determined by `R`
and disjoint from `J`, so `(I a \ J) ∩ E a` is disjoint from `⋃_{u ∈ s} (I u ∩ E u)` and has
measure `μ(I a \ J) · μ(E a) ≥ μ(I a \ J) · m`. -/
theorem real_biUnion_inter_ge_of_indep (μ : Measure (Set ι)) [IsFiniteMeasure μ] (R : Set ι)
    (s : Finset κ) (I E : κ → Set (Set ι))
    (hI : ∀ u ∈ s, DeterminedBy (I u) R)
    (hIm : ∀ u ∈ s, MeasurableSet (I u)) (hEm : ∀ u ∈ s, MeasurableSet (E u))
    (hind : ∀ u ∈ s, ∀ A : Set (Set ι), DeterminedBy A R → MeasurableSet A →
      μ.real (A ∩ E u) = μ.real A * μ.real (E u))
    {m : ℝ} (hm : ∀ u ∈ s, m ≤ μ.real (E u)) :
    μ.real (⋃ u ∈ s, I u) * m ≤ μ.real (⋃ u ∈ s, I u ∩ E u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ u ∈ s, u ∈ insert a s := fun u hu => Finset.mem_insert_of_mem hu
    have haa : a ∈ insert a s := Finset.mem_insert_self a s
    have ih' := ih (fun u hu => hI u (hs u hu)) (fun u hu => hIm u (hs u hu))
      (fun u hu => hEm u (hs u hu)) (fun u hu => hind u (hs u hu)) (fun u hu => hm u (hs u hu))
    set J : Set (Set ι) := ⋃ u ∈ s, I u with hJ
    have hJdet : DeterminedBy J R :=
      DeterminedBy.iUnion fun u => DeterminedBy.iUnion fun hu => hI u (hs u hu)
    have hJm : MeasurableSet J := Finset.measurableSet_biUnion _ fun u hu => hIm u (hs u hu)
    have hdiffdet : DeterminedBy (I a \ J) R := (hI a haa).inter hJdet.compl
    have hdiffm : MeasurableSet (I a \ J) := (hIm a haa).diff hJm
    -- the union of the `I u` over `insert a s` is `J` together with the fresh part of `I a`
    have h1 : μ.real (⋃ u ∈ insert a s, I u) = μ.real J + μ.real (I a \ J) := by
      rw [Finset.set_biUnion_insert, ← hJ, Set.union_comm, ← Set.union_sdiff_self]
      exact measureReal_union (Set.disjoint_sdiff_right) hdiffm (measure_ne_top _ _)
        (measure_ne_top _ _)
    -- the union of the `I u ∩ E u` over `insert a s` contains the disjoint union of the old one
    -- and `(I a \ J) ∩ E a`
    have h2 : μ.real (⋃ u ∈ s, I u ∩ E u) + μ.real ((I a \ J) ∩ E a)
        ≤ μ.real (⋃ u ∈ insert a s, I u ∩ E u) := by
      have hdisj : Disjoint (⋃ u ∈ s, I u ∩ E u) ((I a \ J) ∩ E a) := by
        rw [Set.disjoint_left]
        intro ω hω hω'
        obtain ⟨u, hu, hωu⟩ := Set.mem_iUnion₂.1 hω
        exact hω'.1.2 (Set.mem_iUnion₂.2 ⟨u, hu, hωu.1⟩)
      have hsub : (⋃ u ∈ s, I u ∩ E u) ∪ ((I a \ J) ∩ E a) ⊆ ⋃ u ∈ insert a s, I u ∩ E u := by
        rw [Finset.set_biUnion_insert]
        rintro ω (hω | hω)
        · exact Or.inr hω
        · exact Or.inl ⟨hω.1.1, hω.2⟩
      rw [← measureReal_union hdisj (hdiffm.inter (hEm a haa)) (measure_ne_top _ _)
        (measure_ne_top _ _)]
      exact measureReal_mono hsub (measure_ne_top _ _)
    have h3 : μ.real ((I a \ J) ∩ E a) = μ.real (I a \ J) * μ.real (E a) :=
      hind a haa _ hdiffdet hdiffm
    have h4 : μ.real (I a \ J) * m ≤ μ.real (I a \ J) * μ.real (E a) :=
      mul_le_mul_of_nonneg_left (hm a haa) measureReal_nonneg
    rw [h1, add_mul]
    linarith

/-- **The decisive lemma for a product measure**: the family `I u` is determined by the
complement of the finite set `F` of coordinates and the family `E u` by `F` itself. -/
theorem prodBernoulli_real_biUnion_inter_ge (p : ι → unitInterval) (F : Finset ι) (s : Finset κ)
    (I E : κ → Set (Set ι))
    (hI : ∀ u ∈ s, DeterminedBy (I u) (↑F : Set ι)ᶜ) (hE : ∀ u ∈ s, DeterminedBy (E u) (↑F : Set ι))
    (hIm : ∀ u ∈ s, MeasurableSet (I u)) (hEm : ∀ u ∈ s, MeasurableSet (E u))
    {m : ℝ} (hm : ∀ u ∈ s, m ≤ (prodBernoulli p).real (E u)) :
    (prodBernoulli p).real (⋃ u ∈ s, I u) * m ≤ (prodBernoulli p).real (⋃ u ∈ s, I u ∩ E u) :=
  real_biUnion_inter_ge_of_indep (prodBernoulli p) (↑F : Set ι)ᶜ s I E hI hIm hEm
    (fun u hu A hA hAm => by
      rw [Set.inter_comm, prodBernoulli_real_inter_of_determinedBy p F (hE u hu) hA (hEm u hu) hAm,
        mul_comm])
    hm

/-- The same with the roles of `F` and its complement exchanged. -/
theorem prodBernoulli_real_biUnion_inter_ge' (p : ι → unitInterval) (F : Finset ι) (s : Finset κ)
    (I E : κ → Set (Set ι))
    (hI : ∀ u ∈ s, DeterminedBy (I u) (↑F : Set ι)) (hE : ∀ u ∈ s, DeterminedBy (E u) (↑F : Set ι)ᶜ)
    (hIm : ∀ u ∈ s, MeasurableSet (I u)) (hEm : ∀ u ∈ s, MeasurableSet (E u))
    {m : ℝ} (hm : ∀ u ∈ s, m ≤ (prodBernoulli p).real (E u)) :
    (prodBernoulli p).real (⋃ u ∈ s, I u) * m ≤ (prodBernoulli p).real (⋃ u ∈ s, I u ∩ E u) :=
  real_biUnion_inter_ge_of_indep (prodBernoulli p) (↑F : Set ι) s I E hI hIm hEm
    (fun u hu _ hA hAm => prodBernoulli_real_inter_of_determinedBy p F hA (hE u hu) hAm (hEm u hu))
    hm

/-- The decisive lemma with two disjoint finite supports. -/
theorem prodBernoulli_real_biUnion_inter_ge_disjoint (p : ι → unitInterval) {F F' : Finset ι}
    (hFF' : Disjoint F F') (s : Finset κ) (I E : κ → Set (Set ι))
    (hI : ∀ u ∈ s, DeterminedBy (I u) (↑F : Set ι)) (hE : ∀ u ∈ s, DeterminedBy (E u) (↑F' : Set ι))
    (hIm : ∀ u ∈ s, MeasurableSet (I u)) (hEm : ∀ u ∈ s, MeasurableSet (E u))
    {m : ℝ} (hm : ∀ u ∈ s, m ≤ (prodBernoulli p).real (E u)) :
    (prodBernoulli p).real (⋃ u ∈ s, I u) * m ≤ (prodBernoulli p).real (⋃ u ∈ s, I u ∩ E u) :=
  prodBernoulli_real_biUnion_inter_ge' p F s I E hI
    (fun u hu => (hE u hu).mono fun _ hi hiF =>
      Finset.disjoint_left.1 hFF' (Finset.mem_coe.1 hiF) (Finset.mem_coe.1 hi))
    hIm hEm hm

end Decisive

/-! ## Pinning a finite set of coordinates: patterns, sums over patterns, Markov -/

section Pinning

variable {ι : Type*}

/-- Pinning to the pattern `ξ` is overwriting by `ξ`. -/
theorem substitute_eq_overwrite (S ξ : Set ι) :
    substitute S (fun i => i ∈ ξ) = overwrite S ξ := by
  funext ω
  ext i
  by_cases hi : i ∈ S
  · rw [mem_substitute_of_mem _ hi, mem_overwrite_iff_of_mem hi]
  · rw [mem_substitute_of_notMem _ hi, mem_overwrite_iff_of_not_mem hi]

/-- Two configurations agreeing on `K \ R` have substitutes agreeing on `K`. -/
theorem substitute_agree_of_agree {K R : Set ι} (val : ι → Prop) {ω ω' : Set ι}
    (h : ∀ i ∈ K \ R, (i ∈ ω ↔ i ∈ ω')) :
    ∀ i ∈ K, (i ∈ substitute R val ω ↔ i ∈ substitute R val ω') := by
  intro i hi
  by_cases hiR : i ∈ R
  · rw [mem_substitute_of_mem val hiR, mem_substitute_of_mem val hiR]
  · rw [mem_substitute_of_notMem val hiR, mem_substitute_of_notMem val hiR]
    exact h i ⟨hi, hiR⟩

/-- `ω ∩ K = ω' ∩ K` from pointwise agreement on `K`. -/
theorem inter_eq_of_forall_iff {K : Set ι} {ω ω' : Set ι} (h : ∀ i ∈ K, (i ∈ ω ↔ i ∈ ω')) :
    ω ∩ K = ω' ∩ K := by
  ext i
  simp only [Set.mem_inter_iff]
  exact ⟨fun hi => ⟨(h i hi.2).1 hi.1, hi.2⟩, fun hi => ⟨(h i hi.2).2 hi.1, hi.2⟩⟩

/-- Pointwise agreement on `K` from `ω ∩ K = ω' ∩ K`. -/
theorem forall_iff_of_inter_eq {K : Set ι} {ω ω' : Set ι} (h : ω ∩ K = ω' ∩ K) :
    ∀ i ∈ K, (i ∈ ω ↔ i ∈ ω') := by
  intro i hi
  have := Set.ext_iff.1 h i
  simp only [Set.mem_inter_iff, hi, and_true] at this
  exact this

/-- **Substitution shrinks the support**: if `A` is determined by `K`, then the pinned event
`substitute R val ⁻¹' A` is determined by `K \ R`. -/
theorem determinedBy_substitute_preimage_of_determinedBy {A : Set (Set ι)} {K : Set ι}
    (hA : DeterminedBy A K) (R : Set ι) (val : ι → Prop) :
    DeterminedBy (substitute R val ⁻¹' A) (K \ R) := by
  rw [determinedBy_iff] at hA ⊢
  intro ω ω' h
  simp only [Set.mem_preimage]
  exact hA _ _ (inter_eq_of_forall_iff (substitute_agree_of_agree val (forall_iff_of_inter_eq h)))

/-- **Conditioning on a pattern is pinning**: `P(A ∩ [ξ]_S) = P([ξ]_S) · P^ξ(A)`. -/
theorem real_inter_localCylinder_eq_mul_pinnedProb (w : ι → unitInterval) (S : Finset ι)
    (ξ : Set ι) {A : Set (Set ι)} (hA : MeasurableSet A) :
    (prodBernoulli w).real (A ∩ localCylinder (↑S : Set ι) ξ) =
      (prodBernoulli w).real (localCylinder (↑S : Set ι) ξ) *
        pinnedProb w (↑S : Set ι) (fun i => i ∈ ξ) A := by
  rw [pinnedProb, substitute_eq_overwrite, inter_localCylinder_eq_preimage_overwrite_inter,
    Set.inter_comm]
  exact prodBernoulli_real_inter_of_determinedBy w S (determinedBy_localCylinder _ _)
    (determinedBy_preimage_overwrite _ _ _) (measurableSet_localCylinder S.finite_toSet.countable _)
    (measurable_overwrite _ _ hA)

open Classical in
/-- **The patterns of `S` partition the space**: `P(A) = Σ_{T ⊆ S} P(A ∩ [T]_S)`. -/
theorem real_eq_sum_inter_localCylinder (w : ι → unitInterval) (S : Finset ι) {A : Set (Set ι)}
    (hA : MeasurableSet A) :
    (prodBernoulli w).real A =
      ∑ T ∈ S.powerset, (prodBernoulli w).real (A ∩ localCylinder (↑S : Set ι) (↑T : Set ι)) := by
  have hdec : A = ⋃ T ∈ S.powerset, A ∩ localCylinder (↑S : Set ι) (↑T : Set ι) := by
    ext ω
    constructor
    · intro hω
      exact Set.mem_iUnion₂.2 ⟨S.filter (· ∈ ω), Finset.mem_powerset.2 (Finset.filter_subset _ _),
        hω, mem_localCylinder_filter S ω⟩
    · intro hω
      obtain ⟨T, -, hωA, -⟩ := Set.mem_iUnion₂.1 hω
      exact hωA
  conv_lhs => rw [hdec]
  refine measureReal_biUnion_finset ?_ ?_ ?_
  · intro T hT T' hT' hne
    exact (localCylinder_disjoint (Finset.mem_powerset.1 (Finset.mem_coe.1 hT))
      (Finset.mem_powerset.1 (Finset.mem_coe.1 hT')) hne).mono Set.inter_subset_right
      Set.inter_subset_right
  · intro T _
    exact hA.inter (measurableSet_localCylinder S.finite_toSet.countable _)
  · intro T _
    exact measure_ne_top _ _

/-- The probabilities of the patterns of `S` sum to `1`. -/
theorem sum_real_localCylinder (w : ι → unitInterval) (S : Finset ι) :
    ∑ T ∈ S.powerset, (prodBernoulli w).real (localCylinder (↑S : Set ι) (↑T : Set ι)) = 1 := by
  have h := real_eq_sum_inter_localCylinder w S (A := Set.univ) MeasurableSet.univ
  simp only [Set.univ_inter, probReal_univ] at h
  exact h.symm

open Classical in
/-- On the cylinder `[T]_S`, an event determined by `S` is everything or nothing. -/
theorem inter_localCylinder_of_determinedBy {B : Set (Set ι)} {S : Finset ι}
    (hB : DeterminedBy B (↑S : Set ι)) {T : Finset ι} (hT : T ⊆ S) :
    B ∩ localCylinder (↑S : Set ι) (↑T : Set ι) =
      if (↑T : Set ι) ∈ B then localCylinder (↑S : Set ι) (↑T : Set ι) else ∅ := by
  ext ω
  by_cases hTB : (↑T : Set ι) ∈ B
  · rw [if_pos hTB]
    exact ⟨fun h => h.2, fun hω => ⟨(mem_iff_coe_mem_of_determinedBy hB hT hω).2 hTB, hω⟩⟩
  · rw [if_neg hTB]
    exact ⟨fun h => hTB ((mem_iff_coe_mem_of_determinedBy hB hT h.2).1 h.1), fun h => h.elim⟩

/-- The pinned probability only reads the pattern on the pinned set. -/
theorem pinnedProb_congr_pattern (w : ι → unitInterval) (S : Set ι) {ω ω' : Set ι}
    (h : ∀ i ∈ S, (i ∈ ω ↔ i ∈ ω')) (A : Set (Set ι)) :
    pinnedProb w S (fun i => i ∈ ω) A = pinnedProb w S (fun i => i ∈ ω') A :=
  pinnedProb_congr_val w S h A

/-- The event "the pinned probability of `A` given the pattern on `S` is at most `c`" is
determined by `S`. -/
theorem determinedBy_setOf_pinnedProb_le (w : ι → unitInterval) (S : Set ι) (A : Set (Set ι))
    (c : ℝ) : DeterminedBy {ω : Set ι | pinnedProb w S (fun i => i ∈ ω) A ≤ c} S := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_setOf_eq, pinnedProb_congr_pattern w S (forall_iff_of_inter_eq h) A]

/-- The event "the pinned probability of `A` given the pattern on `S` exceeds `c`" is
determined by `S`. -/
theorem determinedBy_setOf_lt_pinnedProb (w : ι → unitInterval) (S : Set ι) (A : Set (Set ι))
    (c : ℝ) : DeterminedBy {ω : Set ι | c < pinnedProb w S (fun i => i ∈ ω) A} S := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_setOf_eq, pinnedProb_congr_pattern w S (forall_iff_of_inter_eq h) A]

/-- **Markov's inequality over the patterns of `S`**: the patterns for which the pinned probability
of `A` is at most `1 - δ` have total mass at most `(1 - P(A)) / δ`. -/
theorem mul_real_setOf_pinnedProb_le_le (w : ι → unitInterval) (S : Finset ι) {A : Set (Set ι)}
    (hA : MeasurableSet A) (δ : ℝ) :
    δ * (prodBernoulli w).real {ω : Set ι | pinnedProb w (↑S : Set ι) (fun i => i ∈ ω) A ≤ 1 - δ}
      ≤ 1 - (prodBernoulli w).real A := by
  classical
  set Low : Set (Set ι) := {ω | pinnedProb w (↑S : Set ι) (fun i => i ∈ ω) A ≤ 1 - δ} with hLow
  have hLowdet : DeterminedBy Low (↑S : Set ι) := determinedBy_setOf_pinnedProb_le w _ A _
  have hLowm : MeasurableSet Low := hLowdet.measurableSet_of_finset
  rw [real_eq_sum_inter_localCylinder w S hLowm, real_eq_sum_inter_localCylinder w S hA,
    ← sum_real_localCylinder w S, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun T hT => ?_
  have hTS : T ⊆ S := Finset.mem_powerset.1 hT
  rw [inter_localCylinder_of_determinedBy hLowdet hTS,
    real_inter_localCylinder_eq_mul_pinnedProb w S _ hA]
  have h0 : 0 ≤ (prodBernoulli w).real (localCylinder (↑S : Set ι) (↑T : Set ι)) :=
    measureReal_nonneg
  by_cases hTL : (↑T : Set ι) ∈ Low
  · rw [if_pos hTL]
    have hle : pinnedProb w (↑S : Set ι) (fun i => i ∈ (↑T : Set ι)) A ≤ 1 - δ := hTL
    nlinarith
  · rw [if_neg hTL, measureReal_empty, mul_zero]
    have hle : pinnedProb w (↑S : Set ι) (fun i => i ∈ (↑T : Set ι)) A ≤ 1 :=
      pinnedProb_le_one_coord w _ _ A
    nlinarith

end Pinning

/-! ## Contacts, gates and the blocking of entry into a box -/

section Contacts

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

open scoped Classical

/-- The endpoint of a confined connection is open and inside the confining set. -/
theorem mem_of_connWithin {S : Set V} {x y : V} {ω : SiteConfig V}
    (h : ω ∈ connWithin G S x y) : y ∈ ω ∩ S :=
  mem_of_mem_siteCluster G (ω ∩ S) ⟨h.1, h.2⟩

/-- A confined connection prepended by an open edge inside the confining set. -/
theorem connWithin_of_adj_of_connWithin {S : Set V} {x y z : V} {ω : SiteConfig V}
    (hxy : G.Adj x y) (hx : x ∈ ω ∩ S) (hy : y ∈ ω ∩ S) (h : ω ∈ connWithin G S y z) :
    ω ∈ connWithin G S x z :=
  ⟨hx, ((openSiteGraph_adj_iff' G (ω ∩ S) x y).2 ⟨hxy, hx, hy⟩).reachable.trans h.2⟩

/-- Confined connections compose, in the union of the two confining sets. -/
theorem connWithin_trans {S S' : Set V} {x y z : V} {ω : SiteConfig V}
    (h : ω ∈ connWithin G S x y) (h' : ω ∈ connWithin G S' y z) :
    ω ∈ connWithin G (S ∪ S') x z :=
  ⟨⟨h.1.1, Or.inl h.1.2⟩,
    (connWithin_mono_set G Set.subset_union_left x y h).2.trans
      (connWithin_mono_set G Set.subset_union_right y z h').2⟩

/-- **A walk from outside a box to inside it crosses its boundary**: some open site `y` of `D`
is adjacent to a site `x` reached from the start by an open path avoiding `D`. -/
theorem exists_crossing_of_walk (Dom D : Finset V) {ω : SiteConfig V} :
    ∀ {a b : V} (_ : (openSiteGraph G (ω ∩ (↑Dom : Set V))).Walk a b),
      a ∈ ω → a ∈ Dom → a ∉ D → b ∈ D →
        ∃ x y, ω ∈ connWithin G (↑(Dom \ D) : Set V) a x ∧ y ∈ D ∧ G.Adj x y ∧ y ∈ ω := by
  classical
  intro a b p
  induction p with
  | nil =>
    intro _ _ ha hb
    exact absurd hb ha
  | @cons u v w huv _ ih =>
    intro hu hDom hD hw
    have hadj := (openSiteGraph_adj_iff' G _ u v).1 huv
    have huS : u ∈ ω ∩ (↑(Dom \ D) : Set V) := ⟨hu, Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hDom, hD⟩)⟩
    by_cases hv : v ∈ D
    · exact ⟨u, v, ⟨huS, SimpleGraph.Reachable.refl u⟩, hv, hadj.1, hadj.2.2.1⟩
    · obtain ⟨x, y, hx, hy, hxy, hyω⟩ := ih hadj.2.2.1 hadj.2.2.2 hv hw
      refine ⟨x, y, ?_, hy, hxy, hyω⟩
      exact connWithin_of_adj_of_connWithin G hadj.1 huS
        ⟨hadj.2.2.1, Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hadj.2.2.2, hv⟩)⟩ hx

open Classical in
/-- The sites of `Dom` outside `D` that are adjacent to `D`. -/
def outerBoundary (Dom D : Finset V) : Finset V :=
  (Dom \ D).filter fun x => ∃ y ∈ D, G.Adj x y

open Classical in
/-- **The contacts** of the source `o` on the box `D`: the sites of the outer boundary of `D`
joined to `o` by an open path inside `Dom` avoiding `D`.  A function of the configuration outside
`D` only. -/
def contacts (Dom D : Finset V) (o : V) (ω : SiteConfig V) : Finset V :=
  (outerBoundary G Dom D).filter fun x => ω ∈ connWithin G (↑(Dom \ D) : Set V) o x

open Classical in
/-- **The inward gate** of a set `K` of exterior sites: the sites of `D` adjacent to `K`. -/
def gate (D K : Finset V) : Finset V := D.filter fun y => ∃ x ∈ K, G.Adj x y

/-- The level is *poor*: fewer than `N` contacts. -/
def poor (Dom D : Finset V) (o : V) (N : ℕ) : Set (SiteConfig V) :=
  {ω | (contacts G Dom D o ω).card < N}

/-- The level is *killed*: it is poor and every site of the gate of its contacts is closed. -/
def killed (Dom D : Finset V) (o : V) (N : ℕ) : Set (SiteConfig V) :=
  {ω | (contacts G Dom D o ω).card < N ∧ ∀ y ∈ gate G D (contacts G Dom D o ω), y ∉ ω}

theorem killed_subset_poor (Dom D : Finset V) (o : V) (N : ℕ) :
    killed G Dom D o N ⊆ poor G Dom D o N := fun _ h => h.1

theorem contacts_subset (Dom D : Finset V) (o : V) (ω : SiteConfig V) :
    contacts G Dom D o ω ⊆ outerBoundary G Dom D := by
  classical
  exact Finset.filter_subset _ _

theorem outerBoundary_subset (Dom D : Finset V) : outerBoundary G Dom D ⊆ Dom \ D := by
  classical
  exact Finset.filter_subset _ _

/-- **A killed level blocks the source from the box**: if all gate sites of the contacts are
closed, no open path inside `Dom` joins `o` to a subset `B` of `D`. -/
theorem killed_subset_compl_connWithinSet (Dom D : Finset V) {o : V} (ho : o ∉ D) (N : ℕ)
    {B : Set V} (hB : B ⊆ ↑D) :
    killed G Dom D o N ⊆ (connWithinSet G (↑Dom : Set V) o B)ᶜ := by
  classical
  rintro ω ⟨-, hclosed⟩ hconn
  obtain ⟨b, hb, hob⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 hconn
  obtain ⟨⟨hoω, hoDom⟩, ⟨p⟩⟩ := hob
  obtain ⟨x, y, hx, hy, hxy, hyω⟩ :=
    exists_crossing_of_walk G Dom D p hoω (Finset.mem_coe.1 hoDom) ho (Finset.mem_coe.1 (hB hb))
  have hxc : x ∈ contacts G Dom D o ω := by
    rw [contacts, Finset.mem_filter]
    refine ⟨?_, hx⟩
    rw [outerBoundary, Finset.mem_filter]
    exact ⟨Finset.mem_coe.1 (mem_of_connWithin G hx).2, y, hy, hxy⟩
  refine hclosed y ?_ hyω
  rw [gate, Finset.mem_filter]
  exact ⟨hy, x, hxc, hxy⟩

/-- The contacts read the configuration outside `D` only. -/
theorem contacts_congr {Dom D : Finset V} {o : V} {ω ω' : SiteConfig V}
    (h : ω ∩ (↑(Dom \ D) : Set V) = ω' ∩ (↑(Dom \ D) : Set V)) :
    contacts G Dom D o ω = contacts G Dom D o ω' := by
  classical
  simp only [contacts]
  refine Finset.filter_congr fun x _ => ?_
  exact (determinedBy_iff _ _).1 (determinedBy_connWithin G _ o x) ω ω' h

theorem determinedBy_contacts_eq (Dom D : Finset V) (o : V) (K : Finset V) :
    DeterminedBy {ω : SiteConfig V | contacts G Dom D o ω = K} (↑(Dom \ D) : Set V) := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_setOf_eq, contacts_congr G h]

theorem determinedBy_poor (Dom D : Finset V) (o : V) (N : ℕ) :
    DeterminedBy (poor G Dom D o N) (↑(Dom \ D) : Set V) := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [poor, Set.mem_setOf_eq, contacts_congr G h]

/-- The gate of exterior sites lies in the outermost layer of `D`, provided the next box `D'`
avoids that layer. -/
theorem gate_subset_sdiff {D D' K : Finset V}
    (hgate : ∀ x ∉ D, ∀ y ∈ D, G.Adj x y → y ∉ D') (hK : ∀ x ∈ K, x ∉ D) :
    gate G D K ⊆ D \ D' := by
  classical
  intro y hy
  rw [gate, Finset.mem_filter] at hy
  obtain ⟨hyD, x, hxK, hxy⟩ := hy
  exact Finset.mem_sdiff.2 ⟨hyD, hgate x (hK x hxK) y hyD hxy⟩

theorem determinedBy_killed {Dom D D' : Finset V} (o : V) (N : ℕ) (hDDom : D ⊆ Dom)
    (hD'D : D' ⊆ D) (hgate : ∀ x ∉ D, ∀ y ∈ D, G.Adj x y → y ∉ D') :
    DeterminedBy (killed G Dom D o N) (↑(Dom \ D') : Set V) := by
  classical
  rw [determinedBy_iff]
  intro ω ω' h
  have hagree := forall_iff_of_inter_eq h
  have hsub : (↑(Dom \ D) : Set V) ⊆ (↑(Dom \ D') : Set V) := by
    intro i hi
    rw [Finset.mem_coe, Finset.mem_sdiff] at hi ⊢
    exact ⟨hi.1, fun hi' => hi.2 (hD'D hi')⟩
  have hK : contacts G Dom D o ω = contacts G Dom D o ω' :=
    contacts_congr G (inter_eq_of_forall_iff fun i hi => hagree i (hsub hi))
  have hnotD : ∀ x ∈ contacts G Dom D o ω, x ∉ D := fun x hx =>
    (Finset.mem_sdiff.1 (outerBoundary_subset G Dom D (contacts_subset G Dom D o ω hx))).2
  simp only [killed, Set.mem_setOf_eq, ← hK]
  refine and_congr Iff.rfl (forall₂_congr fun y hy => ?_)
  have hyD : y ∈ D \ D' := gate_subset_sdiff G hgate hnotD hy
  have hy' : y ∈ (↑(Dom \ D') : Set V) := by
    rw [Finset.mem_coe, Finset.mem_sdiff]
    exact ⟨hDDom (Finset.mem_sdiff.1 hyD).1, (Finset.mem_sdiff.1 hyD).2⟩
  exact not_congr (hagree y hy')

/-- Relative form of `gate_subset_sdiff`: only gate sites belonging to the ambient domain are
needed.  This is the form used for contact gates, since contacts lie in `Dom \ D`. -/
theorem gate_subset_sdiff_rel {Dom D D' K : Finset V}
    (hgateRel : ∀ x ∈ Dom, x ∉ D → ∀ y ∈ D, G.Adj x y → y ∉ D')
    (hKDom : K ⊆ Dom) (hK : ∀ x ∈ K, x ∉ D) :
    gate G D K ⊆ D \ D' := by
  classical
  intro y hy
  rw [gate, Finset.mem_filter] at hy
  obtain ⟨hyD, x, hxK, hxy⟩ := hy
  exact Finset.mem_sdiff.2 ⟨hyD, hgateRel x (hKDom hxK) (hK x hxK) y hyD hxy⟩

/-- Relative form of `determinedBy_killed`.  Every use of the gate is at a contact, and
`outerBoundary_subset` puts every contact in the ambient domain. -/
theorem determinedBy_killed_rel {Dom D D' : Finset V} (o : V) (N : ℕ) (hDDom : D ⊆ Dom)
    (hD'D : D' ⊆ D)
    (hgateRel : ∀ x ∈ Dom, x ∉ D → ∀ y ∈ D, G.Adj x y → y ∉ D') :
    DeterminedBy (killed G Dom D o N) (↑(Dom \ D') : Set V) := by
  classical
  rw [determinedBy_iff]
  intro ω ω' h
  have hagree := forall_iff_of_inter_eq h
  have hsub : (↑(Dom \ D) : Set V) ⊆ (↑(Dom \ D') : Set V) := by
    intro i hi
    rw [Finset.mem_coe, Finset.mem_sdiff] at hi ⊢
    exact ⟨hi.1, fun hi' => hi.2 (hD'D hi')⟩
  have hK : contacts G Dom D o ω = contacts G Dom D o ω' :=
    contacts_congr G (inter_eq_of_forall_iff fun i hi => hagree i (hsub hi))
  have hcontacts : contacts G Dom D o ω ⊆ Dom \ D :=
    (contacts_subset G Dom D o ω).trans (outerBoundary_subset G Dom D)
  have hKDom : contacts G Dom D o ω ⊆ Dom := fun x hx =>
    (Finset.mem_sdiff.1 (hcontacts hx)).1
  have hnotD : ∀ x ∈ contacts G Dom D o ω, x ∉ D := fun x hx =>
    (Finset.mem_sdiff.1 (hcontacts hx)).2
  simp only [killed, Set.mem_setOf_eq, ← hK]
  refine and_congr Iff.rfl (forall₂_congr fun y hy => ?_)
  have hyD : y ∈ D \ D' := gate_subset_sdiff_rel G hgateRel hKDom hnotD hy
  have hy' : y ∈ (↑(Dom \ D') : Set V) := by
    rw [Finset.mem_coe, Finset.mem_sdiff]
    exact ⟨hDDom (Finset.mem_sdiff.1 hyD).1, (Finset.mem_sdiff.1 hyD).2⟩
  exact not_congr (hagree y hy')

end Contacts


/-! ## The per-level killing bound and the many-contacts theorem -/

section ManyContacts

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

open scoped Classical

/-- The event that some site of `F` is open is determined by `F`. -/
theorem determinedBy_exists_mem (F : Finset V) :
    DeterminedBy {ω : SiteConfig V | ∃ y ∈ F, y ∈ ω} (↑F : Set V) := by
  rw [determinedBy_iff]
  intro ω ω' h
  have hagree := forall_iff_of_inter_eq h
  simp only [Set.mem_setOf_eq]
  exact exists_congr fun y => and_congr_right fun hy => hagree y (Finset.mem_coe.2 hy)

/-- **Some site of `F` is open with probability at most `1 - (1 - q)^n`** when every site of `F`
has parameter at most `q` and `|F| ≤ n`. -/
theorem real_exists_mem_le (w : V → unitInterval) (F : Finset V) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (hw : ∀ y ∈ F, (w y : ℝ) ≤ q) {n : ℕ} (hF : F.card ≤ n) :
    (prodBernoulli w).real {ω : SiteConfig V | ∃ y ∈ F, y ∈ ω} ≤ 1 - (1 - q) ^ n := by
  have hcompl : {ω : SiteConfig V | ∃ y ∈ F, y ∈ ω} = {ω : SiteConfig V | ∀ y ∈ F, y ∉ ω}ᶜ := by
    ext ω; simp
  have hm : MeasurableSet {ω : SiteConfig V | ∀ y ∈ F, y ∉ ω} :=
    measurableSet_forall_notMem_of_countable (T := (↑F : Set V)) F.finite_toSet.countable
  rw [hcompl, measureReal_compl hm, probReal_univ, prodBernoulli_real_forall_notMem]
  have h1 : (1 - q) ^ n ≤ (1 - q) ^ F.card :=
    pow_le_pow_of_le_one (by linarith) (by linarith) hF
  have h2 : (1 - q) ^ F.card ≤ ∏ i ∈ F, (1 - (w i : ℝ)) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun i _ => by linarith) (fun i hi => by linarith [hw i hi])
  linarith

/-- The gate of `K` has at most `Δ · |K|` sites when every site has at most `Δ` neighbours in
`D`. -/
theorem card_gate_le {D : Finset V} {Δ : ℕ} (hdeg : ∀ x, (D.filter (G.Adj x)).card ≤ Δ)
    (K : Finset V) : (gate G D K).card ≤ Δ * K.card := by
  classical
  have hsub : gate G D K ⊆ K.biUnion fun x => D.filter (G.Adj x) := by
    intro y hy
    rw [gate, Finset.mem_filter] at hy
    obtain ⟨hyD, x, hxK, hxy⟩ := hy
    exact Finset.mem_biUnion.2 ⟨x, hxK, Finset.mem_filter.2 ⟨hyD, hxy⟩⟩
  calc (gate G D K).card ≤ (K.biUnion fun x => D.filter (G.Adj x)).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ K, (D.filter (G.Adj x)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ K, Δ := Finset.sum_le_sum fun x _ => hdeg x
    _ = Δ * K.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

open Classical in
/-- **The per-level killing bound.**  Conditionally on the configuration outside `D`, a poor level
is killed with probability at least `(1 - q)^{Δ N}`: the gate of the (fewer than `N`) contacts has
at most `Δ N` sites, all of parameter at most `q`, and it is read by nothing outside `D`.  Stated
for every event `Z` determined by the exterior. -/
theorem real_inter_poor_diff_killed_le (w : V → unitInterval) (Dom D : Finset V) (o : V)
    (N Δ : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hw : ∀ y ∈ D, (w y : ℝ) ≤ q)
    (hdeg : ∀ x, (D.filter (G.Adj x)).card ≤ Δ) {Z : Set (SiteConfig V)}
    (hZ : DeterminedBy Z (↑(Dom \ D) : Set V)) :
    (prodBernoulli w).real (Z ∩ (poor G Dom D o N \ killed G Dom D o N)) ≤
      (1 - (1 - q) ^ (Δ * N)) * (prodBernoulli w).real (Z ∩ poor G Dom D o N) := by
  set 𝒦 : Finset (Finset V) := (outerBoundary G Dom D).powerset.filter fun K => K.card < N with h𝒦
  set C : Finset V → Set (SiteConfig V) := fun K => Z ∩ {ω | contacts G Dom D o ω = K} with hC
  have hCdet : ∀ K, DeterminedBy (C K) (↑(Dom \ D) : Set V) := fun K =>
    hZ.inter (determinedBy_contacts_eq G Dom D o K)
  have hCm : ∀ K, MeasurableSet (C K) := fun K => (hCdet K).measurableSet_of_finset
  have hCdisj : (↑𝒦 : Set (Finset V)).PairwiseDisjoint C := by
    intro K _ K' _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, hK⟩ ⟨-, hK'⟩
    exact hne (hK.symm.trans hK')
  have hopen : ∀ K, DeterminedBy {ω : SiteConfig V | ∃ y ∈ gate G D K, y ∈ ω}
      (↑(gate G D K) : Set V) := fun K => determinedBy_exists_mem (gate G D K)
  have hopenm : ∀ K, MeasurableSet {ω : SiteConfig V | ∃ y ∈ gate G D K, y ∈ ω} := fun K =>
    (hopen K).measurableSet_of_finset
  have eq1 : Z ∩ poor G Dom D o N = ⋃ K ∈ 𝒦, C K := by
    ext ω
    simp only [Set.mem_inter_iff, poor, Set.mem_setOf_eq, Set.mem_iUnion, hC, h𝒦,
      Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · rintro ⟨hZω, hlt⟩
      exact ⟨contacts G Dom D o ω, ⟨contacts_subset G Dom D o ω, hlt⟩, hZω, rfl⟩
    · rintro ⟨K, ⟨-, hlt⟩, hZω, rfl⟩
      exact ⟨hZω, hlt⟩
  have eq2 : Z ∩ (poor G Dom D o N \ killed G Dom D o N) =
      ⋃ K ∈ 𝒦, C K ∩ {ω | ∃ y ∈ gate G D K, y ∈ ω} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_sdiff, poor, killed, Set.mem_setOf_eq, Set.mem_iUnion,
      hC, h𝒦, Finset.mem_filter, Finset.mem_powerset, exists_prop, not_and, not_forall,
      not_not]
    constructor
    · rintro ⟨hZω, hlt, hex⟩
      obtain ⟨y, hy, hyω⟩ := hex hlt
      exact ⟨contacts G Dom D o ω, ⟨contacts_subset G Dom D o ω, hlt⟩, ⟨hZω, rfl⟩, y, hy, hyω⟩
    · rintro ⟨K, ⟨-, hlt⟩, ⟨hZω, rfl⟩, y, hy, hyω⟩
      exact ⟨hZω, hlt, fun _ => ⟨y, hy, hyω⟩⟩
  rw [eq1, eq2, measureReal_biUnion_finset hCdisj (fun K _ => hCm K) (fun K _ => measure_ne_top _ _),
    measureReal_biUnion_finset (hCdisj.mono fun K => Set.inter_subset_left)
      (fun K _ => (hCm K).inter (hopenm K)) (fun K _ => measure_ne_top _ _), Finset.mul_sum]
  refine Finset.sum_le_sum fun K hK => ?_
  have hKlt : K.card < N := (Finset.mem_filter.1 hK).2
  have hKsub : K ⊆ outerBoundary G Dom D := Finset.mem_powerset.1 (Finset.mem_filter.1 hK).1
  -- independence of the gate from the exterior
  have hind : (prodBernoulli w).real (C K ∩ {ω | ∃ y ∈ gate G D K, y ∈ ω}) =
      (prodBernoulli w).real (C K) * (prodBernoulli w).real {ω | ∃ y ∈ gate G D K, y ∈ ω} := by
    rw [Set.inter_comm, mul_comm]
    refine prodBernoulli_real_inter_of_determinedBy w (gate G D K) (hopen K) ?_ (hopenm K) (hCm K)
    refine (hCdet K).mono fun i hi hi' => ?_
    rw [Finset.mem_coe, Finset.mem_sdiff] at hi
    rw [Finset.mem_coe, gate, Finset.mem_filter] at hi'
    exact hi.2 hi'.1
  have hgateq : ∀ y ∈ gate G D K, (w y : ℝ) ≤ q := fun y hy =>
    hw y (Finset.mem_filter.1 hy).1
  have hcard : (gate G D K).card ≤ Δ * N :=
    le_trans (card_gate_le G hdeg K) (Nat.mul_le_mul_left Δ hKlt.le)
  have hle := real_exists_mem_le w (gate G D K) hq0 hq1 hgateq hcard
  rw [hind, mul_comm]
  exact mul_le_mul_of_nonneg_right hle measureReal_nonneg

/-- **A poor level is killed with conditional probability at least `(1 - q)^{Δ N}`**, in the
unconditional form used by the level induction. -/
theorem real_poor_diff_killed_le (w : V → unitInterval) (Dom D : Finset V) (o : V) (N Δ : ℕ)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hw : ∀ y ∈ D, (w y : ℝ) ≤ q)
    (hdeg : ∀ x, (D.filter (G.Adj x)).card ≤ Δ) :
    (prodBernoulli w).real (poor G Dom D o N \ killed G Dom D o N) ≤
      (1 - (1 - q) ^ (Δ * N)) * (prodBernoulli w).real (poor G Dom D o N) := by
  have h := real_inter_poor_diff_killed_le G w Dom D o N Δ hq0 hq1 hw hdeg
    (Z := Set.univ) (determinedBy_univ _)
  simpa only [Set.univ_inter] using h

/-- The event that no level `j ≤ i` is killed. -/
def survive (Dom : Finset V) (D : ℕ → Finset V) (o : V) (N : ℕ) (i : ℕ) :
    Set (SiteConfig V) :=
  ⋂ j ∈ Finset.range (i + 1), (killed G Dom (D j) o N)ᶜ

theorem biInter_range_succ' {α : Type*} (f : ℕ → Set α) (n : ℕ) :
    (⋂ j ∈ Finset.range (n + 1), f j) = f 0 ∩ ⋂ j ∈ Finset.range n, f (j + 1) := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_range]
  constructor
  · intro h
    exact ⟨h 0 (Nat.succ_pos n), fun j hj => h (j + 1) (Nat.succ_lt_succ hj)⟩
  · rintro ⟨h0, h⟩ j hj
    cases j with
    | zero => exact h0
    | succ j => exact h j (Nat.lt_of_succ_lt_succ hj)

theorem survive_zero (Dom : Finset V) (D : ℕ → Finset V) (o : V) (N : ℕ) :
    survive G Dom D o N 0 = (killed G Dom (D 0) o N)ᶜ := by
  simp [survive]

theorem survive_succ (Dom : Finset V) (D : ℕ → Finset V) (o : V) (N i : ℕ) :
    survive G Dom D o N (i + 1) =
      (killed G Dom (D 0) o N)ᶜ ∩ survive G Dom (fun j => D (j + 1)) o N i := by
  simp only [survive]
  exact biInter_range_succ' (fun j => (killed G Dom (D j) o N)ᶜ) (i + 1)

theorem subset_survive_of_forall {Dom : Finset V} {D : ℕ → Finset V} {o : V} {N : ℕ}
    {A : Set (SiteConfig V)} {L : ℕ} (hA : ∀ j < L, A ⊆ (killed G Dom (D j) o N)ᶜ) {i : ℕ}
    (hi : i < L) : A ⊆ survive G Dom D o N i := by
  intro ω hω
  simp only [survive, Set.mem_iInter, Finset.mem_range]
  intro j hj
  exact hA j (lt_of_le_of_lt (Nat.lt_succ_iff.1 hj) hi) hω

/-- `killed` is determined by `Dom ∪ D`, unconditionally: its contacts read `Dom \ D` and its
gate lies in `D`. -/
theorem determinedBy_killed_union (Dom D : Finset V) (o : V) (N : ℕ) :
    DeterminedBy (killed G Dom D o N) (↑(Dom ∪ D) : Set V) := by
  classical
  rw [determinedBy_iff]
  intro ω ω' h
  have hagree := forall_iff_of_inter_eq h
  have hK : contacts G Dom D o ω = contacts G Dom D o ω' := by
    refine contacts_congr G (inter_eq_of_forall_iff fun i hi => hagree i ?_)
    rw [Finset.mem_coe, Finset.mem_sdiff] at hi
    exact Finset.mem_coe.2 (Finset.mem_union_left _ hi.1)
  simp only [killed, Set.mem_setOf_eq, ← hK]
  refine and_congr Iff.rfl (forall₂_congr fun y hy => ?_)
  have hyD : y ∈ D := (Finset.mem_filter.1 hy).1
  exact not_congr (hagree y (Finset.mem_coe.2 (Finset.mem_union_right _ hyD)))

theorem measurableSet_killed (Dom D : Finset V) (o : V) (N : ℕ) :
    MeasurableSet (killed G Dom D o N) :=
  (determinedBy_killed_union G Dom D o N).measurableSet_of_finset

theorem measurableSet_poor (Dom D : Finset V) (o : V) (N : ℕ) :
    MeasurableSet (poor G Dom D o N) :=
  (determinedBy_poor G Dom D o N).measurableSet_of_finset

theorem measurableSet_survive (Dom : Finset V) (D : ℕ → Finset V) (o : V) (N i : ℕ) :
    MeasurableSet (survive G Dom D o N i) :=
  Finset.measurableSet_biInter _ fun j _ => (measurableSet_killed G Dom (D j) o N).compl

/-- Nested boxes: `D j ⊆ D i` for `i ≤ j < L`. -/
theorem subset_of_le_of_lt {D : ℕ → Finset V} {L : ℕ}
    (hnest : ∀ i, i + 1 < L → D (i + 1) ⊆ D i) :
    ∀ i j, i ≤ j → j < L → D j ⊆ D i := by
  intro i j hij
  induction hij with
  | refl => intro _; exact Finset.Subset.refl _
  | step _ ih =>
    intro hlt
    exact (hnest _ hlt).trans (ih (lt_trans (Nat.lt_succ_self _) hlt))

/-- **The many-contacts estimate.**  Levels `D 0 ⊇ D 1 ⊇ ⋯ ⊇ D (L-1)` inside `Dom`, each next
box avoiding the outermost layer of the previous one, every site of every level of parameter at
most `q`, and at most `Δ` neighbours per site.  Then the expected number of poor levels survived,
`Σ_i P(no level ≤ i killed, level i poor)`, is at most `(1 - q_N) / q_N` with
`q_N = (1 - q)^{Δ N}`, uniformly in the number of levels.

Proof by induction on the number of levels: the outermost level is poor with probability `π` and
then killed with conditional probability at least `q_N`; on the event that it is not killed, the
configuration outside the second box is pinned, the remaining levels form an instance of the same
statement for the pinned product law, and the bound `b = (1 - q_N)/q_N` satisfies
`(1 - q_N) π + b (1 - q_N π) = b`. -/
theorem sum_real_survive_inter_poor_le (Dom : Finset V) (o : V) (N Δ : ℕ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) :
    ∀ (L : ℕ) (D : ℕ → Finset V) (w : V → unitInterval),
      (∀ i < L, D i ⊆ Dom) → (∀ i, i + 1 < L → D (i + 1) ⊆ D i) →
      (∀ i, i + 1 < L → ∀ x ∉ D i, ∀ y ∈ D i, G.Adj x y → y ∉ D (i + 1)) →
      (∀ i < L, ∀ y ∈ D i, (w y : ℝ) ≤ q) →
      ∑ i ∈ Finset.range L,
          (prodBernoulli w).real (survive G Dom D o N i ∩ poor G Dom (D i) o N)
        ≤ (1 - (1 - q) ^ (Δ * N)) / (1 - q) ^ (Δ * N) := by
  have hqN0 : 0 < (1 - q) ^ (Δ * N) := pow_pos (by linarith) _
  have hqN1 : (1 - q) ^ (Δ * N) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hb0 : 0 ≤ (1 - (1 - q) ^ (Δ * N)) / (1 - q) ^ (Δ * N) :=
    div_nonneg (by linarith) hqN0.le
  intro L
  induction L with
  | zero =>
    intro D w _ _ _ _
    simpa using hb0
  | succ L ih =>
    intro D w hsub hnest hgate hw
    set qN : ℝ := (1 - q) ^ (Δ * N) with hqN
    set b : ℝ := (1 - qN) / qN with hb
    have hbqN : b * qN = 1 - qN := div_mul_cancel₀ _ hqN0.ne'
    -- the outermost level
    have hdeg0 : ∀ x, ((D 0).filter (G.Adj x)).card ≤ Δ := fun x =>
      le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (hsub 0 (Nat.succ_pos L))))
        (hdeg x)
    have h0 := real_poor_diff_killed_le G w Dom (D 0) o N Δ hq0 hq1.le (hw 0 (Nat.succ_pos L))
      hdeg0
    set π : ℝ := (prodBernoulli w).real (poor G Dom (D 0) o N) with hπ
    set f0 : ℝ := (prodBernoulli w).real (poor G Dom (D 0) o N \ killed G Dom (D 0) o N) with hf0
    have hπ0 : 0 ≤ π := measureReal_nonneg
    have hf00 : 0 ≤ f0 := measureReal_nonneg
    have hkilled : (prodBernoulli w).real (killed G Dom (D 0) o N) = π - f0 := by
      have h := measureReal_inter_add_sdiff (μ := prodBernoulli w) (s := poor G Dom (D 0) o N)
        (measurableSet_killed G Dom (D 0) o N) (measure_ne_top _ _)
      rw [Set.inter_eq_right.2 (killed_subset_poor G Dom (D 0) o N)] at h
      linarith
    have hcompl : (prodBernoulli w).real (killed G Dom (D 0) o N)ᶜ = 1 - π + f0 := by
      rw [measureReal_compl (measurableSet_killed G Dom (D 0) o N), probReal_univ, hkilled]
      ring
    -- the remaining levels, through the pinned law on the exterior of `D 1`
    have hrest : ∑ i ∈ Finset.range L, (prodBernoulli w).real
        (survive G Dom D o N (i + 1) ∩ poor G Dom (D (i + 1)) o N)
          ≤ b * (prodBernoulli w).real (killed G Dom (D 0) o N)ᶜ := by
      rcases Nat.eq_zero_or_pos L with hL | hL
      · subst hL
        simp only [Finset.range_zero, Finset.sum_empty]
        exact mul_nonneg hb0 measureReal_nonneg
      · set R : Finset V := Dom \ D 1 with hR
        have hB : DeterminedBy (killed G Dom (D 0) o N)ᶜ (↑R : Set V) :=
          (determinedBy_killed G o N (hsub 0 (Nat.succ_pos L)) (hnest 0 (by omega))
            (hgate 0 (by omega))).compl
        obtain ⟨𝒯, h𝒯⟩ : ∃ 𝒯 : Finset (Finset V), 𝒯 = R.powerset.filter
            (fun T : Finset V => (↑T : Set V) ∈ (killed G Dom (D 0) o N)ᶜ) := ⟨_, rfl⟩
        have hsumB : (prodBernoulli w).real (killed G Dom (D 0) o N)ᶜ =
            ∑ T ∈ 𝒯, (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) := by
          rw [h𝒯]
          convert prodBernoulli_real_eq_sum_localCylinder w R hB using 3
        have hX : ∀ i, MeasurableSet
            (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) := fun i =>
          (measurableSet_survive G Dom (fun j => D (j + 1)) o N i).inter
            (measurableSet_poor G Dom (D (i + 1)) o N)
        have hterm : ∀ i ∈ Finset.range L, (prodBernoulli w).real
            (survive G Dom D o N (i + 1) ∩ poor G Dom (D (i + 1)) o N) =
            ∑ T ∈ 𝒯,
              (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) *
                (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                  (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) := by
          intro i _
          rw [survive_succ, Set.inter_assoc, Set.inter_comm, h𝒯]
          convert prodBernoulli_real_inter_eq_sum_pinW w R (hX i) hB using 3
        have hIH : ∀ T ∈ 𝒯,
            ∑ i ∈ Finset.range L, (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
              (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) ≤ b := by
          intro T _
          refine ih (fun j => D (j + 1)) (pinW w (↑R : Set V) (↑T : Set V))
            (fun i hi => hsub (i + 1) (by omega)) (fun i hi => hnest (i + 1) (by omega))
            (fun i hi => hgate (i + 1) (by omega)) ?_
          intro i hi y hy
          have hyD1 : y ∈ D 1 :=
            subset_of_le_of_lt hnest 1 (i + 1) (by omega) (by omega) hy
          have hyR : y ∉ (↑R : Set V) := by
            rw [Finset.mem_coe, hR, Finset.mem_sdiff]
            exact fun h => h.2 hyD1
          rw [pinW_apply_of_not_mem w _ hyR]
          exact hw (i + 1) (by omega) y hy
        calc ∑ i ∈ Finset.range L, (prodBernoulli w).real
                (survive G Dom D o N (i + 1) ∩ poor G Dom (D (i + 1)) o N)
            = ∑ i ∈ Finset.range L, ∑ T ∈ 𝒯,
                (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) *
                  (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                    (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) :=
              Finset.sum_congr rfl hterm
          _ = ∑ T ∈ 𝒯, ∑ i ∈ Finset.range L,
                (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) *
                  (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                    (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) :=
              Finset.sum_comm
          _ = ∑ T ∈ 𝒯,
                (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) *
                  ∑ i ∈ Finset.range L,
                    (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                      (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) := by
              refine Finset.sum_congr rfl fun T _ => ?_
              rw [Finset.mul_sum]
          _ ≤ ∑ T ∈ 𝒯, (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) * b :=
              Finset.sum_le_sum fun T hT =>
                mul_le_mul_of_nonneg_left (hIH T hT) measureReal_nonneg
          _ = b * (prodBernoulli w).real (killed G Dom (D 0) o N)ᶜ := by
              rw [← Finset.sum_mul, hsumB, mul_comm]
    -- assemble
    rw [Finset.sum_range_succ', survive_zero, Set.inter_comm, ← Set.sdiff_eq, ← hf0, hcompl] at *
    have h1 : b * (1 - π + f0) ≤ b * (1 - π + (1 - qN) * π) :=
      mul_le_mul_of_nonneg_left (by linarith) hb0
    have h2 : b * (1 - π + (1 - qN) * π) = b - (1 - qN) * π := by
      linear_combination (-π) * hbqN
    linarith

/-- Relative-gate form of `sum_real_survive_inter_poor_le`.  In the induction the gate is used
only to show that the killed event is determined outside the next box; the relevant exterior
vertices are contacts and hence belong to `Dom`. -/
theorem sum_real_survive_inter_poor_le_rel (Dom : Finset V) (o : V) (N Δ : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) :
    ∀ (L : ℕ) (D : ℕ → Finset V) (w : V → unitInterval),
      (∀ i < L, D i ⊆ Dom) → (∀ i, i + 1 < L → D (i + 1) ⊆ D i) →
      (∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ D i →
        ∀ y ∈ D i, G.Adj x y → y ∉ D (i + 1)) →
      (∀ i < L, ∀ y ∈ D i, (w y : ℝ) ≤ q) →
      ∑ i ∈ Finset.range L,
          (prodBernoulli w).real (survive G Dom D o N i ∩ poor G Dom (D i) o N)
        ≤ (1 - (1 - q) ^ (Δ * N)) / (1 - q) ^ (Δ * N) := by
  have hqN0 : 0 < (1 - q) ^ (Δ * N) := pow_pos (by linarith) _
  have hqN1 : (1 - q) ^ (Δ * N) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hb0 : 0 ≤ (1 - (1 - q) ^ (Δ * N)) / (1 - q) ^ (Δ * N) :=
    div_nonneg (by linarith) hqN0.le
  intro L
  induction L with
  | zero =>
    intro D w _ _ _ _
    simpa using hb0
  | succ L ih =>
    intro D w hsub hnest hgateRel hw
    set qN : ℝ := (1 - q) ^ (Δ * N) with hqN
    set b : ℝ := (1 - qN) / qN with hb
    have hbqN : b * qN = 1 - qN := div_mul_cancel₀ _ hqN0.ne'
    have hdeg0 : ∀ x, ((D 0).filter (G.Adj x)).card ≤ Δ := fun x =>
      le_trans (Finset.card_le_card (Finset.filter_subset_filter _ (hsub 0 (Nat.succ_pos L))))
        (hdeg x)
    have h0 := real_poor_diff_killed_le G w Dom (D 0) o N Δ hq0 hq1.le
      (hw 0 (Nat.succ_pos L)) hdeg0
    set π : ℝ := (prodBernoulli w).real (poor G Dom (D 0) o N) with hπ
    set f0 : ℝ := (prodBernoulli w).real (poor G Dom (D 0) o N \ killed G Dom (D 0) o N)
      with hf0
    have hπ0 : 0 ≤ π := measureReal_nonneg
    have hf00 : 0 ≤ f0 := measureReal_nonneg
    have hkilled : (prodBernoulli w).real (killed G Dom (D 0) o N) = π - f0 := by
      have h := measureReal_inter_add_sdiff (μ := prodBernoulli w) (s := poor G Dom (D 0) o N)
        (measurableSet_killed G Dom (D 0) o N) (measure_ne_top _ _)
      rw [Set.inter_eq_right.2 (killed_subset_poor G Dom (D 0) o N)] at h
      linarith
    have hcompl : (prodBernoulli w).real (killed G Dom (D 0) o N)ᶜ = 1 - π + f0 := by
      rw [measureReal_compl (measurableSet_killed G Dom (D 0) o N), probReal_univ, hkilled]
      ring
    have hrest : ∑ i ∈ Finset.range L, (prodBernoulli w).real
        (survive G Dom D o N (i + 1) ∩ poor G Dom (D (i + 1)) o N)
          ≤ b * (prodBernoulli w).real (killed G Dom (D 0) o N)ᶜ := by
      rcases Nat.eq_zero_or_pos L with hL | hL
      · subst hL
        simp only [Finset.range_zero, Finset.sum_empty]
        exact mul_nonneg hb0 measureReal_nonneg
      · set R : Finset V := Dom \ D 1 with hR
        have hB : DeterminedBy (killed G Dom (D 0) o N)ᶜ (↑R : Set V) :=
          (determinedBy_killed_rel G o N (hsub 0 (Nat.succ_pos L)) (hnest 0 (by omega))
            (hgateRel 0 (by omega))).compl
        obtain ⟨𝒱, h𝒱⟩ : ∃ 𝒱 : Finset (Finset V), 𝒱 = R.powerset.filter
            (fun T : Finset V => (↑T : Set V) ∈ (killed G Dom (D 0) o N)ᶜ) := ⟨_, rfl⟩
        have hsumB : (prodBernoulli w).real (killed G Dom (D 0) o N)ᶜ =
            ∑ T ∈ 𝒱, (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) := by
          rw [h𝒱]
          convert prodBernoulli_real_eq_sum_localCylinder w R hB using 3
        have hX : ∀ i, MeasurableSet
            (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) := fun i =>
          (measurableSet_survive G Dom (fun j => D (j + 1)) o N i).inter
            (measurableSet_poor G Dom (D (i + 1)) o N)
        have hterm : ∀ i ∈ Finset.range L, (prodBernoulli w).real
            (survive G Dom D o N (i + 1) ∩ poor G Dom (D (i + 1)) o N) =
            ∑ T ∈ 𝒱,
              (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) *
                (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                  (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) := by
          intro i _
          rw [survive_succ, Set.inter_assoc, Set.inter_comm, h𝒱]
          convert prodBernoulli_real_inter_eq_sum_pinW w R (hX i) hB using 3
        have hIH : ∀ T ∈ 𝒱,
            ∑ i ∈ Finset.range L, (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
              (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) ≤ b := by
          intro T _
          refine ih (fun j => D (j + 1)) (pinW w (↑R : Set V) (↑T : Set V))
            (fun i hi => hsub (i + 1) (by omega)) (fun i hi => hnest (i + 1) (by omega))
            (fun i hi => hgateRel (i + 1) (by omega)) ?_
          intro i hi y hy
          have hyD1 : y ∈ D 1 :=
            subset_of_le_of_lt hnest 1 (i + 1) (by omega) (by omega) hy
          have hyR : y ∉ (↑R : Set V) := by
            rw [Finset.mem_coe, hR, Finset.mem_sdiff]
            exact fun h => h.2 hyD1
          rw [pinW_apply_of_not_mem w _ hyR]
          exact hw (i + 1) (by omega) y hy
        calc ∑ i ∈ Finset.range L, (prodBernoulli w).real
                (survive G Dom D o N (i + 1) ∩ poor G Dom (D (i + 1)) o N)
            = ∑ i ∈ Finset.range L, ∑ T ∈ 𝒱,
                (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) *
                  (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                    (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) :=
              Finset.sum_congr rfl hterm
          _ = ∑ T ∈ 𝒱, ∑ i ∈ Finset.range L,
                (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) *
                  (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                    (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) :=
              Finset.sum_comm
          _ = ∑ T ∈ 𝒱,
                (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) *
                  ∑ i ∈ Finset.range L,
                    (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                      (survive G Dom (fun j => D (j + 1)) o N i ∩ poor G Dom (D (i + 1)) o N) := by
              refine Finset.sum_congr rfl fun T _ => ?_
              rw [Finset.mul_sum]
          _ ≤ ∑ T ∈ 𝒱, (prodBernoulli w).real (localCylinder (↑R : Set V) (↑T : Set V)) * b :=
              Finset.sum_le_sum fun T hT =>
                mul_le_mul_of_nonneg_left (hIH T hT) measureReal_nonneg
          _ = b * (prodBernoulli w).real (killed G Dom (D 0) o N)ᶜ := by
              rw [← Finset.sum_mul, hsumB, mul_comm]
    rw [Finset.sum_range_succ', survive_zero, Set.inter_comm, ← Set.sdiff_eq, ← hf0, hcompl] at *
    have h1 : b * (1 - π + f0) ≤ b * (1 - π + (1 - qN) * π) :=
      mul_le_mul_of_nonneg_left (by linarith) hb0
    have h2 : b * (1 - π + (1 - qN) * π) = b - (1 - qN) * π := by
      linear_combination (-π) * hbqN
    linarith

/-- **Pigeonhole over the levels**: some level `i < L` has
`P(A ∩ level i poor) ≤ 1 / (L · q_N)` whenever `A` is contained in the complement of every
killing event. -/
theorem exists_level_real_inter_poor_le (Dom : Finset V) (o : V) (N Δ : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ}
    (hL : 0 < L) (D : ℕ → Finset V) (w : V → unitInterval) (hsub : ∀ i < L, D i ⊆ Dom)
    (hnest : ∀ i, i + 1 < L → D (i + 1) ⊆ D i)
    (hgate : ∀ i, i + 1 < L → ∀ x ∉ D i, ∀ y ∈ D i, G.Adj x y → y ∉ D (i + 1))
    (hw : ∀ i < L, ∀ y ∈ D i, (w y : ℝ) ≤ q) {A : Set (SiteConfig V)}
    (hA : ∀ i < L, A ⊆ (killed G Dom (D i) o N)ᶜ) :
    ∃ i < L, (prodBernoulli w).real (A ∩ poor G Dom (D i) o N) ≤
      1 / ((L : ℝ) * (1 - q) ^ (Δ * N)) := by
  have hqN0 : 0 < (1 - q) ^ (Δ * N) := pow_pos (by linarith) _
  have hsum := sum_real_survive_inter_poor_le G Dom o N Δ hq0 hq1 hdeg L D w hsub hnest hgate hw
  have hle : ∑ i ∈ Finset.range L, (prodBernoulli w).real (A ∩ poor G Dom (D i) o N) ≤
      ∑ i ∈ Finset.range L,
        (prodBernoulli w).real (survive G Dom D o N i ∩ poor G Dom (D i) o N) :=
    Finset.sum_le_sum fun i hi =>
      measureReal_mono (Set.inter_subset_inter_left _
        (subset_survive_of_forall G hA (Finset.mem_range.1 hi))) (measure_ne_top _ _)
  have hbound : (1 - (1 - q) ^ (Δ * N)) / (1 - q) ^ (Δ * N) ≤
      ∑ _i ∈ Finset.range L, 1 / ((L : ℝ) * (1 - q) ^ (Δ * N)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hLpos : (0 : ℝ) < L := Nat.cast_pos.2 hL
    have hcancel : (L : ℝ) * (1 / ((L : ℝ) * (1 - q) ^ (Δ * N))) = 1 / (1 - q) ^ (Δ * N) := by
      field_simp
    rw [hcancel]
    exact (div_le_div_iff_of_pos_right hqN0).2 (by linarith)
  obtain ⟨i, hi, hile⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.2 hL⟩
    (le_trans hle (le_trans hsum hbound))
  exact ⟨i, Finset.mem_range.1 hi, hile⟩

/-- Relative-gate form of `exists_level_real_inter_poor_le`. -/
theorem exists_level_real_inter_poor_le_rel (Dom : Finset V) (o : V) (N Δ : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ}
    (hL : 0 < L) (D : ℕ → Finset V) (w : V → unitInterval) (hsub : ∀ i < L, D i ⊆ Dom)
    (hnest : ∀ i, i + 1 < L → D (i + 1) ⊆ D i)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ D i →
      ∀ y ∈ D i, G.Adj x y → y ∉ D (i + 1))
    (hw : ∀ i < L, ∀ y ∈ D i, (w y : ℝ) ≤ q) {A : Set (SiteConfig V)}
    (hA : ∀ i < L, A ⊆ (killed G Dom (D i) o N)ᶜ) :
    ∃ i < L, (prodBernoulli w).real (A ∩ poor G Dom (D i) o N) ≤
      1 / ((L : ℝ) * (1 - q) ^ (Δ * N)) := by
  have hqN0 : 0 < (1 - q) ^ (Δ * N) := pow_pos (by linarith) _
  have hsum := sum_real_survive_inter_poor_le_rel G Dom o N Δ hq0 hq1 hdeg L D w hsub
    hnest hgateRel hw
  have hle : ∑ i ∈ Finset.range L, (prodBernoulli w).real (A ∩ poor G Dom (D i) o N) ≤
      ∑ i ∈ Finset.range L,
        (prodBernoulli w).real (survive G Dom D o N i ∩ poor G Dom (D i) o N) :=
    Finset.sum_le_sum fun i hi =>
      measureReal_mono (Set.inter_subset_inter_left _
        (subset_survive_of_forall G hA (Finset.mem_range.1 hi))) (measure_ne_top _ _)
  have hbound : (1 - (1 - q) ^ (Δ * N)) / (1 - q) ^ (Δ * N) ≤
      ∑ _i ∈ Finset.range L, 1 / ((L : ℝ) * (1 - q) ^ (Δ * N)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hLpos : (0 : ℝ) < L := Nat.cast_pos.2 hL
    have hcancel : (L : ℝ) * (1 / ((L : ℝ) * (1 - q) ^ (Δ * N))) =
        1 / (1 - q) ^ (Δ * N) := by
      field_simp
    rw [hcancel]
    exact (div_le_div_iff_of_pos_right hqN0).2 (by linarith)
  obtain ⟨i, hi, hile⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.2 hL⟩
    (le_trans hle (le_trans hsum hbound))
  exact ⟨i, Finset.mem_range.1 hi, hile⟩

/-- **Many contacts at one level.**  If the source reaches `B ⊆ D i` (for all levels) with
probability more than `1 - δ` and `L · δ · q_N ≥ 1`, some level has at least `N` contacts with
probability more than `1 - 2δ`. -/
theorem exists_level_real_poor_compl_gt (Dom : Finset V) (o : V) (N Δ : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ}
    (hL : 0 < L) (D : ℕ → Finset V) (w : V → unitInterval) (hsub : ∀ i < L, D i ⊆ Dom)
    (hnest : ∀ i, i + 1 < L → D (i + 1) ⊆ D i)
    (hgate : ∀ i, i + 1 < L → ∀ x ∉ D i, ∀ y ∈ D i, G.Adj x y → y ∉ D (i + 1))
    (hw : ∀ i < L, ∀ y ∈ D i, (w y : ℝ) ≤ q) (ho : ∀ i < L, o ∉ D i) {B : Set V}
    (hB : ∀ i < L, B ⊆ ↑(D i)) {δ : ℝ}
    (hLδ : 1 ≤ (L : ℝ) * δ * (1 - q) ^ (Δ * N))
    (hsrc : 1 - δ < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    ∃ i < L, 1 - 2 * δ < (prodBernoulli w).real (poor G Dom (D i) o N)ᶜ := by
  have hqN0 : 0 < (1 - q) ^ (Δ * N) := pow_pos (by linarith) _
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.2 hL
  obtain ⟨i, hi, hile⟩ := exists_level_real_inter_poor_le G Dom o N Δ hq0 hq1 hdeg hL D w hsub
    hnest hgate hw (A := connWithinSet G (↑Dom : Set V) o B)
    (fun j hj => Set.subset_compl_comm.1 (killed_subset_compl_connWithinSet G Dom (D j) (ho j hj) N (hB j hj)))
  refine ⟨i, hi, ?_⟩
  have hδ' : 1 / ((L : ℝ) * (1 - q) ^ (Δ * N)) ≤ δ := by
    rw [div_le_iff₀ (mul_pos hLpos hqN0)]
    linarith [hLδ]
  have hsplit := measureReal_inter_add_sdiff (μ := prodBernoulli w)
    (s := connWithinSet G (↑Dom : Set V) o B) (measurableSet_poor G Dom (D i) o N)
    (measure_ne_top _ _)
  have hmono : (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B \ poor G Dom (D i) o N)
      ≤ (prodBernoulli w).real (poor G Dom (D i) o N)ᶜ :=
    measureReal_mono (fun ω hω => hω.2) (measure_ne_top _ _)
  linarith

/-- Relative-gate form of `exists_level_real_poor_compl_gt`. -/
theorem exists_level_real_poor_compl_gt_rel (Dom : Finset V) (o : V) (N Δ : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ}
    (hL : 0 < L) (D : ℕ → Finset V) (w : V → unitInterval) (hsub : ∀ i < L, D i ⊆ Dom)
    (hnest : ∀ i, i + 1 < L → D (i + 1) ⊆ D i)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ D i →
      ∀ y ∈ D i, G.Adj x y → y ∉ D (i + 1))
    (hw : ∀ i < L, ∀ y ∈ D i, (w y : ℝ) ≤ q) (ho : ∀ i < L, o ∉ D i) {B : Set V}
    (hB : ∀ i < L, B ⊆ ↑(D i)) {δ : ℝ}
    (hLδ : 1 ≤ (L : ℝ) * δ * (1 - q) ^ (Δ * N))
    (hsrc : 1 - δ < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    ∃ i < L, 1 - 2 * δ < (prodBernoulli w).real (poor G Dom (D i) o N)ᶜ := by
  have hqN0 : 0 < (1 - q) ^ (Δ * N) := pow_pos (by linarith) _
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.2 hL
  obtain ⟨i, hi, hile⟩ := exists_level_real_inter_poor_le_rel G Dom o N Δ hq0 hq1 hdeg hL
    D w hsub hnest hgateRel hw (A := connWithinSet G (↑Dom : Set V) o B)
    (fun j hj => Set.subset_compl_comm.1
      (killed_subset_compl_connWithinSet G Dom (D j) (ho j hj) N (hB j hj)))
  refine ⟨i, hi, ?_⟩
  have hδ' : 1 / ((L : ℝ) * (1 - q) ^ (Δ * N)) ≤ δ := by
    rw [div_le_iff₀ (mul_pos hLpos hqN0)]
    linarith [hLδ]
  have hsplit := measureReal_inter_add_sdiff (μ := prodBernoulli w)
    (s := connWithinSet G (↑Dom : Set V) o B) (measurableSet_poor G Dom (D i) o N)
    (measure_ne_top _ _)
  have hmono : (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B \ poor G Dom (D i) o N)
      ≤ (prodBernoulli w).real (poor G Dom (D i) o N)ᶜ :=
    measureReal_mono (fun ω hω => hω.2) (measure_ne_top _ _)
  linarith

end ManyContacts

/-! ## The relay step: from the source to a reliable relay to the target

At a fixed level with boxes `Int ⊆ O ⊆ D ⊆ Dom` and shell `S = O \ Int`, a relay `u ∈ S` is
*reliable* for the pattern `ω ∩ S` when, with the shell pinned to that pattern, `u` is joined to
the target inside `O` with probability more than `1 - δ`.  The source reaches `u` by a path
avoiding the interior `Int`; with the shell pinned, that event is decided by the coordinates
outside `Int` and the relay event by those inside, so the decisive lemma applies pattern by
pattern.  No gluing inequality enters. -/

section Relay

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

open scoped Classical

/-- The relay event: `u` is joined to the target `T` by an open path inside `O`. -/
def toTarget (O : Finset V) (T : Set V) (u : V) : Set (SiteConfig V) :=
  connWithinSet G (↑O : Set V) u T

/-- The source event: `o` is joined to `u` by an open path inside `Dom` avoiding `Int`. -/
def fromSource (Dom Int : Finset V) (o u : V) : Set (SiteConfig V) :=
  connWithin G (↑(Dom \ Int) : Set V) o u

/-- `u` is a reliable relay for the shell pattern of `ω`. -/
def reliable (w : V → unitInterval) (S O : Finset V) (T : Set V) (δ : ℝ) (ω : SiteConfig V)
    (u : V) : Prop :=
  1 - δ < pinnedProb w (↑S : Set V) (fun i => i ∈ ω) (toTarget G O T u)

/-- The source reaches some reliable relay of the shell, avoiding the interior. -/
def reachRelay (w : V → unitInterval) (Dom O Int : Finset V) (o : V) (T : Set V) (δ : ℝ) :
    Set (SiteConfig V) :=
  ⋃ u ∈ O \ Int, {ω | reliable G w (O \ Int) O T δ ω u} ∩ fromSource G Dom Int o u

/-- The source reaches some reliable relay of the shell, which reaches the target inside `O`. -/
def reachRelayTarget (w : V → unitInterval) (Dom O Int : Finset V) (o : V) (T : Set V) (δ : ℝ) :
    Set (SiteConfig V) :=
  ⋃ u ∈ O \ Int, {ω | reliable G w (O \ Int) O T δ ω u} ∩
    (fromSource G Dom Int o u ∩ toTarget G O T u)

theorem determinedBy_toTarget (O : Finset V) (T : Set V) (u : V) :
    DeterminedBy (toTarget G O T u) (↑O : Set V) :=
  determinedBy_connWithinSet G _ u T

theorem measurableSet_toTarget (O : Finset V) (T : Set V) (u : V) :
    MeasurableSet (toTarget G O T u) :=
  (determinedBy_toTarget G O T u).measurableSet_of_finset

theorem determinedBy_fromSource (Dom Int : Finset V) (o u : V) :
    DeterminedBy (fromSource G Dom Int o u) (↑(Dom \ Int) : Set V) :=
  determinedBy_connWithin G _ o u

theorem measurableSet_fromSource (Dom Int : Finset V) (o u : V) :
    MeasurableSet (fromSource G Dom Int o u) :=
  (determinedBy_fromSource G Dom Int o u).measurableSet_of_finset

theorem determinedBy_reliable (w : V → unitInterval) (S O : Finset V) (T : Set V) (δ : ℝ)
    (u : V) : DeterminedBy {ω : SiteConfig V | reliable G w S O T δ ω u} (↑S : Set V) :=
  determinedBy_setOf_lt_pinnedProb w _ _ _

theorem reliable_congr (w : V → unitInterval) (S O : Finset V) (T : Set V) (δ : ℝ)
    {ω ω' : SiteConfig V} (h : ω ∩ (↑S : Set V) = ω' ∩ (↑S : Set V)) (u : V) :
    reliable G w S O T δ ω u ↔ reliable G w S O T δ ω' u := by
  simp only [reliable, pinnedProb_congr_pattern w _ (forall_iff_of_inter_eq h)]

/-- A source-to-relay path followed by a relay-to-target path joins the source to the target
inside `Dom`. -/
theorem fromSource_inter_toTarget_subset {Dom O Int : Finset V} (hODom : O ⊆ Dom) (o : V)
    (T : Set V) (u : V) :
    fromSource G Dom Int o u ∩ toTarget G O T u ⊆ connWithinSet G (↑Dom : Set V) o T := by
  rintro ω ⟨h1, h2⟩
  obtain ⟨t, ht, h2⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 h2
  refine (mem_connWithinSet_iff _ _ _ _ _).2 ⟨t, ht, ?_⟩
  refine connWithin_mono_set G ?_ o t (connWithin_trans G h1 h2)
  intro i hi
  rcases hi with hi | hi
  · exact Finset.mem_coe.2 (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).1
  · exact Finset.mem_coe.2 (hODom (Finset.mem_coe.1 hi))

theorem reachRelayTarget_subset {Dom O Int : Finset V} (hODom : O ⊆ Dom) (w : V → unitInterval)
    (o : V) (T : Set V) (δ : ℝ) :
    reachRelayTarget G w Dom O Int o T δ ⊆ connWithinSet G (↑Dom : Set V) o T := by
  refine Set.iUnion₂_subset fun u _ => ?_
  exact Set.inter_subset_right.trans (fromSource_inter_toTarget_subset G hODom o T u)

theorem determinedBy_reachRelay (w : V → unitInterval) (Dom O Int : Finset V) (o : V) (T : Set V)
    (δ : ℝ) (hODom : O ⊆ Dom) :
    DeterminedBy (reachRelay G w Dom O Int o T δ) (↑Dom : Set V) := by
  refine DeterminedBy.iUnion fun u => DeterminedBy.iUnion fun _ => DeterminedBy.inter ?_ ?_
  · refine (determinedBy_reliable G w _ O T δ u).mono fun i hi => ?_
    exact Finset.mem_coe.2 (hODom (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).1)
  · exact (determinedBy_fromSource G Dom Int o u).mono fun i hi =>
      Finset.mem_coe.2 (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).1

theorem determinedBy_reachRelayTarget (w : V → unitInterval) (Dom O Int : Finset V) (o : V)
    (T : Set V) (δ : ℝ) (hODom : O ⊆ Dom) :
    DeterminedBy (reachRelayTarget G w Dom O Int o T δ) (↑Dom : Set V) := by
  refine DeterminedBy.iUnion fun u => DeterminedBy.iUnion fun _ =>
    DeterminedBy.inter ?_ (DeterminedBy.inter ?_ ?_)
  · refine (determinedBy_reliable G w _ O T δ u).mono fun i hi => ?_
    exact Finset.mem_coe.2 (hODom (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).1)
  · exact (determinedBy_fromSource G Dom Int o u).mono fun i hi =>
      Finset.mem_coe.2 (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).1
  · exact (determinedBy_toTarget G O T u).mono fun i hi => Finset.mem_coe.2 (hODom hi)

/-- **The relay step, pattern by pattern.**  With the shell `S = O \ Int` pinned to a pattern `ξ`,
the events `fromSource o u` are determined by the coordinates outside `Int` and the events
`toTarget u` by those inside `Int`, so the decisive lemma gives

`P^ξ(⋃_{u reliable for ξ} fromSource ∩ toTarget) ≥ P^ξ(⋃_{u reliable for ξ} fromSource) · (1 - δ)`. -/
theorem pinnedProb_reachRelayTarget_ge (w : V → unitInterval) (Dom O Int : Finset V) (o : V)
    (T : Set V) (δ : ℝ) (ξ : Set V) :
    pinnedProb w (↑(O \ Int) : Set V) (fun i => i ∈ ξ)
        (⋃ u ∈ (O \ Int).filter (fun u => reliable G w (O \ Int) O T δ ξ u),
          fromSource G Dom Int o u) * (1 - δ) ≤
      pinnedProb w (↑(O \ Int) : Set V) (fun i => i ∈ ξ)
        (⋃ u ∈ (O \ Int).filter (fun u => reliable G w (O \ Int) O T δ ξ u),
          fromSource G Dom Int o u ∩ toTarget G O T u) := by
  set S : Finset V := O \ Int with hS
  set val : V → Prop := fun i => i ∈ ξ with hval
  simp only [pinnedProb, Set.preimage_iUnion₂, Set.preimage_inter]
  refine prodBernoulli_real_biUnion_inter_ge w Int _ (fun u => substitute (↑S : Set V) val ⁻¹'
    fromSource G Dom Int o u) (fun u => substitute (↑S : Set V) val ⁻¹' toTarget G O T u)
    ?_ ?_ ?_ ?_ ?_
  · intro u _
    refine (determinedBy_substitute_preimage_of_determinedBy (determinedBy_fromSource G Dom Int o u)
      _ _).mono fun i hi => ?_
    have hi1 := Finset.mem_sdiff.1 (Finset.mem_coe.1 hi.1)
    exact fun hiI => hi1.2 (Finset.mem_coe.1 hiI)
  · intro u _
    refine (determinedBy_substitute_preimage_of_determinedBy (determinedBy_toTarget G O T u)
      _ _).mono fun i hi => ?_
    have hiO := Finset.mem_coe.1 hi.1
    have hiS := hi.2
    rw [Finset.mem_coe, hS, Finset.mem_sdiff] at hiS
    by_contra hiI
    exact hiS ⟨hiO, fun h => hiI (Finset.mem_coe.2 h)⟩
  · intro u _
    exact measurableSet_substitute_preimage _ _ (measurableSet_fromSource G Dom Int o u)
  · intro u _
    exact measurableSet_substitute_preimage _ _ (measurableSet_toTarget G O T u)
  · intro u hu
    have hrel : reliable G w S O T δ ξ u := (Finset.mem_filter.1 hu).2
    exact le_of_lt hrel

/-- On the cylinder of a pattern, the relay events coincide with their pattern-frozen forms. -/
theorem reachRelayTarget_inter_localCylinder (w : V → unitInterval) (Dom O Int : Finset V) (o : V)
    (T : Set V) (δ : ℝ) (ξ : Set V) :
    reachRelayTarget G w Dom O Int o T δ ∩ localCylinder (↑(O \ Int) : Set V) ξ =
      (⋃ u ∈ (O \ Int).filter (fun u => reliable G w (O \ Int) O T δ ξ u),
        fromSource G Dom Int o u ∩ toTarget G O T u) ∩ localCylinder (↑(O \ Int) : Set V) ξ := by
  ext ω
  simp only [reachRelayTarget, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq,
    Finset.mem_filter, exists_prop]
  constructor
  · rintro ⟨⟨u, hu, hrel, hω⟩, hcyl⟩
    refine ⟨⟨u, ⟨hu, ?_⟩, hω⟩, hcyl⟩
    have h : ω ∩ (↑(O \ Int) : Set V) = ξ ∩ (↑(O \ Int) : Set V) :=
      inter_eq_of_forall_iff fun i hi => hcyl i hi
    exact (reliable_congr G w _ O T δ h u).1 hrel
  · rintro ⟨⟨u, ⟨hu, hrel⟩, hω⟩, hcyl⟩
    refine ⟨⟨u, hu, ?_, hω⟩, hcyl⟩
    have h : ω ∩ (↑(O \ Int) : Set V) = ξ ∩ (↑(O \ Int) : Set V) :=
      inter_eq_of_forall_iff fun i hi => hcyl i hi
    exact (reliable_congr G w _ O T δ h u).2 hrel

theorem reachRelay_inter_localCylinder (w : V → unitInterval) (Dom O Int : Finset V) (o : V)
    (T : Set V) (δ : ℝ) (ξ : Set V) :
    reachRelay G w Dom O Int o T δ ∩ localCylinder (↑(O \ Int) : Set V) ξ =
      (⋃ u ∈ (O \ Int).filter (fun u => reliable G w (O \ Int) O T δ ξ u),
        fromSource G Dom Int o u) ∩ localCylinder (↑(O \ Int) : Set V) ξ := by
  ext ω
  simp only [reachRelay, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq,
    Finset.mem_filter, exists_prop]
  constructor
  · rintro ⟨⟨u, hu, hrel, hω⟩, hcyl⟩
    refine ⟨⟨u, ⟨hu, ?_⟩, hω⟩, hcyl⟩
    have h : ω ∩ (↑(O \ Int) : Set V) = ξ ∩ (↑(O \ Int) : Set V) :=
      inter_eq_of_forall_iff fun i hi => hcyl i hi
    exact (reliable_congr G w _ O T δ h u).1 hrel
  · rintro ⟨⟨u, ⟨hu, hrel⟩, hω⟩, hcyl⟩
    refine ⟨⟨u, hu, ?_, hω⟩, hcyl⟩
    have h : ω ∩ (↑(O \ Int) : Set V) = ξ ∩ (↑(O \ Int) : Set V) :=
      inter_eq_of_forall_iff fun i hi => hcyl i hi
    exact (reliable_congr G w _ O T δ h u).2 hrel

/-- **The relay step, averaged over the shell patterns.**  Reaching a reliable relay and, from it,
the target has probability at least `(1 - δ)` times the probability of reaching a reliable relay.
This is the place where the manuscript invokes the gluing inequality; here the decisive lemma does
the work, pattern by pattern, and the patterns are summed. -/
theorem real_reachRelayTarget_ge (w : V → unitInterval) {Dom O Int : Finset V} (hODom : O ⊆ Dom)
    (o : V) (T : Set V) (δ : ℝ) :
    (prodBernoulli w).real (reachRelay G w Dom O Int o T δ) * (1 - δ) ≤
      (prodBernoulli w).real (reachRelayTarget G w Dom O Int o T δ) := by
  have hXm : MeasurableSet (reachRelay G w Dom O Int o T δ) :=
    (determinedBy_reachRelay G w Dom O Int o T δ hODom).measurableSet_of_finset
  have hYm : MeasurableSet (reachRelayTarget G w Dom O Int o T δ) :=
    (determinedBy_reachRelayTarget G w Dom O Int o T δ hODom).measurableSet_of_finset
  rw [real_eq_sum_inter_localCylinder w (O \ Int) hXm,
    real_eq_sum_inter_localCylinder w (O \ Int) hYm, Finset.sum_mul]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [reachRelay_inter_localCylinder, reachRelayTarget_inter_localCylinder,
    real_inter_localCylinder_eq_mul_pinnedProb w (O \ Int) _
      (Finset.measurableSet_biUnion _ fun u _ => measurableSet_fromSource G Dom Int o u),
    real_inter_localCylinder_eq_mul_pinnedProb w (O \ Int) _
      (Finset.measurableSet_biUnion _ fun u _ =>
        (measurableSet_fromSource G Dom Int o u).inter (measurableSet_toTarget G O T u)),
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (pinnedProb_reachRelayTarget_ge G w Dom O Int o T δ _)
    measureReal_nonneg

end Relay

/-! ## Finite pinned gluing with a confined target set

The manuscript-style `D` interface below needs the pinned-site gluing input after the shell has
been fixed.  The input is stated for a single target vertex on `Fin n`; the next lemmas transport
it to an arbitrary finite vertex type, replace the target vertex by a finite target set using one
auxiliary root, and finally identify connections in the induced graph on a finite domain with
connections confined to that domain. -/

section ConfinedGluing

variable {V : Type*}

theorem mem_siteConn_restrict_equiv [Fintype V] (G : SimpleGraph V) (w : V → unitInterval)
    (e : V ≃ Fin (Fintype.card V)) (x y : V) (ω : SiteConfig V) :
    restrictSite e.symm ω ∈ siteConn (G.comap e.symm) (e x) (e y) ↔ ω ∈ siteConn G x y := by
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨by simpa using hx, by simpa using reachable_map_of_restrictSite G ω hxy⟩
  · rintro ⟨hx, hxy⟩
    refine ⟨by simpa using hx, ?_⟩
    let φ : openSiteGraph G ω →g
        openSiteGraph (G.comap e.symm) (restrictSite e.symm ω) :=
      { toFun := e
        map_rel' := fun {a b} hab => by
          rw [openSiteGraph_adj_iff'] at hab ⊢
          exact ⟨by simpa using hab.1, by simpa using hab.2.1, by simpa using hab.2.2⟩ }
    change (openSiteGraph (G.comap e.symm) (restrictSite e.symm ω)).Reachable (φ x) (φ y)
    exact hxy.map φ

theorem siteBernoulli_real_siteConn_equiv [Fintype V] (G : SimpleGraph V)
    (w : V → unitInterval) (e : V ≃ Fin (Fintype.card V)) (x y : V) :
    (siteBernoulli (w ∘ e.symm)).real (siteConn (G.comap e.symm) (e x) (e y)) =
      (siteBernoulli w).real (siteConn G x y) := by
  rw [← siteBernoulli_real_preimage_restrictSite w e.symm.injective
    (measurableSet_siteConn (G.comap e.symm) (e x) (e y))]
  congr 1
  ext ω
  exact mem_siteConn_restrict_equiv G w e x y ω

theorem siteBernoulli_real_siteConnSet_equiv [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : V → unitInterval) (e : V ≃ Fin (Fintype.card V))
    (x : V) (A : Finset V) :
    (siteBernoulli (w ∘ e.symm)).real
        (siteConnSet (G.comap e.symm) (e x) ↑(A.map e.toEmbedding)) =
      (siteBernoulli w).real (siteConnSet G x ↑A) := by
  rw [← siteBernoulli_real_preimage_restrictSite w e.symm.injective
    (by exact Finset.measurableSet_biUnion _ fun a _ => measurableSet_siteConn _ _ _)]
  congr 1
  ext ω
  simp only [Set.mem_preimage, siteConnSet, Set.mem_iUnion, exists_prop, Finset.mem_coe,
    Finset.mem_map_equiv]
  constructor
  · rintro ⟨a, ha, hconn⟩
    refine ⟨e.symm a, ha, ?_⟩
    simpa using (mem_siteConn_restrict_equiv G w e x (e.symm a) ω).1 (by simpa using hconn)
  · rintro ⟨a, ha, hconn⟩
    refine ⟨e a, by simpa using ha, ?_⟩
    simpa using (mem_siteConn_restrict_equiv G w e x a ω).2 hconn

theorem siteConn_comm (G : SimpleGraph V) (x y : V) : siteConn G x y = siteConn G y x := by
  ext ω
  constructor
  · rintro ⟨hx, hxy⟩
    exact ⟨mem_of_mem_siteCluster G ω ⟨hx, hxy⟩, hxy.symm⟩
  · rintro ⟨hy, hyx⟩
    exact ⟨mem_of_mem_siteCluster G ω ⟨hy, hyx⟩, hyx.symm⟩

theorem siteConnSet_eq_biUnion_comm [DecidableEq V] (G : SimpleGraph V) (x : V)
    (T : Finset V) : siteConnSet G x ↑T = ⋃ t ∈ T, siteConn G t x := by
  ext ω
  simp only [siteConnSet, Set.mem_iUnion, exists_prop, Finset.mem_coe]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, by rwa [siteConn_comm]⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, by rwa [siteConn_comm]⟩

theorem pinnedSiteGluing_target_fin (hgl : PinnedSiteGluing) (n : ℕ)
    (G : SimpleGraph (Fin n)) (w : Fin n → unitInterval) (A : Finset (Fin n))
    (hA : A.Nonempty) (T : Finset (Fin n)) (o : Fin n)
    (hwo : w o = 1) (hAw : ∀ a ∈ A, w a = 1) :
    (siteBernoulli w).real (siteConnSet G o ↑A) *
        A.inf' hA (fun a => (siteBernoulli w).real (siteConnSet G a ↑T)) ≤
      (siteBernoulli w).real (siteConnSet G o ↑T) := by
  classical
  let H := rootGraph G T
  let w' := rootWeight w
  let A' := A.map (rootEmb n)
  have hA' : A'.Nonempty := hA.map
  have hkey := hgl (n + 1) H w' A' hA' o.castSucc (Fin.last n)
    (by simp [w', hwo]) (by simp [w']) (by
      intro a ha
      obtain ⟨a, haA, rfl⟩ := Finset.mem_map.1 ha
      simp [w', hAw a haA])
  have hsource : (siteBernoulli w).real (siteConnSet G o ↑A) ≤
      (siteBernoulli w').real (siteConnSet H o.castSucc ↑A') := by
    have hsub : restrictSite Fin.castSucc ⁻¹' (siteConnSet G o ↑A) ⊆
        siteConnSet H o.castSucc ↑A' := by
      intro ω hω
      obtain ⟨a, ha, hconn⟩ := Set.mem_iUnion₂.1 hω
      refine Set.mem_iUnion₂.2 ⟨a.castSucc, Finset.mem_map.2 ⟨a, Finset.mem_coe.1 ha, rfl⟩, ?_⟩
      exact ⟨hconn.1, reachable_castSucc_of_reachable G T ω hconn.2⟩
    calc
      (siteBernoulli w).real (siteConnSet G o ↑A) =
          (siteBernoulli w').real (restrictSite Fin.castSucc ⁻¹' (siteConnSet G o ↑A)) := by
            rw [siteBernoulli_real_preimage_restrictSite w' (Fin.castSucc_injective n)
              (by exact Finset.measurableSet_biUnion _ fun a _ => measurableSet_siteConn _ _ _)]
            simpa [w'] using (congrArg (fun f : Fin n → unitInterval =>
              (siteBernoulli f).real (siteConnSet G o ↑A)) (rootWeight_comp_castSucc w)).symm
      _ ≤ (siteBernoulli w').real (siteConnSet H o.castSucc ↑A') :=
        measureReal_mono hsub (measure_ne_top _ _)
  have hrelay : A.inf' hA (fun a => (siteBernoulli w).real (siteConnSet G a ↑T)) =
      A'.inf' hA' (fun a => (siteBernoulli w').real (siteConn H a (Fin.last n))) := by
    apply le_antisymm
    · refine Finset.le_inf' hA' _ ?_
      intro a' ha'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 ha'
      calc
        A.inf' hA (fun a => (siteBernoulli w).real (siteConnSet G a ↑T)) ≤
            (siteBernoulli w).real (siteConnSet G a ↑T) := Finset.inf'_le _ ha
        _ = (siteBernoulli w').real (siteConn H a.castSucc (Fin.last n)) := by
          have h := measureReal_root_biUnion G T w ({a} : Set (Fin n))
          simpa [H, w', siteConnSet, siteConn_comm] using h.symm
    · refine Finset.le_inf' hA _ ?_
      intro a ha
      refine le_trans (Finset.inf'_le _ (Finset.mem_map.2 ⟨a, ha, rfl⟩)) ?_
      have h := measureReal_root_biUnion G T w ({a} : Set (Fin n))
      simpa [H, w', siteConnSet, siteConn_comm] using h.le
  have htarget : (siteBernoulli w').real (siteConn H o.castSucc (Fin.last n)) =
      (siteBernoulli w).real (siteConnSet G o ↑T) := by
    have h := measureReal_root_biUnion G T w ({o} : Set (Fin n))
    simpa [H, w', siteConnSet, siteConn_comm] using h
  rw [← htarget, hrelay]
  exact le_trans (mul_le_mul_of_nonneg_right hsource (Finset.le_inf' hA' _ fun a _ => measureReal_nonneg)) hkey

theorem pinnedSiteGluing_target_fintype [Fintype V] [DecidableEq V]
    (hgl : PinnedSiteGluing) (G : SimpleGraph V) (w : V → unitInterval)
    (A : Finset V) (hA : A.Nonempty) (T : Finset V) (o : V)
    (hwo : w o = 1) (hAw : ∀ a ∈ A, w a = 1) :
    (siteBernoulli w).real (siteConnSet G o ↑A) *
        A.inf' hA (fun a => (siteBernoulli w).real (siteConnSet G a ↑T)) ≤
      (siteBernoulli w).real (siteConnSet G o ↑T) := by
  classical
  let e := Fintype.equivFin V
  let G' := G.comap e.symm
  let w' := w ∘ e.symm
  let A' := A.map e.toEmbedding
  let T' := T.map e.toEmbedding
  have hA' : A'.Nonempty := hA.map
  have hkey := pinnedSiteGluing_target_fin hgl (Fintype.card V) G' w' A' hA' T' (e o)
    (by simp [w', hwo]) (by
      intro a ha
      obtain ⟨a, haA, rfl⟩ := Finset.mem_map.1 ha
      simp [w', hAw a haA])
  have hsource := siteBernoulli_real_siteConnSet_equiv G w e o A
  have htarget := siteBernoulli_real_siteConnSet_equiv G w e o T
  have hrelay : A'.inf' hA' (fun a => (siteBernoulli w').real (siteConnSet G' a ↑T')) =
      A.inf' hA (fun a => (siteBernoulli w).real (siteConnSet G a ↑T)) := by
    apply le_antisymm
    · refine Finset.le_inf' hA _ ?_
      intro a ha
      refine le_trans (Finset.inf'_le _ (Finset.mem_map.2 ⟨a, ha, rfl⟩)) ?_
      simpa [G', w', T'] using (siteBernoulli_real_siteConnSet_equiv G w e a T).le
    · refine Finset.le_inf' hA' _ ?_
      intro a' ha'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 ha'
      refine le_trans (Finset.inf'_le _ ha) ?_
      simpa [G', w', T'] using (siteBernoulli_real_siteConnSet_equiv G w e a T).symm.le
  calc
    (siteBernoulli w).real (siteConnSet G o ↑A) *
          A.inf' hA (fun a => (siteBernoulli w).real (siteConnSet G a ↑T)) =
        (siteBernoulli w').real (siteConnSet G' (e o) ↑A') *
          A'.inf' hA' (fun a => (siteBernoulli w').real (siteConnSet G' a ↑T')) := by
            rw [hsource, hrelay]
    _ ≤ (siteBernoulli w').real (siteConnSet G' (e o) ↑T') := hkey
    _ = (siteBernoulli w).real (siteConnSet G o ↑T) := htarget

theorem reachable_induce {S : Set V} (G : SimpleGraph V) (ω : SiteConfig V) :
    ∀ {x y : V}, (openSiteGraph G (ω ∩ S)).Reachable x y → (hx : x ∈ S) → (hy : y ∈ S) →
      (openSiteGraph (G.comap (Subtype.val : S → V))
        (restrictSite Subtype.val ω)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro x y hxy hx hy
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c _ hac _ ih =>
    obtain ⟨hGac, haω, hcω⟩ := (openSiteGraph_adj_iff' G (ω ∩ S) a c).1 hac
    refine (SimpleGraph.Adj.reachable ?_).trans (ih hcω.2 hy)
    exact (openSiteGraph_adj_iff' (G.comap (Subtype.val : S → V)) _ ⟨a, haω.2⟩
      ⟨c, hcω.2⟩).2 ⟨SimpleGraph.comap_adj.2 hGac, haω.1, hcω.1⟩

theorem mem_siteConn_restrict_subtype_iff (G : SimpleGraph V) (D : Finset V)
    (x y : V) (hx : x ∈ D) (hy : y ∈ D) (ω : SiteConfig V) :
    restrictSite (Subtype.val : (↑D : Set V) → V) ω ∈
        siteConn (G.comap (Subtype.val : (↑D : Set V) → V)) ⟨x, Finset.mem_coe.2 hx⟩
          ⟨y, Finset.mem_coe.2 hy⟩ ↔
      ω ∈ connWithin G (↑D : Set V) x y := by
  constructor
  · rintro ⟨hxopen, hxy⟩
    refine ⟨⟨by simpa using hxopen, Finset.mem_coe.2 hx⟩, ?_⟩
    have heq : restrictSite (Subtype.val : (↑D : Set V) → V) (ω ∩ (↑D : Set V)) =
        restrictSite Subtype.val ω := by
      ext a
      simp only [restrictSite, Set.mem_preimage, Set.mem_inter_iff]
      exact and_iff_left a.property
    rw [← heq] at hxy
    exact reachable_map_of_restrictSite G (ω ∩ (↑D : Set V)) hxy
  · rintro ⟨hxopen, hxy⟩
    have hy' : y ∈ (↑D : Set V) :=
      (mem_of_mem_siteCluster G (ω ∩ (↑D : Set V)) ⟨hxopen, hxy⟩).2
    refine ⟨by simpa using hxopen.1, ?_⟩
    exact reachable_induce G ω hxy hxopen.2 hy'

theorem siteBernoulli_real_connWithinSet_subtype [DecidableEq V] (G : SimpleGraph V)
    (w : V → unitInterval) (D A : Finset V) (hAD : A ⊆ D) (x : V) (hx : x ∈ D) :
    let AD : Finset (↑D : Set V) := D.attach.filter fun a => (a : V) ∈ A
    (siteBernoulli (w ∘ (Subtype.val : (↑D : Set V) → V))).real
        (siteConnSet (G.comap (Subtype.val : (↑D : Set V) → V))
          ⟨x, Finset.mem_coe.2 hx⟩ ↑AD) =
      (siteBernoulli w).real (connWithinSet G (↑D : Set V) x ↑A) := by
  classical
  let AD : Finset (↑D : Set V) := D.attach.filter fun a => (a : V) ∈ A
  change (siteBernoulli (w ∘ (Subtype.val : (↑D : Set V) → V))).real
      (siteConnSet (G.comap (Subtype.val : (↑D : Set V) → V))
        ⟨x, Finset.mem_coe.2 hx⟩ ↑AD) =
    (siteBernoulli w).real (connWithinSet G (↑D : Set V) x ↑A)
  have hm : MeasurableSet (siteConnSet (G.comap (Subtype.val : (↑D : Set V) → V))
      ⟨x, Finset.mem_coe.2 hx⟩ ↑AD) :=
    Finset.measurableSet_biUnion _ fun a _ => measurableSet_siteConn _ _ _
  have hmeasure := siteBernoulli_real_preimage_restrictSite w Subtype.val_injective hm
  rw [← hmeasure]
  congr 1
  ext ω
  change (restrictSite (Subtype.val : (↑D : Set V) → V) ω ∈
      siteConnSet (G.comap (Subtype.val : (↑D : Set V) → V))
        ⟨x, Finset.mem_coe.2 hx⟩ (↑AD : Set (↑D : Set V))) ↔
    ω ∈ connWithinSet G (↑D : Set V) x ↑A
  rw [mem_connWithinSet_iff]
  simp only [siteConnSet, Set.mem_iUnion, exists_prop, Finset.mem_coe]
  constructor
  · rintro ⟨a, ha, hconn⟩
    have haA : (a : V) ∈ A := (Finset.mem_filter.1 (show a ∈ AD from ha)).2
    refine ⟨a, haA, ?_⟩
    exact (mem_siteConn_restrict_subtype_iff G D x a hx
      (Finset.mem_coe.1 a.property) ω).1 hconn
  · rintro ⟨a, ha, hconn⟩
    have haD := hAD ha
    let aD : (↑D : Set V) := ⟨a, Finset.mem_coe.2 haD⟩
    refine ⟨aD, (show aD ∈ AD from Finset.mem_filter.2 ⟨Finset.mem_attach D aD, ha⟩), ?_⟩
    exact (mem_siteConn_restrict_subtype_iff G D x a hx haD ω).2 hconn

theorem pinnedSiteGluing_connWithinSet [DecidableEq V] (hgl : PinnedSiteGluing)
    (G : SimpleGraph V) (w : V → unitInterval) (D A T : Finset V) (hAD : A ⊆ D)
    (hTD : T ⊆ D) (hA : A.Nonempty) (o : V) (hoD : o ∈ D) (hwo : w o = 1)
    (hAw : ∀ a ∈ A, w a = 1) :
    (siteBernoulli w).real (connWithinSet G (↑D : Set V) o ↑A) *
        A.inf' hA (fun a => (siteBernoulli w).real (connWithinSet G (↑D : Set V) a ↑T)) ≤
      (siteBernoulli w).real (connWithinSet G (↑D : Set V) o ↑T) := by
  classical
  let W := (↑D : Set V)
  let H : SimpleGraph W := G.comap Subtype.val
  let wD : W → unitInterval := w ∘ Subtype.val
  let oD : W := ⟨o, Finset.mem_coe.2 hoD⟩
  let AD : Finset W := D.attach.filter fun a => (a : V) ∈ A
  let TD : Finset W := D.attach.filter fun t => (t : V) ∈ T
  have hADne : AD.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨a, Finset.mem_coe.2 (hAD ha)⟩,
      Finset.mem_filter.2 ⟨Finset.mem_attach _ _, ha⟩⟩
  have hkey := pinnedSiteGluing_target_fintype hgl H wD AD hADne TD oD
    (by simp [wD, oD, hwo]) (by
      intro a ha
      exact hAw a ((Finset.mem_filter.1 ha).2))
  have hsource : (siteBernoulli wD).real (siteConnSet H oD ↑AD) =
      (siteBernoulli w).real (connWithinSet G (↑D : Set V) o ↑A) := by
    simpa [W, H, wD, oD, AD] using
      (siteBernoulli_real_connWithinSet_subtype G w D A hAD o hoD)
  have htarget : (siteBernoulli wD).real (siteConnSet H oD ↑TD) =
      (siteBernoulli w).real (connWithinSet G (↑D : Set V) o ↑T) := by
    simpa [W, H, wD, oD, TD] using
      (siteBernoulli_real_connWithinSet_subtype G w D T hTD o hoD)
  have hrelay : AD.inf' hADne
        (fun a => (siteBernoulli wD).real (siteConnSet H a ↑TD)) =
      A.inf' hA
        (fun a => (siteBernoulli w).real (connWithinSet G (↑D : Set V) a ↑T)) := by
    apply le_antisymm
    · refine Finset.le_inf' hA _ ?_
      intro a ha
      let aD : W := ⟨a, Finset.mem_coe.2 (hAD ha)⟩
      refine le_trans (Finset.inf'_le _ (show aD ∈ AD from ?_)) ?_
      · exact Finset.mem_filter.2 ⟨Finset.mem_attach D aD, ha⟩
      · simpa [W, H, wD, TD, aD] using
          (siteBernoulli_real_connWithinSet_subtype G w D T hTD a (hAD ha)).le
    · refine Finset.le_inf' hADne _ ?_
      intro a ha
      have haA : (a : V) ∈ A := (Finset.mem_filter.1 ha).2
      refine le_trans (Finset.inf'_le _ haA) ?_
      simpa [W, H, wD, TD] using
        (siteBernoulli_real_connWithinSet_subtype G w D T hTD (a : V)
          (Finset.mem_coe.1 a.property)).symm.le
  rw [hsource, hrelay, htarget] at hkey
  exact hkey

end ConfinedGluing

/-! ## Relay through the declared middle domain -/

section RelayD

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

open scoped Classical

/-- The source reaches an open shell vertex which is reliable for connection to `T` inside `D`.
Unlike `reachRelay`, only the shell `O \ Int` is pinned; the target path may use all of `D`. -/
def reachRelayD (w : V → unitInterval) (Dom D O Int : Finset V) (o : V) (T : Set V)
    (δ : ℝ) : Set (SiteConfig V) :=
  ⋃ u ∈ O \ Int, { ω | reliable G w (O \ Int) D T δ ω u } ∩ fromSource G Dom Int o u

theorem determinedBy_reachRelayD (w : V → unitInterval) (Dom D O Int : Finset V)
    (hODom : O ⊆ Dom) (o : V) (T : Set V) (δ : ℝ) :
    DeterminedBy (reachRelayD G w Dom D O Int o T δ) (↑Dom : Set V) := by
  refine DeterminedBy.iUnion fun u => DeterminedBy.iUnion fun _ => DeterminedBy.inter ?_ ?_
  · refine (determinedBy_reliable G w _ D T δ u).mono fun i hi => ?_
    exact Finset.mem_coe.2 (hODom (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).1)
  · exact (determinedBy_fromSource G Dom Int o u).mono fun i hi =>
      Finset.mem_coe.2 (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).1

theorem reachRelayD_inter_localCylinder (w : V → unitInterval) (Dom D O Int : Finset V)
    (o : V) (T : Set V) (δ : ℝ) (ξ : Set V) :
    reachRelayD G w Dom D O Int o T δ ∩ localCylinder (↑(O \ Int) : Set V) ξ =
      (⋃ u ∈ (O \ Int).filter (fun u => u ∈ ξ ∧ reliable G w (O \ Int) D T δ ξ u),
        fromSource G Dom Int o u) ∩ localCylinder (↑(O \ Int) : Set V) ξ := by
  ext ω
  simp only [reachRelayD, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq,
    Finset.mem_filter, exists_prop]
  constructor
  · rintro ⟨⟨u, hu, hrel, hsrc⟩, hcyl⟩
    have huω : u ∈ ω := (mem_of_connWithin G hsrc).1
    have huξ : u ∈ ξ := (hcyl u (Finset.mem_coe.2 hu)).mp huω
    have htrace : ω ∩ (↑(O \ Int) : Set V) = ξ ∩ (↑(O \ Int) : Set V) :=
      inter_eq_of_forall_iff fun i hi => hcyl i hi
    exact ⟨⟨u, ⟨hu, huξ, (reliable_congr G w _ D T δ htrace u).1 hrel⟩, hsrc⟩, hcyl⟩
  · rintro ⟨⟨u, ⟨hu, huξ, hrel⟩, hsrc⟩, hcyl⟩
    have htrace : ω ∩ (↑(O \ Int) : Set V) = ξ ∩ (↑(O \ Int) : Set V) :=
      inter_eq_of_forall_iff fun i hi => hcyl i hi
    exact ⟨⟨u, hu, (reliable_congr G w _ D T δ htrace u).2 hrel, hsrc⟩, hcyl⟩

/-- Pinning a positive-probability finite pattern is the corresponding product law. -/
theorem pinnedProb_eq_real_pinW_of_pos (w : V → unitInterval) (F : Finset V) (ξ : Set V)
    {A : Set (SiteConfig V)} (hA : MeasurableSet A)
    (hpos : 0 < (prodBernoulli w).real (localCylinder (↑F : Set V) ξ)) :
    pinnedProb w (↑F : Set V) (fun i => i ∈ ξ) A =
      (prodBernoulli (pinW w (↑F : Set V) ξ)).real A := by
  have h1 := real_inter_localCylinder_eq_mul_pinnedProb w F ξ hA
  have h2 := prodBernoulli_real_inter_localCylinder w F ξ hA
  rw [h1] at h2
  exact mul_left_cancel₀ (ne_of_gt hpos) h2

/-- A source-to-relay connection avoiding `Int` is a connection inside `Dom`. -/
theorem fromSource_subset_connWithin {Dom Int : Finset V} (o u : V) :
    fromSource G Dom Int o u ⊆ connWithin G (↑Dom : Set V) o u :=
  connWithin_mono_set G (fun i hi => Finset.mem_coe.2 (Finset.mem_sdiff.1
    (Finset.mem_coe.1 hi)).1) o u

/-- On a fixed shell pattern, the pinned-site gluing inequality connects the source to the
declared target inside `Dom`. -/
theorem pinnedProb_reachRelayD_le_target (hgl : PinnedSiteGluing)
    (w : V → unitInterval) {Dom D O Int : Finset V} (hIntO : Int ⊆ O)
    (hOD : O ⊆ D) (hDDom : D ⊆ Dom) (o : V) (hoDom : o ∈ Dom) (hoD : o ∉ D)
    (hwo : w o = 1) (T : Set V) {δ : ℝ} (hδ1 : δ ≤ 1) (ξ : Set V)
    (hpos : 0 < (prodBernoulli w).real (localCylinder (↑(O \ Int) : Set V) ξ)) :
    pinnedProb w (↑(O \ Int) : Set V) (fun i => i ∈ ξ)
        (⋃ u ∈ (O \ Int).filter
          (fun u => u ∈ ξ ∧ reliable G w (O \ Int) D T δ ξ u),
          fromSource G Dom Int o u) * (1 - δ) ≤
      pinnedProb w (↑(O \ Int) : Set V) (fun i => i ∈ ξ)
        (connWithinSet G (↑Dom : Set V) o T) := by
  classical
  let S := O \ Int
  let A := S.filter (fun u => u ∈ ξ ∧ reliable G w S D T δ ξ u)
  let Tfin := Dom.filter fun t => t ∈ T
  by_cases hA : A.Nonempty
  · let wp := pinW w (↑S : Set V) ξ
    have hADom : A ⊆ Dom := by
      intro a ha
      exact hDDom (hOD (Finset.mem_sdiff.1 (Finset.mem_filter.1 ha).1).1)
    have hTDom : Tfin ⊆ Dom := fun _ ht => (Finset.mem_filter.1 ht).1
    have hwpO : wp o = 1 := by
      dsimp [wp]
      rw [pinW_apply_of_not_mem, hwo]
      intro hoS
      exact hoD (hOD (Finset.mem_sdiff.1 (Finset.mem_coe.1 hoS)).1)
    have hwpA : ∀ a ∈ A, wp a = 1 := by
      intro a ha
      dsimp [wp]
      exact pinW_apply_of_mem_of_mem _
        (Finset.mem_coe.2 (Finset.mem_filter.1 ha).1) (Finset.mem_filter.1 ha).2.1
    have hglue := pinnedSiteGluing_connWithinSet hgl G wp Dom A Tfin hADom hTDom hA o
      hoDom hwpO hwpA
    have hsourceSub : (⋃ u ∈ A, fromSource G Dom Int o u) ⊆
        connWithinSet G (↑Dom : Set V) o ↑A :=
      Set.iUnion₂_mono fun u _ => fromSource_subset_connWithin G o u
    have hsource : (prodBernoulli wp).real (⋃ u ∈ A, fromSource G Dom Int o u) ≤
        (prodBernoulli wp).real (connWithinSet G (↑Dom : Set V) o ↑A) :=
      measureReal_mono hsourceSub (measure_ne_top _ _)
    have hrelay : 1 - δ ≤ A.inf' hA
        (fun a => (prodBernoulli wp).real (connWithinSet G (↑Dom : Set V) a ↑Tfin)) := by
      refine Finset.le_inf' hA _ ?_
      intro a ha
      have hrel := (Finset.mem_filter.1 ha).2.2
      have hDsub : connWithinSet G (↑D : Set V) a T ⊆
          connWithinSet G (↑Dom : Set V) a ↑Tfin := by
        rintro ω hω
        obtain ⟨t, htT, hat⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 hω
        refine (mem_connWithinSet_iff _ _ _ _ _).2 ⟨t, ?_, connWithin_mono_set G ?_ a t hat⟩
        · exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hDDom
            (mem_of_connWithin G hat).2, htT⟩)
        · intro i hi
          exact Finset.mem_coe.2 (hDDom (Finset.mem_coe.1 hi))
      have hmD := measurableSet_toTarget G D T a
      have hpinD : pinnedProb w (↑S : Set V) (fun i => i ∈ ξ)
          (toTarget G D T a) = (prodBernoulli wp).real (toTarget G D T a) := by
        simpa [wp] using pinnedProb_eq_real_pinW_of_pos w S ξ hmD (by simpa [S] using hpos)
      exact (le_of_lt hrel).trans (by
        rw [hpinD]
        exact measureReal_mono hDsub (measure_ne_top _ _))
    have hmSource : MeasurableSet (⋃ u ∈ A, fromSource G Dom Int o u) :=
      Finset.measurableSet_biUnion _ fun u _ => measurableSet_fromSource G Dom Int o u
    have hmTarget : MeasurableSet (connWithinSet G (↑Dom : Set V) o T) :=
      measurableSet_connWithinSet G Dom o T
    change pinnedProb w (↑S : Set V) (fun i => i ∈ ξ)
        (⋃ u ∈ A, fromSource G Dom Int o u) * (1 - δ) ≤
      pinnedProb w (↑S : Set V) (fun i => i ∈ ξ)
        (connWithinSet G (↑Dom : Set V) o T)
    rw [pinnedProb_eq_real_pinW_of_pos w S ξ hmSource (by simpa [S] using hpos),
      pinnedProb_eq_real_pinW_of_pos w S ξ hmTarget (by simpa [S] using hpos)]
    change (prodBernoulli wp).real (⋃ u ∈ A, fromSource G Dom Int o u) * (1 - δ) ≤
      (prodBernoulli wp).real (connWithinSet G (↑Dom : Set V) o T)
    calc
      (prodBernoulli wp).real (⋃ u ∈ A, fromSource G Dom Int o u) * (1 - δ) ≤
          (prodBernoulli wp).real (connWithinSet G (↑Dom : Set V) o ↑A) * (1 - δ) :=
        mul_le_mul_of_nonneg_right hsource (by linarith)
      _ ≤ (prodBernoulli wp).real (connWithinSet G (↑Dom : Set V) o ↑A) *
          A.inf' hA (fun a => (prodBernoulli wp).real
            (connWithinSet G (↑Dom : Set V) a ↑Tfin)) :=
        mul_le_mul_of_nonneg_left hrelay measureReal_nonneg
      _ ≤ (prodBernoulli wp).real (connWithinSet G (↑Dom : Set V) o ↑Tfin) := hglue
      _ ≤ (prodBernoulli wp).real (connWithinSet G (↑Dom : Set V) o T) :=
        measureReal_mono (by
          intro ω hω
          obtain ⟨t, ht, hconn⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 hω
          exact (mem_connWithinSet_iff _ _ _ _ _).2
            ⟨t, (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2, hconn⟩) (measure_ne_top _ _)
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA
    change pinnedProb w (↑S : Set V) (fun i => i ∈ ξ)
        (⋃ u ∈ A, fromSource G Dom Int o u) * (1 - δ) ≤ _
    rw [hAempty]
    simp [pinnedProb]

/-- Averaged over shell patterns, a reached reliable relay connects to `T` with the gluing factor
`1 - δ`. -/
theorem real_reachRelayD_target_ge (hgl : PinnedSiteGluing) (w : V → unitInterval)
    {Dom D O Int : Finset V} (hIntO : Int ⊆ O) (hOD : O ⊆ D) (hDDom : D ⊆ Dom)
    (o : V) (hoDom : o ∈ Dom) (hoD : o ∉ D) (hwo : w o = 1) (T : Set V) {δ : ℝ}
    (hδ1 : δ ≤ 1) :
    (prodBernoulli w).real (reachRelayD G w Dom D O Int o T δ) * (1 - δ) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hXm : MeasurableSet (reachRelayD G w Dom D O Int o T δ) :=
    (determinedBy_reachRelayD G w Dom D O Int (hOD.trans hDDom) o T δ).measurableSet_of_finset
  have hYm : MeasurableSet (connWithinSet G (↑Dom : Set V) o T) :=
    measurableSet_connWithinSet G Dom o T
  rw [real_eq_sum_inter_localCylinder w (O \ Int) hXm,
    real_eq_sum_inter_localCylinder w (O \ Int) hYm, Finset.sum_mul]
  refine Finset.sum_le_sum fun ξ _ => ?_
  rw [reachRelayD_inter_localCylinder]
  rw [real_inter_localCylinder_eq_mul_pinnedProb w (O \ Int) _
    (Finset.measurableSet_biUnion _ fun u _ => measurableSet_fromSource G Dom Int o u),
    real_inter_localCylinder_eq_mul_pinnedProb w (O \ Int) _ hYm, mul_assoc]
  by_cases hc : (prodBernoulli w).real (localCylinder (↑(O \ Int) : Set V) ξ) = 0
  · rw [hc]
    simp only [zero_mul]
    exact le_rfl
  · exact mul_le_mul_of_nonneg_left
      (pinnedProb_reachRelayD_le_target G hgl w hIntO hOD hDDom o hoDom hoD hwo T hδ1 ξ
        (lt_of_le_of_ne measureReal_nonneg (Ne.symm hc))) measureReal_nonneg

end RelayD

/-! ## Reliable faces, seeds, and the one-level theorem -/

section OneLevel

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

open scoped Classical

/-- Some open site of the face `U` is a reliable relay for the shell pattern. -/
def reliableFace (w : V → unitInterval) (S O : Finset V) (T : Set V) (δ : ℝ) (U : Finset V) :
    Set (SiteConfig V) :=
  ⋃ u ∈ U, {ω : SiteConfig V | u ∈ ω} ∩ {ω | reliable G w S O T δ ω u}

theorem determinedBy_reliableFace (w : V → unitInterval) {S : Finset V} (O : Finset V) (T : Set V)
    (δ : ℝ) {U : Finset V} (hU : U ⊆ S) :
    DeterminedBy (reliableFace G w S O T δ U) (↑S : Set V) := by
  refine DeterminedBy.iUnion fun u => DeterminedBy.iUnion fun hu => DeterminedBy.inter ?_ ?_
  · exact (determinedBy_setOf_mem u).mono (Set.singleton_subset_iff.2 (Finset.mem_coe.2 (hU hu)))
  · exact determinedBy_reliable G w S O T δ u

theorem measurableSet_reliableFace (w : V → unitInterval) {S : Finset V} (O : Finset V)
    (T : Set V) (δ : ℝ) {U : Finset V} (hU : U ⊆ S) :
    MeasurableSet (reliableFace G w S O T δ U) :=
  (determinedBy_reliableFace G w O T δ hU).measurableSet_of_finset

/-- The pattern of a substituted configuration on the pinned set is the prescribed one. -/
theorem substitute_inter_coe (S : Finset V) (ω ω₁ : SiteConfig V) :
    substitute (↑S : Set V) (fun i => i ∈ ω) ω₁ ∩ (↑S : Set V) = ω ∩ (↑S : Set V) := by
  rw [substitute_inter_eq]
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  exact and_comm

/-- **A reliable face from a shell-determined reliability event.**  If every configuration of
`Gx` has an open face site `u` such that every configuration of `Gx` with the same shell pattern
joins `u` to the target inside `O`, then whenever the pinned probability of `Gx` exceeds `1 - δ`,
some open face site is a reliable relay. -/
theorem setOf_lt_pinnedProb_subset_reliableFace (w : V → unitInterval) {S : Finset V}
    (O : Finset V) (T : Set V) {δ : ℝ} (hδ1 : δ ≤ 1) {U : Finset V} (hU : U ⊆ S)
    {Gx : Set (SiteConfig V)}
    (hrelay : ∀ ω ∈ Gx, ∃ u ∈ U, u ∈ ω ∧ ∀ ω' ∈ Gx,
      ω' ∩ (↑S : Set V) = ω ∩ (↑S : Set V) → ω' ∈ toTarget G O T u) :
    {ω : SiteConfig V | 1 - δ < pinnedProb w (↑S : Set V) (fun i => i ∈ ω) Gx} ⊆
      reliableFace G w S O T δ U := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  -- the pinned event is nonempty
  have hne : (substitute (↑S : Set V) (fun i => i ∈ ω) ⁻¹' Gx).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [pinnedProb, h, measureReal_empty] at hω
    linarith
  obtain ⟨ω₁, hω₁⟩ := hne
  set ω₀ := substitute (↑S : Set V) (fun i => i ∈ ω) ω₁ with hω₀
  have hω₀S : ω₀ ∩ (↑S : Set V) = ω ∩ (↑S : Set V) := substitute_inter_coe S ω ω₁
  obtain ⟨u, huU, huω₀, hall⟩ := hrelay ω₀ hω₁
  refine Set.mem_iUnion₂.2 ⟨u, huU, ?_, ?_⟩
  · have : u ∈ ω₀ ∩ (↑S : Set V) := ⟨huω₀, Finset.mem_coe.2 (hU huU)⟩
    rw [hω₀S] at this
    exact this.1
  · show 1 - δ < pinnedProb w (↑S : Set V) (fun i => i ∈ ω) (toTarget G O T u)
    refine lt_of_lt_of_le hω ?_
    unfold pinnedProb
    refine measureReal_mono (fun ω₂ hω₂ => ?_) (measure_ne_top _ _)
    refine hall _ hω₂ ?_
    rw [substitute_inter_coe, hω₀S]

/-- **The reliable-face bound.**  If `P(Gx) ≥ 1 - η`, then the face is reliable with probability
at least `1 - η / δ`: Markov's inequality over the shell patterns. -/
theorem real_reliableFace_ge (w : V → unitInterval) {S : Finset V} (O : Finset V) (T : Set V)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {U : Finset V} (hU : U ⊆ S) {Gx : Set (SiteConfig V)}
    (hGm : MeasurableSet Gx)
    (hrelay : ∀ ω ∈ Gx, ∃ u ∈ U, u ∈ ω ∧ ∀ ω' ∈ Gx,
      ω' ∩ (↑S : Set V) = ω ∩ (↑S : Set V) → ω' ∈ toTarget G O T u)
    {η : ℝ} (hG : 1 - η ≤ (prodBernoulli w).real Gx) :
    1 - η / δ ≤ (prodBernoulli w).real (reliableFace G w S O T δ U) := by
  have hmarkov := mul_real_setOf_pinnedProb_le_le w S hGm δ
  set Low : Set (SiteConfig V) :=
    {ω | pinnedProb w (↑S : Set V) (fun i => i ∈ ω) Gx ≤ 1 - δ} with hLow
  have hLowm : MeasurableSet Low :=
    (determinedBy_setOf_pinnedProb_le w _ Gx _).measurableSet_of_finset
  have hcompl : Lowᶜ = {ω : SiteConfig V | 1 - δ < pinnedProb w (↑S : Set V) (fun i => i ∈ ω) Gx} := by
    ext ω
    simp only [hLow, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have hsub : Lowᶜ ⊆ reliableFace G w S O T δ U := by
    rw [hcompl]
    exact setOf_lt_pinnedProb_subset_reliableFace G w O T hδ1 hU hrelay
  have h1 : (prodBernoulli w).real Lowᶜ ≤ (prodBernoulli w).real (reliableFace G w S O T δ U) :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [measureReal_compl hLowm, probReal_univ] at h1
  have h2 : (prodBernoulli w).real Low ≤ η / δ := by
    rw [le_div_iff₀ hδ0]
    linarith
  linarith

/-- The seed event of the contact `x`: `x` is a selected contact and its seed is open. -/
def seedOpen (Dom D : Finset V) (o : V) (sel : Finset V → Finset V) (J : V → Finset V) (x : V) :
    Set (SiteConfig V) :=
  {ω | x ∈ sel (contacts G Dom D o ω)} ∩ {ω | (↑(J x) : Set V) ⊆ ω}

theorem determinedBy_seedOpen (Dom D : Finset V) (o : V) (sel : Finset V → Finset V)
    (J : V → Finset V) (x : V) :
    DeterminedBy (seedOpen G Dom D o sel J x) ((↑(Dom \ D) : Set V) ∪ (↑(J x) : Set V)) := by
  refine DeterminedBy.inter (DeterminedBy.mono ?_ Set.subset_union_left)
    ((determinedBy_allOpen _).mono Set.subset_union_right)
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_setOf_eq, contacts_congr G h]

theorem measurableSet_seedOpen (Dom D : Finset V) (o : V) (sel : Finset V → Finset V)
    (J : V → Finset V) (x : V) : MeasurableSet (seedOpen G Dom D o sel J x) := by
  have h := determinedBy_seedOpen G Dom D o sel J x
  rw [← Finset.coe_union] at h
  exact h.measurableSet_of_finset

/-- **The seed bound.**  On a level with at least `N` contacts, `k` selected contacts have pairwise
disjoint seeds of at most `s` sites each, lying inside `D` where the parameter is at least `q`;
all their seeds are closed with probability at most `(1 - q^s)^k`. -/
theorem real_poorCompl_diff_seeds_le (w : V → unitInterval) (Dom D : Finset V) (o : V)
    (N k s : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (sel : Finset V → Finset V)
    (J : V → Finset V) (hsel_sub : ∀ K, sel K ⊆ K)
    (hsel_card : ∀ K ⊆ outerBoundary G Dom D, N ≤ K.card → k ≤ (sel K).card)
    (hsel_disj : ∀ K, (↑(sel K) : Set V).PairwiseDisjoint J)
    (hJD : ∀ x ∈ outerBoundary G Dom D, J x ⊆ D)
    (hs : ∀ x ∈ outerBoundary G Dom D, (J x).card ≤ s)
    (hw : ∀ x ∈ outerBoundary G Dom D, ∀ y ∈ J x, q ≤ (w y : ℝ)) :
    (prodBernoulli w).real ((poor G Dom D o N)ᶜ \
        ⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) ≤ (1 - q ^ s) ^ k := by
  set 𝒦 : Finset (Finset V) := (outerBoundary G Dom D).powerset.filter fun K => N ≤ K.card
    with h𝒦
  set C : V → Set (SiteConfig V) := fun x => {ω : SiteConfig V | (↑(J x) : Set V) ⊆ ω}ᶜ with hC
  set E : Finset V → Set (SiteConfig V) := fun K =>
    {ω : SiteConfig V | contacts G Dom D o ω = K} ∩ ⋂ x ∈ sel K, C x with hE
  have hqs0 : 0 ≤ 1 - q ^ s := by linarith [pow_le_one₀ hq0 hq1 (n := s)]
  have hqs1 : 1 - q ^ s ≤ 1 := by linarith [pow_nonneg hq0 s]
  have heq : (poor G Dom D o N)ᶜ \ (⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) =
      ⋃ K ∈ 𝒦, E K := by
    ext ω
    simp only [Set.mem_sdiff, Set.mem_compl_iff, poor, Set.mem_setOf_eq, not_lt, Set.mem_iUnion,
      exists_prop, not_exists, not_and, hE, hC, Set.mem_inter_iff, Set.mem_iInter, h𝒦,
      Finset.mem_filter, Finset.mem_powerset, seedOpen]
    constructor
    · rintro ⟨hN, hno⟩
      refine ⟨contacts G Dom D o ω, ⟨contacts_subset G Dom D o ω, hN⟩, rfl, fun x hx hJ => ?_⟩
      exact hno x (contacts_subset G Dom D o ω (hsel_sub _ hx)) hx hJ
    · rintro ⟨K, ⟨-, hN⟩, rfl, hall⟩
      exact ⟨hN, fun x _ hx hJ => hall x hx hJ⟩
  have hCm : ∀ x, MeasurableSet (C x) := fun x =>
    (determinedBy_allOpen (↑(J x) : Set V)).measurableSet_of_finset.compl
  have hKm : ∀ K, MeasurableSet {ω : SiteConfig V | contacts G Dom D o ω = K} := fun K =>
    (determinedBy_contacts_eq G Dom D o K).measurableSet_of_finset
  have hEm : ∀ K, MeasurableSet (E K) := fun K =>
    (hKm K).inter (Finset.measurableSet_biInter _ fun x _ => hCm x)
  have hKdisj : (↑𝒦 : Set (Finset V)).PairwiseDisjoint
      fun K => {ω : SiteConfig V | contacts G Dom D o ω = K} := by
    intro K _ K' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω hK hK'
    exact hne (hK.symm.trans hK')
  have hEdisj : (↑𝒦 : Set (Finset V)).PairwiseDisjoint E :=
    hKdisj.mono fun K => Set.inter_subset_left
  rw [heq, measureReal_biUnion_finset hEdisj (fun K _ => hEm K) (fun K _ => measure_ne_top _ _)]
  -- each term factorises
  have hterm : ∀ K ∈ 𝒦, (prodBernoulli w).real (E K) ≤
      (prodBernoulli w).real {ω : SiteConfig V | contacts G Dom D o ω = K} * (1 - q ^ s) ^ k := by
    intro K hK
    have hKsub : K ⊆ outerBoundary G Dom D :=
      Finset.mem_powerset.1 (Finset.mem_filter.1 hK).1
    have hKN : N ≤ K.card := (Finset.mem_filter.1 hK).2
    have hA : DeterminedBy {ω : SiteConfig V | contacts G Dom D o ω = K}
        (⋃ x ∈ sel K, (↑(J x) : Set V))ᶜ := by
      refine (determinedBy_contacts_eq G Dom D o K).mono fun i hi => ?_
      rw [Set.mem_compl_iff, Set.mem_iUnion₂]
      rintro ⟨x, hx, hix⟩
      have hiD : i ∈ D := hJD x (hKsub (hsel_sub K hx)) (Finset.mem_coe.1 hix)
      exact (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).2 hiD
    have hfac := prodBernoulli_real_inter_biInter_of_determinedBy w (sel K) J (hsel_disj K)
      (C := C) (fun x _ => (determinedBy_allOpen (↑(J x) : Set V)).compl) (fun x _ => hCm x)
      hA (hKm K)
    rw [hE]
    simp only
    rw [hfac]
    refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
    -- each seed is closed with probability at most `1 - q^s`
    have hone : ∀ x ∈ sel K, (prodBernoulli w).real (C x) ≤ 1 - q ^ s := by
      intro x hx
      have hxb : x ∈ outerBoundary G Dom D := hKsub (hsel_sub K hx)
      rw [hC]
      simp only
      rw [measureReal_compl (determinedBy_allOpen (↑(J x) : Set V)).measurableSet_of_finset,
        probReal_univ, prodBernoulli_real_subset]
      have h1 : q ^ s ≤ q ^ (J x).card := pow_le_pow_of_le_one hq0 hq1 (hs x hxb)
      have h2 : q ^ (J x).card ≤ ∏ i ∈ J x, (w i : ℝ) := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod (fun i _ => hq0) (fun i hi => hw x hxb i hi)
      linarith
    calc ∏ x ∈ sel K, (prodBernoulli w).real (C x)
        ≤ ∏ _x ∈ sel K, (1 - q ^ s) :=
          Finset.prod_le_prod (fun x _ => measureReal_nonneg) hone
      _ = (1 - q ^ s) ^ (sel K).card := Finset.prod_const _
      _ ≤ (1 - q ^ s) ^ k := pow_le_pow_of_le_one hqs0 hqs1 (hsel_card K hKsub hKN)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ K ∈ 𝒦, (prodBernoulli w).real {ω : SiteConfig V | contacts G Dom D o ω = K} ≤ 1 := by
    rw [← measureReal_biUnion_finset hKdisj (fun K _ => hKm K) (fun K _ => measure_ne_top _ _)]
    exact measureReal_le_one
  have hpow : 0 ≤ (1 - q ^ s) ^ k := pow_nonneg hqs0 k
  nlinarith

/-- **A selected contact with an open seed, together with a reliable open face site, gives a
reliable relay reached from the source avoiding the interior.**  This is the deterministic content
of the shell-window construction: the seed lies in the layer `D \ O`, the face in the shell
`O \ Int`, and the contact outside `D`, so the path from the source never enters `Int`. -/
theorem seedOpen_inter_reliableFace_subset (w : V → unitInterval) {Dom D O Int : Finset V}
    (hIntO : Int ⊆ O) (hOD : O ⊆ D) (hDDom : D ⊆ Dom) (o : V) (T : Set V) (δ : ℝ)
    (sel : Finset V → Finset V) (J U : V → Finset V) (hsel_sub : ∀ K, sel K ⊆ K) {x : V}
    (hx : x ∈ outerBoundary G Dom D) (hU : U x ⊆ O \ Int) (hJD : J x ⊆ D)
    (hJO : ∀ y ∈ J x, y ∉ O)
    (hW3 : ∀ u ∈ U x, (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
      connWithin G (insert x (insert u (↑(J x) : Set V))) x u) :
    seedOpen G Dom D o sel J x ∩ reliableFace G w (O \ Int) O T δ (U x) ⊆
      reachRelay G w Dom O Int o T δ := by
  rintro ω ⟨⟨hxsel, hJω⟩, hface⟩
  obtain ⟨u, huU, huω, hrel⟩ := Set.mem_iUnion₂.1 hface
  have hxc : x ∈ contacts G Dom D o ω := hsel_sub _ hxsel
  have hox : ω ∈ connWithin G (↑(Dom \ D) : Set V) o x := (Finset.mem_filter.1 hxc).2
  have hxω : x ∈ ω := (mem_of_connWithin G hox).1
  have hsub : insert x (insert u (↑(J x) : Set V)) ⊆ ω := by
    intro i hi
    rcases hi with rfl | hi
    · exact hxω
    rcases hi with rfl | hi
    · exact huω
    · exact hJω hi
  have hxu : ω ∈ connWithin G (insert x (insert u (↑(J x) : Set V))) x u :=
    isUpperSet_connWithin G _ x u hsub (hW3 u huU)
  refine Set.mem_iUnion₂.2 ⟨u, hU huU, hrel, ?_⟩
  refine connWithin_mono_set G ?_ o u (connWithin_trans G hox hxu)
  intro i hi
  rw [Finset.mem_coe, Finset.mem_sdiff]
  rcases hi with hi | hi
  · have h := Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)
    exact ⟨h.1, fun h' => h.2 (hOD (hIntO h'))⟩
  · rcases hi with rfl | hi
    · have h := Finset.mem_sdiff.1 (outerBoundary_subset G Dom D hx)
      exact ⟨h.1, fun h' => h.2 (hOD (hIntO h'))⟩
    rcases hi with rfl | hi
    · have h := Finset.mem_sdiff.1 (hU huU)
      exact ⟨hDDom (hOD h.1), h.2⟩
    · have hiJ := Finset.mem_coe.1 hi
      exact ⟨hDDom (hJD hiJ), fun h' => hJO i hiJ (hIntO h')⟩

/-- `D`-relay form of `seedOpen_inter_reliableFace_subset`: the shell alone is pinned and the
reliable continuation is allowed to use the declared middle domain `D`. -/
theorem seedOpen_inter_reliableFaceD_subset (w : V → unitInterval)
    {Dom D O Int : Finset V} (hIntO : Int ⊆ O) (hOD : O ⊆ D) (hDDom : D ⊆ Dom)
    (o : V) (T : Set V) (δ : ℝ) (sel : Finset V → Finset V) (J U : V → Finset V)
    (hsel_sub : ∀ K, sel K ⊆ K) {x : V} (hx : x ∈ outerBoundary G Dom D)
    (hU : U x ⊆ O \ Int) (hJD : J x ⊆ D) (hJO : ∀ y ∈ J x, y ∉ O)
    (hW3 : ∀ u ∈ U x, (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
      connWithin G (insert x (insert u (↑(J x) : Set V))) x u) :
    seedOpen G Dom D o sel J x ∩ reliableFace G w (O \ Int) D T δ (U x) ⊆
      reachRelayD G w Dom D O Int o T δ := by
  rintro ω ⟨⟨hxsel, hJω⟩, hface⟩
  obtain ⟨u, huU, huω, hrel⟩ := Set.mem_iUnion₂.1 hface
  have hxc : x ∈ contacts G Dom D o ω := hsel_sub _ hxsel
  have hox : ω ∈ connWithin G (↑(Dom \ D) : Set V) o x := (Finset.mem_filter.1 hxc).2
  have hxω : x ∈ ω := (mem_of_connWithin G hox).1
  have hsub : insert x (insert u (↑(J x) : Set V)) ⊆ ω := by
    intro i hi
    rcases hi with rfl | hi
    · exact hxω
    rcases hi with rfl | hi
    · exact huω
    · exact hJω hi
  have hxu : ω ∈ connWithin G (insert x (insert u (↑(J x) : Set V))) x u :=
    isUpperSet_connWithin G _ x u hsub (hW3 u huU)
  refine Set.mem_iUnion₂.2 ⟨u, hU huU, hrel, ?_⟩
  refine connWithin_mono_set G ?_ o u (connWithin_trans G hox hxu)
  intro i hi
  rw [Finset.mem_coe, Finset.mem_sdiff]
  rcases hi with hi | hi
  · have h := Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)
    exact ⟨h.1, fun h' => h.2 (hOD (hIntO h'))⟩
  · rcases hi with rfl | hi
    · have h := Finset.mem_sdiff.1 (outerBoundary_subset G Dom D hx)
      exact ⟨h.1, fun h' => h.2 (hOD (hIntO h'))⟩
    rcases hi with rfl | hi
    · have h := Finset.mem_sdiff.1 (hU huU)
      exact ⟨hDDom (hOD h.1), h.2⟩
    · have hiJ := Finset.mem_coe.1 hi
      exact ⟨hDDom (hJD hiJ), fun h' => hJO i hiJ (hIntO h')⟩

/-- **One manuscript-style level with support and relay in `D`.**  This is the old seed and
reliable-face calculation with the final pattern-wise step supplied by `PinnedSiteGluing`. -/
theorem real_target_ge_one_level_D (hgl : PinnedSiteGluing) (w : V → unitInterval)
    {Dom D O Int : Finset V} (hIntO : Int ⊆ O) (hOD : O ⊆ D) (hDDom : D ⊆ Dom)
    (o : V) (hoDom : o ∈ Dom) (hoD : o ∉ D) (hwo : w o = 1) (T : Set V)
    (N k s : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (sel : Finset V → Finset V) (J U : V → Finset V) (Gx : V → Set (SiteConfig V))
    (hsel_sub : ∀ K, sel K ⊆ K)
    (hsel_card : ∀ K ⊆ outerBoundary G Dom D, N ≤ K.card → k ≤ (sel K).card)
    (hsel_disj : ∀ K, (↑(sel K) : Set V).PairwiseDisjoint J)
    (hU : ∀ x ∈ outerBoundary G Dom D, U x ⊆ O \ Int)
    (hJD : ∀ x ∈ outerBoundary G Dom D, J x ⊆ D)
    (hJO : ∀ x ∈ outerBoundary G Dom D, ∀ y ∈ J x, y ∉ O)
    (hs : ∀ x ∈ outerBoundary G Dom D, (J x).card ≤ s)
    (hW3 : ∀ x ∈ outerBoundary G Dom D, ∀ u ∈ U x,
      (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
        connWithin G (insert x (insert u (↑(J x) : Set V))) x u)
    (hwJ : ∀ x ∈ outerBoundary G Dom D, ∀ y ∈ J x, q ≤ (w y : ℝ))
    (hGm : ∀ x ∈ outerBoundary G Dom D, MeasurableSet (Gx x))
    (hrelay : ∀ x ∈ outerBoundary G Dom D, ∀ ω ∈ Gx x, ∃ u ∈ U x, u ∈ ω ∧
      ∀ ω' ∈ Gx x, ω' ∩ (↑(O \ Int) : Set V) = ω ∩ (↑(O \ Int) : Set V) →
        ω' ∈ toTarget G D T u)
    {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hηδ : η ≤ δ)
    (hG : ∀ x ∈ outerBoundary G Dom D, 1 - η ≤ (prodBernoulli w).real (Gx x)) :
    ((prodBernoulli w).real (poor G Dom D o N)ᶜ - (1 - q ^ s) ^ k) *
        (1 - η / δ) * (1 - δ) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hseed := real_poorCompl_diff_seeds_le G w Dom D o N k s hq0 hq1 sel J hsel_sub
    hsel_card hsel_disj hJD hs hwJ
  have hUm : MeasurableSet (⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) :=
    Finset.measurableSet_biUnion _ fun x _ => measurableSet_seedOpen G Dom D o sel J x
  have h1 : (prodBernoulli w).real (poor G Dom D o N)ᶜ - (1 - q ^ s) ^ k ≤
      (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D,
        seedOpen G Dom D o sel J x) := by
    have h := measureReal_inter_add_sdiff (μ := prodBernoulli w)
      (s := (poor G Dom D o N)ᶜ) hUm (measure_ne_top _ _)
    have hmono : (prodBernoulli w).real ((poor G Dom D o N)ᶜ ∩
        ⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) ≤
        (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D,
          seedOpen G Dom D o sel J x) :=
      measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
    linarith
  have h2 := prodBernoulli_real_biUnion_inter_ge w (O \ Int)
    (outerBoundary G Dom D) (fun x => seedOpen G Dom D o sel J x)
    (fun x => reliableFace G w (O \ Int) D T δ (U x))
    (fun x hx => by
      refine (determinedBy_seedOpen G Dom D o sel J x).mono fun i hi => ?_
      rw [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, not_and, not_not]
      intro hiO
      rcases hi with hi | hi
      · exact absurd (hOD hiO) (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).2
      · exact absurd hiO (hJO x hx i (Finset.mem_coe.1 hi)))
    (fun x hx => determinedBy_reliableFace G w D T δ (hU x hx))
    (fun x _ => measurableSet_seedOpen G Dom D o sel J x)
    (fun x hx => measurableSet_reliableFace G w D T δ (hU x hx))
    (m := 1 - η / δ)
    (fun x hx => real_reliableFace_ge G w D T hδ0 hδ1 (hU x hx) (hGm x hx)
      (hrelay x hx) (hG x hx))
  have h3 : (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D,
      seedOpen G Dom D o sel J x ∩ reliableFace G w (O \ Int) D T δ (U x)) ≤
      (prodBernoulli w).real (reachRelayD G w Dom D O Int o T δ) :=
    measureReal_mono (Set.iUnion₂_subset fun x hx =>
      seedOpen_inter_reliableFaceD_subset G w hIntO hOD hDDom o T δ sel J U hsel_sub hx
        (hU x hx) (hJD x hx) (hJO x hx) (hW3 x hx)) (measure_ne_top _ _)
  have h4 := real_reachRelayD_target_ge G hgl w hIntO hOD hDDom o hoDom hoD hwo T hδ1
  have hm0 : 0 ≤ 1 - η / δ := by
    rw [sub_nonneg, div_le_one hδ0]
    exact hηδ
  have hδ' : 0 ≤ 1 - δ := by linarith
  calc
    ((prodBernoulli w).real (poor G Dom D o N)ᶜ - (1 - q ^ s) ^ k) *
          (1 - η / δ) * (1 - δ) ≤
        (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D,
          seedOpen G Dom D o sel J x) * (1 - η / δ) * (1 - δ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hm0) hδ'
    _ ≤ (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D,
          seedOpen G Dom D o sel J x ∩ reliableFace G w (O \ Int) D T δ (U x)) *
          (1 - δ) := mul_le_mul_of_nonneg_right h2 hδ'
    _ ≤ (prodBernoulli w).real (reachRelayD G w Dom D O Int o T δ) * (1 - δ) :=
      mul_le_mul_of_nonneg_right h3 hδ'
    _ ≤ (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := h4

/-- **The one-level theorem.**  On a level with boxes `Int ⊆ O ⊆ D ⊆ Dom`, seeds and faces as in the
shell-window construction, and reliability events of probability at least `1 - η`:

`(P(level rich) - (1 - q^s)^k) · (1 - η/δ) · (1 - δ) ≤ P(o ↔ T inside Dom)`.

The five inequalities composed are: the seed bound, the decisive lemma applied to the seed events
(outside the shell) and the face events (on the shell), the deterministic inclusion of a seed and a
reliable face in a reliable relay, the relay step (the decisive lemma applied pattern by pattern to
the source events outside `Int` and the relay events inside `Int`), and path concatenation. -/
theorem real_target_ge_one_level (w : V → unitInterval) {Dom D O Int : Finset V}
    (hIntO : Int ⊆ O) (hOD : O ⊆ D) (hDDom : D ⊆ Dom) (o : V) (T : Set V) (N k s : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (sel : Finset V → Finset V) (J U : V → Finset V)
    (Gx : V → Set (SiteConfig V)) (hsel_sub : ∀ K, sel K ⊆ K)
    (hsel_card : ∀ K ⊆ outerBoundary G Dom D, N ≤ K.card → k ≤ (sel K).card)
    (hsel_disj : ∀ K, (↑(sel K) : Set V).PairwiseDisjoint J)
    (hU : ∀ x ∈ outerBoundary G Dom D, U x ⊆ O \ Int)
    (hJD : ∀ x ∈ outerBoundary G Dom D, J x ⊆ D)
    (hJO : ∀ x ∈ outerBoundary G Dom D, ∀ y ∈ J x, y ∉ O)
    (hs : ∀ x ∈ outerBoundary G Dom D, (J x).card ≤ s)
    (hW3 : ∀ x ∈ outerBoundary G Dom D, ∀ u ∈ U x,
      (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
        connWithin G (insert x (insert u (↑(J x) : Set V))) x u)
    (hwJ : ∀ x ∈ outerBoundary G Dom D, ∀ y ∈ J x, q ≤ (w y : ℝ))
    (hGm : ∀ x ∈ outerBoundary G Dom D, MeasurableSet (Gx x))
    (hrelay : ∀ x ∈ outerBoundary G Dom D, ∀ ω ∈ Gx x, ∃ u ∈ U x, u ∈ ω ∧ ∀ ω' ∈ Gx x,
      ω' ∩ (↑(O \ Int) : Set V) = ω ∩ (↑(O \ Int) : Set V) → ω' ∈ toTarget G O T u)
    {δ η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hηδ : η ≤ δ)
    (hG : ∀ x ∈ outerBoundary G Dom D, 1 - η ≤ (prodBernoulli w).real (Gx x)) :
    ((prodBernoulli w).real (poor G Dom D o N)ᶜ - (1 - q ^ s) ^ k) * (1 - η / δ) * (1 - δ) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hODom : O ⊆ Dom := hOD.trans hDDom
  -- step 1: the seed bound
  have hseed := real_poorCompl_diff_seeds_le G w Dom D o N k s hq0 hq1 sel J hsel_sub hsel_card
    hsel_disj hJD hs hwJ
  have hUm : MeasurableSet (⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) :=
    Finset.measurableSet_biUnion _ fun x _ => measurableSet_seedOpen G Dom D o sel J x
  have h1 : (prodBernoulli w).real (poor G Dom D o N)ᶜ - (1 - q ^ s) ^ k ≤
      (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) := by
    have h := measureReal_inter_add_sdiff (μ := prodBernoulli w) (s := (poor G Dom D o N)ᶜ) hUm
      (measure_ne_top _ _)
    have hmono : (prodBernoulli w).real ((poor G Dom D o N)ᶜ ∩
        ⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) ≤
        (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) :=
      measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
    linarith
  -- step 2: the decisive lemma for seeds (outside the shell) against faces (on the shell)
  have h2 := prodBernoulli_real_biUnion_inter_ge w (O \ Int) (outerBoundary G Dom D)
    (fun x => seedOpen G Dom D o sel J x) (fun x => reliableFace G w (O \ Int) O T δ (U x))
    (fun x hx => by
      refine (determinedBy_seedOpen G Dom D o sel J x).mono fun i hi => ?_
      rw [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, not_and, not_not]
      intro hiO
      rcases hi with hi | hi
      · exact absurd (hOD hiO) (Finset.mem_sdiff.1 (Finset.mem_coe.1 hi)).2
      · exact absurd hiO (hJO x hx i (Finset.mem_coe.1 hi)))
    (fun x hx => determinedBy_reliableFace G w O T δ (hU x hx))
    (fun x _ => measurableSet_seedOpen G Dom D o sel J x)
    (fun x hx => measurableSet_reliableFace G w O T δ (hU x hx))
    (m := 1 - η / δ)
    (fun x hx => real_reliableFace_ge G w O T hδ0 hδ1 (hU x hx) (hGm x hx) (hrelay x hx) (hG x hx))
  -- step 3: seeds and reliable faces give reliable relays
  have h3 : (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D,
      seedOpen G Dom D o sel J x ∩ reliableFace G w (O \ Int) O T δ (U x)) ≤
      (prodBernoulli w).real (reachRelay G w Dom O Int o T δ) :=
    measureReal_mono (Set.iUnion₂_subset fun x hx =>
      seedOpen_inter_reliableFace_subset G w hIntO hOD hDDom o T δ sel J U hsel_sub hx (hU x hx)
        (hJD x hx) (hJO x hx) (hW3 x hx)) (measure_ne_top _ _)
  -- step 4: the relay step
  have h4 := real_reachRelayTarget_ge G w (Int := Int) hODom o T δ
  -- step 5: concatenation
  have h5 : (prodBernoulli w).real (reachRelayTarget G w Dom O Int o T δ) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) :=
    measureReal_mono (reachRelayTarget_subset G hODom w o T δ) (measure_ne_top _ _)
  have hm0 : 0 ≤ 1 - η / δ := by
    rw [sub_nonneg, div_le_one hδ0]
    exact hηδ
  have hδ' : 0 ≤ 1 - δ := by linarith
  calc ((prodBernoulli w).real (poor G Dom D o N)ᶜ - (1 - q ^ s) ^ k) * (1 - η / δ) * (1 - δ)
      ≤ (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D, seedOpen G Dom D o sel J x) *
          (1 - η / δ) * (1 - δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hm0) hδ'
    _ ≤ (prodBernoulli w).real (⋃ x ∈ outerBoundary G Dom D,
          seedOpen G Dom D o sel J x ∩ reliableFace G w (O \ Int) O T δ (U x)) * (1 - δ) :=
        mul_le_mul_of_nonneg_right h2 hδ'
    _ ≤ (prodBernoulli w).real (reachRelay G w Dom O Int o T δ) * (1 - δ) :=
        mul_le_mul_of_nonneg_right h3 hδ'
    _ ≤ (prodBernoulli w).real (reachRelayTarget G w Dom O Int o T δ) := h4
    _ ≤ (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := h5

end OneLevel

/-! ## The target-extension theorem -/

section Assembly

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

open scoped Classical

/-- **The shell-window data of one level.**  Boxes `Int ⊆ O ⊆ D ⊆ Dom` not containing the source;
for each contact `x` on the outer boundary of `D` a face `U x` in the shell `O \ Int`, a seed
`J x` in the layer `D \ O` joining `x` to every open site of the face, a selection `sel` of
contacts with pairwise disjoint seeds, and a reliability event `Gx x` determined by `O` whose
shell pattern fixes an open face site joined to the target inside `O` on all of `Gx x`. -/
structure LevelGeometry (Dom : Finset V) (o : V) (T : Set V) where
  D : Finset V
  O : Finset V
  Int : Finset V
  U : V → Finset V
  J : V → Finset V
  sel : Finset V → Finset V
  Gx : V → Set (SiteConfig V)
  hIntO : Int ⊆ O
  hOD : O ⊆ D
  hDDom : D ⊆ Dom
  ho : o ∉ D
  hU : ∀ x ∈ outerBoundary G Dom D, U x ⊆ O \ Int
  hJD : ∀ x ∈ outerBoundary G Dom D, J x ⊆ D
  hJO : ∀ x ∈ outerBoundary G Dom D, ∀ y ∈ J x, y ∉ O
  hW3 : ∀ x ∈ outerBoundary G Dom D, ∀ u ∈ U x,
    (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
      connWithin G (insert x (insert u (↑(J x) : Set V))) x u
  hsel_sub : ∀ K, sel K ⊆ K
  hsel_disj : ∀ K, (↑(sel K) : Set V).PairwiseDisjoint J
  hGdet : ∀ x ∈ outerBoundary G Dom D, DeterminedBy (Gx x) (↑O : Set V)
  hrelay : ∀ x ∈ outerBoundary G Dom D, ∀ ω ∈ Gx x, ∃ u ∈ U x, u ∈ ω ∧ ∀ ω' ∈ Gx x,
    ω' ∩ (↑(O \ Int) : Set V) = ω ∩ (↑(O \ Int) : Set V) → ω' ∈ toTarget G O T u

/-- **Manuscript-style shell-window data with support and relay in `D`.**  The event at a contact
declares its own finite support `S x ⊆ D`; matching the shell pattern fixes an open face site whose
continuation reaches the target inside `D`.  Thus a genuine contact outside `D` need not belong to
the support. -/
structure LevelGeometryD (Dom : Finset V) (o : V) (T : Set V) where
  D : Finset V
  O : Finset V
  Int : Finset V
  U : V → Finset V
  J : V → Finset V
  sel : Finset V → Finset V
  Gx : V → Set (SiteConfig V)
  S : V → Finset V
  hIntO : Int ⊆ O
  hOD : O ⊆ D
  hDDom : D ⊆ Dom
  hoDom : o ∈ Dom
  ho : o ∉ D
  hU : ∀ x ∈ outerBoundary G Dom D, U x ⊆ O \ Int
  hJD : ∀ x ∈ outerBoundary G Dom D, J x ⊆ D
  hJO : ∀ x ∈ outerBoundary G Dom D, ∀ y ∈ J x, y ∉ O
  hW3 : ∀ x ∈ outerBoundary G Dom D, ∀ u ∈ U x,
    (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
      connWithin G (insert x (insert u (↑(J x) : Set V))) x u
  hsel_sub : ∀ K, sel K ⊆ K
  hsel_disj : ∀ K, (↑(sel K) : Set V).PairwiseDisjoint J
  hS : ∀ x ∈ outerBoundary G Dom D, S x ⊆ D
  hGdet : ∀ x ∈ outerBoundary G Dom D, DeterminedBy (Gx x) (↑(S x) : Set V)
  hrelay : ∀ x ∈ outerBoundary G Dom D, ∀ ω ∈ Gx x, ∃ u ∈ U x, u ∈ ω ∧ ∀ ω' ∈ Gx x,
    ω' ∩ (↑(O \ Int) : Set V) = ω ∩ (↑(O \ Int) : Set V) → ω' ∈ toTarget G D T u

/-- **A concrete genuine-contact witness for `LevelGeometryD`.**  In the complete graph on the
integers, `1` is on the outer boundary of `D = {0,2}` inside `Dom = {0,1,2}`.  The event says that
some member of the two-site face `{0,2}` is open; that whole face is its support and target.  Thus
the witness neither contains its exterior contact nor designates one mandatory open relay. -/
def genuineContactLevelGeometryD :
    LevelGeometryD (SimpleGraph.completeGraph ℤ) ({0, 1, 2} : Finset ℤ) 1
      ({0, 2} : Set ℤ) where
  D := {0, 2}
  O := {0, 2}
  Int := ∅
  U := fun _ => {0, 2}
  J := fun _ => ∅
  sel := id
  Gx := fun _ => {ω : SiteConfig ℤ | ∃ u ∈ ({0, 2} : Finset ℤ), u ∈ ω}
  S := fun _ => {0, 2}
  hIntO := by simp
  hOD := by simp
  hDDom := by simp
  hoDom := by simp
  ho := by simp
  hU := by simp
  hJD := by simp
  hJO := by simp
  hW3 := by
    intro x hx u hu
    have hxu : x ≠ u := by
      intro h
      subst h
      exact (Finset.mem_sdiff.1
        (outerBoundary_subset (SimpleGraph.completeGraph ℤ) ({0, 1, 2} : Finset ℤ)
          {0, 2} hx)).2 hu
    refine ⟨⟨by simp, by simp⟩, ?_⟩
    exact SimpleGraph.Adj.reachable ((openSiteGraph_adj_iff' _ _ x u).2
      ⟨by simpa [hxu], by simp, by simp⟩)
  hsel_sub := fun _ => Finset.Subset.rfl
  hsel_disj := by
    intro K x hx y hy hxy
    simp
  hS := by simp
  hGdet := by
    intro x hx
    exact determinedBy_exists_mem ({0, 2} : Finset ℤ)
  hrelay := by
    intro x hx ω hω
    obtain ⟨u, hu, huω⟩ := hω
    refine ⟨u, hu, huω, ?_⟩
    intro ω' hω' hagree
    rw [toTarget, mem_connWithinSet_iff]
    have huω' : u ∈ ω' := by
      have hu' : u ∈ ω' ∩ (↑(({0, 2} : Finset ℤ) \ ∅) : Set ℤ) := by
        rw [hagree]
        exact ⟨huω, by simpa using hu⟩
      exact hu'.1
    refine ⟨u, by simpa using hu, ⟨⟨huω', Finset.mem_coe.2 hu⟩,
      SimpleGraph.Reachable.refl u⟩⟩

theorem one_mem_outerBoundary_genuineContact :
    (1 : ℤ) ∈ outerBoundary (SimpleGraph.completeGraph ℤ) ({0, 1, 2} : Finset ℤ)
      {0, 2} := by
  simp [outerBoundary]

/-- Both singleton configurations realize the genuine-contact event.  In particular, the event
does not secretly designate either member of its two-site relay face as the mandatory open site. -/
theorem genuineContact_two_event_witnesses :
    ({0} : SiteConfig ℤ) ∈ genuineContactLevelGeometryD.Gx 1 ∧
      ({2} : SiteConfig ℤ) ∈ genuineContactLevelGeometryD.Gx 1 := by
  constructor
  · exact ⟨0, by simp, by simp⟩
  · exact ⟨2, by simp, by simp⟩

/-- **Target extension, at an arbitrary parameter, with the cylinder bounds as hypotheses.**
Levels `lv 0, …, lv (L-1)` with nested boxes each avoiding the outermost layer of the previous
one, the box `B ⊆ D` of every level, every site of every level of parameter `q < 1`, at most `Δ`
neighbours per site inside `Dom`; the finitely many cylinder-event bounds are, for every level and
every potential contact, `P_q(Gx x) ≥ 1 - 3δ²`; and the numerical conditions are
`L δ (1 - q)^{Δ N} ≥ 1` and `(1 - q^s)^k ≤ δ`.  Then

`P(o ↔ B inside Dom) > 1 - δ  ⟹  P(o ↔ T inside Dom) ≥ (1 - 3δ)² (1 - δ)`.

No gluing inequality is used: the two applications of the decisive lemma are in
`real_target_ge_one_level`. -/
theorem targetExtension (Dom : Finset V) (o : V) (T : Set V) {Δ : ℕ}
    (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ} (hL : 0 < L)
    (lv : ℕ → LevelGeometry G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgate : ∀ i, i + 1 < L → ∀ x ∉ (lv i).D, ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D) (qI : unitInterval) (hq1 : (qI : ℝ) < 1)
    (w : V → unitInterval) (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ outerBoundary G Dom (lv i).D, N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D, ((lv i).J x).card ≤ s)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (hLδ : 1 ≤ (L : ℝ) * δ * (1 - (qI : ℝ)) ^ (Δ * N)) (hk : (1 - (qI : ℝ) ^ s) ^ k ≤ δ)
    (hG : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * δ ^ 2 ≤ (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - δ < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hq0 : (0 : ℝ) ≤ qI := qI.2.1
  have hw' : ∀ i < L, ∀ y ∈ (lv i).D, (w y : ℝ) ≤ qI := fun i hi y hy => by rw [hw i hi y hy]
  -- a level with many contacts
  obtain ⟨i, hi, hrich⟩ := exists_level_real_poor_compl_gt G Dom o N Δ hq0 hq1 hdeg hL
    (fun i => (lv i).D) w (fun i hi => (lv i).hDDom) hnest hgate hw' (fun i hi => (lv i).ho) hB
    hLδ hsrc
  -- the one-level theorem at that level
  have hη : 3 * δ ^ 2 ≤ δ := by nlinarith
  have hGw : ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * δ ^ 2 ≤ (prodBernoulli w).real ((lv i).Gx x) := by
    intro x hx
    have hGm : MeasurableSet ((lv i).Gx x) :=
      ((lv i).hGdet x hx).measurableSet_of_finset
    have htrans := prodBernoulli_real_eq_of_determinedBy (fun _ : V => qI) w
      (F := (↑(lv i).O : Set V))
      (fun y hy => ((hw i hi y ((lv i).hOD (Finset.mem_coe.1 hy)))).symm) ((lv i).hGdet x hx) hGm
    rw [← htrans]
    exact hG i hi x hx
  have hone := real_target_ge_one_level G w (lv i).hIntO (lv i).hOD (lv i).hDDom o T N k s hq0
    hq1.le (lv i).sel (lv i).J (lv i).U (lv i).Gx (lv i).hsel_sub (hsel_card i hi)
    (lv i).hsel_disj (lv i).hU (lv i).hJD (lv i).hJO (hs i hi) (lv i).hW3
    (fun x hx y hy => by rw [hw i hi y ((lv i).hJD x hx hy)])
    (fun x hx => ((lv i).hGdet x hx).measurableSet_of_finset) (lv i).hrelay hδ0 (by linarith) hη
    hGw
  have h3 : 3 * δ ^ 2 / δ = 3 * δ := by
    field_simp
  rw [h3] at hone
  have hA : 1 - 3 * δ ≤ (prodBernoulli w).real (poor G Dom (lv i).D o N)ᶜ - (1 - (qI : ℝ) ^ s) ^ k := by
    linarith
  have h13 : 0 ≤ 1 - 3 * δ := by linarith
  have h1 : 0 ≤ 1 - δ := by linarith
  calc (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ)
      ≤ ((prodBernoulli w).real (poor G Dom (lv i).D o N)ᶜ - (1 - (qI : ℝ) ^ s) ^ k) *
          (1 - 3 * δ) * (1 - δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h13) h1
    _ ≤ (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := hone

/-- **Target extension with the gate relative to the ambient domain.**  This is the natural form:
the gate is used only at contacts in `outerBoundary G Dom (lv i).D`, hence only at vertices of
`Dom`. -/
theorem targetExtension_rel (Dom : Finset V) (o : V) (T : Set V) {Δ : ℕ}
    (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ} (hL : 0 < L)
    (lv : ℕ → LevelGeometry G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ (lv i).D →
      ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D) (qI : unitInterval) (hq1 : (qI : ℝ) < 1)
    (w : V → unitInterval) (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D, ((lv i).J x).card ≤ s)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (hLδ : 1 ≤ (L : ℝ) * δ * (1 - (qI : ℝ)) ^ (Δ * N))
    (hk : (1 - (qI : ℝ) ^ s) ^ k ≤ δ)
    (hG : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * δ ^ 2 ≤ (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - δ < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hq0 : (0 : ℝ) ≤ qI := qI.2.1
  have hw' : ∀ i < L, ∀ y ∈ (lv i).D, (w y : ℝ) ≤ qI := fun i hi y hy => by
    rw [hw i hi y hy]
  obtain ⟨i, hi, hrich⟩ := exists_level_real_poor_compl_gt_rel G Dom o N Δ hq0 hq1 hdeg hL
    (fun i => (lv i).D) w (fun i hi => (lv i).hDDom) hnest hgateRel hw'
    (fun i hi => (lv i).ho) hB hLδ hsrc
  have hη : 3 * δ ^ 2 ≤ δ := by nlinarith
  have hGw : ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * δ ^ 2 ≤ (prodBernoulli w).real ((lv i).Gx x) := by
    intro x hx
    have hGm : MeasurableSet ((lv i).Gx x) :=
      ((lv i).hGdet x hx).measurableSet_of_finset
    have htrans := prodBernoulli_real_eq_of_determinedBy (fun _ : V => qI) w
      (F := (↑(lv i).O : Set V))
      (fun y hy => ((hw i hi y ((lv i).hOD (Finset.mem_coe.1 hy)))).symm)
      ((lv i).hGdet x hx) hGm
    rw [← htrans]
    exact hG i hi x hx
  have hone := real_target_ge_one_level G w (lv i).hIntO (lv i).hOD (lv i).hDDom o T
    N k s hq0 hq1.le (lv i).sel (lv i).J (lv i).U (lv i).Gx (lv i).hsel_sub
    (hsel_card i hi) (lv i).hsel_disj (lv i).hU (lv i).hJD (lv i).hJO (hs i hi)
    (lv i).hW3 (fun x hx y hy => by rw [hw i hi y ((lv i).hJD x hx hy)])
    (fun x hx => ((lv i).hGdet x hx).measurableSet_of_finset) (lv i).hrelay hδ0
    (by linarith) hη hGw
  have h3 : 3 * δ ^ 2 / δ = 3 * δ := by
    field_simp
  rw [h3] at hone
  have hA : 1 - 3 * δ ≤
      (prodBernoulli w).real (poor G Dom (lv i).D o N)ᶜ - (1 - (qI : ℝ) ^ s) ^ k := by
    linarith
  have h13 : 0 ≤ 1 - 3 * δ := by linarith
  have h1 : 0 ≤ 1 - δ := by linarith
  calc (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ)
      ≤ ((prodBernoulli w).real (poor G Dom (lv i).D o N)ᶜ - (1 - (qI : ℝ) ^ s) ^ k) *
          (1 - 3 * δ) * (1 - δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h13) h1
    _ ≤ (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := hone

/-- **Target extension with event support and relay in `D`, using the relative gate.**  This is the
manuscript interface for an outer-boundary window.  Its only additional mathematical input is the
isolated pinned-site gluing inequality used in `real_target_ge_one_level_D`. -/
theorem targetExtension_D (hgl : PinnedSiteGluing) (Dom : Finset V) (o : V) (T : Set V)
    {Δ : ℕ} (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ} (hL : 0 < L)
    (lv : ℕ → LevelGeometryD G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ (lv i).D →
      ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D) (qI : unitInterval) (hq1 : (qI : ℝ) < 1)
    (w : V → unitInterval) (hwo : w o = 1)
    (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D, ((lv i).J x).card ≤ s)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (hLδ : 1 ≤ (L : ℝ) * δ * (1 - (qI : ℝ)) ^ (Δ * N))
    (hk : (1 - (qI : ℝ) ^ s) ^ k ≤ δ)
    (hG : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * δ ^ 2 ≤ (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - δ < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hq0 : (0 : ℝ) ≤ qI := qI.2.1
  have hw' : ∀ i < L, ∀ y ∈ (lv i).D, (w y : ℝ) ≤ qI := fun i hi y hy => by
    rw [hw i hi y hy]
  obtain ⟨i, hi, hrich⟩ := exists_level_real_poor_compl_gt_rel G Dom o N Δ hq0 hq1 hdeg hL
    (fun i => (lv i).D) w (fun i hi => (lv i).hDDom) hnest hgateRel hw'
    (fun i hi => (lv i).ho) hB hLδ hsrc
  have hη : 3 * δ ^ 2 ≤ δ := by nlinarith
  have hGw : ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * δ ^ 2 ≤ (prodBernoulli w).real ((lv i).Gx x) := by
    intro x hx
    have hGm : MeasurableSet ((lv i).Gx x) :=
      ((lv i).hGdet x hx).measurableSet_of_finset
    have htrans := prodBernoulli_real_eq_of_determinedBy (fun _ : V => qI) w
      (F := (↑((lv i).S x) : Set V))
      (fun y hy => ((hw i hi y ((lv i).hS x hx (Finset.mem_coe.1 hy)))).symm)
      ((lv i).hGdet x hx) hGm
    rw [← htrans]
    exact hG i hi x hx
  have hone := real_target_ge_one_level_D G hgl w (lv i).hIntO (lv i).hOD
    (lv i).hDDom o (lv i).hoDom (lv i).ho hwo T N k s hq0 hq1.le (lv i).sel
    (lv i).J (lv i).U (lv i).Gx (lv i).hsel_sub (hsel_card i hi) (lv i).hsel_disj
    (lv i).hU (lv i).hJD (lv i).hJO (hs i hi) (lv i).hW3
    (fun x hx y hy => by rw [hw i hi y ((lv i).hJD x hx hy)])
    (fun x hx => ((lv i).hGdet x hx).measurableSet_of_finset) (lv i).hrelay hδ0
    (by linarith) hη hGw
  have h3 : 3 * δ ^ 2 / δ = 3 * δ := by field_simp
  rw [h3] at hone
  have hA : 1 - 3 * δ ≤
      (prodBernoulli w).real (poor G Dom (lv i).D o N)ᶜ - (1 - (qI : ℝ) ^ s) ^ k := by
    linarith
  have h13 : 0 ≤ 1 - 3 * δ := by linarith
  have h1 : 0 ≤ 1 - δ := by linarith
  calc
    (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ) ≤
        ((prodBernoulli w).real (poor G Dom (lv i).D o N)ᶜ -
          (1 - (qI : ℝ) ^ s) ^ k) * (1 - 3 * δ) * (1 - δ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h13) h1
    _ ≤ (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := hone

/-- `ε`–`δ` form of `targetExtension_D`, still with the domain-relative gate. -/
theorem targetExtension_eps_D (hgl : PinnedSiteGluing) (Dom : Finset V) (o : V) (T : Set V)
    {Δ : ℕ} (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ} (hL : 0 < L)
    (lv : ℕ → LevelGeometryD G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ (lv i).D →
      ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D) (qI : unitInterval) (hq1 : (qI : ℝ) < 1)
    (w : V → unitInterval) (hwo : w o = 1)
    (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D, ((lv i).J x).card ≤ s)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hLδ : 1 ≤ (L : ℝ) * (ε / 8) * (1 - (qI : ℝ)) ^ (Δ * N))
    (hk : (1 - (qI : ℝ) ^ s) ^ k ≤ ε / 8)
    (hG : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * (ε / 8) ^ 2 ≤ (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - ε / 8 < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    1 - ε < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have h := targetExtension_D G hgl Dom o T hdeg hL lv hnest hgateRel hB qI hq1 w hwo hw
    N k s hsel_card hs (δ := ε / 8) (by linarith) (by linarith) hLδ hk hG hsrc
  set δ : ℝ := ε / 8 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 / 8 := by rw [hδ]; linarith
  have hcube : 1 - 7 * δ ≤ (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ) := by
    have : 0 ≤ δ ^ 2 * (5 - 3 * δ) := mul_nonneg (sq_nonneg δ) (by linarith)
    nlinarith
  have hε : 1 - ε < 1 - 7 * δ := by rw [hδ]; linarith
  linarith

/-- The original global-gate statement is a direct specialization of `targetExtension_rel`. -/
theorem targetExtension_via_rel (Dom : Finset V) (o : V) (T : Set V) {Δ : ℕ}
    (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ} (hL : 0 < L)
    (lv : ℕ → LevelGeometry G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgate : ∀ i, i + 1 < L → ∀ x ∉ (lv i).D, ∀ y ∈ (lv i).D,
      G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D) (qI : unitInterval) (hq1 : (qI : ℝ) < 1)
    (w : V → unitInterval) (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D, ((lv i).J x).card ≤ s)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3)
    (hLδ : 1 ≤ (L : ℝ) * δ * (1 - (qI : ℝ)) ^ (Δ * N))
    (hk : (1 - (qI : ℝ) ^ s) ^ k ≤ δ)
    (hG : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * δ ^ 2 ≤ (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - δ < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  exact targetExtension_rel G Dom o T hdeg hL lv hnest
    (fun i hi x _ => hgate i hi x) hB qI hq1 w hw N k s hsel_card hs hδ0 hδ1 hLδ hk hG hsrc

/-- **Target extension in the `ε`–`δ` form of the manuscript**, with the explicit choice
`δ = ε / 8`: from `P(o ↔ B) > 1 - ε/8` to `P(o ↔ T) > 1 - ε`.  The number `δ` depends on `ε`
alone, before the geometry and the parameter. -/
theorem targetExtension_eps (Dom : Finset V) (o : V) (T : Set V) {Δ : ℕ}
    (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ} (hL : 0 < L)
    (lv : ℕ → LevelGeometry G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgate : ∀ i, i + 1 < L → ∀ x ∉ (lv i).D, ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D) (qI : unitInterval) (hq1 : (qI : ℝ) < 1)
    (w : V → unitInterval) (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ outerBoundary G Dom (lv i).D, N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D, ((lv i).J x).card ≤ s)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hLδ : 1 ≤ (L : ℝ) * (ε / 8) * (1 - (qI : ℝ)) ^ (Δ * N))
    (hk : (1 - (qI : ℝ) ^ s) ^ k ≤ ε / 8)
    (hG : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * (ε / 8) ^ 2 ≤ (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - ε / 8 < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    1 - ε < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have h := targetExtension G Dom o T hdeg hL lv hnest hgate hB qI hq1 w hw N k s hsel_card hs
    (δ := ε / 8) (by linarith) (by linarith) hLδ hk hG hsrc
  set δ : ℝ := ε / 8 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 / 8 := by rw [hδ]; linarith
  have hcube : 1 - 7 * δ ≤ (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ) := by
    have : 0 ≤ δ ^ 2 * (5 - 3 * δ) := mul_nonneg (sq_nonneg δ) (by linarith)
    nlinarith
  have hε : 1 - ε < 1 - 7 * δ := by rw [hδ]; linarith
  linarith

/-- **Relative-gate target extension in the `ε`–`δ` form of the manuscript.** -/
theorem targetExtension_eps_rel (Dom : Finset V) (o : V) (T : Set V) {Δ : ℕ}
    (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ} (hL : 0 < L)
    (lv : ℕ → LevelGeometry G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ (lv i).D →
      ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D) (qI : unitInterval) (hq1 : (qI : ℝ) < 1)
    (w : V → unitInterval) (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D, ((lv i).J x).card ≤ s)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hLδ : 1 ≤ (L : ℝ) * (ε / 8) * (1 - (qI : ℝ)) ^ (Δ * N))
    (hk : (1 - (qI : ℝ) ^ s) ^ k ≤ ε / 8)
    (hG : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * (ε / 8) ^ 2 ≤ (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - ε / 8 < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    1 - ε < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have h := targetExtension_rel G Dom o T hdeg hL lv hnest hgateRel hB qI hq1 w hw N k s
    hsel_card hs (δ := ε / 8) (by linarith) (by linarith) hLδ hk hG hsrc
  set δ : ℝ := ε / 8 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 / 8 := by rw [hδ]; linarith
  have hcube : 1 - 7 * δ ≤ (1 - 3 * δ) * (1 - 3 * δ) * (1 - δ) := by
    have : 0 ≤ δ ^ 2 * (5 - 3 * δ) := mul_nonneg (sq_nonneg δ) (by linarith)
    nlinarith
  have hε : 1 - ε < 1 - 7 * δ := by rw [hδ]; linarith
  linarith

/-- The original global-gate `ε`–`δ` statement is a direct specialization of
`targetExtension_eps_rel`. -/
theorem targetExtension_eps_via_rel (Dom : Finset V) (o : V) (T : Set V) {Δ : ℕ}
    (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Δ) {L : ℕ} (hL : 0 < L)
    (lv : ℕ → LevelGeometry G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgate : ∀ i, i + 1 < L → ∀ x ∉ (lv i).D, ∀ y ∈ (lv i).D,
      G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D) (qI : unitInterval) (hq1 : (qI : ℝ) < 1)
    (w : V → unitInterval) (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI) (N k s : ℕ)
    (hsel_card : ∀ i < L, ∀ K ⊆ outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D, ((lv i).J x).card ≤ s)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hLδ : 1 ≤ (L : ℝ) * (ε / 8) * (1 - (qI : ℝ)) ^ (Δ * N))
    (hk : (1 - (qI : ℝ) ^ s) ^ k ≤ ε / 8)
    (hG : ∀ i < L, ∀ x ∈ outerBoundary G Dom (lv i).D,
      1 - 3 * (ε / 8) ^ 2 ≤ (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - ε / 8 < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    1 - ε < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  exact targetExtension_eps_rel G Dom o T hdeg hL lv hnest
    (fun i hi x _ => hgate i hi x) hB qI hq1 w hw N k s hsel_card hs hε0 hε1 hLδ hk hG hsrc

end Assembly

end KNAll.Site.TargetExt

end
