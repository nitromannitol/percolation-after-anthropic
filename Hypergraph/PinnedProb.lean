import Hypergraph.SiteStatements

/-!
# Pinned probabilities

Later stages of the development condition on a finite transcript that fixes the states of finitely
many coordinates.  Genuine conditional probabilities would carry a positive-denominator side
condition through every statement, so instead we substitute the pinned values into the configuration
and take an ordinary product probability.  The result is denominator-free and total: `pinnedProb` is
defined for every pinning, including impossible ones.

* `substitute R val ω` is `ω` overwritten on `R` by the prescribed values `val`.
* `pinnedProb p R val A` is the `prodBernoulli p`-probability of `A` after that overwriting.

The workhorse is `pinnedProb_union_eq`: enlarging the pinned set by coordinates that the event
cannot see leaves the pinned probability alone.  It is the form in which the later macro-exploration
arguments use independence, and it needs no measure theory beyond congruence of a measure along an
equality of sets.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {ι : Type*}

/-! ## Overwriting coordinates -/

open Classical in
/-- Overwrite the coordinates in `R` by the prescribed values. -/
def substitute (R : Set ι) (val : ι → Prop) (ω : Set ι) : Set ι :=
  {i | if i ∈ R then val i else i ∈ ω}

/-- On a pinned coordinate the substituted configuration takes the prescribed value. -/
theorem mem_substitute_of_mem {R : Set ι} (val : ι → Prop) {ω : Set ι} {i : ι} (hi : i ∈ R) :
    i ∈ substitute R val ω ↔ val i := by
  classical
  simp [substitute, hi]

/-- Off the pinned set the substituted configuration agrees with the original one. -/
theorem mem_substitute_of_notMem {R : Set ι} (val : ι → Prop) {ω : Set ι} {i : ι} (hi : i ∉ R) :
    i ∈ substitute R val ω ↔ i ∈ ω := by
  classical
  simp [substitute, hi]

/-- Pinning no coordinate is the identity. -/
@[simp] theorem substitute_empty (val : ι → Prop) (ω : Set ι) :
    substitute (∅ : Set ι) val ω = ω := by
  ext i
  exact mem_substitute_of_notMem val (notMem_empty i)

/-- Substitution is measurable for the product σ-algebra on `Set ι`: each coordinate of the output
is either a constant or the corresponding coordinate of the input. -/
theorem measurable_substitute (R : Set ι) (val : ι → Prop) :
    Measurable (substitute R val) := by
  classical
  refine measurable_set_iff.2 fun i => ?_
  by_cases hi : i ∈ R
  · have h : (fun ω : Set ι => i ∈ substitute R val ω) = fun _ : Set ι => val i := by
      funext ω
      exact propext (mem_substitute_of_mem val hi)
    rw [h]
    exact measurable_const
  · have h : (fun ω : Set ι => i ∈ substitute R val ω) = fun ω : Set ι => i ∈ ω := by
      funext ω
      exact propext (mem_substitute_of_notMem val hi)
    rw [h]
    exact measurable_set_mem i

/-! ## Pinned probabilities -/

/-- The probability of `A` when the coordinates in `R` are pinned to `val`. -/
def pinnedProb (p : ι → unitInterval) (R : Set ι) (val : ι → Prop) (A : Set (Set ι)) : ℝ :=
  (prodBernoulli p).real (substitute R val ⁻¹' A)

/-- Pinning nothing changes nothing. -/
theorem pinnedProb_empty (p : ι → unitInterval) (val : ι → Prop) (A : Set (Set ι)) :
    pinnedProb p ∅ val A = (prodBernoulli p).real A := by
  have h : substitute (∅ : Set ι) val ⁻¹' A = A := by
    ext ω
    simp
  rw [pinnedProb, h]

/-- **The irrelevant-extension lemma.**  If `A` is determined by the coordinates in `S`, and the
extra pinned coordinates `T` meet `S` only inside `R`, then extending the pinning from `R` to
`R ∪ T` does not change the probability.

The proof is pointwise: on `S` the two substituted configurations agree, so `A` cannot tell them
apart, hence the two preimages are the same set. -/
theorem pinnedProb_union_eq (p : ι → unitInterval) {R T S : Set ι} (val : ι → Prop)
    {A : Set (Set ι)} (hA : DeterminedBy A S) (hTS : Disjoint T (S \ R)) :
    pinnedProb p (R ∪ T) val A = pinnedProb p R val A := by
  have hagree : ∀ ω : Set ι, ∀ i ∈ S,
      (i ∈ substitute (R ∪ T) val ω ↔ i ∈ substitute R val ω) := by
    intro ω i hiS
    by_cases hiR : i ∈ R
    · rw [mem_substitute_of_mem val (mem_union_left T hiR), mem_substitute_of_mem val hiR]
    · have hiT : i ∉ T := fun hiT => Set.disjoint_left.1 hTS hiT ⟨hiS, hiR⟩
      have hiRT : i ∉ R ∪ T := by simp [hiR, hiT]
      rw [mem_substitute_of_notMem val hiRT, mem_substitute_of_notMem val hiR]
  have hpre : substitute (R ∪ T) val ⁻¹' A = substitute R val ⁻¹' A := by
    ext ω
    simp only [Set.mem_preimage]
    refine (determinedBy_iff A S).1 hA _ _ ?_
    ext i
    simp only [Set.mem_inter_iff]
    exact ⟨fun h => ⟨(hagree ω i h.2).1 h.1, h.2⟩, fun h => ⟨(hagree ω i h.2).2 h.1, h.2⟩⟩
  rw [pinnedProb, pinnedProb, hpre]

/-- **Pinning coordinates the event does not see.**  If `A` is determined by the complement of `R`,
then pinning inside `R` does not change its probability. -/
theorem pinnedProb_eq_of_determinedBy_compl (p : ι → unitInterval) (R : Set ι) (val : ι → Prop)
    {A : Set (Set ι)} (hA : DeterminedBy A Rᶜ) :
    pinnedProb p R val A = (prodBernoulli p).real A := by
  have hdisj : Disjoint R (Rᶜ \ ∅) := by
    rw [Set.sdiff_empty]
    exact disjoint_compl_right
  have h := pinnedProb_union_eq p (R := (∅ : Set ι)) (T := R) (S := Rᶜ) val hA hdisj
  rw [Set.empty_union] at h
  rw [h, pinnedProb_empty]

end KNAll.Site

end
