import Hypergraph.HyperExpose
import Hypergraph.HyperFibre
import Hypergraph.HyperOneCluster

/-!
# The four-quantity comparison, indexed by label sets

The induction behind the finite hyperedge inequality compares four expectations indexed by the set of
exposed labels found open, and closes by the four functions theorem of Ahlswede and Daykin, available
as `four_functions_theorem_univ`.  That theorem consumes a pointwise inequality whose two right-hand
quantities are evaluated at the meet and at the join of the two indices.  This module states and
proves that comparison with label sets as the index from the outset, and settles how much of the
bookkeeping of `KN/HyperExpose.lean` the comparison actually consumes.

## What is defined here

* `anchoredSource` — a source described by a set of labels rather than by a set of vertices: for a
  label type `M`, an anchor map `anchor : M → Set V` and an ambient vertex set `A`, the subset
  `Q ⊆ M` determines the vertex set `(⋃ m ∈ Q, anchor m) ∩ A`.  Unions of label sets go to unions of
  sources exactly (`anchoredSource_union`); intersections give only the inclusion
  `anchoredSource_inter_subset`, and `exists_anchoredSource_inter_ssubset` refutes the reverse
  inclusion.  `anchoredSource_incidence` identifies the construction with the `traceOutside` of
  `KN/HyperTrace.lean` when the anchor is the incidence map and the ambient set is the complement of
  the exposed set, so the counterexamples of that module apply here verbatim.

* `avoidBlock` — the single quantity out of which all four functions are built.  For a base avoided
  set `B` and a functional `F` it is the expectation of `fibreMean H S F` on the event that the
  cluster of `S` avoids `B` together with the source anchored at the label set `N`:

      avoidBlock H S anchor A B F N
        = ∫ ω in avoidEvent H S (B ∪ anchoredSource anchor A N), fibreMean H S F ω .

  It is a function of the LABEL set `N`.  The anchored source occurs inside the definition and is
  never itself an index.

## The four functions

With a source `S`, base avoided sets `X` and `Y`, and increasing nonnegative functionals `f` and `g`
fixed, the four functions of `Set M → ℝ` are

    E N  = avoidBlock H S anchor A  X       f                    N
    Y N  = avoidBlock H S anchor A  Y       g                    N
    M N  = avoidBlock H S anchor A (X ∪ Y) (fun _ => 1)          N
    X N  = avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K)  N

and `avoidBlock_mul_le` is

    E N * Y N'  ≤  M (N ∪ N') * X (N ∩ N') .

The third is the probability of an avoidance event, by `avoidBlock_one`; writing it as a block with
the constant integrand keeps all four of the same shape, which is what the application of the four
functions theorem wants.  Everything is a finite integral or a finite weighted sum against
`prodBernoulli`; no event is conditioned on and no denominator appears.  `avoidBlock_eq_sum_cluster`
expands a block over the possible clusters, the denominator-free replacement for a conditional
expectation, from `setIntegral_fibreMean_eq_sum`.

`sum_avoidBlock_mul_le` and `sum_weight_avoidBlock_mul_le` are the applications of
`four_functions_theorem_univ` on the lattice `Set M`, the second carrying a product weight on the
label sets, which satisfies the lattice condition with equality by `weight_inter_mul_union` and so
passes through the pointwise comparison.

## How much of the record the comparison uses

`avoidIntegral_mul_le_of_lax` is the kernel, and it isolates the answer.  Writing `T` and `T'` for
the two sources and `Tu`, `Ti` for whatever is offered in the join and the meet slots, the proof of
the comparison uses exactly

    Tu ⊆ T ∪ T'    and    Ti ⊆ T ∩ T' ,

and nothing else about them.  Both inclusions point the harmless way: a smaller avoided set gives a
larger block, because a block is decreasing in its avoided set (`avoidIntegral_antitone_avoided`).

So the exact intersection identity of `KN/HyperExpose.lean` is **not** what forces the label
indexing here.  `avoidIntegral_mul_le_vertex` records the consequence: the same comparison holds with
plain vertex sets as the index, where the join and meet slots are the honest `T ∪ T'` and `T ∩ T'`,
and the lax inclusion of `traceOutside_inter_subset` is enough to feed it.  This matches
`KN/HyperOneCluster.lean`, which runs the whole induction with a vertex record.

What the exactness does buy is stated in `record_mul_le_of_reduced`: for an *arbitrary* quadruple of
functions on the lattice of reduced label sets, a comparison of the reduced model transports to a
comparison indexed by the original label sets, by `record_union` and `record_inter` alone.  That
transport is false for the vertex record, and `exists_traceOutside_four_functions_fail` exhibits a
hypergraph, two label sets and a log-supermodular `Ψ` for which the transported inequality fails
outright.  The `Ψ` there is *increasing* in the vertex set, and that is the whole boundary: the
blocks of this module are decreasing in the record, and for decreasing functions antitonicity absorbs
the lax intersection, while for increasing ones it works the wrong way and nothing absorbs it.

The place where the labels are genuinely irreplaceable is upstream, in `KN/HyperExpose.lean` itself:
`prodBernoulli_map_reduceConfig` holds because `originalLabel` is injective, so the reduced model is a
relabelling of `E` and carries the product law.  The vertex record is not injective, by
`exists_traceOutside_not_injective`, so a reduction built on traces would merge two exposed labels
and the outer sum of an exposure step would no longer be an expectation.

## References

* R. Ahlswede, D. E. Daykin, *An inequality for the weights of two families of sets, their unions
  and intersections*, Z. Wahrsch. Verw. Gebiete 43 (1978), 183–185.
* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation
  and related processes*, Random Structures Algorithms 29 (2006), Thm. 1.1.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Literature.BHK2006 (weight weight_nonneg weight_inter_mul_union sum_ind_mono)
open scoped Classical

variable {V E M : Type*}

/-! ## Anchored sources

A source given by a set of labels.  The anchor map sends a label to the vertices it contributes, and
the ambient vertex set cuts the result down to the model currently in play.
-/

/-- The source determined by the label set `Q`: the union of the anchors of the labels of `Q`,
intersected with the ambient vertex set `A`. -/
def anchoredSource (anchor : M → Set V) (A : Set V) (Q : Set M) : Set V :=
  (⋃ m ∈ Q, anchor m) ∩ A

theorem mem_anchoredSource_iff (anchor : M → Set V) (A : Set V) (Q : Set M) (x : V) :
    x ∈ anchoredSource anchor A Q ↔ (∃ m ∈ Q, x ∈ anchor m) ∧ x ∈ A := by
  constructor
  · rintro ⟨hx, hA⟩
    obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨⟨m, hm, hxm⟩, hA⟩
  · rintro ⟨⟨m, hm, hxm⟩, hA⟩
    exact ⟨Set.mem_iUnion₂.2 ⟨m, hm, hxm⟩, hA⟩

/-- An anchored source lies in the ambient vertex set. -/
theorem anchoredSource_subset_ambient (anchor : M → Set V) (A : Set V) (Q : Set M) :
    anchoredSource anchor A Q ⊆ A := Set.inter_subset_right

theorem anchoredSource_empty (anchor : M → Set V) (A : Set V) :
    anchoredSource anchor A (∅ : Set M) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨⟨m, hm, -⟩, -⟩ := (mem_anchoredSource_iff anchor A ∅ x).1 hx
  exact hm

/-- **The assignment is monotone.**  More labels anchor more vertices. -/
theorem anchoredSource_mono (anchor : M → Set V) (A : Set V) {Q Q' : Set M} (h : Q ⊆ Q') :
    anchoredSource anchor A Q ⊆ anchoredSource anchor A Q' := by
  intro x hx
  obtain ⟨⟨m, hm, hxm⟩, hA⟩ := (mem_anchoredSource_iff anchor A Q x).1 hx
  exact (mem_anchoredSource_iff anchor A Q' x).2 ⟨⟨m, h hm, hxm⟩, hA⟩

/-- **Unions of label sets go to unions of sources, exactly.**  A vertex is anchored at `Q ∪ Q'`
precisely when a single label of `Q`, or a single label of `Q'`, anchors it. -/
theorem anchoredSource_union (anchor : M → Set V) (A : Set V) (Q Q' : Set M) :
    anchoredSource anchor A (Q ∪ Q')
      = anchoredSource anchor A Q ∪ anchoredSource anchor A Q' := by
  ext x
  simp only [Set.mem_union, mem_anchoredSource_iff]
  constructor
  · rintro ⟨⟨m, hm | hm, hxm⟩, hA⟩
    · exact Or.inl ⟨⟨m, hm, hxm⟩, hA⟩
    · exact Or.inr ⟨⟨m, hm, hxm⟩, hA⟩
  · rintro (⟨⟨m, hm, hxm⟩, hA⟩ | ⟨⟨m, hm, hxm⟩, hA⟩)
    · exact ⟨⟨m, Or.inl hm, hxm⟩, hA⟩
    · exact ⟨⟨m, Or.inr hm, hxm⟩, hA⟩

/-- **Intersections of label sets survive only one way.**  A vertex anchored at a label common to
`Q` and `Q'` is of course anchored at `Q` and at `Q'`.  The reverse inclusion fails, by
`exists_anchoredSource_inter_ssubset`: a vertex can be anchored at `Q` by one label and at `Q'` by a
different one, and then nothing anchors it at `Q ∩ Q'`.

So the assignment is a homomorphism for unions and only a lax one for intersections, and the source
of a label set does not determine the label set.  The inclusion proved here is nevertheless in the
direction the comparison needs, because a smaller avoided set makes an avoidance event larger; that
is `avoidIntegral_mul_le_of_lax`, and it is the reason the weaker direction is enough. -/
theorem anchoredSource_inter_subset (anchor : M → Set V) (A : Set V) (Q Q' : Set M) :
    anchoredSource anchor A (Q ∩ Q')
      ⊆ anchoredSource anchor A Q ∩ anchoredSource anchor A Q' :=
  Set.subset_inter (anchoredSource_mono anchor A Set.inter_subset_left)
    (anchoredSource_mono anchor A Set.inter_subset_right)

/-- **The vertex record of `KN/HyperTrace.lean` is an anchored source.**  Anchoring a label at its
incidence set, with the complement of the exposed set as ambient, gives exactly `traceOutside`. -/
theorem anchoredSource_incidence (H : Hypergraph V E) (Z : Set V) (I : Set E) :
    anchoredSource H.incidence Zᶜ I = traceOutside H Z I := by
  ext x
  rw [mem_anchoredSource_iff, mem_traceOutside_iff]
  constructor
  · rintro ⟨⟨e, he, hxe⟩, hZ⟩
    exact ⟨e, he, hxe, hZ⟩
  · rintro ⟨e, he, hxe, hZ⟩
    exact ⟨⟨e, he, hxe⟩, hZ⟩

/-- **The reverse inclusion of `anchoredSource_inter_subset` is false.**  One vertex, two labels,
both anchored at that vertex: the label sets `{true}` and `{false}` are disjoint, so nothing is
anchored at their intersection, while each of them anchors the whole vertex set.  The source of a
label set therefore forgets which labels the set contains. -/
theorem exists_anchoredSource_inter_ssubset :
    ∃ (W N : Type) (_ : Fintype W) (_ : Fintype N) (anchor : N → Set W) (A : Set W) (Q Q' : Set N),
      ¬ (anchoredSource anchor A Q ∩ anchoredSource anchor A Q'
          ⊆ anchoredSource anchor A (Q ∩ Q')) := by
  refine ⟨Unit, Bool, inferInstance, inferInstance, fun _ => Set.univ, Set.univ,
    {true}, {false}, ?_⟩
  intro hsub
  have h1 : (() : Unit) ∈ anchoredSource (fun _ : Bool => (Set.univ : Set Unit)) Set.univ {true} :=
    (mem_anchoredSource_iff _ _ _ _).2 ⟨⟨true, rfl, Set.mem_univ _⟩, Set.mem_univ _⟩
  have h2 : (() : Unit) ∈ anchoredSource (fun _ : Bool => (Set.univ : Set Unit)) Set.univ {false} :=
    (mem_anchoredSource_iff _ _ _ _).2 ⟨⟨false, rfl, Set.mem_univ _⟩, Set.mem_univ _⟩
  obtain ⟨⟨b, hb, -⟩, -⟩ := (mem_anchoredSource_iff _ _ _ _).1 (hsub ⟨h1, h2⟩)
  have hbt : b = true := hb.1
  have hbf : b = false := hb.2
  rw [hbt] at hbf
  exact Bool.noConfusion hbf

/-! ## Elementary behaviour of the avoidance integral

Two facts that `KN/HyperAvoid.lean` does not carry: the integral of a nonnegative functional is
nonnegative, and it decreases when the avoided set grows.  The second is what lets the comparison run
on inclusions rather than on identities.
-/

theorem avoidIntegral_nonneg (H : Hypergraph V E) (S X : Set V) {F : Set V → ℝ}
    (hF0 : ∀ K, 0 ≤ F K) : 0 ≤ avoidIntegral H S X F :=
  integral_nonneg fun _ => hF0 _

/-- **Avoiding more is harder.**  For a nonnegative integrand the avoidance integral decreases when
the avoided set grows: the avoidance event shrinks, by `avoidEvent_antitone`, and the integrand does
not change sign. -/
theorem avoidIntegral_antitone_avoided [Fintype E] (H : Hypergraph V E) (S : Set V)
    {W W' : Set V} (hW : W ⊆ W') {F : Set V → ℝ} (hF0 : ∀ K, 0 ≤ F K) :
    avoidIntegral H S W' F ≤ avoidIntegral H S W F := by
  rw [avoidIntegral_eq_sum H S W' F, avoidIntegral_eq_sum H S W F]
  exact sum_ind_mono (fun e => unitInterval.nonneg (H.prob e))
    (fun e => unitInterval.le_one (H.prob e)) (fun _ => hF0 _)
    (fun _ hω => avoidEvent_antitone H S hW hω)

/-! ## The kernel of the comparison

The comparison, before any record is fixed.  Two sources `T` and `T'` are added to the two base
avoided sets, and two further sets `Tu` and `Ti` are offered in the join and the meet slots.  The
proof uses `Tu ⊆ T ∪ T'` and `Ti ⊆ T ∩ T'`, and nothing else about them: both point the harmless way,
because a block decreases in its avoided set.
-/

/-- **The comparison from two inclusions.**  For increasing nonnegative `f` and `g`,

    avoidIntegral (X ∪ T) f · avoidIntegral (Y ∪ T') g
      ≤ P(avoid ((X ∪ Y) ∪ Tu)) · avoidIntegral ((X ∩ Y) ∪ Ti) (f · g)

whenever `Tu ⊆ T ∪ T'` and `Ti ⊆ T ∩ T'`.

The input is `avoidIntegral_mul_le_inter`, the hyperedge form of van den Berg, Häggström and Kahn's
Theorem 1.1, applied to the avoided sets `X ∪ T` and `Y ∪ T'`.  Its right-hand side carries the union
and the intersection of those two sets; the two hypotheses put `(X ∪ Y) ∪ Tu` inside the union and
`(X ∩ Y) ∪ Ti` inside the intersection, and both moves enlarge the corresponding quantity.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1] -/
theorem avoidIntegral_mul_le_of_lax [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (X Y T T' Tu Ti : Set V) (hu : Tu ⊆ T ∪ T') (hi : Ti ⊆ T ∩ T')
    {f g : Set V → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) :
    avoidIntegral H S (X ∪ T) f * avoidIntegral H S (Y ∪ T') g
      ≤ (prodBernoulli H.prob).real (avoidEvent H S ((X ∪ Y) ∪ Tu)) *
          avoidIntegral H S ((X ∩ Y) ∪ Ti) (fun K => f K * g K) := by
  have key := avoidIntegral_mul_le_inter H S (X ∪ T) (Y ∪ T') hf hg hf0 hg0
  have hsubU : (X ∪ Y) ∪ Tu ⊆ (X ∪ T) ∪ (Y ∪ T') := by
    refine Set.union_subset (fun x hx => ?_) fun x hx => ?_
    · rcases hx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · rcases hu hx with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
  have hsubI : (X ∩ Y) ∪ Ti ⊆ (X ∪ T) ∩ (Y ∪ T') := by
    refine Set.union_subset (fun x hx => ⟨Or.inl hx.1, Or.inl hx.2⟩) fun x hx => ?_
    exact ⟨Or.inr (hi hx).1, Or.inr (hi hx).2⟩
  have h1 : avoidIntegral H S ((X ∪ T) ∩ (Y ∪ T')) (fun K => f K * g K)
      ≤ avoidIntegral H S ((X ∩ Y) ∪ Ti) (fun K => f K * g K) :=
    avoidIntegral_antitone_avoided H S hsubI fun K => mul_nonneg (hf0 K) (hg0 K)
  have h2 : (prodBernoulli H.prob).real (avoidEvent H S ((X ∪ T) ∪ (Y ∪ T')))
      ≤ (prodBernoulli H.prob).real (avoidEvent H S ((X ∪ Y) ∪ Tu)) := by
    rw [← avoidIntegral_one H S ((X ∪ T) ∪ (Y ∪ T')), ← avoidIntegral_one H S ((X ∪ Y) ∪ Tu)]
    exact avoidIntegral_antitone_avoided H S hsubU fun _ => zero_le_one
  calc avoidIntegral H S (X ∪ T) f * avoidIntegral H S (Y ∪ T') g
      ≤ avoidIntegral H S ((X ∪ T) ∩ (Y ∪ T')) (fun K => f K * g K) *
          (prodBernoulli H.prob).real (avoidEvent H S ((X ∪ T) ∪ (Y ∪ T'))) := key
    _ ≤ avoidIntegral H S ((X ∩ Y) ∪ Ti) (fun K => f K * g K) *
          (prodBernoulli H.prob).real (avoidEvent H S ((X ∪ Y) ∪ Tu)) :=
        mul_le_mul h1 h2 measureReal_nonneg
          (avoidIntegral_nonneg H S _ fun K => mul_nonneg (hf0 K) (hg0 K))
    _ = (prodBernoulli H.prob).real (avoidEvent H S ((X ∪ Y) ∪ Tu)) *
          avoidIntegral H S ((X ∩ Y) ∪ Ti) (fun K => f K * g K) := mul_comm _ _

/-- **A vertex indexing satisfies the four functions hypothesis as well.**  Taking the join and the
meet slots to be the honest union and intersection of the two sources, the hypotheses of
`avoidIntegral_mul_le_of_lax` hold with equality.  So the exact intersection identity of
`KN/HyperExpose.lean` is not what the comparison needs: a record that only satisfies
`traceOutside_inter_subset` feeds this statement, which is why the induction of
`KN/HyperOneCluster.lean` runs on a vertex record. -/
theorem avoidIntegral_mul_le_vertex [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (X Y T T' : Set V) {f g : Set V → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) :
    avoidIntegral H S (X ∪ T) f * avoidIntegral H S (Y ∪ T') g
      ≤ (prodBernoulli H.prob).real (avoidEvent H S ((X ∪ Y) ∪ (T ∪ T'))) *
          avoidIntegral H S ((X ∩ Y) ∪ (T ∩ T')) (fun K => f K * g K) :=
  avoidIntegral_mul_le_of_lax H S X Y T T' (T ∪ T') (T ∩ T') Set.Subset.rfl Set.Subset.rfl
    hf hg hf0 hg0

/-! ## Blocks: the quantities the comparison compares

A block is the expectation of `fibreMean H S F` on an avoidance event whose avoided set is a fixed
base together with the source anchored at a label set.  The label set is the index; the source it
anchors appears only inside the avoided set.
-/

/-- The expectation of `F` at the cluster of `S`, on the event that the cluster avoids `B` together
with the source anchored at the label set `N`. -/
def avoidBlock (H : Hypergraph V E) (S : Set V) (anchor : M → Set V) (A : Set V) (B : Set V)
    (F : Set V → ℝ) (N : Set M) : ℝ :=
  ∫ ω in avoidEvent H S (B ∪ anchoredSource anchor A N), fibreMean H S F ω
    ∂(prodBernoulli H.prob)

/-- A block is an avoidance integral with the anchored source added to the avoided set. -/
theorem avoidBlock_eq_avoidIntegral (H : Hypergraph V E) (S : Set V) (anchor : M → Set V)
    (A B : Set V) (F : Set V → ℝ) (N : Set M) :
    avoidBlock H S anchor A B F N = avoidIntegral H S (B ∪ anchoredSource anchor A N) F := rfl

theorem avoidBlock_nonneg (H : Hypergraph V E) (S : Set V) (anchor : M → Set V) (A B : Set V)
    {F : Set V → ℝ} (hF0 : ∀ K, 0 ≤ F K) (N : Set M) : 0 ≤ avoidBlock H S anchor A B F N :=
  avoidIntegral_nonneg H S _ hF0

/-- At the constant one a block is the probability of its avoidance event.  This is the third of the
four functions. -/
theorem avoidBlock_one [Fintype E] (H : Hypergraph V E) (S : Set V) (anchor : M → Set V)
    (A B : Set V) (N : Set M) :
    avoidBlock H S anchor A B (fun _ => 1) N
      = (prodBernoulli H.prob).real (avoidEvent H S (B ∪ anchoredSource anchor A N)) := by
  rw [avoidBlock_eq_avoidIntegral]
  exact avoidIntegral_one H S _

/-- Blocks are monotone in the integrand. -/
theorem avoidBlock_mono [Fintype E] (H : Hypergraph V E) (S : Set V) (anchor : M → Set V)
    (A B : Set V) {F G : Set V → ℝ} (hFG : ∀ K, F K ≤ G K) (N : Set M) :
    avoidBlock H S anchor A B F N ≤ avoidBlock H S anchor A B G N :=
  avoidIntegral_mono H S _ hFG

/-- **A block is a decreasing function of its label set.**  More exposed labels anchor a larger
source, hence a larger avoided set.  This is the variance that makes the lax intersection of
`anchoredSource_inter_subset` harmless; `exists_traceOutside_four_functions_fail` shows that for an
increasing function of the record it is not. -/
theorem avoidBlock_antitone [Fintype E] (H : Hypergraph V E) (S : Set V) (anchor : M → Set V)
    (A B : Set V) {F : Set V → ℝ} (hF0 : ∀ K, 0 ≤ F K) {N N' : Set M} (h : N ⊆ N') :
    avoidBlock H S anchor A B F N' ≤ avoidBlock H S anchor A B F N :=
  avoidIntegral_antitone_avoided H S
    (Set.union_subset_union_right B (anchoredSource_mono anchor A h)) hF0

/-- **The denominator-free expansion of a block.**  Over a finite vertex type a block is the finite
sum over the possible clusters `K` of `F K` weighted by the probability that the cluster of `S` is
`K` and avoids the block's avoided set.  A cluster event of probability zero contributes zero, so no
conditioning and no normalization occur; this is `setIntegral_fibreMean_eq_sum`. -/
theorem avoidBlock_eq_sum_cluster [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (anchor : M → Set V) (A B : Set V) (F : Set V → ℝ) (N : Set M) :
    avoidBlock H S anchor A B F N
      = ∑ K : Finset V, F (↑K : Set V) *
          (prodBernoulli H.prob).real
            (clusterEvent H S (↑K : Set V) ∩
              avoidEvent H S (B ∪ anchoredSource anchor A N)) :=
  setIntegral_fibreMean_eq_sum H S F (measurableSet_avoidEvent H S _)

/-! ## The comparison, over label sets -/

/-- **The four-quantity comparison.**  With a source `S`, base avoided sets `X` and `Y`, and
increasing nonnegative functionals `f` and `g`,

    avoidBlock X f N * avoidBlock Y g N'
      ≤ avoidBlock (X ∪ Y) 1 (N ∪ N') * avoidBlock (X ∩ Y) (f · g) (N ∩ N') ,

the indices `N` and `N'` being sets of labels and the union and the intersection on the right being
operations on label sets.

The two facts about the indexing that the proof consumes are `anchoredSource_union`, used only as the
inclusion `⊆`, and `anchoredSource_inter_subset`; both are supplied to
`avoidIntegral_mul_le_of_lax`. -/
theorem avoidBlock_mul_le [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (anchor : M → Set V) (A X Y : Set V) {f g : Set V → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) (N N' : Set M) :
    avoidBlock H S anchor A X f N * avoidBlock H S anchor A Y g N'
      ≤ avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) (N ∪ N') *
          avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) (N ∩ N') := by
  have hu : anchoredSource anchor A (N ∪ N')
      ⊆ anchoredSource anchor A N ∪ anchoredSource anchor A N' :=
    le_of_eq (anchoredSource_union anchor A N N')
  rw [avoidBlock_one]
  exact avoidIntegral_mul_le_of_lax H S X Y (anchoredSource anchor A N)
    (anchoredSource anchor A N') (anchoredSource anchor A (N ∪ N'))
    (anchoredSource anchor A (N ∩ N')) hu (anchoredSource_inter_subset anchor A N N')
    hf hg hf0 hg0

/-- `avoidBlock_mul_le` in the shape the four functions theorem consumes: the meet and the join of
the two label sets, in that order. -/
theorem avoidBlock_inf_sup_mul_le [Fintype V] [Fintype E] (H : Hypergraph V E) (S : Set V)
    (anchor : M → Set V) (A X Y : Set V) {f g : Set V → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) (N N' : Set M) :
    avoidBlock H S anchor A X f N * avoidBlock H S anchor A Y g N'
      ≤ avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) (N ⊓ N') *
          avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) (N ⊔ N') := by
  calc avoidBlock H S anchor A X f N * avoidBlock H S anchor A Y g N'
      ≤ avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) (N ∪ N') *
          avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) (N ∩ N') :=
        avoidBlock_mul_le H S anchor A X Y hf hg hf0 hg0 N N'
    _ = avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) (N ⊓ N') *
          avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) (N ⊔ N') := mul_comm _ _

/-! ## The four functions theorem

The comparison is a pointwise statement about a pair of label sets, in the exact shape of the
hypothesis of `four_functions_theorem_univ` on the lattice `Set M`.  Summing over all label sets is
then immediate.  The second form carries a product weight on the label sets, which satisfies the
lattice condition with equality (`weight_inter_mul_union`), so the pointwise hypothesis survives
multiplication by it; that is the form in which an exposure step is summed.
-/

/-- **Ahlswede–Daykin, applied.**  Summing the four blocks over all label sets.
[cite: AhlswedeDaykin1978] -/
theorem sum_avoidBlock_mul_le [Fintype V] [Fintype E] [Fintype M] (H : Hypergraph V E) (S : Set V)
    (anchor : M → Set V) (A X Y : Set V) {f g : Set V → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) :
    (∑ N : Set M, avoidBlock H S anchor A X f N) *
        ∑ N : Set M, avoidBlock H S anchor A Y g N
      ≤ (∑ N : Set M, avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) N) *
          ∑ N : Set M, avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) N :=
  four_functions_theorem_univ
    (fun N : Set M => avoidBlock H S anchor A X f N)
    (fun N : Set M => avoidBlock H S anchor A Y g N)
    (fun N : Set M => avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) N)
    (fun N : Set M => avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) N)
    (fun N => avoidBlock_nonneg H S anchor A X hf0 N)
    (fun N => avoidBlock_nonneg H S anchor A Y hg0 N)
    (fun N => avoidBlock_nonneg H S anchor A (X ∩ Y) (fun K => mul_nonneg (hf0 K) (hg0 K)) N)
    (fun N => avoidBlock_nonneg H S anchor A (X ∪ Y) (fun _ => zero_le_one) N)
    fun N N' => avoidBlock_inf_sup_mul_le H S anchor A X Y hf hg hf0 hg0 N N'

/-- **The weighted form.**  A product weight on the label sets satisfies the lattice condition with
equality, so it can be carried through the pointwise comparison and the four functions theorem
applies to the weighted blocks.  This is the form an exposure step produces, the weight being the
law of the exposed labels; and the identity `weight_inter_mul_union` it rests on is an identity on
the lattice of LABEL sets. -/
theorem sum_weight_avoidBlock_mul_le [Fintype V] [Fintype E] [Fintype M] (H : Hypergraph V E)
    (S : Set V) (anchor : M → Set V) (A X Y : Set V) {f g : Set V → ℝ}
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K)
    (w : M → ℝ) (hw0 : ∀ m, 0 ≤ w m) (hw1 : ∀ m, w m ≤ 1) :
    (∑ N : Set M, weight w N * avoidBlock H S anchor A X f N) *
        ∑ N : Set M, weight w N * avoidBlock H S anchor A Y g N
      ≤ (∑ N : Set M, weight w N * avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) N) *
          ∑ N : Set M, weight w N * avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) N := by
  refine four_functions_theorem_univ
    (fun N : Set M => weight w N * avoidBlock H S anchor A X f N)
    (fun N : Set M => weight w N * avoidBlock H S anchor A Y g N)
    (fun N : Set M => weight w N * avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) N)
    (fun N : Set M => weight w N * avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) N)
    (fun N => mul_nonneg (weight_nonneg hw0 hw1 N) (avoidBlock_nonneg H S anchor A X hf0 N))
    (fun N => mul_nonneg (weight_nonneg hw0 hw1 N) (avoidBlock_nonneg H S anchor A Y hg0 N))
    (fun N => mul_nonneg (weight_nonneg hw0 hw1 N)
      (avoidBlock_nonneg H S anchor A (X ∩ Y) (fun K => mul_nonneg (hf0 K) (hg0 K)) N))
    (fun N => mul_nonneg (weight_nonneg hw0 hw1 N)
      (avoidBlock_nonneg H S anchor A (X ∪ Y) (fun _ => zero_le_one) N))
    fun N N' => ?_
  have hb := avoidBlock_mul_le H S anchor A X Y hf hg hf0 hg0 N N'
  have hw := weight_inter_mul_union w N N'
  have hnn : 0 ≤ weight w (N ∩ N') * weight w (N ∪ N') :=
    mul_nonneg (weight_nonneg hw0 hw1 _) (weight_nonneg hw0 hw1 _)
  show weight w N * avoidBlock H S anchor A X f N *
      (weight w N' * avoidBlock H S anchor A Y g N')
    ≤ weight w (N ∩ N') * avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) (N ∩ N') *
      (weight w (N ∪ N') * avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) (N ∪ N'))
  calc weight w N * avoidBlock H S anchor A X f N *
        (weight w N' * avoidBlock H S anchor A Y g N')
      = (weight w N * weight w N') *
          (avoidBlock H S anchor A X f N * avoidBlock H S anchor A Y g N') := by ring
    _ = (weight w (N ∩ N') * weight w (N ∪ N')) *
          (avoidBlock H S anchor A X f N * avoidBlock H S anchor A Y g N') := by rw [hw]
    _ ≤ (weight w (N ∩ N') * weight w (N ∪ N')) *
          (avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) (N ∪ N') *
            avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) (N ∩ N')) :=
        mul_le_mul_of_nonneg_left hb hnn
    _ = weight w (N ∩ N') * avoidBlock H S anchor A (X ∩ Y) (fun K => f K * g K) (N ∩ N') *
          (weight w (N ∪ N') * avoidBlock H S anchor A (X ∪ Y) (fun _ => 1) (N ∪ N')) := by
        ring

/-! ## The exposure step

After exposing the labels incident to `Z` the model is `reducedHyper H Z`, whose labels are the
reduced labels of `KN/HyperExpose.lean`, and a set of labels of the original model is carried into it
by `record`.  Because `record` preserves unions and intersections exactly, a four-quantity comparison
of the reduced model, indexed by reduced label sets, is a four-quantity comparison of the original
model, indexed by the original label sets, for an arbitrary quadruple of functions.
-/

/-- **The exposure step, in general form.**  A comparison indexed by the label sets of the reduced
model transports to a comparison indexed by the label sets of the original model.  The proof is
`record_union` and `record_inter`, both exact equalities, and no property of the four functions is
used.

This is where the exactness earns its keep.  With a vertex record in place of `record` neither slot
can be rewritten, only included, and `exists_traceOutside_four_functions_fail` shows that for a
suitable increasing `Ψ` the transported inequality is then false.  For the particular quadruple of
this module the transport survives anyway, because the blocks are decreasing in the record
(`avoidBlock_antitone`); the generality here is what the exact identities add. -/
theorem record_mul_le_of_reduced (H : Hypergraph V E) (Z : Set V)
    (Ψ₁ Ψ₂ Ψ₃ Ψ₄ : Set (reducedLabel H Z) → ℝ)
    (hΨ : ∀ P P' : Set (reducedLabel H Z), Ψ₁ P * Ψ₂ P' ≤ Ψ₃ (P ∪ P') * Ψ₄ (P ∩ P'))
    (N N' : Set E) :
    Ψ₁ (record H Z N) * Ψ₂ (record H Z N')
      ≤ Ψ₃ (record H Z (N ∪ N')) * Ψ₄ (record H Z (N ∩ N')) := by
  rw [record_union, record_inter]
  exact hΨ (record H Z N) (record H Z N')

/-- **The exposure step for the four blocks.**  In the model obtained by exposing the labels incident
to `Z`, with each reduced label anchored at its own incidence set, the comparison holds with the four
blocks indexed by the labels of the original model through `record`.  The two label operations on the
right are carried into the reduced model by `record_union` and `record_inter`. -/
theorem avoidBlock_reducedHyper_record_mul_le [Fintype V] [Fintype E] (H : Hypergraph V E)
    (Z : Set V) (S A X Y : Set V) {f g : Set V → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ K, 0 ≤ f K) (hg0 : ∀ K, 0 ≤ g K) (N N' : Set E) :
    avoidBlock (reducedHyper H Z) S (reducedHyper H Z).incidence A X f (record H Z N) *
        avoidBlock (reducedHyper H Z) S (reducedHyper H Z).incidence A Y g (record H Z N')
      ≤ avoidBlock (reducedHyper H Z) S (reducedHyper H Z).incidence A (X ∪ Y)
            (fun _ => 1) (record H Z (N ∪ N')) *
          avoidBlock (reducedHyper H Z) S (reducedHyper H Z).incidence A (X ∩ Y)
            (fun K => f K * g K) (record H Z (N ∩ N')) := by
  haveI : Fintype (reducedLabel H Z) := Fintype.ofFinite _
  exact record_mul_le_of_reduced H Z _ _ _ _
    (fun P P' => avoidBlock_mul_le (reducedHyper H Z) S (reducedHyper H Z).incidence A X Y
      hf hg hf0 hg0 P P') N N'

/-! ### Where a vertex record would break

The four functions hypothesis is a statement about a pair of indices, their join and their meet.
Transporting it along a map of index sets and keeping it for every quadruple of functions needs that
map to preserve both operations.  `record` does, by `record_union` and `record_inter`.  The vertex
record does not, and the failure is not a gap in an argument: below is an increasing log-supermodular
`Ψ`, a hypergraph and two label sets for which the transported inequality is false.  The blocks of
this module escape because they run the other way, decreasing in the record.
-/

/-- **The vertex record destroys the four functions hypothesis.**  On the hypergraph of
`KN/HyperTrace.lean` with one vertex and two labels, the indicator `Ψ` of the single vertex, which is
`1` on the whole vertex set and `0` on the empty set, satisfies `Ψ P · Ψ P' ≤ Ψ (P ∪ P') · Ψ (P ∩ P')` for every pair of
vertex sets, and yet

    Ψ (trace {true}) · Ψ (trace {false})  =  1  >  0
      =  Ψ (trace ({true} ∪ {false})) · Ψ (trace ({true} ∩ {false})) ,

because the two labels have the same trace while their intersection is empty.  For an increasing `Ψ`,
indexing the four functions by traces therefore does not merely lose the proof, it loses the
statement. -/
theorem exists_traceOutside_four_functions_fail :
    ∃ (W L : Type) (_ : Fintype W) (_ : Fintype L) (H : Hypergraph W L) (Z : Set W)
      (Ψ : Set W → ℝ) (I J : Set L),
      (∀ P P' : Set W, Ψ P * Ψ P' ≤ Ψ (P ∪ P') * Ψ (P ∩ P')) ∧
      ¬ (Ψ (traceOutside H Z I) * Ψ (traceOutside H Z J)
          ≤ Ψ (traceOutside H Z (I ∪ J)) * Ψ (traceOutside H Z (I ∩ J))) := by
  classical
  refine ⟨Unit, Bool, inferInstance, inferInstance, twoLabelHypergraph, ∅,
    fun P => DecisionTree.ind P (), {true}, {false}, ?_, ?_⟩
  · intro P P'
    show DecisionTree.ind P () * DecisionTree.ind P' ()
      ≤ DecisionTree.ind (P ∪ P') () * DecisionTree.ind (P ∩ P') ()
    by_cases h : (() : Unit) ∈ P
    · by_cases h' : (() : Unit) ∈ P'
      · refine le_of_eq ?_
        rw [DecisionTree.ind_of_mem h, DecisionTree.ind_of_mem h',
          DecisionTree.ind_of_mem (Set.mem_union_left P' h),
          DecisionTree.ind_of_mem (Set.mem_inter h h')]
      · rw [DecisionTree.ind_of_not_mem h', mul_zero]
        exact mul_nonneg (DecisionTree.ind_nonneg _ _) (DecisionTree.ind_nonneg _ _)
    · rw [DecisionTree.ind_of_not_mem h, zero_mul]
      exact mul_nonneg (DecisionTree.ind_nonneg _ _) (DecisionTree.ind_nonneg _ _)
  · intro hle
    have hI : (() : Unit) ∈ traceOutside twoLabelHypergraph ∅ ({true} : Set Bool) :=
      mem_traceOutside_twoLabelHypergraph true ()
    have hJ : (() : Unit) ∈ traceOutside twoLabelHypergraph ∅ ({false} : Set Bool) :=
      mem_traceOutside_twoLabelHypergraph false ()
    have hU : (() : Unit) ∈
        traceOutside twoLabelHypergraph ∅ (({true} : Set Bool) ∪ ({false} : Set Bool)) :=
      traceOutside_mono twoLabelHypergraph ∅ Set.subset_union_left hI
    have hInt : (() : Unit) ∉
        traceOutside twoLabelHypergraph ∅ (({true} : Set Bool) ∩ ({false} : Set Bool)) := by
      intro hmem
      obtain ⟨e, he, -⟩ := (mem_traceOutside_iff twoLabelHypergraph ∅ _ ()).1 hmem
      have h1 : e = true := he.1
      have h2 : e = false := he.2
      rw [h1] at h2
      exact Bool.noConfusion h2
    have hle' :
        DecisionTree.ind (traceOutside twoLabelHypergraph ∅ ({true} : Set Bool)) () *
            DecisionTree.ind (traceOutside twoLabelHypergraph ∅ ({false} : Set Bool)) ()
          ≤ DecisionTree.ind (traceOutside twoLabelHypergraph ∅
                (({true} : Set Bool) ∪ ({false} : Set Bool))) () *
              DecisionTree.ind (traceOutside twoLabelHypergraph ∅
                (({true} : Set Bool) ∩ ({false} : Set Bool))) () := hle
    rw [DecisionTree.ind_of_mem hI, DecisionTree.ind_of_mem hJ, DecisionTree.ind_of_mem hU,
      DecisionTree.ind_of_not_mem hInt] at hle'
    norm_num at hle'

end KNAll.Site

end
