import Hypergraph.FiniteRadiusDomination
import Hypergraph.SiteIntrinsicInputs

/-!
# Finite target-aware site windows

This module is the finite-product core of the three-event construction in Problem A.  For finite
sets

`A ⊆ Q ⊆ P ⊆ O`, `U ⊆ ∂ᵢⁿQ`, and `T ⊆ P \ Q`,

the event is the intersection of:

* a confined hit from `A` to `U` inside `Q`;
* a confined hit from `A` to `T` inside `P`;
* the finite event saying that any two `A`-arms to `∂ᵢⁿQ` coalesce inside `Q`.

Everything below is deterministic or a finite union bound.  In particular, no bond or hyperedge
gluing statement is imported.  The three component probability estimates are deliberately kept as
named hypotheses: they are the analytic/certificate leaves, whereas the target-aware window and
its relay property are closed here.
-/

noncomputable section

namespace KNAll.Site.TargetAware

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V : Type*} [DecidableEq V]

/-! ## Finite connection and coalescence events -/

/-- Some source in `A` is joined to some target in `B`, with the path confined to `R`. -/
def finiteHit (G : SimpleGraph V) (R A B : Finset V) : Set (SiteConfig V) :=
  ⋃ a ∈ (A : Set V), ⋃ b ∈ (B : Set V), connWithin G (R : Set V) a b

theorem mem_finiteHit_iff (G : SimpleGraph V) (R A B : Finset V) (ω : SiteConfig V) :
    ω ∈ finiteHit G R A B ↔
      ∃ a ∈ A, ∃ b ∈ B, ω ∈ connWithin G (R : Set V) a b := by
  simp [finiteHit]

theorem determinedBy_finiteHit (G : SimpleGraph V) (R A B : Finset V) :
    DeterminedBy (finiteHit G R A B) (R : Set V) :=
  DeterminedBy.iUnion fun _ => DeterminedBy.iUnion fun _ =>
    DeterminedBy.iUnion fun _ => DeterminedBy.iUnion fun _ =>
      determinedBy_connWithin G (R : Set V) _ _

theorem measurableSet_finiteHit (G : SimpleGraph V) (R A B : Finset V) :
    MeasurableSet (finiteHit G R A B) :=
  (determinedBy_finiteHit G R A B).measurableSet_of_finset

/-- One ordered pair of source sites has two arms to the inner boundary of `Q`, but the two
sources are not joined inside `Q`. -/
def finiteCoalescenceFailure (G : SimpleGraph V) [G.LocallyFinite]
    (Q : Finset V) (a a' : V) : Set (SiteConfig V) :=
  (connWithinSet G (Q : Set V) a (innerBoundary G Q : Set V) ∩
      connWithinSet G (Q : Set V) a' (innerBoundary G Q : Set V)) ∩
    (connWithin G (Q : Set V) a a')ᶜ

/-- No ordered pair in `A` realizes a two-arm-without-coalescence failure inside `Q`.  This is a
literal complement of a finite union, so it is a finite cylinder without any hidden compactness
or infinite-volume assertion. -/
def finiteCoalescenceGood (G : SimpleGraph V) [G.LocallyFinite]
    (A Q : Finset V) : Set (SiteConfig V) :=
  (⋃ a ∈ (A : Set V), ⋃ a' ∈ (A : Set V), finiteCoalescenceFailure G Q a a')ᶜ

theorem determinedBy_finiteCoalescenceFailure (G : SimpleGraph V) [G.LocallyFinite]
    (Q : Finset V) (a a' : V) :
    DeterminedBy (finiteCoalescenceFailure G Q a a') (Q : Set V) := by
  exact ((determinedBy_connWithinSet G (Q : Set V) a (innerBoundary G Q : Set V)).inter
    (determinedBy_connWithinSet G (Q : Set V) a' (innerBoundary G Q : Set V))).inter
      (determinedBy_connWithin G (Q : Set V) a a').compl

theorem determinedBy_finiteCoalescenceGood (G : SimpleGraph V) [G.LocallyFinite]
    (A Q : Finset V) :
    DeterminedBy (finiteCoalescenceGood G A Q) (Q : Set V) := by
  unfold finiteCoalescenceGood
  exact (DeterminedBy.iUnion fun a => DeterminedBy.iUnion fun _ =>
    DeterminedBy.iUnion fun a' => DeterminedBy.iUnion fun _ =>
      determinedBy_finiteCoalescenceFailure G Q a a').compl

theorem measurableSet_finiteCoalescenceGood (G : SimpleGraph V) [G.LocallyFinite]
    (A Q : Finset V) : MeasurableSet (finiteCoalescenceGood G A Q) :=
  (determinedBy_finiteCoalescenceGood G A Q).measurableSet_of_finset

/-- The pointwise content of `finiteCoalescenceGood`. -/
theorem connWithin_of_finiteCoalescenceGood (G : SimpleGraph V) [G.LocallyFinite]
    {A Q : Finset V} {ω : SiteConfig V} (hgood : ω ∈ finiteCoalescenceGood G A Q)
    {a a' : V} (ha : a ∈ A) (ha' : a' ∈ A)
    (harm : ω ∈ connWithinSet G (Q : Set V) a (innerBoundary G Q : Set V))
    (harm' : ω ∈ connWithinSet G (Q : Set V) a' (innerBoundary G Q : Set V)) :
    ω ∈ connWithin G (Q : Set V) a a' := by
  by_contra hnot
  exact hgood (Set.mem_iUnion₂.2 ⟨a, Finset.mem_coe.2 ha,
    Set.mem_iUnion₂.2 ⟨a', Finset.mem_coe.2 ha', ⟨⟨harm, harm'⟩, hnot⟩⟩⟩)

/-! ## The target-aware window and its canonical relay -/

/-- The three-factor target-aware window `Gᶜᵒᵃˡ ∩ Gᶠᵃᶜᵉ ∩ Gᵗᵃʳᵍᵉᵗ`. -/
def window (G : SimpleGraph V) [G.LocallyFinite]
    (A Q P U T : Finset V) : Set (SiteConfig V) :=
  (finiteCoalescenceGood G A Q ∩ finiteHit G Q A U) ∩ finiteHit G P A T

/-- The complete finite support of the three factors. -/
def support (Q P : Finset V) : Finset V := Q ∪ P

theorem determinedBy_window_support (G : SimpleGraph V) [G.LocallyFinite]
    (A Q P U T : Finset V) :
    DeterminedBy (window G A Q P U T) (support Q P : Set V) := by
  apply DeterminedBy.inter
  · apply DeterminedBy.inter
    · exact (determinedBy_finiteCoalescenceGood G A Q).mono
        (Finset.coe_subset.2 Finset.subset_union_left)
    · exact (determinedBy_finiteHit G Q A U).mono
        (Finset.coe_subset.2 Finset.subset_union_left)
  · exact (determinedBy_finiteHit G P A T).mono
      (Finset.coe_subset.2 Finset.subset_union_right)

/-- If both finite path regions lie in `O`, then the target-aware event is `O`-measurable. -/
theorem determinedBy_window (G : SimpleGraph V) [G.LocallyFinite]
    {A Q P U T O : Finset V} (hQO : Q ⊆ O) (hPO : P ⊆ O) :
    DeterminedBy (window G A Q P U T) (O : Set V) :=
  (determinedBy_window_support G A Q P U T).mono
    (Finset.coe_subset.2 (Finset.union_subset hQO hPO))

theorem measurableSet_window (G : SimpleGraph V) [G.LocallyFinite]
    (A Q P U T : Finset V) : MeasurableSet (window G A Q P U T) :=
  (determinedBy_window_support G A Q P U T).measurableSet_of_finset

/-- The face endpoints which can be selected after observing the `Q`-pattern. -/
def relayCandidates (G : SimpleGraph V) (A Q U : Finset V) (ω : SiteConfig V) : Finset V := by
  classical
  exact U.filter fun u => ∃ a ∈ A, ω ∈ connWithin G (Q : Set V) a u

/-- A canonical endpoint of the face hit.  The fallback is used only off the face event. -/
def canonicalRelay [Inhabited V] (G : SimpleGraph V) (A Q U : Finset V)
    (ω : SiteConfig V) : V :=
  if h : (relayCandidates G A Q U ω).Nonempty then Classical.choose h else default

theorem relayCandidates_nonempty_iff (G : SimpleGraph V) (A Q U : Finset V)
    (ω : SiteConfig V) :
    (relayCandidates G A Q U ω).Nonempty ↔ ω ∈ finiteHit G Q A U := by
  classical
  rw [mem_finiteHit_iff]
  constructor
  · rintro ⟨u, hu⟩
    rw [relayCandidates, Finset.mem_filter] at hu
    obtain ⟨huU, a, haA, hau⟩ := hu
    exact ⟨a, haA, u, huU, hau⟩
  · rintro ⟨a, ha, u, hu, hau⟩
    exact ⟨u, Finset.mem_filter.2 ⟨hu, a, ha, hau⟩⟩

theorem canonicalRelay_spec [Inhabited V] (G : SimpleGraph V)
    {A Q U : Finset V} {ω : SiteConfig V} (hface : ω ∈ finiteHit G Q A U) :
    canonicalRelay G A Q U ω ∈ U ∧
      ∃ a ∈ A, ω ∈ connWithin G (Q : Set V) a (canonicalRelay G A Q U ω) := by
  classical
  have hn := (relayCandidates_nonempty_iff G A Q U ω).2 hface
  rw [canonicalRelay, dif_pos hn]
  exact Finset.mem_filter.1 (Classical.choose_spec hn)

theorem relayCandidates_congr (G : SimpleGraph V) {A Q U : Finset V}
    {ω ω' : SiteConfig V} (hagree : ω ∩ (Q : Set V) = ω' ∩ (Q : Set V)) :
    relayCandidates G A Q U ω = relayCandidates G A Q U ω' := by
  classical
  ext u
  simp only [relayCandidates, Finset.mem_filter]
  refine and_congr_right fun _hu => ?_
  refine exists_congr fun a => ?_
  refine and_congr_right fun _ha => ?_
  exact (determinedBy_iff _ _).1 (determinedBy_connWithin G (Q : Set V) a u)
    ω ω' hagree

theorem canonicalRelay_congr [Inhabited V] (G : SimpleGraph V) {A Q U : Finset V}
    {ω ω' : SiteConfig V} (hagree : ω ∩ (Q : Set V) = ω' ∩ (Q : Set V)) :
    canonicalRelay G A Q U ω = canonicalRelay G A Q U ω' := by
  unfold canonicalRelay
  rw [relayCandidates_congr G hagree]

/-- Both endpoints of a confined connection are open and lie in its confining set. -/
theorem endpoints_of_connWithin (G : SimpleGraph V) {R : Set V} {x y : V}
    {ω : SiteConfig V} (h : ω ∈ connWithin G R x y) :
    x ∈ ω ∩ R ∧ y ∈ ω ∩ R := by
  exact ⟨h.1, mem_of_mem_siteCluster G (ω ∩ R) ⟨h.1, h.2⟩⟩

/-- The canonical face endpoint is open. -/
theorem canonicalRelay_mem_config [Inhabited V] (G : SimpleGraph V)
    {A Q U : Finset V} {ω : SiteConfig V} (hface : ω ∈ finiteHit G Q A U) :
    canonicalRelay G A Q U ω ∈ ω := by
  obtain ⟨_, a, _, ha⟩ := canonicalRelay_spec G hface
  exact (endpoints_of_connWithin G ha).2.1

/-! ## Deterministic gluing through the finite coalescence event -/

/-- The closed deterministic core of Problem A.  The relay is the canonical endpoint of the face
hit in `ω`.  Agreement on `Q` fixes its face path.  In `ω'`, the target path exits `Q`; the
coalescence factor joins its source to the fixed face-path source, and the three confined paths
concatenate inside `O`.

Only the target-aware event membership varies with `ω'`; there is no probabilistic gluing
hypothesis. -/
theorem canonicalRelay_toTarget [Inhabited V] (G : SimpleGraph V) [G.LocallyFinite]
    {A Q P U T O : Finset V}
    (hAQ : A ⊆ Q) (hUbd : U ⊆ innerBoundary G Q) (hTQ : Disjoint T Q)
    (hQO : Q ⊆ O) (hPO : P ⊆ O) :
    ∀ ω ∈ window G A Q P U T,
      canonicalRelay G A Q U ω ∈ U ∧ canonicalRelay G A Q U ω ∈ ω ∧
        ∀ ω' ∈ window G A Q P U T,
          ω' ∩ (Q : Set V) = ω ∩ (Q : Set V) →
            ω' ∈ connWithinSet G (O : Set V) (canonicalRelay G A Q U ω) (T : Set V) := by
  intro ω hω
  have hface : ω ∈ finiteHit G Q A U := hω.1.2
  have hspec := canonicalRelay_spec G hface
  refine ⟨hspec.1, canonicalRelay_mem_config G hface, ?_⟩
  intro ω' hω' hagree
  obtain ⟨a, haA, haFace⟩ := hspec.2
  have haFace' : ω' ∈ connWithin G (Q : Set V) a (canonicalRelay G A Q U ω) := by
    exact ((determinedBy_iff _ _).1
      (determinedBy_connWithin G (Q : Set V) a (canonicalRelay G A Q U ω))
      ω ω' hagree.symm).1 haFace
  obtain ⟨a', ha'A, t, htT, ha't⟩ := (mem_finiteHit_iff G P A T ω').1 hω'.2
  obtain ⟨path⟩ := ha't.2
  have ha'Q : a' ∈ Q := hAQ ha'A
  have htQ : t ∉ Q := fun ht => Finset.disjoint_left.1 hTQ htT ht
  obtain ⟨b, hbBoundary, ha'b0⟩ :=
    FRDom.exists_innerBoundary_connWithin G Q (ω' ∩ (P : Set V)) path ha'Q htQ
  have ha'b : ω' ∈ connWithin G (Q : Set V) a' b :=
    isUpperSet_connWithin G (Q : Set V) a' b Set.inter_subset_left ha'b0
  have haArm : ω' ∈ connWithinSet G (Q : Set V) a (innerBoundary G Q : Set V) := by
    rw [mem_connWithinSet_iff]
    exact ⟨canonicalRelay G A Q U ω,
      Finset.mem_coe.2 (hUbd hspec.1), haFace'⟩
  have ha'Arm : ω' ∈ connWithinSet G (Q : Set V) a' (innerBoundary G Q : Set V) := by
    rw [mem_connWithinSet_iff]
    exact ⟨b, Finset.mem_coe.2 hbBoundary, ha'b⟩
  have haa' : ω' ∈ connWithin G (Q : Set V) a a' :=
    connWithin_of_finiteCoalescenceGood G hω'.1.1 haA ha'A haArm ha'Arm
  have hrelayOpen := (endpoints_of_connWithin G haFace').2.1
  have hrelayA : ω' ∈ connWithin G (Q : Set V) (canonicalRelay G A Q U ω) a :=
    ⟨⟨hrelayOpen, (endpoints_of_connWithin G haFace').2.2⟩, haFace'.2.symm⟩
  have hrelayAO := connWithin_mono_set G (Finset.coe_subset.2 hQO)
    (canonicalRelay G A Q U ω) a hrelayA
  have haa'O := connWithin_mono_set G (Finset.coe_subset.2 hQO) a a' haa'
  have ha'tO := connWithin_mono_set G (Finset.coe_subset.2 hPO) a' t ha't
  rw [mem_connWithinSet_iff]
  exact ⟨t, Finset.mem_coe.2 htT,
    ⟨hrelayAO.1, (hrelayAO.2.trans haa'O.2).trans ha'tO.2⟩⟩

/-- Agreement on any observed shell `S` containing `Q` fixes the canonical relay and its face
path.  This is the form expected by shell-window interfaces whose agreement premise is stated on
`O \ Int` rather than on `Q` itself. -/
theorem canonicalRelay_toTarget_of_shellAgreement [Inhabited V]
    (G : SimpleGraph V) [G.LocallyFinite] {A Q P U T O S : Finset V}
    (hAQ : A ⊆ Q) (hUbd : U ⊆ innerBoundary G Q) (hTQ : Disjoint T Q)
    (hQO : Q ⊆ O) (hPO : P ⊆ O) (hQS : Q ⊆ S) :
    ∀ ω ∈ window G A Q P U T,
      canonicalRelay G A Q U ω ∈ U ∧ canonicalRelay G A Q U ω ∈ ω ∧
        ∀ ω' ∈ window G A Q P U T,
          ω' ∩ (S : Set V) = ω ∩ (S : Set V) →
            ω' ∈ connWithinSet G (O : Set V) (canonicalRelay G A Q U ω) (T : Set V) := by
  intro ω hω
  obtain ⟨hu, huω, hrelay⟩ := canonicalRelay_toTarget G hAQ hUbd hTQ hQO hPO ω hω
  refine ⟨hu, huω, fun ω' hω' hagree => hrelay ω' hω' ?_⟩
  apply Set.ext
  intro x
  have hxS (hxQ : x ∈ (Q : Set V)) : x ∈ (S : Set V) :=
    Finset.mem_coe.2 (hQS (Finset.mem_coe.1 hxQ))
  constructor
  · rintro ⟨hxω', hxQ⟩
    have hx := (Set.ext_iff.1 hagree x).1 ⟨hxω', hxS hxQ⟩
    exact ⟨hx.1, hxQ⟩
  · rintro ⟨hxω, hxQ⟩
    have hx := (Set.ext_iff.1 hagree x).2 ⟨hxω, hxS hxQ⟩
    exact ⟨hx.1, hxQ⟩

/-! ## The exact finite union bound -/

/-- Three component success bounds at loss `τ` imply the exact window bound `1 - 3τ`. -/
theorem one_sub_three_mul_le_prob_window (G : SimpleGraph V) [G.LocallyFinite]
    (w : V → unitInterval) (A Q P U T : Finset V) {τ : ℝ}
    (hcoal : 1 - τ ≤ (prodBernoulli w).real (finiteCoalescenceGood G A Q))
    (hface : 1 - τ ≤ (prodBernoulli w).real (finiteHit G Q A U))
    (htarget : 1 - τ ≤ (prodBernoulli w).real (finiteHit G P A T)) :
    1 - 3 * τ ≤ (prodBernoulli w).real (window G A Q P U T) := by
  let μ := prodBernoulli w
  let C := finiteCoalescenceGood G A Q
  let F := finiteHit G Q A U
  let H := finiteHit G P A T
  have hCm : MeasurableSet C := measurableSet_finiteCoalescenceGood G A Q
  have hFm : MeasurableSet F := measurableSet_finiteHit G Q A U
  have hHm : MeasurableSet H := measurableSet_finiteHit G P A T
  have hCc : μ.real Cᶜ ≤ τ := by
    rw [measureReal_compl hCm, probReal_univ]
    linarith
  have hFc : μ.real Fᶜ ≤ τ := by
    rw [measureReal_compl hFm, probReal_univ]
    linarith
  have hHc : μ.real Hᶜ ≤ τ := by
    rw [measureReal_compl hHm, probReal_univ]
    linarith
  have hu₁ := measureReal_union_le (μ := μ) Cᶜ Fᶜ
  have hu₂ := measureReal_union_le (μ := μ) (Cᶜ ∪ Fᶜ) Hᶜ
  have hcomp : μ.real ((C ∩ F) ∩ H)ᶜ ≤ 3 * τ := by
    rw [compl_inter, compl_inter]
    linarith
  change 1 - 3 * τ ≤ μ.real ((C ∩ F) ∩ H)
  rw [measureReal_compl ((hCm.inter hFm).inter hHm), probReal_univ] at hcomp
  simpa [window, C, F, H, μ] using (show 1 - 3 * τ ≤ μ.real ((C ∩ F) ∩ H) by
    linarith)

/-- Strict version of the exact finite three-component union bound. -/
theorem one_sub_three_mul_lt_prob_window (G : SimpleGraph V) [G.LocallyFinite]
    (w : V → unitInterval) (A Q P U T : Finset V) {τ : ℝ}
    (hcoal : 1 - τ < (prodBernoulli w).real (finiteCoalescenceGood G A Q))
    (hface : 1 - τ < (prodBernoulli w).real (finiteHit G Q A U))
    (htarget : 1 - τ < (prodBernoulli w).real (finiteHit G P A T)) :
    1 - 3 * τ < (prodBernoulli w).real (window G A Q P U T) := by
  let μ := prodBernoulli w
  let C := finiteCoalescenceGood G A Q
  let F := finiteHit G Q A U
  let H := finiteHit G P A T
  have hCm : MeasurableSet C := measurableSet_finiteCoalescenceGood G A Q
  have hFm : MeasurableSet F := measurableSet_finiteHit G Q A U
  have hHm : MeasurableSet H := measurableSet_finiteHit G P A T
  have hCc : μ.real Cᶜ < τ := by
    rw [measureReal_compl hCm, probReal_univ]
    linarith
  have hFc : μ.real Fᶜ < τ := by
    rw [measureReal_compl hFm, probReal_univ]
    linarith
  have hHc : μ.real Hᶜ < τ := by
    rw [measureReal_compl hHm, probReal_univ]
    linarith
  have hu₁ := measureReal_union_le (μ := μ) Cᶜ Fᶜ
  have hu₂ := measureReal_union_le (μ := μ) (Cᶜ ∪ Fᶜ) Hᶜ
  have hcomp : μ.real ((C ∩ F) ∩ H)ᶜ < 3 * τ := by
    rw [compl_inter, compl_inter]
    linarith
  change 1 - 3 * τ < μ.real ((C ∩ F) ∩ H)
  rw [measureReal_compl ((hCm.inter hFm).inter hHm), probReal_univ] at hcomp
  simpa [window, C, F, H, μ] using (show 1 - 3 * τ < μ.real ((C ∩ F) ∩ H) by
    linarith)

/-- The component tolerance requested by the finite extraction. -/
def componentTolerance (δ β : ℝ) : ℝ := min (δ ^ 2) β / 4

theorem componentTolerance_nonneg {δ β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ componentTolerance δ β := by
  unfold componentTolerance
  positivity

theorem componentTolerance_le_sq (δ : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    componentTolerance δ β ≤ δ ^ 2 := by
  have hmin : min (δ ^ 2) β ≤ δ ^ 2 := min_le_left _ _
  have hmin0 : 0 ≤ min (δ ^ 2) β := le_min (sq_nonneg δ) hβ
  unfold componentTolerance
  nlinarith [sq_nonneg δ]

/-- The certificate-facing form: component loss `min(δ²,β)/4` is more than sufficient for
the target-extension requirement `1 - 3δ²`.  The three component estimates are the only
imported probabilistic hypotheses. -/
theorem one_sub_three_sq_le_prob_window (G : SimpleGraph V) [G.LocallyFinite]
    (w : V → unitInterval) (A Q P U T : Finset V) {δ β : ℝ} (hβ : 0 ≤ β)
    (hcoal : 1 - componentTolerance δ β ≤
      (prodBernoulli w).real (finiteCoalescenceGood G A Q))
    (hface : 1 - componentTolerance δ β ≤
      (prodBernoulli w).real (finiteHit G Q A U))
    (htarget : 1 - componentTolerance δ β ≤
      (prodBernoulli w).real (finiteHit G P A T)) :
    1 - 3 * δ ^ 2 ≤ (prodBernoulli w).real (window G A Q P U T) := by
  have h := one_sub_three_mul_le_prob_window G w A Q P U T hcoal hface htarget
  have hτ := componentTolerance_le_sq δ hβ
  linarith

/-- Strict certificate-facing probability bound. -/
theorem one_sub_three_sq_lt_prob_window (G : SimpleGraph V) [G.LocallyFinite]
    (w : V → unitInterval) (A Q P U T : Finset V) {δ β : ℝ} (hβ : 0 ≤ β)
    (hcoal : 1 - componentTolerance δ β <
      (prodBernoulli w).real (finiteCoalescenceGood G A Q))
    (hface : 1 - componentTolerance δ β <
      (prodBernoulli w).real (finiteHit G Q A U))
    (htarget : 1 - componentTolerance δ β <
      (prodBernoulli w).real (finiteHit G P A T)) :
    1 - 3 * δ ^ 2 < (prodBernoulli w).real (window G A Q P U T) := by
  have h := one_sub_three_mul_lt_prob_window G w A Q P U T hcoal hface htarget
  have hτ := componentTolerance_le_sq δ hβ
  linarith

/-- One theorem collecting exactly the fields a finite shell certificate consumes.  Its first six
hypotheses are finite geometry; its final three hypotheses are the imported analytic probability
leaves.  Determination, the canonical relay property, and the strict `1-3δ²` estimate are proved
from them here. -/
theorem certificateWindow [Inhabited V] (G : SimpleGraph V) [G.LocallyFinite]
    (w : V → unitInterval) {A Q P U T O S : Finset V} {δ β : ℝ}
    (hAQ : A ⊆ Q) (hUbd : U ⊆ innerBoundary G Q) (hTQ : Disjoint T Q)
    (hQO : Q ⊆ O) (hPO : P ⊆ O) (hQS : Q ⊆ S) (hβ : 0 ≤ β)
    (hcoal : 1 - componentTolerance δ β <
      (prodBernoulli w).real (finiteCoalescenceGood G A Q))
    (hface : 1 - componentTolerance δ β <
      (prodBernoulli w).real (finiteHit G Q A U))
    (htarget : 1 - componentTolerance δ β <
      (prodBernoulli w).real (finiteHit G P A T)) :
    DeterminedBy (window G A Q P U T) (O : Set V) ∧
      (∀ ω ∈ window G A Q P U T,
        canonicalRelay G A Q U ω ∈ U ∧ canonicalRelay G A Q U ω ∈ ω ∧
          ∀ ω' ∈ window G A Q P U T,
            ω' ∩ (S : Set V) = ω ∩ (S : Set V) →
              ω' ∈ connWithinSet G (O : Set V)
                (canonicalRelay G A Q U ω) (T : Set V)) ∧
      1 - 3 * δ ^ 2 < (prodBernoulli w).real (window G A Q P U T) := by
  exact ⟨determinedBy_window G hQO hPO,
    canonicalRelay_toTarget_of_shellAgreement G hAQ hUbd hTQ hQO hPO hQS,
    one_sub_three_sq_lt_prob_window G w A Q P U T hβ hcoal hface htarget⟩

/-! ## Explicit all-open satisfiability -/

/-- The all-open configuration realizes the coalescence factor whenever the source sites are
deterministically connected to one another inside `Q`. -/
theorem univ_mem_finiteCoalescenceGood (G : SimpleGraph V) [G.LocallyFinite]
    {A Q : Finset V}
    (hconnected : ∀ a ∈ A, ∀ a' ∈ A,
      (Set.univ : SiteConfig V) ∈ connWithin G (Q : Set V) a a') :
    (Set.univ : SiteConfig V) ∈ finiteCoalescenceGood G A Q := by
  intro hbad
  obtain ⟨a, ha, hbad⟩ := Set.mem_iUnion₂.1 hbad
  obtain ⟨a', ha', hfailure⟩ := Set.mem_iUnion₂.1 hbad
  exact hfailure.2 (hconnected a (Finset.mem_coe.1 ha) a' (Finset.mem_coe.1 ha'))

/-- A direct path-based satisfiability theorem.  Its witness is literally the all-open
configuration, not an inferred `Nonempty` assumption. -/
theorem univ_mem_window (G : SimpleGraph V) [G.LocallyFinite]
    {A Q P U T : Finset V}
    (hconnected : ∀ a ∈ A, ∀ a' ∈ A,
      (Set.univ : SiteConfig V) ∈ connWithin G (Q : Set V) a a')
    (hface : ∃ a ∈ A, ∃ u ∈ U,
      (Set.univ : SiteConfig V) ∈ connWithin G (Q : Set V) a u)
    (htarget : ∃ a ∈ A, ∃ t ∈ T,
      (Set.univ : SiteConfig V) ∈ connWithin G (P : Set V) a t) :
    (Set.univ : SiteConfig V) ∈ window G A Q P U T := by
  refine ⟨⟨univ_mem_finiteCoalescenceGood G hconnected, ?_⟩, ?_⟩
  · rw [mem_finiteHit_iff]
    exact hface
  · rw [mem_finiteHit_iff]
    exact htarget

/-!
The hypotheses of `univ_mem_window` are purely deterministic finite-path data.  For the intended
lattice boxes they follow from the standard fact that an integer box is connected.  They are
separate from the three probability inputs above, so satisfiability cannot be hidden by a false
probability or gluing assumption.
-/

#print axioms KNAll.Site.TargetAware.canonicalRelay_toTarget
#print axioms KNAll.Site.TargetAware.one_sub_three_sq_le_prob_window
#print axioms KNAll.Site.TargetAware.one_sub_three_sq_lt_prob_window
#print axioms KNAll.Site.TargetAware.certificateWindow
#print axioms KNAll.Site.TargetAware.univ_mem_window

end KNAll.Site.TargetAware

end
