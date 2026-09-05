import Hypergraph.CollarReliability
import Hypergraph.ReinforcedShellWindow
import Hypergraph.FiniteHyperGluingClosed

/-!
# Reinforced shell windows feed the pinned relay theorem

The old `LevelGeometryD` split its bridge seed from its relay face.  A reinforced v15 window is
different: the whole rectangular window, including the relay source cube, is sampled in one fresh
collar.  This file supplies the missing direct bridge to `TargetExt.reachRelayD` and the elementary
three-error bookkeeping.  It does not assume any infinite-scale input.
-/

noncomputable section

namespace KNAll.Site.ReinforcedTarget

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {V : Type*} [DecidableEq V]

def openWindow (J : Finset V) : Set (SiteConfig V) :=
  {ω | (↑J : Set V) ⊆ ω}

def lowRelay (G : SimpleGraph V) (w : V → unitInterval) (S D : Finset V)
    (T : Set V) (δ : ℝ) (v : V) : Set (SiteConfig V) :=
  {ω | pinnedProb w (↑S : Set V) (fun i => i ∈ ω)
      (TargetExt.toTarget G D T v) ≤ 1 - δ}

def selectedOpen (G : SimpleGraph V) (Dom O : Finset V) (o : V)
    (sel : Finset V → Finset V) (J : V → Finset V) : Set (SiteConfig V) :=
  ⋃ x ∈ TargetExt.outerBoundary G Dom O,
    TargetExt.selectedAt G Dom O o sel x ∩ openWindow (J x)

def selectedUnreliable (G : SimpleGraph V) (w : V → unitInterval)
    (Dom D O Int : Finset V) (o : V) (T : Set V) (δ : ℝ)
    (sel : Finset V → Finset V) (J : V → Finset V) (v : V → V) :
    Set (SiteConfig V) :=
  ⋃ x ∈ TargetExt.outerBoundary G Dom O,
    TargetExt.selectedAt G Dom O o sel x ∩
      (openWindow (J x) ∩ lowRelay G w (O \ Int) D T δ (v x))

def selectedReliable (G : SimpleGraph V) (w : V → unitInterval)
    (Dom D O Int : Finset V) (o : V) (T : Set V) (δ : ℝ)
    (sel : Finset V → Finset V) (J : V → Finset V) (v : V → V) :
    Set (SiteConfig V) :=
  ⋃ x ∈ TargetExt.outerBoundary G Dom O,
    TargetExt.selectedAt G Dom O o sel x ∩
      (openWindow (J x) ∩
        {ω | TargetExt.reliable G w (O \ Int) D T δ ω (v x)})

theorem determinedBy_openWindow (J : Finset V) :
    DeterminedBy (openWindow J) (↑J : Set V) :=
  determinedBy_allOpen (↑J : Set V)

theorem measurableSet_openWindow (J : Finset V) : MeasurableSet (openWindow J) :=
  (determinedBy_openWindow J).measurableSet_of_finset

theorem isUpperSet_openWindow (J : Finset V) : IsUpperSet (openWindow J) := by
  intro ω ω' hωω' hopen
  exact fun z hz => hωω' (hopen hz)

theorem determinedBy_lowRelay (G : SimpleGraph V) (w : V → unitInterval)
    (S D : Finset V) (T : Set V) (δ : ℝ) (v : V) :
    DeterminedBy (lowRelay G w S D T δ v) (↑S : Set V) :=
  TargetExt.determinedBy_setOf_pinnedProb_le w (↑S : Set V)
    (TargetExt.toTarget G D T v) (1 - δ)

theorem measurableSet_lowRelay (G : SimpleGraph V) (w : V → unitInterval)
    (S D : Finset V) (T : Set V) (δ : ℝ) (v : V) :
    MeasurableSet (lowRelay G w S D T δ v) :=
  (determinedBy_lowRelay G w S D T δ v).measurableSet_of_finset

/-- One reinforced window is open but unreliable only with probability `a*η/δ`.  The named hit
event may use coordinates outside the collar; Harris supplies the factor `P(openWindow)` and the
restricted collar Markov lemma then conditions only on the complete shell pattern. -/
theorem real_openWindow_inter_lowRelay_le
    (G : SimpleGraph V) (w : V → unitInterval) (S D J : Finset V)
    (T : Set V) (v : V) {H : Set (SiteConfig V)}
    (hJS : J ⊆ S) (hHup : IsUpperSet H) (hHm : MeasurableSet H)
    (hforce : openWindow J ∩ H ⊆ TargetExt.toTarget G D T v)
    {δ a η : ℝ} (hδ0 : 0 < δ) (ha0 : 0 ≤ a) (hη0 : 0 ≤ η)
    (hopen : (prodBernoulli w).real (openWindow J) ≤ a)
    (hhit : (prodBernoulli w).real Hᶜ ≤ η) :
    (prodBernoulli w).real
        (openWindow J ∩ lowRelay G w S D T δ v) ≤ a * η / δ := by
  have hOdet : DeterminedBy (openWindow J) (↑S : Set V) :=
    (determinedBy_openWindow J).mono fun x hx => Finset.mem_coe.2 (hJS (Finset.mem_coe.1 hx))
  have hmul := TargetExt.mul_real_open_inter_low_le_mul_hit_compl
    w S (TargetExt.measurableSet_toTarget G D T v) hOdet
    (isUpperSet_openWindow J) hHup hHm hforce δ
  have hprod : (prodBernoulli w).real (openWindow J) *
      (prodBernoulli w).real Hᶜ ≤ a * η :=
    mul_le_mul hopen hhit measureReal_nonneg ha0
  apply (le_div_iff₀ hδ0).2
  rw [mul_comm]
  change δ * (prodBernoulli w).real
      (openWindow J ∩ {ω : SiteConfig V |
        pinnedProb w (↑S : Set V) (fun i => i ∈ ω)
          (TargetExt.toTarget G D T v) ≤ 1 - δ}) ≤ a * η
  exact hmul.trans hprod

/-- A selected contact whose reinforced window is open and whose centre is reliable is exactly a
source-reachable reliable relay in the shell. -/
theorem selectedReliable_subset_reachRelayD
    (G : SimpleGraph V) (w : V → unitInterval)
    {Dom D O Int : Finset V} (hIntO : Int ⊆ O) (hOD : O ⊆ D)
    (hDDom : D ⊆ Dom) (o : V) (T : Set V) (δ : ℝ)
    (sel : Finset V → Finset V) (J : V → Finset V) (v : V → V)
    (hsel_sub : ∀ K, sel K ⊆ K)
    (hJ : ∀ x ∈ TargetExt.outerBoundary G Dom O, J x ⊆ O \ Int)
    (hv : ∀ x ∈ TargetExt.outerBoundary G Dom O, v x ∈ O \ Int)
    (hbridge : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      ∀ ω : SiteConfig V, x ∈ ω → ω ∈ openWindow (J x) →
        ω ∈ connWithin G (insert x (↑(J x) : Set V)) x (v x)) :
    selectedReliable G w Dom D O Int o T δ sel J v ⊆
      TargetExt.reachRelayD G w Dom D O Int o T δ := by
  rintro ω hω
  obtain ⟨x, hxbd, hxsel, hopen, hrel⟩ := Set.mem_iUnion₂.1 hω
  have hxc : x ∈ TargetExt.contacts G Dom O o ω := hsel_sub _ hxsel
  have hox : ω ∈ connWithin G (↑(Dom \ O) : Set V) o x :=
    (Finset.mem_filter.1 hxc).2
  have hxopen : x ∈ ω := (TargetExt.mem_of_connWithin G hox).1
  have hxv := hbridge x hxbd ω hxopen hopen
  have hsource : ω ∈ TargetExt.fromSource G Dom Int o (v x) := by
    refine connWithin_mono_set G ?_ o (v x) (TargetExt.connWithin_trans G hox hxv)
    intro z hz
    rw [Finset.mem_coe, Finset.mem_sdiff]
    rcases hz with hz | hz
    · have hz' := Finset.mem_sdiff.1 (Finset.mem_coe.1 hz)
      exact ⟨hz'.1, fun hzInt => hz'.2 (hIntO hzInt)⟩
    · rcases hz with rfl | hz
      · have hxDomO := TargetExt.outerBoundary_subset G Dom O hxbd
        exact ⟨(Finset.mem_sdiff.1 hxDomO).1,
          fun hxInt => (Finset.mem_sdiff.1 hxDomO).2 (hIntO hxInt)⟩
      · have hzJ := hJ x hxbd (Finset.mem_coe.1 hz)
        exact ⟨hDDom (hOD (Finset.mem_sdiff.1 hzJ).1),
          (Finset.mem_sdiff.1 hzJ).2⟩
  exact Set.mem_iUnion₂.2 ⟨v x, hv x hxbd, hrel, hsource⟩

/-- Removing the selected-unreliable windows from the selected-open windows leaves only selected
reliable windows. -/
theorem selectedOpen_diff_unreliable_subset_reliable
    (G : SimpleGraph V) (w : V → unitInterval)
    (Dom D O Int : Finset V) (o : V) (T : Set V) (δ : ℝ)
    (sel : Finset V → Finset V) (J : V → Finset V) (v : V → V) :
    selectedOpen G Dom O o sel J \
        selectedUnreliable G w Dom D O Int o T δ sel J v ⊆
      selectedReliable G w Dom D O Int o T δ sel J v := by
  rintro ω ⟨hopen, hnotbad⟩
  obtain ⟨x, hxbd, hxsel, hwin⟩ := Set.mem_iUnion₂.1 hopen
  refine Set.mem_iUnion₂.2 ⟨x, hxbd, hxsel, hwin, ?_⟩
  by_contra hnotrel
  apply hnotbad
  refine Set.mem_iUnion₂.2 ⟨x, hxbd, hxsel, hwin, ?_⟩
  change ¬TargetExt.reliable G w (O \ Int) D T δ ω (v x) at hnotrel
  exact le_of_not_gt hnotrel

/-- Three-error bookkeeping: a rich level fails to yield a good reinforced relay only if it has
no selected open window or has a selected open but unreliable window. -/
theorem real_selectedReliable_gt
    (μ : Measure (SiteConfig V)) [IsProbabilityMeasure μ]
    {Rich Open Bad Good : Set (SiteConfig V)} {δ : ℝ}
    (hRich : 1 - 2 * δ < μ.real Rich)
    (hNoOpen : μ.real (Rich \ Open) ≤ δ)
    (hBad : μ.real (Rich ∩ Bad) ≤ δ)
    (hsub : Rich ∩ (Open \ Bad) ⊆ Good) :
    1 - 4 * δ < μ.real Good := by
  have hcover : Rich ⊆ (Rich \ Open) ∪ (Rich ∩ Bad) ∪ Good := by
    intro ω hω
    by_cases ho : ω ∈ Open
    · by_cases hb : ω ∈ Bad
      · exact Or.inl (Or.inr ⟨hω, hb⟩)
      · exact Or.inr (hsub ⟨hω, ho, hb⟩)
    · exact Or.inl (Or.inl ⟨hω, ho⟩)
  have hmono : μ.real Rich ≤ μ.real ((Rich \ Open) ∪ (Rich ∩ Bad) ∪ Good) :=
    measureReal_mono hcover (measure_ne_top _ _)
  have hu1 := measureReal_union_le (μ := μ) (Rich \ Open) (Rich ∩ Bad)
  have hu2 := measureReal_union_le (μ := μ) ((Rich \ Open) ∪ (Rich ∩ Bad)) Good
  linarith

/-- Numerical end of the target argument with the v15 choices
`δ=ε²/64`, `δc=ε/4`. -/
theorem target_error_arithmetic {ε δ δc x y : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : δ = ε ^ 2 / 64) (hδc : δc = ε / 4)
    (hx : 1 - 4 * δ < x) (hy : x * (1 - δc) ≤ y) :
    1 - ε < y := by
  subst δ
  subst δc
  have hx0 : 0 ≤ x := by
    have : 0 < 1 - 4 * (ε ^ 2 / 64) := by nlinarith [sq_nonneg ε]
    linarith
  have hfac : 0 ≤ 1 - ε / 4 := by linarith
  nlinarith [mul_nonneg hx0 hfac, sq_nonneg ε]

end KNAll.Site.ReinforcedTarget

end
