import Hypergraph.TargetExtensionClosed
import Hypergraph.TargetAwareLattice
import Hypergraph.CorridorGeometry
import Hypergraph.SelectionPacking

/-!
# Concrete target-aware packaging for genuine quarter-face targets

The target cylinder at a shell contact generally leaves the current nested barrier, while staying
inside the fresh site subbox.  This file records that distinction explicitly.  It also turns the
existential integer-radius witness in `CorrMove.FaceTarget` into a translated standard orthant,
so the target of the local window is a subset of the caller's actual distant `Tset`.
-/

noncomputable section

namespace KNAll.Site.CoreFaceTarget

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor KNAll.Site.MoveWindowInput
open scoped Classical

variable {d : Nat} [NeZero d]
variable {p q : unitInterval} {chi eps : Real}

/-! ## The corrected fresh-support target-extension interface -/

/-- A target-extension level whose barrier is `D`, but whose finite target cylinder is allowed
to use the whole fresh site subbox `Fresh`.  This is the distinction made in Manuscript Lemma
7.4: the contacts are contacts of a nested enlargement of `B`, whereas the geometry leading to
the distant target is only required to stay in the ambient site subbox. -/
structure FreshLevel {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (Dom Fresh : Finset V) (o : V) (T : Set V) where
  D : Finset V
  O : Finset V
  Int : Finset V
  U : V → Finset V
  J : V → Finset V
  sel : Finset V → Finset V
  Gx : V → Set (SiteConfig V)
  support : V → Finset V
  hIntO : Int ⊆ O
  hOD : O ⊆ D
  hDFresh : D ⊆ Fresh
  hFreshDom : Fresh ⊆ Dom
  hoDom : o ∈ Dom
  hoFresh : o ∉ Fresh
  hU : ∀ x ∈ TargetExt.outerBoundary G Dom D, U x ⊆ O \ Int
  hJD : ∀ x ∈ TargetExt.outerBoundary G Dom D, J x ⊆ D
  hJO : ∀ x ∈ TargetExt.outerBoundary G Dom D, ∀ y ∈ J x, y ∉ O
  hW3 : ∀ x ∈ TargetExt.outerBoundary G Dom D, ∀ u ∈ U x,
    (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
      connWithin G (insert x (insert u (↑(J x) : Set V))) x u
  hsel_sub : ∀ K, sel K ⊆ K
  hsel_disj : ∀ K, (↑(sel K) : Set V).PairwiseDisjoint J
  hsupport : ∀ x ∈ TargetExt.outerBoundary G Dom D, support x ⊆ Fresh
  hGdet : ∀ x ∈ TargetExt.outerBoundary G Dom D,
    DeterminedBy (Gx x) (↑(support x) : Set V)
  hrelay : ∀ x ∈ TargetExt.outerBoundary G Dom D, ∀ omega ∈ Gx x,
    ∃ u ∈ U x, u ∈ omega ∧ ∀ omega' ∈ Gx x,
      omega' ∩ (↑(O \ Int) : Set V) = omega ∩ (↑(O \ Int) : Set V) →
        omega' ∈ TargetExt.toTarget G Fresh T u

section FreshOneLevel

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- A selected barrier contact and its open seed reach any reliable face relay; the continuation
may use `Fresh`, rather than being incorrectly confined to the current barrier. -/
theorem seedOpen_inter_reliableFaceFresh_subset (w : V → unitInterval)
    {Dom Fresh D O Int : Finset V} (hIntO : Int ⊆ O) (hOD : O ⊆ D)
    (hDFresh : D ⊆ Fresh) (hDDom : D ⊆ Dom) (hFreshDom : Fresh ⊆ Dom)
    (o : V) (T : Set V) (delta : Real) (sel : Finset V → Finset V)
    (J U : V → Finset V) (hsel_sub : ∀ K, sel K ⊆ K) {x : V}
    (hx : x ∈ TargetExt.outerBoundary G Dom D) (hU : U x ⊆ O \ Int)
    (hJD : J x ⊆ D) (hJO : ∀ y ∈ J x, y ∉ O)
    (hW3 : ∀ u ∈ U x,
      (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
        connWithin G (insert x (insert u (↑(J x) : Set V))) x u) :
    TargetExt.seedOpen G Dom D o sel J x ∩
        TargetExt.reliableFace G w (O \ Int) Fresh T delta (U x) ⊆
      TargetExt.reachRelayD G w Dom Fresh O Int o T delta := by
  rintro omega ⟨⟨hxsel, hJomega⟩, hface⟩
  obtain ⟨u, huU, huomega, hrel⟩ := Set.mem_iUnion₂.1 hface
  have hxc : x ∈ TargetExt.contacts G Dom D o omega := hsel_sub _ hxsel
  have hox : omega ∈ connWithin G (↑(Dom \ D) : Set V) o x :=
    (Finset.mem_filter.1 hxc).2
  have hxomega : x ∈ omega := (TargetExt.mem_of_connWithin G hox).1
  have hsub : insert x (insert u (↑(J x) : Set V)) ⊆ omega := by
    intro z hz
    rcases hz with rfl | hz
    · exact hxomega
    rcases hz with rfl | hz
    · exact huomega
    · exact hJomega hz
  have hxu : omega ∈ connWithin G (insert x (insert u (↑(J x) : Set V))) x u :=
    isUpperSet_connWithin G _ x u hsub (hW3 u huU)
  refine Set.mem_iUnion₂.2 ⟨u, hU huU, hrel, ?_⟩
  change omega ∈ connWithin G (↑(Dom \ Int) : Set V) o u
  refine connWithin_mono_set G ?_ o u (TargetExt.connWithin_trans G hox hxu)
  intro z hz
  rw [Finset.mem_coe, Finset.mem_sdiff]
  rcases hz with hz | hz
  · have hz' := Finset.mem_sdiff.1 (Finset.mem_coe.1 hz)
    exact ⟨hz'.1, fun hInt => hz'.2 (hOD (hIntO hInt))⟩
  · rcases hz with rfl | hz
    · have hx' := Finset.mem_sdiff.1 (TargetExt.outerBoundary_subset G Dom D hx)
      exact ⟨hx'.1, fun hInt => hx'.2 (hOD (hIntO hInt))⟩
    rcases hz with rfl | hz
    · have hu' := Finset.mem_sdiff.1 (hU huU)
      exact ⟨hFreshDom (hDFresh (hOD hu'.1)), hu'.2⟩
    · have hzJ := Finset.mem_coe.1 hz
      exact ⟨hFreshDom (hDFresh (hJD hzJ)),
        fun hInt => hJO z hzJ (hIntO hInt)⟩

end FreshOneLevel

section FreshOneLevelEstimate

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The one-level estimate with barrier contacts at `D` and distant continuation inside
`Fresh`.  The proved finite hyperedge inequality supplies the final pattern-wise gluing step. -/
theorem real_target_ge_one_level_fresh (w : V → unitInterval)
    {Dom Fresh D O Int : Finset V} (hIntO : Int ⊆ O) (hOD : O ⊆ D)
    (hDFresh : D ⊆ Fresh) (hFreshDom : Fresh ⊆ Dom)
    (o : V) (hoDom : o ∈ Dom) (hoFresh : o ∉ Fresh) (hwo : w o = 1)
    (T : Set V) (N k s : Nat) {q : Real} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (sel : Finset V → Finset V) (J U : V → Finset V)
    (Gx : V → Set (SiteConfig V)) (hsel_sub : ∀ K, sel K ⊆ K)
    (hsel_card : ∀ K ⊆ TargetExt.outerBoundary G Dom D,
      N ≤ K.card → k ≤ (sel K).card)
    (hsel_disj : ∀ K, (↑(sel K) : Set V).PairwiseDisjoint J)
    (hU : ∀ x ∈ TargetExt.outerBoundary G Dom D, U x ⊆ O \ Int)
    (hJD : ∀ x ∈ TargetExt.outerBoundary G Dom D, J x ⊆ D)
    (hJO : ∀ x ∈ TargetExt.outerBoundary G Dom D, ∀ y ∈ J x, y ∉ O)
    (hs : ∀ x ∈ TargetExt.outerBoundary G Dom D, (J x).card ≤ s)
    (hW3 : ∀ x ∈ TargetExt.outerBoundary G Dom D, ∀ u ∈ U x,
      (insert x (insert u (↑(J x) : Set V)) : SiteConfig V) ∈
        connWithin G (insert x (insert u (↑(J x) : Set V))) x u)
    (hwJ : ∀ x ∈ TargetExt.outerBoundary G Dom D, ∀ y ∈ J x, q ≤ (w y : Real))
    (hGm : ∀ x ∈ TargetExt.outerBoundary G Dom D, MeasurableSet (Gx x))
    (hrelay : ∀ x ∈ TargetExt.outerBoundary G Dom D, ∀ omega ∈ Gx x,
      ∃ u ∈ U x, u ∈ omega ∧ ∀ omega' ∈ Gx x,
        omega' ∩ (↑(O \ Int) : Set V) = omega ∩ (↑(O \ Int) : Set V) →
          omega' ∈ TargetExt.toTarget G Fresh T u)
    {delta eta : Real} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hetadelta : eta ≤ delta)
    (hGood : ∀ x ∈ TargetExt.outerBoundary G Dom D,
      1 - eta ≤ (prodBernoulli w).real (Gx x)) :
    ((prodBernoulli w).real (TargetExt.poor G Dom D o N)ᶜ - (1 - q ^ s) ^ k) *
        (1 - eta / delta) * (1 - delta) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hseed := TargetExt.real_poorCompl_diff_seeds_le G w Dom D o N k s hq0 hq1
    sel J hsel_sub hsel_card hsel_disj hJD hs hwJ
  have hUm : MeasurableSet
      (⋃ x ∈ TargetExt.outerBoundary G Dom D, TargetExt.seedOpen G Dom D o sel J x) :=
    Finset.measurableSet_biUnion _ fun x _ => TargetExt.measurableSet_seedOpen G Dom D o sel J x
  have h1 : (prodBernoulli w).real (TargetExt.poor G Dom D o N)ᶜ -
        (1 - q ^ s) ^ k ≤
      (prodBernoulli w).real
        (⋃ x ∈ TargetExt.outerBoundary G Dom D, TargetExt.seedOpen G Dom D o sel J x) := by
    have hadd := measureReal_inter_add_sdiff (μ := prodBernoulli w)
      (s := (TargetExt.poor G Dom D o N)ᶜ) hUm (measure_ne_top _ _)
    have hmono :
        (prodBernoulli w).real ((TargetExt.poor G Dom D o N)ᶜ ∩
          ⋃ x ∈ TargetExt.outerBoundary G Dom D, TargetExt.seedOpen G Dom D o sel J x) ≤
        (prodBernoulli w).real
          (⋃ x ∈ TargetExt.outerBoundary G Dom D, TargetExt.seedOpen G Dom D o sel J x) :=
      measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
    linarith
  have h2 := TargetExt.prodBernoulli_real_biUnion_inter_ge w (O \ Int)
    (TargetExt.outerBoundary G Dom D) (fun x => TargetExt.seedOpen G Dom D o sel J x)
    (fun x => TargetExt.reliableFace G w (O \ Int) Fresh T delta (U x))
    (fun x hx => by
      refine (TargetExt.determinedBy_seedOpen G Dom D o sel J x).mono fun z hz => ?_
      rw [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, not_and, not_not]
      intro hzO
      rcases hz with hz | hz
      · exact absurd (hOD hzO)
          (Finset.mem_sdiff.1 (Finset.mem_coe.1 hz)).2
      · exact absurd hzO (hJO x hx z (Finset.mem_coe.1 hz)))
    (fun x hx => TargetExt.determinedBy_reliableFace G w Fresh T delta (hU x hx))
    (fun x _ => TargetExt.measurableSet_seedOpen G Dom D o sel J x)
    (fun x hx => TargetExt.measurableSet_reliableFace G w Fresh T delta (hU x hx))
    (m := 1 - eta / delta)
    (fun x hx => TargetExt.real_reliableFace_ge G w Fresh T hdelta0 hdelta1
      (hU x hx) (hGm x hx) (hrelay x hx) (hGood x hx))
  have h3 : (prodBernoulli w).real
        (⋃ x ∈ TargetExt.outerBoundary G Dom D,
          TargetExt.seedOpen G Dom D o sel J x ∩
            TargetExt.reliableFace G w (O \ Int) Fresh T delta (U x)) ≤
      (prodBernoulli w).real (TargetExt.reachRelayD G w Dom Fresh O Int o T delta) :=
    measureReal_mono (Set.iUnion₂_subset fun x hx =>
      seedOpen_inter_reliableFaceFresh_subset G w hIntO hOD hDFresh
        (hDFresh.trans hFreshDom) hFreshDom o T delta sel J U hsel_sub hx
        (hU x hx) (hJD x hx) (hJO x hx) (hW3 x hx)) (measure_ne_top _ _)
  have h4 := TargetExt.real_reachRelayD_target_ge G
    FiniteHyperGluingClosed.pinnedSiteGluing w hIntO (hOD.trans hDFresh)
      hFreshDom o hoDom hoFresh hwo T hdelta1
  have hm0 : 0 ≤ 1 - eta / delta := by
    rw [sub_nonneg, div_le_one hdelta0]
    exact hetadelta
  have hdelta' : 0 ≤ 1 - delta := by linarith
  calc
    ((prodBernoulli w).real (TargetExt.poor G Dom D o N)ᶜ - (1 - q ^ s) ^ k) *
          (1 - eta / delta) * (1 - delta) ≤
        (prodBernoulli w).real
            (⋃ x ∈ TargetExt.outerBoundary G Dom D,
              TargetExt.seedOpen G Dom D o sel J x) *
          (1 - eta / delta) * (1 - delta) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hm0) hdelta'
    _ ≤ (prodBernoulli w).real
          (⋃ x ∈ TargetExt.outerBoundary G Dom D,
            TargetExt.seedOpen G Dom D o sel J x ∩
              TargetExt.reliableFace G w (O \ Int) Fresh T delta (U x)) *
          (1 - delta) := mul_le_mul_of_nonneg_right h2 hdelta'
    _ ≤ (prodBernoulli w).real (TargetExt.reachRelayD G w Dom Fresh O Int o T delta) *
          (1 - delta) := mul_le_mul_of_nonneg_right h3 hdelta'
    _ ≤ (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := h4

end FreshOneLevelEstimate

section FreshAssembly

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Target extension for shell barriers whose distant finite windows are supported anywhere in
the common fresh site subbox. -/
theorem targetExtension_fresh (Dom Fresh : Finset V) (o : V) (T : Set V)
    {Delta : Nat} (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Delta)
    {L : Nat} (hL : 0 < L)
    (lv : Nat → FreshLevel G Dom Fresh o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ (lv i).D →
      ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D)
    (qI : unitInterval) (hq1 : (qI : Real) < 1)
    (w : V → unitInterval) (hwo : w o = 1)
    (hwFresh : ∀ y ∈ Fresh, w y = qI) (N k s : Nat)
    (hsel_card : ∀ i < L, ∀ K ⊆ TargetExt.outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      ((lv i).J x).card ≤ s)
    {delta : Real} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1 / 3)
    (hLdelta : 1 ≤ (L : Real) * delta * (1 - (qI : Real)) ^ (Delta * N))
    (hk : (1 - (qI : Real) ^ s) ^ k ≤ delta)
    (hGood : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      1 - 3 * delta ^ 2 ≤
        (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - delta <
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    (1 - 3 * delta) * (1 - 3 * delta) * (1 - delta) ≤
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hq0 : (0 : Real) ≤ qI := qI.2.1
  have hwBarrier : ∀ i < L, ∀ y ∈ (lv i).D, (w y : Real) ≤ qI := by
    intro i hi y hy
    rw [hwFresh y ((lv i).hDFresh hy)]
  obtain ⟨i, hi, hrich⟩ := TargetExt.exists_level_real_poor_compl_gt_rel G Dom o N Delta
    hq0 hq1 hdeg hL (fun i => (lv i).D) w
    (fun i hi => (lv i).hDFresh.trans (lv i).hFreshDom) hnest hgateRel hwBarrier
    (fun i hi hoD => (lv i).hoFresh ((lv i).hDFresh hoD)) hB hLdelta hsrc
  have heta : 3 * delta ^ 2 ≤ delta := by nlinarith
  have hGoodW : ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      1 - 3 * delta ^ 2 ≤ (prodBernoulli w).real ((lv i).Gx x) := by
    intro x hx
    have hGm : MeasurableSet ((lv i).Gx x) :=
      ((lv i).hGdet x hx).measurableSet_of_finset
    have htrans := prodBernoulli_real_eq_of_determinedBy (fun _ : V => qI) w
      (F := (↑((lv i).support x) : Set V))
      (fun y hy => (hwFresh y ((lv i).hsupport x hx (Finset.mem_coe.1 hy))).symm)
      ((lv i).hGdet x hx) hGm
    rw [← htrans]
    exact hGood i hi x hx
  have hone := real_target_ge_one_level_fresh G w (lv i).hIntO (lv i).hOD
    (lv i).hDFresh (lv i).hFreshDom o (lv i).hoDom (lv i).hoFresh hwo T
    N k s hq0 hq1.le (lv i).sel (lv i).J (lv i).U (lv i).Gx
    (lv i).hsel_sub (hsel_card i hi) (lv i).hsel_disj (lv i).hU (lv i).hJD
    (lv i).hJO (hs i hi) (lv i).hW3
    (fun x hx y hy => by rw [hwFresh y ((lv i).hDFresh ((lv i).hJD x hx hy))])
    (fun x hx => ((lv i).hGdet x hx).measurableSet_of_finset) (lv i).hrelay
    hdelta0 (by linarith) heta hGoodW
  have h3 : 3 * delta ^ 2 / delta = 3 * delta := by field_simp
  rw [h3] at hone
  have hA : 1 - 3 * delta ≤
      (prodBernoulli w).real (TargetExt.poor G Dom (lv i).D o N)ᶜ -
        (1 - (qI : Real) ^ s) ^ k := by
    linarith
  have h13 : 0 ≤ 1 - 3 * delta := by linarith
  have h1 : 0 ≤ 1 - delta := by linarith
  calc
    (1 - 3 * delta) * (1 - 3 * delta) * (1 - delta) ≤
        ((prodBernoulli w).real (TargetExt.poor G Dom (lv i).D o N)ᶜ -
          (1 - (qI : Real) ^ s) ^ k) * (1 - 3 * delta) * (1 - delta) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h13) h1
    _ ≤ (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := hone

/-- Epsilon-delta form of `targetExtension_fresh`. -/
theorem targetExtension_eps_fresh (Dom Fresh : Finset V) (o : V) (T : Set V)
    {Delta : Nat} (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Delta)
    {L : Nat} (hL : 0 < L)
    (lv : Nat → FreshLevel G Dom Fresh o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ (lv i).D →
      ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D)
    (qI : unitInterval) (hq1 : (qI : Real) < 1)
    (w : V → unitInterval) (hwo : w o = 1)
    (hwFresh : ∀ y ∈ Fresh, w y = qI) (N k s : Nat)
    (hsel_card : ∀ i < L, ∀ K ⊆ TargetExt.outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      ((lv i).J x).card ≤ s)
    {eps : Real} (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hLdelta : 1 ≤ (L : Real) * (eps / 8) *
      (1 - (qI : Real)) ^ (Delta * N))
    (hk : (1 - (qI : Real) ^ s) ^ k ≤ eps / 8)
    (hGood : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      1 - 3 * (eps / 8) ^ 2 ≤
        (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - eps / 8 <
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    1 - eps < (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o T) := by
  have hout := targetExtension_fresh G Dom Fresh o T hdeg hL lv hnest hgateRel hB
    qI hq1 w hwo hwFresh N k s hsel_card hs (delta := eps / 8)
    (by linarith) (by linarith) hLdelta hk hGood hsrc
  let delta : Real := eps / 8
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta ≤ 1 / 8 := by dsimp [delta]; linarith
  have hcube : 1 - 7 * delta ≤
      (1 - 3 * delta) * (1 - 3 * delta) * (1 - delta) := by
    have : 0 ≤ delta ^ 2 * (5 - 3 * delta) :=
      mul_nonneg (sq_nonneg delta) (by linarith)
    nlinarith
  have heps : 1 - eps < 1 - 7 * delta := by dsimp [delta]; linarith
  simpa only [delta] using lt_of_lt_of_le heps (hcube.trans hout)

end FreshAssembly

/-! ## Transcript and `CoreRes.FaceInputs` adapters -/

/-- The finite family consumed by the fresh-support target extension.  Its target cylinders are
visible through `FreshLevel`; no target probability conclusion is stored in this object. -/
structure FreshQueryDatum (h : MacroExp.Tr d) (q : unitInterval)
    (Dom Fresh Bset Tset : Finset (Site d)) (eps : Real) where
  levels : Nat
  contacts : Nat
  seedCount : Nat
  seedSize : Nat
  levels_pos : 0 < levels
  lv : Nat → FreshLevel (zdGraph d) Dom Fresh (MacroExp.emb 0)
    (↑Tset : Set (Site d))
  nested : ∀ j, j + 1 < levels → (lv (j + 1)).D ⊆ (lv j).D
  gateRel : ∀ j, j + 1 < levels → ∀ x ∈ Dom, x ∉ (lv j).D →
    ∀ y ∈ (lv j).D, (zdGraph d).Adj x y → y ∉ (lv (j + 1)).D
  source_target : ∀ j, j < levels → (↑Bset : Set (Site d)) ⊆ ↑(lv j).D
  select : ∀ j, j < levels →
    ∀ K ⊆ TargetExt.outerBoundary (zdGraph d) Dom (lv j).D,
      contacts ≤ K.card → seedCount ≤ ((lv j).sel K).card
  seed_card : ∀ j, j < levels →
    ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (lv j).D,
      ((lv j).J x).card ≤ seedSize
  level_budget : 1 ≤ (levels : Real) * (eps / 8) *
    (1 - (q : Real)) ^ ((2 * d) * contacts)
  seed_budget : (1 - (q : Real) ^ seedSize) ^ seedCount ≤ eps / 8
  reliable : ∀ j, j < levels →
    ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (lv j).D,
      1 - 3 * (eps / 8) ^ 2 ≤
        (siteBernoulli (fun _ : Site d => q)).real ((lv j).Gx x)

/-- Apply a fresh-support query under the actual transcript law.  The recorded-open source is the
forced-open vertex required by the manuscript gluing step. -/
theorem FreshQueryDatum.apply {h : MacroExp.Tr d} {q : unitInterval}
    (hq0 : 0 < (q : Real)) (hq1 : (q : Real) < 1)
    {Dom Fresh Bset Tset : Finset (Site d)} {eps : Real}
    (D : FreshQueryDatum h q Dom Fresh Bset Tset eps)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfresh : Disjoint h.inspected Fresh)
    (hsrc : 1 - eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Bset : Set (Site d)))) :
    1 - eps < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Tset : Set (Site d))) := by
  rw [CorrMove.prob_eq_product h q hq0 hq1
    (measurableSet_connWithinSet (zdGraph d) Dom (MacroExp.emb 0)
      (↑Tset : Set (Site d)))]
  rw [CorrMove.prob_eq_product h q hq0 hq1
    (measurableSet_connWithinSet (zdGraph d) Dom (MacroExp.emb 0)
      (↑Bset : Set (Site d)))] at hsrc
  let w : Site d → unitInterval :=
    pinW (fun _ : Site d => q) (↑h.inspected : Set (Site d))
      (↑h.openSites : Set (Site d))
  have hwo : w (MacroExp.emb 0) = 1 := by
    dsimp only [w]
    exact pinW_apply_of_mem_of_mem _
      (Finset.mem_coe.2 (h.openSites_subset horigin)) (Finset.mem_coe.2 horigin)
  have hwFresh : ∀ y ∈ Fresh, w y = q := by
    intro y hy
    dsimp only [w]
    rw [pinW_apply_of_not_mem]
    intro hyI
    exact Finset.disjoint_left.1 hfresh (Finset.mem_coe.1 hyI) hy
  exact targetExtension_eps_fresh (zdGraph d) Dom Fresh (MacroExp.emb 0)
    (↑Tset : Set (Site d)) (Delta := 2 * d) (by
      intro x
      rw [Finset.filter_congr_decidable]
      exact MacroExp.card_le_of_forall_adj fun y hy => (Finset.mem_filter.1 hy).2)
    D.levels_pos D.lv D.nested D.gateRel
    D.source_target q hq1 w hwo hwFresh D.contacts D.seedCount D.seedSize
    D.select D.seed_card heps0 heps1 D.level_budget D.seed_budget D.reliable hsrc

/-- A concrete fresh-support datum for every genuine quarter-face target query. -/
abbrev FreshFaceWindowFamily (R : Nat) (h : MacroExp.Tr d) (q : unitInterval)
    (Dom : Finset (Site d)) : Type :=
  ∀ (Fresh Bset Tset : Finset (Site d)) (eps : Real),
    0 < eps → eps ≤ 1 →
    Disjoint h.inspected Fresh → (MacroExp.emb 0 : Site d) ∉ Fresh → Fresh ⊆ Dom →
    CorrMove.FaceTarget (R : Int) Fresh Bset Tset →
      FreshQueryDatum h q Dom Fresh Bset Tset eps

/-- Genuine target-aware shell families discharge the exact `FaceInputs` consumed by
`CoreAcceptedAssembly`.  The source-open premise is already part of that assembly's admissible
history, but was absent from the older standalone `FaceInputs` abbreviation. -/
theorem faceInputs_of_freshWindowFamily {q : unitInterval}
    (hq0 : 0 < (q : Real)) (hq1 : (q : Real) < 1)
    {R : Nat} {h : MacroExp.Tr d} {Dom : Finset (Site d)}
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (F : FreshFaceWindowFamily (d := d) R h q Dom) :
    CoreRes.FaceInputs (d := d) R h q Dom := by
  intro Fresh Bset Tset eps heps0 heps1 hfresh hzero hFreshDom htarget hsrc
  exact (F Fresh Bset Tset eps heps0 heps1 hfresh hzero hFreshDom htarget).apply
    hq0 hq1 heps0 heps1 horigin hfresh hsrc

/-- A natural-radius, genuinely oriented target selected from `CorrMove.FaceTarget`. -/
structure ChosenTarget (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (R : Nat) (Fresh Bset Tset : Finset (Site d)) (v : Site d) where
  radius : Nat
  axis : Fin d
  sigma : Int
  tau : Fin d → Int
  sigma_eq : sigma = 1 ∨ sigma = -1
  local_lt_radius : S.localRadius < radius
  owner_subset_fresh : TargetAwareLattice.shiftedOwner radius v ⊆ Fresh
  target_subset : TargetAwareLattice.shiftedTarget radius v
      (axis, TargetAwareLattice.qfaceUnits axis sigma tau) ⊆ Tset

/-- `FaceTarget` supplies an actual distant orthant, not an outward-sphere surrogate. -/
theorem exists_chosenTarget
    (S : TargetAwareLattice.BaseScales (d := d) q chi) (R : Nat)
    (hscale : S.localRadius < R) {Fresh Bset Tset : Finset (Site d)}
    (hface : CorrMove.FaceTarget (R : Int) Fresh Bset Tset) (v : Site d)
    (hnear : ∃ b ∈ Bset, ∀ j, |v j - b j| ≤ (R : Int)) :
    Nonempty (ChosenTarget S R Fresh Bset Tset v) := by
  obtain ⟨ell, a, sigma, tau, hRell, hsigma, hcube, hqface⟩ := hface v hnear
  have hell0 : 0 ≤ ell := le_trans (Int.natCast_nonneg R) hRell
  let n : Nat := ell.toNat
  have hncast : (n : Int) = ell := Int.toNat_of_nonneg hell0
  refine ⟨{
    radius := n
    axis := a
    sigma := sigma
    tau := tau
    sigma_eq := hsigma
    local_lt_radius := ?_
    owner_subset_fresh := ?_
    target_subset := ?_ }⟩
  · have hRnZ : (R : Int) ≤ (n : Int) := by simpa only [hncast] using hRell
    have hRn : R ≤ n := by exact_mod_cast hRnZ
    exact hscale.trans_le hRn
  · rw [TargetAwareLattice.shiftedOwner,
      TargetAwareLattice.shiftFinset_box_eq_cube, hncast]
    exact hcube
  · exact (TargetAwareLattice.shiftedTarget_subset_qface n v a sigma tau hsigma).trans
      (by simpa only [hncast] using hqface)

/-- A deterministic choice of the genuine target at every point where the target relation applies. -/
def chooseTarget
    (S : TargetAwareLattice.BaseScales (d := d) q chi) (R : Nat)
    (hscale : S.localRadius < R) {Fresh Bset Tset : Finset (Site d)}
    (hface : CorrMove.FaceTarget (R : Int) Fresh Bset Tset)
    (v : Site d) (hnear : ∃ b ∈ Bset, ∀ j, |v j - b j| ≤ (R : Int)) :
    ChosenTarget S R Fresh Bset Tset v :=
  Classical.choice (exists_chosenTarget S R hscale hface v hnear)

/-! ## One concrete corridor shell level -/

/-- The target-aware translated local cube is literally the contact cube from
`CorridorGeometry` when their radii agree. -/
theorem shiftedLocalBox_eq_cube
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat) (x : Site d)
    (hM : Sc.M = S.localRadius) :
    TargetAwareLattice.shiftedLocalBox S (Corridor.cubeCentre Sc c j x) =
      Corridor.cube Sc c j x := by
  have hMcast : (Sc.M : Int) = (S.localRadius : Int) := by exact_mod_cast hM
  ext z
  rw [TargetAwareLattice.shiftedLocalBox,
    TargetAwareLattice.shiftFinset_box_eq_cube, CorrMove.mem_cube,
    Corridor.cube, Corridor.mem_rbox]
  constructor
  · intro hz a
    have ha := hz a
    rw [abs_le] at ha
    rw [hMcast]
    omega
  · intro hz a
    have ha := hz a
    rw [abs_le]
    rw [hMcast] at ha
    omega

/-- The standard orthant chosen with the contact's outward sign lies in the literal corridor
face.  Transverse zero signs merely select one quarter of that face. -/
theorem shiftedLocalFace_subset_face
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat) {Dom : Finset (Site d)}
    {x : Site d} (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.Dbox Sc c j))
    (hM : Sc.M = S.localRadius) :
    TargetAwareLattice.shiftedFace S (Corridor.cubeCentre Sc c j x)
        (Corridor.cI Sc c j x,
          TargetAwareLattice.qfaceUnits (Corridor.cI Sc c j x)
            (Corridor.cσ Sc c j x) (fun _ => 0)) ⊆
      Corridor.face Sc c j x := by
  intro u hu
  have hcontact := Corridor.isContact_of_mem_outerBoundary Sc c j Dom hx
  have hsign : Corridor.cσ Sc c j x = 1 ∨ Corridor.cσ Sc c j x = -1 :=
    (Corridor.dir_spec hcontact).1
  have hq := TargetAwareLattice.shifted_orthantFace_subset_qface
    (Corridor.cubeCentre Sc c j x) S.localRadius (Corridor.cI Sc c j x)
      (Corridor.cσ Sc c j x) (fun _ => 0) hsign hu
  rw [CorrMove.mem_qface] at hq
  rw [Corridor.face, Finset.mem_filter]
  constructor
  · rw [← shiftedLocalBox_eq_cube S Sc c j x hM]
    rw [TargetAwareLattice.shiftedFace] at hu
    rw [TargetAwareLattice.shiftedLocalBox]
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hu
    exact Finset.mem_image.2 ⟨z, (mem_orthantFace.1 hz).1, rfl⟩
  · have haxis := hq.2.1
    have hcentre :
        Corridor.cubeCentre Sc c j x (Corridor.cI Sc c j x) =
          c (Corridor.cI Sc c j x) + Corridor.cσ Sc c j x *
            (Corridor.ρO Sc j (Corridor.cI Sc c j x) - Sc.M) := by
      simp [Corridor.cubeCentre]
    rw [hcentre, ← hM] at haxis
    rcases hsign with hs | hs <;> rw [hs] at haxis ⊢ <;> omega

/-- The outward quarter of the local translated box used at a corridor contact. -/
def corridorLocalFace (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    (x : Site d) : MoveWindowInput.FaceIndex d :=
  (Corridor.cI Sc c j x,
    TargetAwareLattice.qfaceUnits (Corridor.cI Sc c j x)
      (Corridor.cσ Sc c j x) (fun _ => 0))

/-- A total choice of far target radii and orientations.  Its three specifications are only
required at actual contacts, which is exactly where the target-extension level consumes them. -/
structure ContactTargetPlan
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    (Dom Fresh Bset Tset : Finset (Site d)) where
  radius : Site d → Nat
  targetFace : Site d → MoveWindowInput.FaceIndex d
  local_lt_radius : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
    (Corridor.Dbox Sc c j), S.localRadius < radius x
  owner_subset_fresh : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
    (Corridor.Dbox Sc c j),
      TargetAwareLattice.shiftedOwner (radius x) (Corridor.cubeCentre Sc c j x) ⊆ Fresh
  target_subset : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
    (Corridor.Dbox Sc c j),
      TargetAwareLattice.shiftedTarget (radius x) (Corridor.cubeCentre Sc c j x)
        (targetFace x) ⊆ Tset

/-- The genuine `FaceTarget` relation and the explicit contact-to-base proximity produce the
complete target plan.  Thus `ContactTargetPlan` introduces no independent target-cylinder
existence assumption. -/
theorem contactTargetPlan_nonempty
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)} (R : Nat)
    (hscale : S.localRadius < R)
    (hface : CorrMove.FaceTarget (R : Int) Fresh Bset Tset)
    (hnear : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc c j),
        ∃ b ∈ Bset, ∀ a, |Corridor.cubeCentre Sc c j x a - b a| ≤ (R : Int)) :
    Nonempty (ContactTargetPlan S Sc c j Dom Fresh Bset Tset) := by
  classical
  let C : ∀ (x : Site d), x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc c j) → ChosenTarget S R Fresh Bset Tset
        (Corridor.cubeCentre Sc c j x) :=
    fun x hx => chooseTarget S R hscale hface _ (hnear x hx)
  let radius : Site d → Nat := fun x =>
    if hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.Dbox Sc c j)
    then (C x hx).radius else S.localRadius + 1
  let targetFace : Site d → MoveWindowInput.FaceIndex d := fun x =>
    if hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.Dbox Sc c j)
    then ((C x hx).axis,
      TargetAwareLattice.qfaceUnits (C x hx).axis (C x hx).sigma (C x hx).tau)
    else corridorLocalFace Sc c j x
  refine ⟨{
    radius := radius
    targetFace := targetFace
    local_lt_radius := ?_
    owner_subset_fresh := ?_
    target_subset := ?_ }⟩
  · intro x hx
    simp only [radius, dif_pos hx]
    exact (C x hx).local_lt_radius
  · intro x hx
    simp only [radius, dif_pos hx]
    exact (C x hx).owner_subset_fresh
  · intro x hx
    simp only [radius, targetFace, dif_pos hx]
    exact (C x hx).target_subset

/-- The finite event attached to a corridor contact and its selected genuine distant target. -/
def corridorWindow
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset) (x : Site d) :
    Set (SiteConfig (Site d)) :=
  TargetAwareLattice.shiftedBaseWindow S (P.radius x)
    (Corridor.cubeCentre Sc c j x) (corridorLocalFace Sc c j x) (P.targetFace x)

/-- A fitted corridor shell, together with the non-circular far-target plan, is a concrete
fresh-support target-extension level.  Its event is the translated three-factor window from
`TargetAwareLattice`, and its continuation reaches the caller's literal `Tset`. -/
noncomputable def freshLevelOfCorridor
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset)
    (hf : Corridor.Fits Sc j) (hM : Sc.M = S.localRadius)
    (hDFresh : Corridor.Dbox Sc c j ⊆ Fresh) (hFreshDom : Fresh ⊆ Dom)
    (hoDom : (MacroExp.emb 0 : Site d) ∈ Dom)
    (hoFresh : (MacroExp.emb 0 : Site d) ∉ Fresh) :
    FreshLevel (zdGraph d) Dom Fresh (MacroExp.emb 0)
      (↑Tset : Set (Site d)) where
  D := Corridor.Dbox Sc c j
  O := Corridor.Obox Sc c j
  Int := Corridor.Ibox Sc c j
  U := fun x => TargetAwareLattice.shiftedFace S (Corridor.cubeCentre Sc c j x)
    (corridorLocalFace Sc c j x)
  J := Corridor.seed Sc c j
  sel := Corridor.selC Sc c j
  Gx := corridorWindow S Sc c j P
  support := fun x => TargetAwareLattice.shiftedOwner (P.radius x)
    (Corridor.cubeCentre Sc c j x)
  hIntO := Corridor.Ibox_subset_Obox Sc c j
  hOD := Corridor.Obox_subset_Dbox Sc c j
  hDFresh := hDFresh
  hFreshDom := hFreshDom
  hoDom := hoDom
  hoFresh := hoFresh
  hU := by
    intro x hx
    exact (shiftedLocalFace_subset_face S Sc c j hx hM).trans
      (Corridor.face_subset_shell hf
        (Corridor.isContact_of_mem_outerBoundary Sc c j Dom hx))
  hJD := by
    intro x hx
    exact Corridor.seed_subset_Dbox hf
      (Corridor.isContact_of_mem_outerBoundary Sc c j Dom hx)
  hJO := by
    intro x hx
    exact Corridor.seed_disjoint_Obox hf
      (Corridor.isContact_of_mem_outerBoundary Sc c j Dom hx)
  hW3 := by
    intro x hx u hu
    exact Corridor.connWithin_seed hf
      (Corridor.isContact_of_mem_outerBoundary Sc c j Dom hx)
      ((shiftedLocalFace_subset_face S Sc c j hx hM) hu)
  hsel_sub := Corridor.selC_subset Sc c j
  hsel_disj := Corridor.selC_pairwiseDisjoint_seed Sc c j hf
  hsupport := P.owner_subset_fresh
  hGdet := by
    intro x hx
    exact (TargetAwareLattice.shiftedBaseWindow_facts S (P.radius x)
      (P.local_lt_radius x hx) (Corridor.cubeCentre Sc c j x)
      (corridorLocalFace Sc c j x) (P.targetFace x)).determined
  hrelay := by
    intro x hx omega homega
    let F := TargetAwareLattice.shiftedBaseWindow_facts S (P.radius x)
      (P.local_lt_radius x hx) (Corridor.cubeCentre Sc c j x)
      (corridorLocalFace Sc c j x) (P.targetFace x)
    obtain ⟨u, hu, huopen, hrelay⟩ := F.relay omega homega
    refine ⟨u, hu, huopen, ?_⟩
    intro omega' homega' hagree
    have hlocal :
        omega' ∩ (↑(TargetAwareLattice.shiftedLocalBox S
            (Corridor.cubeCentre Sc c j x)) : Set (Site d)) =
          omega ∩ ↑(TargetAwareLattice.shiftedLocalBox S
            (Corridor.cubeCentre Sc c j x)) := by
      ext z
      by_cases hz : z ∈ TargetAwareLattice.shiftedLocalBox S
          (Corridor.cubeCentre Sc c j x)
      · have hzShell : z ∈ Corridor.Obox Sc c j \ Corridor.Ibox Sc c j := by
          rw [shiftedLocalBox_eq_cube S Sc c j x hM] at hz
          exact Corridor.cube_subset_shell hf
            (Corridor.isContact_of_mem_outerBoundary Sc c j Dom hx) hz
        have heq := Set.ext_iff.1 hagree z
        simpa only [Set.mem_inter_iff, Finset.mem_coe, hz, hzShell, and_true] using heq
      · simp only [Set.mem_inter_iff, Finset.mem_coe, hz, and_false]
    have hconn := hrelay omega' homega' hlocal
    rw [TargetExt.toTarget]
    obtain ⟨t, ht, hut⟩ := (mem_connWithinSet_iff (zdGraph d)
      (↑(TargetAwareLattice.shiftedOwner (P.radius x)
        (Corridor.cubeCentre Sc c j x)) : Set (Site d)) u
      (↑(TargetAwareLattice.shiftedTarget (P.radius x)
        (Corridor.cubeCentre Sc c j x) (P.targetFace x)) : Set (Site d)) omega').1 hconn
    refine (mem_connWithinSet_iff (zdGraph d) (↑Fresh : Set (Site d)) u
      (↑Tset : Set (Site d)) omega').2 ⟨t, ?_, ?_⟩
    · exact Finset.mem_coe.2 (P.target_subset x hx (Finset.mem_coe.1 ht))
    · exact connWithin_mono_set (zdGraph d)
        (Finset.coe_subset.2 (P.owner_subset_fresh x hx)) u t hut

@[simp] theorem freshLevelOfCorridor_Gx
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset)
    (hf : Corridor.Fits Sc j) (hM : Sc.M = S.localRadius)
    (hDFresh : Corridor.Dbox Sc c j ⊆ Fresh) (hFreshDom : Fresh ⊆ Dom)
    (hoDom : (MacroExp.emb 0 : Site d) ∈ Dom)
    (hoFresh : (MacroExp.emb 0 : Site d) ∉ Fresh) (x : Site d) :
    (freshLevelOfCorridor S Sc c j P hf hM hDFresh hFreshDom hoDom hoFresh).Gx x =
      corridorWindow S Sc c j P x := rfl

/-- The base three-factor estimate is exactly the reliability bound required by the fresh query
package when its tolerance is `(eps / 8)^2`. -/
theorem freshLevelOfCorridor_reliable
    (S : TargetAwareLattice.BaseScales (d := d) q ((eps / 8) ^ 2))
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset)
    {x : Site d} (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc c j)) :
    1 - 3 * (eps / 8) ^ 2 ≤
      (siteBernoulli (fun _ : Site d => q)).real (corridorWindow S Sc c j P x) := by
  exact (TargetAwareLattice.shiftedBaseWindow_facts S (P.radius x)
    (P.local_lt_radius x hx) (Corridor.cubeCentre Sc c j x)
    (corridorLocalFace Sc c j x) (P.targetFace x)).window_bound.le

/-- Every selected contact event has the explicit all-open witness. -/
theorem corridorWindow_nonempty
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset)
    {x : Site d} (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc c j)) :
    (corridorWindow S Sc c j P x).Nonempty := by
  exact ⟨Set.univ, (TargetAwareLattice.shiftedBaseWindow_facts S (P.radius x)
    (P.local_lt_radius x hx) (Corridor.cubeCentre Sc c j x)
    (corridorLocalFace Sc c j x) (P.targetFace x)).allOpen_mem⟩

/-- The selected far target lies in its declared owner.  Together with
`ContactTargetPlan.owner_subset_fresh`, this records the missing `target ⊆ P ⊆ Fresh`
collar check explicitly. -/
theorem contactTarget_subset_owner
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset)
    {x : Site d} (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc c j)) :
    TargetAwareLattice.shiftedTarget (P.radius x) (Corridor.cubeCentre Sc c j x)
        (P.targetFace x) ⊆
      TargetAwareLattice.shiftedOwner (P.radius x) (Corridor.cubeCentre Sc c j x) := by
  exact (TargetAwareLattice.shiftedBaseWindow_facts S (P.radius x)
    (P.local_lt_radius x hx) (Corridor.cubeCentre Sc c j x)
    (corridorLocalFace Sc c j x) (P.targetFace x)).target_subset_owner

/-- Freshness makes every selected owner disjoint from the already inspected path region. -/
theorem contactOwner_disjoint_inspected {h : MacroExp.Tr d}
    (S : TargetAwareLattice.BaseScales (d := d) q chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset)
    (hfresh : Disjoint h.inspected Fresh)
    {x : Site d} (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc c j)) :
    Disjoint h.inspected
      (TargetAwareLattice.shiftedOwner (P.radius x) (Corridor.cubeCentre Sc c j x)) :=
  hfresh.mono_right (P.owner_subset_fresh x hx)

/-! ## A finite corridor family and the exact residual geometric certificate -/

/-- `safeLevel L hL j` agrees with `j` below `L` and is the valid fallback level zero above it.
It lets the finite shell family populate the formally total `FreshQueryDatum.lv` field without
asking for impossible fitted shrinking boxes at every natural index. -/
def safeLevel (L : Nat) (hL : 0 < L) (j : Nat) : Nat :=
  if j < L then j else 0

theorem safeLevel_lt (L : Nat) (hL : 0 < L) (j : Nat) : safeLevel L hL j < L := by
  simp only [safeLevel]
  split_ifs with hj
  · exact hj
  · exact hL

@[simp] theorem safeLevel_eq_of_lt (L : Nat) (hL : 0 < L) {j : Nat} (hj : j < L) :
    safeLevel L hL j = j := by simp [safeLevel, hj]

/-- The exact finite geometric/arithmetic object still required from the shell construction.
It contains no window probability and no target conclusion.  In particular `near` is the sole
bridge from every corridor contact cube centre to the base face `Bset`; `FaceTarget` then produces
the actual distant target cylinders theoremically via `contactTargetPlan_nonempty`. -/
structure CorridorQueryGeometry
    (S : TargetAwareLattice.BaseScales (d := d) p ((eps / 8) ^ 2))
    (q : unitInterval) (R : Nat) (Sc : Corridor.Scales d) (c : Site d)
    (Dom Fresh Bset : Finset (Site d)) (eps : Real) where
  levels : Nat
  contacts : Nat
  seedCount : Nat
  seedSize : Nat
  levels_pos : 0 < levels
  fits : ∀ j, j < levels → Corridor.Fits Sc j
  local_radius_eq : Sc.M = S.localRadius
  barrier_subset_fresh : ∀ j, j < levels → Corridor.Dbox Sc c j ⊆ Fresh
  near : ∀ j, j < levels →
    ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.Dbox Sc c j),
      ∃ b ∈ Bset, ∀ a,
        |Corridor.cubeCentre Sc c j x a - b a| ≤ (R : Int)
  source_target : ∀ j, j < levels →
    (↑Bset : Set (Site d)) ⊆ ↑(Corridor.Dbox Sc c j)
  select : ∀ j, j < levels →
    ∀ K ⊆ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.Dbox Sc c j),
      contacts ≤ K.card → seedCount ≤ (Corridor.selC Sc c j K).card
  seed_card : ∀ j, j < levels →
    ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.Dbox Sc c j),
      (Corridor.seed Sc c j x).card ≤ seedSize
  level_budget : 1 ≤ (levels : Real) * (eps / 8) *
    (1 - (q : Real)) ^ ((2 * d) * contacts)
  seed_budget : (1 - (q : Real) ^ seedSize) ^ seedCount ≤ eps / 8

/-- The selected genuine target plan at the valid representative of an arbitrary natural level. -/
noncomputable def corridorContactPlanAt
    (S : TargetAwareLattice.BaseScales (d := d) p ((eps / 8) ^ 2))
    (q : unitInterval)
    (R : Nat) (hscale : S.localRadius < R)
    (Sc : Corridor.Scales d) (c : Site d)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (C : CorridorQueryGeometry S q R Sc c Dom Fresh Bset eps)
    (hface : CorrMove.FaceTarget (R : Int) Fresh Bset Tset)
    (j : Nat) (hj : j < C.levels) :
    ContactTargetPlan S Sc c j Dom Fresh Bset Tset :=
  Classical.choice (contactTargetPlan_nonempty S Sc c j R hscale hface (C.near j hj))

/-- The exact translated/oriented finite-cylinder call made at one genuine contact. -/
def corridorWindowCall
    (S : TargetAwareLattice.BaseScales (d := d) p chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset)
    (x : Site d) (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc c j)) : TargetAwareLattice.WindowCall S where
  targetRadius := P.radius x
  centre := Corridor.cubeCentre Sc c j x
  localFace := corridorLocalFace Sc c j x
  targetFace := P.targetFace x
  local_lt_target := P.local_lt_radius x hx

/-- Reading a member of a descended finite call list gives the needed probability of its
literal corridor window at `q`. -/
theorem corridorWindow_lt_prob_of_windowBounds
    (S : TargetAwareLattice.BaseScales (d := d) p chi)
    (Sc : Corridor.Scales d) (c : Site d) (j : Nat)
    {Dom Fresh Bset Tset : Finset (Site d)}
    (P : ContactTargetPlan S Sc c j Dom Fresh Bset Tset)
    (x : Site d) (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc c j)) (q : unitInterval)
    (calls : List (TargetAwareLattice.WindowCall S))
    (hcall : corridorWindowCall S Sc c j P x hx ∈ calls)
    (hvalid : ∀ b ∈ TargetAwareLattice.windowBounds S calls, b.2 < b.1.prob q) :
    1 - 3 * chi < (siteBernoulli (fun _ : Site d => q)).real
      (corridorWindow S Sc c j P x) := by
  have hmem :
      (TargetAwareLattice.windowExperiment S
          (corridorWindowCall S Sc c j P x hx), 1 - 3 * chi) ∈
        TargetAwareLattice.windowBounds S calls := by
    rw [TargetAwareLattice.windowBounds]
    exact List.mem_map.2 ⟨_, hcall, rfl⟩
  have hb := hvalid _ hmem
  simpa only [CylinderExperiment.prob, TargetAwareLattice.windowExperiment_event,
    corridorWindowCall, corridorWindow] using hb

/-- One complete, step-specific query after finite-cylinder descent.  Its base scales live at the
extraction parameter `p`; only the finitely listed calls are assumed valid at the smaller `q`.
Thus this object contains no `BaseScales q` and no infinite post-descent face family. -/
structure DescendedCorridorQuery (p q : unitInterval) (R : Nat)
    (Dom Fresh Bset Tset : Finset (Site d)) (eps : Real) where
  S : TargetAwareLattice.BaseScales (d := d) p ((eps / 8) ^ 2)
  Sc : Corridor.Scales d
  center : Site d
  local_lt_face_radius : S.localRadius < R
  geometry : CorridorQueryGeometry S q R Sc center Dom Fresh Bset eps
  faceTarget : CorrMove.FaceTarget (R : Int) Fresh Bset Tset
  calls : List (TargetAwareLattice.WindowCall S)
  contains : ∀ j, (hj : j < geometry.levels) →
    ∀ x, (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (Corridor.Dbox Sc center j)) →
      corridorWindowCall S Sc center j
        (corridorContactPlanAt S q R local_lt_face_radius Sc center geometry
          faceTarget j hj) x hx ∈ calls
  valid_at_q : ∀ b ∈ TargetAwareLattice.windowBounds S calls, b.2 < b.1.prob q

/-- Validity of a finite call list is satisfiable already at its extraction parameter. -/
theorem windowBounds_valid_satisfiable
    (S : TargetAwareLattice.BaseScales (d := d) p chi)
    (calls : List (TargetAwareLattice.WindowCall S)) :
    ∀ b ∈ TargetAwareLattice.windowBounds S calls, b.2 < b.1.prob p :=
  TargetAwareLattice.windowBounds_valid_at_extraction S calls

/-- The valid representative of each finite corridor shell, assembled with its actual target. -/
noncomputable def corridorFreshLevelAt
    {p q : unitInterval} {R : Nat}
    {Dom Fresh Bset Tset : Finset (Site d)} {eps : Real}
    (W : DescendedCorridorQuery (d := d) p q R Dom Fresh Bset Tset eps)
    (hFreshDom : Fresh ⊆ Dom) (hoDom : (MacroExp.emb 0 : Site d) ∈ Dom)
    (hoFresh : (MacroExp.emb 0 : Site d) ∉ Fresh) (j : Nat) :
    FreshLevel (zdGraph d) Dom Fresh (MacroExp.emb 0) (↑Tset : Set (Site d)) :=
  freshLevelOfCorridor W.S W.Sc W.center
    (safeLevel W.geometry.levels W.geometry.levels_pos j)
    (corridorContactPlanAt W.S q R W.local_lt_face_radius W.Sc W.center W.geometry
      W.faceTarget _ (safeLevel_lt W.geometry.levels W.geometry.levels_pos j))
    (W.geometry.fits _ (safeLevel_lt W.geometry.levels W.geometry.levels_pos j))
    W.geometry.local_radius_eq
    (W.geometry.barrier_subset_fresh _
      (safeLevel_lt W.geometry.levels W.geometry.levels_pos j))
    hFreshDom hoDom hoFresh

@[simp] theorem corridorFreshLevelAt_D
    {p q : unitInterval} {R : Nat}
    {Dom Fresh Bset Tset : Finset (Site d)} {eps : Real}
    (W : DescendedCorridorQuery (d := d) p q R Dom Fresh Bset Tset eps)
    (hFreshDom : Fresh ⊆ Dom) (hoDom : (MacroExp.emb 0 : Site d) ∈ Dom)
    (hoFresh : (MacroExp.emb 0 : Site d) ∉ Fresh) (j : Nat) :
    (corridorFreshLevelAt W hFreshDom hoDom hoFresh j).D =
      Corridor.Dbox W.Sc W.center
        (safeLevel W.geometry.levels W.geometry.levels_pos j) := rfl

/-- A corridor certificate discharges every field of the corrected fresh query datum.  The only
probabilistic fact used here is `BaseScales.window_bound`; all nesting, gating, seed geometry and
the actual far-target inclusion are compiled consequences of the stated certificate. -/
noncomputable def DescendedCorridorQuery.toFreshQueryDatum
    {h : MacroExp.Tr d} {p q : unitInterval} {R : Nat}
    {Dom Fresh Bset Tset : Finset (Site d)} {eps : Real}
    (W : DescendedCorridorQuery (d := d) p q R Dom Fresh Bset Tset eps)
    (hFreshDom : Fresh ⊆ Dom) (hoDom : (MacroExp.emb 0 : Site d) ∈ Dom)
    (hoFresh : (MacroExp.emb 0 : Site d) ∉ Fresh) :
    FreshQueryDatum h q Dom Fresh Bset Tset eps where
  levels := W.geometry.levels
  contacts := W.geometry.contacts
  seedCount := W.geometry.seedCount
  seedSize := W.geometry.seedSize
  levels_pos := W.geometry.levels_pos
  lv := corridorFreshLevelAt W hFreshDom hoDom hoFresh
  nested := by
    intro j hj
    simp only [corridorFreshLevelAt_D]
    rw [safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos (j := j + 1) hj,
      safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos (j := j) (by omega)]
    exact Corridor.Dbox_succ_subset W.Sc W.center j
  gateRel := by
    intro j hj x hxDom hxout y hy hxy
    simp only [corridorFreshLevelAt_D] at hxout hy ⊢
    rw [safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos
      (j := j) (by omega)] at hxout hy
    rw [safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos (j := j + 1) hj]
    exact Corridor.gate W.Sc W.center j hxout hy hxy
  source_target := by
    intro j hj
    simp only [corridorFreshLevelAt_D]
    rw [safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos hj]
    exact W.geometry.source_target j hj
  select := by
    intro j hj K hK hcard
    have hK' : K ⊆ TargetExt.outerBoundary (zdGraph d) Dom
        (Corridor.Dbox W.Sc W.center j) := by
      simpa only [corridorFreshLevelAt_D,
        safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos (j := j) hj] using hK
    change W.geometry.seedCount ≤
      (Corridor.selC W.Sc W.center
        (safeLevel W.geometry.levels W.geometry.levels_pos j) K).card
    rw [safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos (j := j) hj]
    exact W.geometry.select j hj K hK' hcard
  seed_card := by
    intro j hj x hx
    have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
        (Corridor.Dbox W.Sc W.center j) := by
      simpa only [corridorFreshLevelAt_D,
        safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos (j := j) hj] using hx
    change (Corridor.seed W.Sc W.center
      (safeLevel W.geometry.levels W.geometry.levels_pos j) x).card ≤ W.geometry.seedSize
    rw [safeLevel_eq_of_lt W.geometry.levels W.geometry.levels_pos (j := j) hj]
    exact W.geometry.seed_card j hj x hx'
  level_budget := W.geometry.level_budget
  seed_budget := W.geometry.seed_budget
  reliable := by
    intro j hj x hx
    let j' := safeLevel W.geometry.levels W.geometry.levels_pos j
    have hj' : j' < W.geometry.levels := safeLevel_lt _ _ _
    let P := corridorContactPlanAt W.S q R W.local_lt_face_radius W.Sc W.center
      W.geometry W.faceTarget j' hj'
    change 1 - 3 * (eps / 8) ^ 2 ≤
      (siteBernoulli (fun _ : Site d => q)).real
        (corridorWindow W.S W.Sc W.center j' P x)
    exact (corridorWindow_lt_prob_of_windowBounds W.S W.Sc W.center j' P x hx q
      W.calls (W.contains j' hj' x hx) W.valid_at_q).le

/-- Execute one step-specific descended query.  This is the finite-call replacement for assuming
an infinite `FaceInputs` family at the descended parameter. -/
theorem DescendedCorridorQuery.apply
    {h : MacroExp.Tr d} {p q : unitInterval} {R : Nat}
    {Dom Fresh Bset Tset : Finset (Site d)} {eps : Real}
    (W : DescendedCorridorQuery (d := d) p q R Dom Fresh Bset Tset eps)
    (hq0 : 0 < (q : Real)) (hq1 : (q : Real) < 1)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfresh : Disjoint h.inspected Fresh) (hFreshDom : Fresh ⊆ Dom)
    (hoDom : (MacroExp.emb 0 : Site d) ∈ Dom)
    (hoFresh : (MacroExp.emb 0 : Site d) ∉ Fresh)
    (hsrc : 1 - eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Bset : Set (Site d)))) :
    1 - eps < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Tset : Set (Site d))) := by
  exact (W.toFreshQueryDatum hFreshDom hoDom hoFresh).apply hq0 hq1
    heps0 heps1 horigin hfresh hsrc

/-! ## Direct discharge of `CoreRes.FaceInputs` -/

/-- Extraction-scale base data exist at `p`; descent later transports only `W.calls`, never the
infinite `BaseScales.quarter` field, to `q`. -/
theorem baseScales_nonempty_for_faceTolerance (p : unitInterval)
    (htheta : 0 < thetaSite d p) {eps : Real} (heps : 0 < eps) :
    Nonempty (TargetAwareLattice.BaseScales (d := d) p ((eps / 8) ^ 2)) := by
  apply TargetAwareLattice.exists_baseScales_of_thetaSite_pos p htheta
  positivity

/-- The shortest remaining universal shell input.  For each literal `FaceTarget`, it must choose
a fitted nested corridor family whose contacts are within radius `R` of the current base face.
No target hit, window probability, or gluing statement occurs in this interface. -/
abbrev DescendedCorridorQueryFamily (p q : unitInterval) (R : Nat)
    (h : MacroExp.Tr d) (Dom : Finset (Site d)) : Prop :=
  ∀ (Fresh Bset Tset : Finset (Site d)) (eps : Real),
    0 < eps → eps ≤ 1 →
    Disjoint h.inspected Fresh → (MacroExp.emb 0 : Site d) ∉ Fresh → Fresh ⊆ Dom →
    CorrMove.FaceTarget (R : Int) Fresh Bset Tset →
    Bset.Nonempty →
    (1 - eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Bset : Set (Site d)))) →
      Nonempty (DescendedCorridorQuery (d := d) p q R Dom Fresh Bset Tset eps)

/-- The strict source hypothesis in `FaceInputs` rules out the vacuous empty-base instance.
This is why the residual certificate family may soundly require `Bset.Nonempty`. -/
theorem base_nonempty_of_source_prob {h : MacroExp.Tr d} {q : unitInterval}
    {Dom Bset : Finset (Site d)} {eps : Real} (heps1 : eps ≤ 1)
    (hsrc : 1 - eps / 8 < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑Dom : Set (Site d))
        (MacroExp.emb 0) (↑Bset : Set (Site d)))) :
    Bset.Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  subst Bset
  have hempty : connWithinSet (zdGraph d) (↑Dom : Set (Site d))
      (MacroExp.emb 0) (∅ : Set (Site d)) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun omega homega => ?_
    obtain ⟨a, ha, -⟩ := (mem_connWithinSet_iff (zdGraph d) (↑Dom : Set (Site d))
      (MacroExp.emb 0) (∅ : Set (Site d)) omega).1 homega
    exact ha
  rw [Finset.coe_empty, hempty, FRDom.Transcript.prob_eq,
    pinnedProb_emptyEvent] at hsrc
  linarith

/-- The finite shell certificate family supplies the exact face-extension interface consumed by
`CoreAcceptedAssembly`.  This theorem composes the concrete translated windows, the corrected
fresh-support extension, and the transcript/product-law transfer. -/
theorem faceInputs_of_descendedCorridorQueryFamily {p q : unitInterval}
    (hq0 : 0 < (q : Real)) (hq1 : (q : Real) < 1)
    {R : Nat} {h : MacroExp.Tr d} {Dom : Finset (Site d)}
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hoDom : (MacroExp.emb 0 : Site d) ∈ Dom)
    (F : DescendedCorridorQueryFamily (d := d) p q R h Dom) :
    CoreRes.FaceInputs (d := d) R h q Dom := by
  intro Fresh Bset Tset eps heps0 heps1 hfresh hoFresh hFreshDom hface hsrc
  have hBset : Bset.Nonempty := base_nonempty_of_source_prob heps1 hsrc
  let W : DescendedCorridorQuery (d := d) p q R Dom Fresh Bset Tset eps :=
    Classical.choice (F Fresh Bset Tset eps heps0 heps1 hfresh hoFresh hFreshDom
      hface hBset hsrc)
  exact W.apply hq0 hq1 heps0 heps1 horigin hfresh hFreshDom hoDom hoFresh hsrc

end KNAll.Site.CoreFaceTarget

end


#print axioms KNAll.Site.CoreFaceTarget.exists_chosenTarget
#print axioms KNAll.Site.CoreFaceTarget.contactTargetPlan_nonempty
#print axioms KNAll.Site.CoreFaceTarget.freshLevelOfCorridor_reliable
#print axioms KNAll.Site.CoreFaceTarget.DescendedCorridorQuery.toFreshQueryDatum
#print axioms KNAll.Site.CoreFaceTarget.DescendedCorridorQuery.apply
#print axioms KNAll.Site.CoreFaceTarget.corridorWindow_nonempty
#print axioms KNAll.Site.CoreFaceTarget.contactTarget_subset_owner
#print axioms KNAll.Site.CoreFaceTarget.contactOwner_disjoint_inspected
#print axioms KNAll.Site.CoreFaceTarget.base_nonempty_of_source_prob
#print axioms KNAll.Site.CoreFaceTarget.faceInputs_of_descendedCorridorQueryFamily
