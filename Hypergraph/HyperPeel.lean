import Hypergraph.HyperAvoid
import Percolation.Continuity.CSH.PeelTools

/-!
# Avoided peeling for the hyperedge model

The hyperedge analogue of `KN/AvoidedDefs.lean`, `KN/AvoidedPeelTools.lean` and
`KN/AvoidedPeel.lean`.  Everything there is stated for a bond model `w : Sym2 V → [0,1]`; here the
model is a finite hypergraph `H : Hypergraph V E` with arbitrary incidence sets, and the
configuration space is `Set E`.

The functionals are read at the VERTEX cluster `hyperClusterSet H ω {x}` rather than at a cluster of
labels.  In the bond development the conditioned covariance `covD` reads a functional of the edge
cluster and the peeling feeds it `clusterFun`, the vertex functional pulled back along the span; a
vertex record needs no such pullback, and since every monotone functional of the vertex cluster is a
monotone functional of the label cluster, the hierarchy hypothesis carried here is the weaker of the
two.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Continuity
open scoped Classical

/-! ## Reachability in the hyperedge model -/

section Basic

variable {V E : Type*}

@[simp] theorem mem_hyperConn (H : Hypergraph V E) (x y : V) (ω : Set E) :
    ω ∈ hyperConn H x y ↔ (openHyperGraph H ω).Reachable x y := Iff.rfl

theorem mem_hyperClusterSet_singleton (H : Hypergraph V E) (ω : Set E) (x z : V) :
    z ∈ hyperClusterSet H ω ({x} : Set V) ↔ (openHyperGraph H ω).Reachable x z := by
  constructor
  · rintro ⟨u, hu, hr⟩
    rw [mem_singleton_iff] at hu
    exact hu ▸ hr
  · intro h
    exact ⟨x, rfl, h⟩

/-- The avoidance event of a singleton source, unfolded. -/
theorem mem_avoidEvent_singleton (H : Hypergraph V E) (a : V) (Y : Set V) (ω : Set E) :
    ω ∈ avoidEvent H ({a} : Set V) Y ↔ ∀ y ∈ Y, ¬ (openHyperGraph H ω).Reachable a y := by
  rw [mem_avoidEvent, Set.disjoint_left]
  constructor
  · intro h y hy hr
    exact h ((mem_hyperClusterSet_singleton H ω a y).2 hr) hy
  · intro h z hz hzY
    exact h z hzY ((mem_hyperClusterSet_singleton H ω a z).1 hz)

/-- Two joined vertices have the same cluster. -/
theorem hyperClusterSet_singleton_eq_of_reachable (H : Hypergraph V E) {ω : Set E} {x y : V}
    (h : (openHyperGraph H ω).Reachable x y) :
    hyperClusterSet H ω ({x} : Set V) = hyperClusterSet H ω ({y} : Set V) := by
  ext z
  rw [mem_hyperClusterSet_singleton, mem_hyperClusterSet_singleton]
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

/-- With no open label, reachability is equality. -/
theorem eq_of_reachable_empty (H : Hypergraph V E) {x y : V}
    (h : (openHyperGraph H (∅ : Set E)).Reachable x y) : x = y := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ =>
      obtain ⟨-, e, he, -, -⟩ := (openHyperGraph_adj_iff H ∅ _ _).1 hadj
      simp at he

/-- The empty configuration lies in every singleton avoidance event whose target misses the
source. -/
theorem empty_mem_avoidEvent (H : Hypergraph V E) {a : V} {Y : Set V} (ha : a ∉ Y) :
    (∅ : Set E) ∈ avoidEvent H ({a} : Set V) Y := by
  rw [mem_avoidEvent_singleton]
  intro y hy hr
  exact ha ((eq_of_reachable_empty H hr) ▸ hy)

/-- In the empty configuration the cluster of `k` is `{k}`. -/
theorem hyperClusterSet_empty_subset (H : Hypergraph V E) (k : V) :
    hyperClusterSet H (∅ : Set E) ({k} : Set V) ⊆ ({k} : Set V) := by
  intro z hz
  rw [mem_hyperClusterSet_singleton] at hz
  exact (eq_of_reachable_empty H hz).symm

end Basic

/-! ## The first-in-rank patterns

The two combinatorial facts about the patterns `P_a = C a ∩ ⋂_{r a' < r a} (C a')ᶜ` used by the
peeling are statements about an arbitrary family of sets, so they are proved once here rather than
for the connection events specifically.
-/

section FirstRank

variable {Ω ι : Type*} [DecidableEq ι]

/-- The patterns are pairwise disjoint when the rank is injective. -/
theorem firstRank_disjoint' (C : ι → Set Ω) (T : Finset ι) (r : ι → ℕ) (hr : Set.InjOn r ↑T) :
    Set.PairwiseDisjoint (↑T : Set ι)
      (fun a => (C a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (C a')ᶜ : Set Ω)) := by
  intro a ha b hb hne
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  rcases lt_or_gt_of_ne (fun h => hne (hr ha hb h)) with hlt | hlt
  · have hna : ω ∈ (C a)ᶜ := by
      have h := h2.2
      rw [Set.mem_iInter₂] at h
      exact h a (Finset.mem_filter.2 ⟨ha, hlt⟩)
    exact hna h1.1
  · have hnb : ω ∈ (C b)ᶜ := by
      have h := h1.2
      rw [Set.mem_iInter₂] at h
      exact h b (Finset.mem_filter.2 ⟨hb, hlt⟩)
    exact hnb h2.1

/-- The patterns cover the union: the rank attains a minimum on the attached indices. -/
theorem firstRank_cover' (C : ι → Set Ω) (T : Finset ι) (r : ι → ℕ) :
    (⋃ a ∈ T, (C a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (C a')ᶜ : Set Ω)) =
      ⋃ a ∈ T, C a := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
  constructor
  · rintro ⟨a, ha, h1, -⟩
    exact ⟨a, ha, h1⟩
  · rintro ⟨a, ha, h1⟩
    have hne : (T.filter fun a' => ω ∈ C a').Nonempty := ⟨a, Finset.mem_filter.2 ⟨ha, h1⟩⟩
    obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image _ r hne
    rw [Finset.mem_filter] at ha₀
    refine ⟨a₀, ha₀.1, ha₀.2, ?_⟩
    rw [Set.mem_iInter₂]
    intro a' ha'
    rw [Finset.mem_filter] at ha'
    intro hω
    exact absurd ha'.2 (not_lt.2 (hmin a' (Finset.mem_filter.2 ⟨ha'.1, hω⟩)))

end FirstRank

/-! ## Definitions -/

section Defs

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The conditional relay mean `m_a^Y = E[F(C_a); a ↮ Y] / P(a ↮ Y)`. -/
def condMeanY (H : Hypergraph V E) (Y : Set V) (F : Set V → ℝ) (a : V) : ℝ :=
  avoidIntegral H ({a} : Set V) Y F / (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y)

/-- The decoy constant `u ↦ P(d ↮ A, d ↔ u) / P(d ↮ A)`. -/
def avoidConst (H : Hypergraph V E) (d : V) (A : Set V) : V → ℝ := fun u =>
  (prodBernoulli H.prob).real (avoidEvent H ({d} : Set V) A ∩ hyperConn H d u) /
    (prodBernoulli H.prob).real (avoidEvent H ({d} : Set V) A)

/-- The decoy/constant list: the avoided set grows along the list. -/
def decoyList (H : Hypergraph V E) : Set V → List V → List (V × (V → ℝ))
  | _, [] => []
  | A, d :: ds => (d, avoidConst H d A) :: decoyList H (insert d A) ds

/-- The observer constant `P(o ↔ v, v ↮ A) / P(v ↮ A)`. -/
def obsConst (H : Hypergraph V E) (o v : V) (A : Set V) : ℝ :=
  (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) A ∩ hyperConn H o v) /
    (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) A)

/-- The conditioned covariance function, denominator-free, read at the vertex cluster of the
owner. -/
def covD (H : Hypergraph V E) (x : V) (Y : Set V) (f : Set V → ℝ) (u : V) : ℝ :=
  (prodBernoulli H.prob).real (avoidEvent H ({x} : Set V) Y) *
      (∫ ω in avoidEvent H ({x} : Set V) Y ∩ hyperConn H x u,
        f (hyperClusterSet H ω ({x} : Set V)) ∂(prodBernoulli H.prob)) -
    avoidIntegral H ({x} : Set V) Y f *
      (prodBernoulli H.prob).real (avoidEvent H ({x} : Set V) Y ∩ hyperConn H x u)

/-- The CSH margin of the datum (owner `x`, avoided set `Y`, decoys `D`, observers `o, v`). -/
def cshMargin (H : Hypergraph V E) (x : V) (Y : Set V) (D : List V) (o v : V)
    (f : Set V → ℝ) : ℝ :=
  CSH.cshMarg (decoyList H (insert x Y) D) (obsConst H o v (insert x Y ∪ {d | d ∈ D})) o v
    (covD H x Y f)

/-- The conditioned slack hierarchy statement for the hyperedge model. -/
def CSHHolds (H : Hypergraph V E) (x : V) (Y : Set V) (D : List V) (o v : V) : Prop :=
  ∀ f : Set V → ℝ, Monotone f → 0 ≤ cshMargin H x Y D o v f

/-- The avoided surplus `Sur^Y_u(T)`. -/
def surplusY (H : Hypergraph V E) (Y : Set V) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ)
    (u : V) : ℝ :=
  (∫ ω in avoidEvent H ({u} : Set V) Y ∩ ⋃ a ∈ T, hyperConn H u a,
      F (hyperClusterSet H ω ({u} : Set V)) ∂(prodBernoulli H.prob)) -
    ∑ a ∈ T, (prodBernoulli H.prob).real
        (avoidEvent H ({u} : Set V) Y ∩
          (hyperConn H u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (hyperConn H u a')ᶜ)) *
      condMeanY H Y F a

/-- The avoided surplus-transfer margin with decoys. -/
def surplusMarginY (H : Hypergraph V E) (Y : Set V) (T : Finset V) (r : V → ℕ) (D : List V)
    (o v : V) (F : Set V → ℝ) : ℝ :=
  CSH.cshMarg (decoyList H (Y ∪ ↑T) D) (obsConst H o v (Y ∪ ↑T ∪ {d | d ∈ D})) o v
    (surplusY H Y T r F)

/-- The surplus of an observer over its first relay, with no base avoided set. -/
def surplus (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (u : V) : ℝ :=
  (∫ ω in ⋃ a ∈ T, hyperConn H u a,
      F (hyperClusterSet H ω ({u} : Set V)) ∂(prodBernoulli H.prob)) -
    ∑ a ∈ T, (prodBernoulli H.prob).real
        (hyperConn H u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (hyperConn H u a')ᶜ) *
      ∫ ω, F (hyperClusterSet H ω ({a} : Set V)) ∂(prodBernoulli H.prob)

/-- The "not isolated" functional of the vertex cluster of `k`. -/
def psiIso (k : V) : Set V → ℝ := fun C => if C ⊆ ({k} : Set V) then 0 else 1

end Defs


/-! ## Elementary consequences of the definitions -/

section Elementary

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The decoys of `decoyList H A D` are the members of `D`. -/
theorem mem_decoyList (H : Hypergraph V E) :
    ∀ (A : Set V) (D : List V) (dc : V × (V → ℝ)), dc ∈ decoyList H A D → dc.1 ∈ D
  | _, [], dc, h => by simp [decoyList] at h
  | A, d :: D, dc, h => by
    simp only [decoyList, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_decoyList H (insert d A) D dc h)

/-- `Marg_L` is compatible with subtraction. -/
theorem cshMarg_sub' {W : Type*} (L : List (W × (W → ℝ))) (p : ℝ) (o v : W) (f g : W → ℝ) :
    CSH.cshMarg L p o v (f - g) = CSH.cshMarg L p o v f - CSH.cshMarg L p o v g := by
  simp only [CSH.cshMarg, CSH.slForm_sub, Pi.sub_apply]
  ring

/-- `Ψ_iso` is monotone. -/
theorem psiIso_mono (k : V) : Monotone (psiIso k) := by
  intro C C' h
  unfold psiIso
  by_cases hC : C ⊆ ({k} : Set V)
  · rw [if_pos hC]
    split_ifs <;> norm_num
  · have hC' : ¬ C' ⊆ ({k} : Set V) := fun h' => hC (h.trans h')
    rw [if_neg hC, if_neg hC']

/-- On `{k ↔ u}` with `u ≠ k` the cluster of `k` is not `{k}`, so `Ψ_iso(C_k) = 1`. -/
theorem psiIso_eq_one_of_reachable (H : Hypergraph V E) {ω : Set E} {k u : V} (huk : u ≠ k)
    (h : (openHyperGraph H ω).Reachable k u) :
    psiIso k (hyperClusterSet H ω ({k} : Set V)) = 1 := by
  unfold psiIso
  rw [if_neg]
  intro hsub
  exact huk (hsub ((mem_hyperClusterSet_singleton H ω k u).2 h))

/-- With no decoys the margin is `Sur^Y_o(T) − p · Sur^Y_v(T)`. -/
theorem surplusMarginY_nil (H : Hypergraph V E) (Y : Set V) (T : Finset V) (r : V → ℕ) (o v : V)
    (F : Set V → ℝ) :
    surplusMarginY H Y T r [] o v F =
      surplusY H Y T r F o -
        (prodBernoulli H.prob).real
            (avoidEvent H ({v} : Set V) (Y ∪ ↑T) ∩ hyperConn H o v) /
            (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ ↑T)) *
          surplusY H Y T r F v := by
  simp only [surplusMarginY, decoyList, CSH.cshMarg_nil, obsConst, List.not_mem_nil, setOf_false,
    union_empty]

/-- **(S5) with avoided set, product form.** -/
theorem surplusTransferY_of_surplusMarginY_nil (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (r : V → ℕ) (o v : V) (F : Set V → ℝ)
    (hpos : 0 < (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ ↑T)))
    (h : 0 ≤ surplusMarginY H Y T r [] o v F) :
    (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ ↑T) ∩ hyperConn H o v) *
        surplusY H Y T r F v ≤
      (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ ↑T)) *
        surplusY H Y T r F o := by
  rw [surplusMarginY_nil] at h
  set M := (prodBernoulli H.prob).real (avoidEvent H ({v} : Set V) (Y ∪ ↑T)) with hM
  set Ev := (prodBernoulli H.prob).real
    (avoidEvent H ({v} : Set V) (Y ∪ ↑T) ∩ hyperConn H o v) with hEv
  have h2 : 0 ≤ M * (surplusY H Y T r F o - Ev / M * surplusY H Y T r F v) :=
    mul_nonneg hpos.le h
  have h3 : M * (surplusY H Y T r F o - Ev / M * surplusY H Y T r F v) =
      M * surplusY H Y T r F o - Ev * surplusY H Y T r F v := by
    field_simp
  linarith [h2, h3]

/-- With `Y = ∅` the avoided surplus is the plain surplus. -/
theorem surplusY_empty (H : Hypergraph V E) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (u : V) :
    surplusY H ∅ T r F u = surplus H T r F u := by
  simp only [surplusY, surplus, condMeanY, avoidIntegral, avoidEvent_empty, Set.univ_inter,
    Measure.restrict_univ, probReal_univ, div_one]

end Elementary


/-! ## The peeling tools -/

section Tools

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Filtering an erased finset by a predicate the erased element fails. -/
theorem filter_erase_of_not {ι : Type*} [DecidableEq ι] {T : Finset ι} {k : ι} {p : ι → Prop}
    [DecidablePred p] (hk : ¬ p k) : (T.erase k).filter p = T.filter p := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨-, ha⟩, hp⟩
    exact ⟨ha, hp⟩
  · rintro ⟨ha, hp⟩
    exact ⟨⟨fun h => hk (h ▸ hp), ha⟩, hp⟩

/-- `∫_{a ↮ Y} F(C_a) = m_a^Y · P(a ↮ Y)`, also when the denominator vanishes. -/
theorem setIntegral_eq_condMeanY_mul (H : Hypergraph V E) (Y : Set V) (F : Set V → ℝ) (a : V) :
    avoidIntegral H ({a} : Set V) Y F =
      condMeanY H Y F a * (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y) := by
  unfold condMeanY
  by_cases h0 : (prodBernoulli H.prob).real (avoidEvent H ({a} : Set V) Y) = 0
  · rw [h0, mul_zero]
    have hz : (prodBernoulli H.prob) (avoidEvent H ({a} : Set V) Y) = 0 := by
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h0
    rw [avoidIntegral, Measure.restrict_eq_zero.2 hz, integral_zero_measure]
  · rw [div_mul_cancel₀ _ h0]

/-- The avoided first-in-rank patterns of `T` have total measure `P(u ↮ Y, u ↔ T)`. -/
theorem sum_measureReal_avoid_firstRank (H : Hypergraph V E) (Y : Set V) (T : Finset V)
    (r : V → ℕ) (u : V) (hr : Set.InjOn r ↑T) :
    ∑ a ∈ T, (prodBernoulli H.prob).real
        (avoidEvent H ({u} : Set V) Y ∩
          (hyperConn H u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (hyperConn H u a')ᶜ)) =
      (prodBernoulli H.prob).real
        (avoidEvent H ({u} : Set V) Y ∩ ⋃ a ∈ T, hyperConn H u a) := by
  have hdisj : Set.PairwiseDisjoint (↑T : Set V) (fun a =>
      (avoidEvent H ({u} : Set V) Y ∩
        (hyperConn H u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (hyperConn H u a')ᶜ))) := by
    intro a ha b hb hab
    exact (firstRank_disjoint' (hyperConn H u) T r hr ha hb hab).mono
      inter_subset_right inter_subset_right
  rw [← firstRank_cover' (hyperConn H u) T r, inter_iUnion₂,
    measureReal_biUnion_finset hdisj (fun a _ => measurableSet_of_fintype _)
      (fun _ _ => measure_ne_top _ _)]

/-- **Lemma P with avoided set**: peeling the rank-maximal relay `k`. -/
theorem surplusY_erase_add (H : Hypergraph V E) (Y : Set V) (T : Finset V) (r : V → ℕ)
    (F : Set V → ℝ) {k : V} (hkT : k ∈ T) (hlt : ∀ a ∈ T.erase k, r a < r k) (u : V) :
    surplusY H Y T r F u = surplusY H Y (T.erase k) r F u +
      ((∫ ω in avoidEvent H ({k} : Set V) (Y ∪ ↑(T.erase k)) ∩ hyperConn H k u,
          F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) -
        (prodBernoulli H.prob).real
            (avoidEvent H ({k} : Set V) (Y ∪ ↑(T.erase k)) ∩ hyperConn H k u) *
          condMeanY H Y F k) := by
  set μ := prodBernoulli H.prob with hμ
  set T' := T.erase k with hT'
  have hint : ∀ (g : Set E → ℝ) (S : Set (Set E)), IntegrableOn g S μ :=
    fun g S => (integrable_of_fintype g).integrableOn
  set f₀ : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({u} : Set V)) with hf₀
  set fk : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({k} : Set V)) with hfk
  set Av : Set (Set E) := avoidEvent H ({u} : Set V) Y with hAv
  set UT : Set (Set E) := ⋃ a ∈ T', hyperConn H u a with hUT
  set Ok : Set (Set E) := hyperConn H u k with hOk
  set Dk : Set (Set E) := avoidEvent H ({k} : Set V) (Y ∪ (↑T' : Set V)) with hDk
  have hfiltT : ∀ a ∈ T', T.filter (fun a' => r a' < r a) = T'.filter (fun a' => r a' < r a) := by
    intro a ha
    rw [hT', filter_erase_of_not]
    exact fun h => lt_asymm h (hlt a ha)
  have hfiltk : T.filter (fun a' => r a' < r k) = T' := by
    ext a
    simp only [Finset.mem_filter, hT', Finset.mem_erase]
    constructor
    · rintro ⟨ha, h⟩
      exact ⟨fun hak => lt_irrefl _ (hak ▸ h), ha⟩
    · rintro ⟨hak, ha⟩
      exact ⟨ha, hlt a (Finset.mem_erase.2 ⟨hak, ha⟩)⟩
  have hPk : (Av ∩ (hyperConn H u k ∩
        ⋂ a' ∈ T.filter (fun a' => r a' < r k), (hyperConn H u a')ᶜ)) = Dk ∩ hyperConn H k u := by
    rw [hfiltk]
    ext ω
    simp only [hAv, hDk, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, mem_hyperConn,
      mem_avoidEvent_singleton, Finset.mem_coe, Set.mem_union]
    constructor
    · rintro ⟨hY, hk', h⟩
      refine ⟨fun a ha hka => ?_, hk'.symm⟩
      rcases ha with ha | ha
      · exact hY a ha (hk'.trans hka)
      · exact h a ha (hk'.trans hka)
    · rintro ⟨h, hk'⟩
      exact ⟨fun y hy hoy => h y (Or.inl hy) (hk'.trans hoy), hk'.symm,
        fun a ha hoa => h a (Or.inr ha) (hk'.trans hoa)⟩
  have hsumT : ∑ a ∈ T, μ.real (Av ∩ (hyperConn H u a ∩
        ⋂ a' ∈ T.filter (fun a' => r a' < r a), (hyperConn H u a')ᶜ)) * condMeanY H Y F a =
      (∑ a ∈ T', μ.real (Av ∩ (hyperConn H u a ∩
        ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (hyperConn H u a')ᶜ)) * condMeanY H Y F a) +
        μ.real (Dk ∩ hyperConn H k u) * condMeanY H Y F k := by
    rw [← Finset.add_sum_erase T _ hkT, hPk, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hfiltT a ha]
  have hUA : (Av ∩ ⋃ a ∈ T, hyperConn H u a) = (Av ∩ UT) ∪ (Av ∩ Ok) := by
    ext ω
    simp only [hUT, hOk, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_union, exists_prop, hT',
      Finset.mem_erase]
    constructor
    · rintro ⟨hA, a, ha, h⟩
      by_cases hak : a = k
      · exact Or.inr ⟨hA, hak ▸ h⟩
      · exact Or.inl ⟨hA, a, ⟨hak, ha⟩, h⟩
    · rintro (⟨hA, a, ⟨-, ha⟩, h⟩ | ⟨hA, h⟩)
      · exact ⟨hA, a, ha, h⟩
      · exact ⟨hA, k, hkT, h⟩
  have h0k : ∀ ω ∈ Dk ∩ hyperConn H k u, f₀ ω = fk ω := by
    intro ω hω
    simp only [hf₀, hfk]
    rw [hyperClusterSet_singleton_eq_of_reachable H (hω.2 : (openHyperGraph H ω).Reachable k u)]
  have hdiff : ((Av ∩ UT) ∪ (Av ∩ Ok)) \ (Av ∩ UT) = Dk ∩ hyperConn H k u := by
    ext ω
    simp only [hUT, hOk, hDk, hAv, Set.mem_sdiff, Set.mem_union, Set.mem_iUnion,
      Set.mem_inter_iff, exists_prop, not_exists, not_and, mem_hyperConn,
      mem_avoidEvent_singleton, Finset.mem_coe]
    constructor
    · rintro ⟨⟨hA, h⟩ | ⟨hA, h⟩, hno⟩
      · obtain ⟨a, ha, h'⟩ := h
        exact absurd h' (hno hA a ha)
      · refine ⟨fun a ha hka => ?_, h.symm⟩
        rcases ha with ha | ha
        · exact hA a ha (h.trans hka)
        · exact hno hA a ha (h.trans hka)
    · rintro ⟨hd, hk'⟩
      exact ⟨Or.inr ⟨fun y hy hoy => hd y (Or.inl hy) (hk'.trans hoy), hk'.symm⟩,
        fun _ a ha hoa => hd a (Or.inr ha) (hk'.trans hoa)⟩
  have hsplit : ∫ ω in (Av ∩ UT) ∪ (Av ∩ Ok), f₀ ω ∂μ =
      (∫ ω in Av ∩ UT, f₀ ω ∂μ) + ∫ ω in Dk ∩ hyperConn H k u, fk ω ∂μ := by
    rw [← integral_inter_add_sdiff (measurableSet_of_fintype (Av ∩ UT)) (hint f₀ _),
      inter_eq_right.2 subset_union_left, hdiff,
      setIntegral_congr_fun (measurableSet_of_fintype _) fun ω hω => h0k ω hω]
  unfold surplusY
  rw [hsumT, hUA, hsplit]
  ring

/-- **Lemma κ with avoided set**: `κ_k = m_k^Y · P(D_k) − ∫_{D_k} F(C_k) ≤ Sur^Y_k(T')`. -/
theorem kappaY_le_surplusY (H : Hypergraph V E) (Y : Set V) (T' : Finset V) (r : V → ℕ)
    (F : Set V → ℝ) (k : V) (hrT : Set.InjOn r ↑T')
    (hmle : ∀ a ∈ T', condMeanY H Y F a ≤ condMeanY H Y F k) :
    condMeanY H Y F k *
        (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) (Y ∪ (↑T' : Set V))) -
      (∫ ω in avoidEvent H ({k} : Set V) (Y ∪ (↑T' : Set V)),
        F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) ≤
      surplusY H Y T' r F k := by
  unfold surplusY
  set μ := prodBernoulli H.prob with hμ
  have hn := fun (S : Set (Set E)) => (measureReal_nonneg : 0 ≤ μ.real S)
  set fk : Set E → ℝ := fun ω => F (hyperClusterSet H ω ({k} : Set V)) with hfk
  set mk : ℝ := condMeanY H Y F k with hmk
  set Ak : Set (Set E) := avoidEvent H ({k} : Set V) Y with hAk
  set Dk : Set (Set E) := avoidEvent H ({k} : Set V) (Y ∪ (↑T' : Set V)) with hDk
  set Wk : Set (Set E) := ⋃ a ∈ T', hyperConn H k a with hWk
  have hDW : Dk = Ak \ Wk := by
    ext ω
    simp only [hDk, hAk, hWk, Set.mem_sdiff, Set.mem_iUnion, mem_hyperConn, not_exists,
      exists_prop, not_and, mem_avoidEvent_singleton, Set.mem_union, Finset.mem_coe]
    constructor
    · intro h
      exact ⟨fun y hy => h y (Or.inl hy), fun a ha => h a (Or.inr ha)⟩
    · rintro ⟨h1, h2⟩ a ha
      rcases ha with ha | ha
      · exact h1 a ha
      · exact h2 a ha
  have hAint : ∫ ω in Ak, fk ω ∂μ = (∫ ω in Ak ∩ Wk, fk ω ∂μ) + ∫ ω in Dk, fk ω ∂μ := by
    rw [hDW]
    exact (integral_inter_add_sdiff (measurableSet_of_fintype Wk)
      ((integrable_of_fintype fk).integrableOn)).symm
  have hAμ : μ.real Ak = μ.real (Ak ∩ Wk) + μ.real Dk := by
    rw [hDW]
    exact (measureReal_inter_add_sdiff (s := Ak) (h := measure_ne_top _ _)
      (measurableSet_of_fintype Wk)).symm
  have hmA : ∫ ω in Ak, fk ω ∂μ = mk * μ.real Ak := setIntegral_eq_condMeanY_mul H Y F k
  rw [hAμ, mul_add] at hmA
  have hWsum : ∑ a ∈ T', μ.real (Ak ∩ (hyperConn H k a ∩
      ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (hyperConn H k a')ᶜ)) = μ.real (Ak ∩ Wk) :=
    sum_measureReal_avoid_firstRank H Y T' r k hrT
  have hsum : ∑ a ∈ T', μ.real (Ak ∩ (hyperConn H k a ∩
        ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (hyperConn H k a')ᶜ)) * condMeanY H Y F a ≤
      mk * μ.real (Ak ∩ Wk) := by
    have hle : ∑ a ∈ T', μ.real (Ak ∩ (hyperConn H k a ∩
          ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (hyperConn H k a')ᶜ)) * condMeanY H Y F a ≤
        ∑ a ∈ T', μ.real (Ak ∩ (hyperConn H k a ∩
          ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (hyperConn H k a')ᶜ)) * mk :=
      Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hmle a ha) (hn _)
    rw [← Finset.sum_mul, hWsum] at hle
    linarith
  change mk * μ.real Dk - ∫ ω in Dk, fk ω ∂μ ≤ (∫ ω in Ak ∩ Wk, fk ω ∂μ) -
    ∑ a ∈ T', μ.real (Ak ∩ (hyperConn H k a ∩
      ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (hyperConn H k a')ᶜ)) * condMeanY H Y F a
  linarith [hsum, hAint, hAμ, hmA]

/-- **The top-relay term against `covD`**, arbitrary avoided set `A` and arbitrary constant `m`. -/
theorem covD_topTerm_eq (H : Hypergraph V E) (A : Set V) (F : Set V → ℝ) (k u : V) (m : ℝ) :
    (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) A) *
        ((∫ ω in avoidEvent H ({k} : Set V) A ∩ hyperConn H k u,
            F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) -
          (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) A ∩ hyperConn H k u) * m) =
      covD H k A F u -
        (m * (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) A) -
          ∫ ω in avoidEvent H ({k} : Set V) A,
            F (hyperClusterSet H ω ({k} : Set V)) ∂(prodBernoulli H.prob)) *
          (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) A ∩ hyperConn H k u) := by
  unfold covD avoidIntegral
  ring

/-- **The `Ψ_iso` identity**: for `u ≠ k`, `covD(k; A; Ψ_iso)(u) = P(D ∩ {C_k = {k}}) · P(D ∩ {k↔u})`. -/
theorem covD_psiIso (H : Hypergraph V E) (A : Set V) (k u : V) (huk : u ≠ k) :
    covD H k A (psiIso k) u =
      (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) A ∩
          {ω : Set E | hyperClusterSet H ω ({k} : Set V) ⊆ ({k} : Set V)}) *
        (prodBernoulli H.prob).real (avoidEvent H ({k} : Set V) A ∩ hyperConn H k u) := by
  set μ := prodBernoulli H.prob with hμ
  set Dk : Set (Set E) := avoidEvent H ({k} : Set V) A with hDk
  set Iso : Set (Set E) :=
    {ω : Set E | hyperClusterSet H ω ({k} : Set V) ⊆ ({k} : Set V)} with hIso
  have h1 : ∫ ω in Dk ∩ hyperConn H k u, psiIso k (hyperClusterSet H ω ({k} : Set V)) ∂μ =
      μ.real (Dk ∩ hyperConn H k u) := by
    rw [setIntegral_congr_fun (measurableSet_of_fintype _)
      (fun ω hω => psiIso_eq_one_of_reachable H huk hω.2), setIntegral_const, smul_eq_mul,
      mul_one]
  have h2 : ∫ ω in Dk, psiIso k (hyperClusterSet H ω ({k} : Set V)) ∂μ =
      μ.real Dk - μ.real (Dk ∩ Iso) := by
    have hsplit := (integral_inter_add_sdiff (measurableSet_of_fintype Iso)
      ((integrable_of_fintype (μ := μ)
        (fun ω => psiIso k (hyperClusterSet H ω ({k} : Set V)))).integrableOn (s := Dk))).symm
    rw [hsplit]
    have ha : ∫ ω in Dk ∩ Iso, psiIso k (hyperClusterSet H ω ({k} : Set V)) ∂μ = 0 := by
      rw [setIntegral_congr_fun (measurableSet_of_fintype _) (fun ω hω => by
        show psiIso k (hyperClusterSet H ω ({k} : Set V)) = (0 : ℝ)
        unfold psiIso
        rw [if_pos (show hyperClusterSet H ω ({k} : Set V) ⊆ ({k} : Set V) from hω.2)])]
      simp
    have hb : ∫ ω in Dk \ Iso, psiIso k (hyperClusterSet H ω ({k} : Set V)) ∂μ =
        μ.real (Dk \ Iso) := by
      rw [setIntegral_congr_fun (measurableSet_of_fintype _) (fun ω hω => by
        show psiIso k (hyperClusterSet H ω ({k} : Set V)) = (1 : ℝ)
        unfold psiIso
        rw [if_neg (show ¬ (hyperClusterSet H ω ({k} : Set V) ⊆ ({k} : Set V)) from hω.2)]),
        setIntegral_const, smul_eq_mul, mul_one]
    rw [ha, hb, zero_add]
    have hms := measureReal_inter_add_sdiff (μ := μ) (s := Dk) (h := measure_ne_top _ _)
      (measurableSet_of_fintype Iso)
    linarith
  unfold covD avoidIntegral
  rw [← hDk, h1, h2]
  ring

end Tools


/-! ## (S5D) with a base avoided set, from the hierarchy -/

section Peel

variable {V E : Type*} [Fintype V] [Fintype E]

/-- **(S5D) with avoided set `Y` from the hierarchy, for the hyperedge model.**  For nondegenerate
label probabilities and observers `o ≠ v` outside `Y`, IF the conditioned slack hierarchy holds for
every owner, avoided set and decoy list with the named vertices distinct, THEN the avoided surplus
margin is nonnegative for every relay set `T` disjoint from `Y`, every `m^Y`-compatible injective
rank, every decoy list `D` outside `Y` and every monotone `F`. -/
theorem surplusMarginY_nonneg_of_csh (H : Hypergraph V E)
    (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1) (Y : Set V) (o v : V) (hoY : o ∉ Y) (hvY : v ∉ Y)
    (hCSH : ∀ (x : V) (Y' : Set V) (D : List V),
      x ∉ Y' → o ≠ x → v ≠ x → o ∉ Y' → v ∉ Y' → D.Nodup →
      (∀ d ∈ D, d ≠ x ∧ d ∉ Y' ∧ d ≠ o ∧ d ≠ v) → CSHHolds H x Y' D o v) :
    ∀ (T : Finset V) (r : V → ℕ) (D : List V) (F : Set V → ℝ),
      (∀ S S' : Set V, S ⊆ S' → F S ≤ F S') → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' → condMeanY H Y F a ≤ condMeanY H Y F a') →
      (∀ a ∈ T, a ∉ Y) → o ∉ T → v ∉ T → D.Nodup →
      (∀ d ∈ D, d ∉ T ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      0 ≤ surplusMarginY H Y T r D o v F := by
  have main : ∀ (N : ℕ) (T : Finset V) (r : V → ℕ) (D : List V) (F : Set V → ℝ), T.card = N →
      (∀ S S' : Set V, S ⊆ S' → F S ≤ F S') → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' → condMeanY H Y F a ≤ condMeanY H Y F a') →
      (∀ a ∈ T, a ∉ Y) → o ∉ T → v ∉ T → D.Nodup →
      (∀ d ∈ D, d ∉ T ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      0 ≤ surplusMarginY H Y T r D o v F := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro T r D F hN hF hr hcompat hTY hoT hvT hD hDT
    set μ := prodBernoulli H.prob with hμ
    rcases T.eq_empty_or_nonempty with hT0 | hne
    · subst hT0
      have h0 : surplusY H Y (∅ : Finset V) r F = fun _ => 0 := by
        funext u
        simp [surplusY]
      rw [surplusMarginY, h0]
      have hz := CSH.slForm_zero (decoyList H (Y ∪ (↑(∅ : Finset V) : Set V)) D)
      simp only [CSH.cshMarg]
      rw [show (fun _ : V => (0 : ℝ)) = (0 : V → ℝ) from rfl, hz]
      simp
    obtain ⟨k, hkT, hkmax⟩ := Finset.exists_max_image T r hne
    set T' : Finset V := T.erase k with hT'
    have hTcard : T'.card < N := by
      have hpos : 0 < T.card := Finset.card_pos.2 hne
      rw [hT', Finset.card_erase_of_mem hkT]
      omega
    have hT'T : ∀ a ∈ T', a ∈ T := fun a ha => Finset.mem_of_mem_erase ha
    have hkT' : k ∉ T' := Finset.notMem_erase k T
    have hlt : ∀ a ∈ T', r a < r k := by
      intro a ha
      rcases (hkmax a (hT'T a ha)).lt_or_eq with h | h
      · exact h
      · exact absurd (hr (hT'T a ha) hkT h) (Finset.ne_of_mem_erase ha)
    have hrT' : Set.InjOn r ↑T' := hr.mono (by intro a ha; exact hT'T a ha)
    have hcompatT' : ∀ a ∈ T', ∀ a' ∈ T', r a < r a' → condMeanY H Y F a ≤ condMeanY H Y F a' :=
      fun a ha a' ha' h => hcompat a (hT'T a ha) a' (hT'T a' ha') h
    have hmle : ∀ a ∈ T', condMeanY H Y F a ≤ condMeanY H Y F k :=
      fun a ha => hcompat a (hT'T a ha) k hkT (hlt a ha)
    have hkY : k ∉ Y := hTY k hkT
    have hko : o ≠ k := fun h => hoT (h ▸ hkT)
    have hkv : v ≠ k := fun h => hvT (h ▸ hkT)
    have hkD : k ∉ D := fun h => (hDT k h).1 hkT
    set A : Set V := Y ∪ (↑T' : Set V) with hA
    have hkA : k ∉ A := by
      rw [hA, Set.mem_union, not_or]
      exact ⟨hkY, fun h => hkT' (Finset.mem_coe.1 h)⟩
    have hoA : o ∉ A := by
      rw [hA, Set.mem_union, not_or]
      exact ⟨hoY, fun h => hoT (hT'T o (Finset.mem_coe.1 h))⟩
    have hvA : v ∉ A := by
      rw [hA, Set.mem_union, not_or]
      exact ⟨hvY, fun h => hvT (hT'T v (Finset.mem_coe.1 h))⟩
    set Dk : Set (Set E) := avoidEvent H ({k} : Set V) A with hDk
    set Iso : Set (Set E) :=
      {ω : Set E | hyperClusterSet H ω ({k} : Set V) ⊆ ({k} : Set V)} with hIso
    set mk : ℝ := condMeanY H Y F k with hmk
    set κ : ℝ := mk * μ.real Dk -
      ∫ ω in Dk, F (hyperClusterSet H ω ({k} : Set V)) ∂μ with hκ
    set L := decoyList H (Y ∪ (↑T : Set V)) D with hL
    set pobs : ℝ := obsConst H o v (Y ∪ (↑T : Set V) ∪ {d | d ∈ D}) with hpobs
    set ck : V → ℝ := avoidConst H k A with hck
    set Tk : V → ℝ := fun u =>
      (∫ ω in Dk ∩ hyperConn H k u, F (hyperClusterSet H ω ({k} : Set V)) ∂μ) -
        μ.real (Dk ∩ hyperConn H k u) * mk with hTk
    have hempty_Dk : (∅ : Set E) ∈ Dk := empty_mem_avoidEvent H hkA
    have hDkpos : 0 < μ.real Dk := prodBernoulli_real_pos_of_nonempty hp ⟨∅, hempty_Dk⟩
    have hisopos : 0 < μ.real (Dk ∩ Iso) :=
      prodBernoulli_real_pos_of_nonempty hp ⟨∅, hempty_Dk, hyperClusterSet_empty_subset H k⟩
    have hins : insert k A = Y ∪ (↑T : Set V) := by
      rw [hA, hT', Finset.coe_erase, ← Set.union_insert, Set.insert_sdiff_singleton,
        Set.insert_eq_of_mem (Finset.mem_coe.2 hkT)]
    have hset2 : A ∪ {d | d ∈ k :: D} = Y ∪ (↑T : Set V) ∪ {d | d ∈ D} := by
      ext a
      simp only [hA, Set.mem_union, Finset.mem_coe, hT', Finset.mem_erase, Set.mem_setOf_eq,
        List.mem_cons]
      constructor
      · rintro ((ha | ⟨-, ha⟩) | rfl | ha)
        · exact Or.inl (Or.inl ha)
        · exact Or.inl (Or.inr ha)
        · exact Or.inl (Or.inr hkT)
        · exact Or.inr ha
      · rintro ((ha | ha) | ha)
        · exact Or.inl (Or.inl ha)
        · by_cases hak : a = k
          · exact Or.inr (Or.inl hak)
          · exact Or.inl (Or.inr ⟨hak, ha⟩)
        · exact Or.inr (Or.inr ha)
    have hcshMargin : ∀ f : Set V → ℝ,
        cshMargin H k A D o v f = CSH.cshMarg L pobs o v (covD H k A f) := by
      intro f
      rw [cshMargin, hins]
    have hnext : surplusMarginY H Y T' r (k :: D) o v F =
        CSH.cshMarg L pobs o v (surplusY H Y T' r F) -
          surplusY H Y T' r F k * CSH.cshMarg L pobs o v ck := by
      rw [surplusMarginY, ← hA, hset2, decoyList, hins, CSH.cshMarg_cons]
    have hpeel : surplusY H Y T r F = surplusY H Y T' r F + Tk := by
      funext u
      rw [Pi.add_apply, surplusY_erase_add H Y T r F hkT hlt u]
    have hTk_cov : (μ.real Dk) • Tk = covD H k A F - (κ * μ.real Dk) • ck := by
      funext u
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have h1 := covD_topTerm_eq H A F k u mk
      have h2 : μ.real (Dk ∩ hyperConn H k u) = μ.real Dk * ck u := by
        simp only [hck, avoidConst, hDk]
        rw [mul_div_cancel₀ _ (ne_of_gt hDkpos)]
      simp only [hTk, hκ, hDk] at h1 h2 ⊢
      rw [h1, h2]
      ring
    have hCSHk := hCSH k A D hkA hko hkv hoA hvA hD
      (fun d hd => ⟨fun h => hkD (h ▸ hd),
        by rw [hA, Set.mem_union, not_or]
           exact ⟨(hDT d hd).2.1, fun h => (hDT d hd).1 (hT'T d (Finset.mem_coe.1 h))⟩,
        (hDT d hd).2.2.1, (hDT d hd).2.2.2⟩)
    have h3 : 0 ≤ CSH.cshMarg L pobs o v (covD H k A F) := by
      rw [← hcshMargin]
      exact hCSHk F (fun a b hab => hF a b hab)
    have h4 : 0 ≤ CSH.cshMarg L pobs o v ck := by
      have hiso := hCSHk (psiIso k) (psiIso_mono k)
      rw [hcshMargin] at hiso
      have hLk : ∀ dc ∈ L, dc.1 ≠ k := fun dc hdc h => hkD (h ▸ mem_decoyList H _ D dc hdc)
      rw [CSH.cshMarg_congr L pobs o v (covD H k A (psiIso k))
        ((μ.real (Dk ∩ Iso) * μ.real Dk) • ck) (fun u => u ≠ k) hLk hko hkv
        (fun u hu => by
          rw [covD_psiIso H A k u hu, Pi.smul_apply, smul_eq_mul]
          simp only [hck, avoidConst, hDk, hIso]
          rw [mul_assoc, mul_div_cancel₀ _ (ne_of_gt hDkpos)]), CSH.cshMarg_smul] at hiso
      exact (mul_nonneg_iff_of_pos_left (mul_pos hisopos hDkpos)).1 hiso
    have h5 : κ ≤ surplusY H Y T' r F k := kappaY_le_surplusY H Y T' r F k hrT' hmle
    have h6 : 0 ≤ surplusMarginY H Y T' r (k :: D) o v F :=
      ih T'.card hTcard T' r (k :: D) F rfl hF hrT' hcompatT' (fun a ha => hTY a (hT'T a ha))
        (fun h => hoT (hT'T o h)) (fun h => hvT (hT'T v h))
        (List.nodup_cons.2 ⟨hkD, hD⟩)
        (fun d hd => by
          rcases List.mem_cons.1 hd with rfl | hd
          · exact ⟨hkT', hkY, hko.symm, hkv.symm⟩
          · exact ⟨fun h => (hDT d hd).1 (hT'T d h), (hDT d hd).2.1, (hDT d hd).2.2.1,
              (hDT d hd).2.2.2⟩)
    have hmain : μ.real Dk * surplusMarginY H Y T r D o v F =
        μ.real Dk * CSH.cshMarg L pobs o v (surplusY H Y T' r F) +
          CSH.cshMarg L pobs o v (covD H k A F) -
            κ * μ.real Dk * CSH.cshMarg L pobs o v ck := by
      have e1 : μ.real Dk * CSH.cshMarg L pobs o v Tk =
          CSH.cshMarg L pobs o v (covD H k A F) -
            κ * μ.real Dk * CSH.cshMarg L pobs o v ck := by
        rw [← CSH.cshMarg_smul, hTk_cov, cshMarg_sub', CSH.cshMarg_smul]
      rw [surplusMarginY, ← hL, ← hpobs, hpeel, CSH.cshMarg_add, mul_add, e1]
      ring
    have hbound : μ.real Dk * surplusMarginY H Y T' r (k :: D) o v F ≤
        μ.real Dk * surplusMarginY H Y T r D o v F := by
      rw [hmain, hnext]
      have hstep := mul_le_mul_of_nonneg_right h5 (mul_nonneg hDkpos.le h4)
      nlinarith [h3, h4, hstep, hDkpos.le]
    exact le_of_mul_le_mul_left (by linarith [mul_nonneg hDkpos.le h6]) hDkpos
  intro T r D F hF hr hcompat hTY hoT hvT hD hDT
  exact main T.card T r D F rfl hF hr hcompat hTY hoT hvT hD hDT

end Peel

end KNAll.Site

end

#print axioms KNAll.Site.surplusMarginY_nonneg_of_csh
#print axioms KNAll.Site.surplusTransferY_of_surplusMarginY_nil
#print axioms KNAll.Site.surplusY_erase_add
#print axioms KNAll.Site.kappaY_le_surplusY
#print axioms KNAll.Site.covD_psiIso
#print axioms KNAll.Site.sum_measureReal_avoid_firstRank
