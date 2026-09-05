import KNConjectures.Question8Cases
import Percolation.Literature.KozmaNitzanPinning

/-!
# Question 8: the pendant tie-breaker and strict/positive equivalence

The old vertices of `Fin n` are embedded in `Fin (n + 1)` by `Fin.castSucc`;
`Fin.last n` is joined only to the selected relay `a`.  Conditioning on that
single pendant edge gives the four identities from the note.  They turn a
positive-score tied minimiser into a strict minimiser, while `q8_zeroScore`
handles the remaining case.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

/-- The new edge from the selected old relay to the pendant relay. -/
def q8PendantEdge {n : ℕ} (a : Fin n) : Sym2 (Fin (n + 1)) :=
  s(a.castSucc, Fin.last n)

/-- Replace `a` in the relay set by the new pendant vertex. -/
def q8PendantRelays {n : ℕ} (A : Finset (Fin n)) (a : Fin n) :
    Finset (Fin (n + 1)) :=
  (A.erase a).map Fin.castSuccEmb ∪ {Fin.last n}

/-- The augmented weight: old pairs keep their weights, the pendant pair has
weight `q`, and every other new pair has weight zero. -/
def q8PendantWeight {n : ℕ} (w : Sym2 (Fin n) → unitInterval)
    (a : Fin n) (q : unitInterval) : Sym2 (Fin (n + 1)) → unitInterval :=
  fun e' ↦
    if h : ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e' then w h.choose
    else if e' = q8PendantEdge a then q else 0

/-- The last vertex cannot be an endpoint of an embedded old pair. -/
private theorem last_not_mem_map_castSucc {n : ℕ} (e : Sym2 (Fin n)) :
    Fin.last n ∉ Sym2.map Fin.castSucc e := by
  rw [Sym2.mem_map]
  rintro ⟨v, -, hv⟩
  exact Fin.castSucc_ne_last v hv

/-- An embedded old pair is not the pendant pair. -/
private theorem map_castSucc_ne_pendant {n : ℕ} (a : Fin n)
    (e : Sym2 (Fin n)) :
    Sym2.map Fin.castSucc e ≠ q8PendantEdge a := by
  intro h
  have hp : Fin.last n ∈ Sym2.map Fin.castSucc e := by
    rw [h, q8PendantEdge]
    exact Sym2.mem_mk_right _ _
  exact last_not_mem_map_castSucc e hp

/-- Old coordinates retain exactly their original weights. -/
theorem q8PendantWeight_map_castSucc {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (q : unitInterval)
    (e : Sym2 (Fin n)) :
    q8PendantWeight w a q (Sym2.map Fin.castSucc e) = w e := by
  unfold q8PendantWeight
  have h : ∃ e₀ : Sym2 (Fin n),
      Sym2.map Fin.castSucc e₀ = Sym2.map Fin.castSucc e := ⟨e, rfl⟩
  rw [dif_pos h, Sym2.map.injective (Fin.castSucc_injective n) h.choose_spec]

/-- The newly added pair has weight `q`. -/
theorem q8PendantWeight_pendant {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (q : unitInterval) :
    q8PendantWeight w a q (q8PendantEdge a) = q := by
  unfold q8PendantWeight
  have h : ¬ ∃ e : Sym2 (Fin n),
      Sym2.map Fin.castSucc e = q8PendantEdge a := by
    rintro ⟨e, he⟩
    exact map_castSucc_ne_pendant a e he
  rw [dif_neg h, if_pos rfl]

/-- Every genuinely new non-pendant pair has weight zero. -/
theorem q8PendantWeight_eq_zero {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (q : unitInterval)
    {e' : Sym2 (Fin (n + 1))}
    (hOld : ¬ ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e')
    (hPendant : e' ≠ q8PendantEdge a) :
    q8PendantWeight w a q e' = 0 := by
  unfold q8PendantWeight
  rw [dif_neg hOld, if_neg hPendant]

/-- The deterministic set of new edges used after conditioning the pendant
edge to be closed (`false`) or open (`true`). -/
private def pendantEdges {n : ℕ} (a : Fin n) (openEdge : Bool) :
    Set (Sym2 (Fin (n + 1))) :=
  if openEdge = true then {q8PendantEdge a} else ∅

/-- Augment an old configuration by a deterministically closed or open pendant
edge. -/
private def pendantConfig {n : ℕ} (a : Fin n) (openEdge : Bool)
    (ω : BondConfig (Fin n)) : BondConfig (Fin (n + 1)) :=
  Sym2.map Fin.castSucc '' ω ∪ pendantEdges a openEdge

/-- The weights of the deterministic conditioned configuration. -/
private def pendantPinnedWeight {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool)
    (e' : Sym2 (Fin (n + 1))) : unitInterval :=
  if h : ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e' then w h.choose
  else if e' ∈ pendantEdges a openEdge then 1 else 0

private theorem pendantPinnedWeight_map_castSucc {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool)
    (e : Sym2 (Fin n)) :
    pendantPinnedWeight w a openEdge (Sym2.map Fin.castSucc e) = w e := by
  unfold pendantPinnedWeight
  have h : ∃ e₀ : Sym2 (Fin n),
      Sym2.map Fin.castSucc e₀ = Sym2.map Fin.castSucc e := ⟨e, rfl⟩
  rw [dif_pos h, Sym2.map.injective (Fin.castSucc_injective n) h.choose_spec]

private theorem pendantPinnedWeight_of_extra {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool)
    {e' : Sym2 (Fin (n + 1))} (he' : e' ∈ pendantEdges a openEdge) :
    pendantPinnedWeight w a openEdge e' = 1 := by
  unfold pendantPinnedWeight
  have hOld : ¬ ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e' := by
    rintro ⟨e, rfl⟩
    have : Sym2.map Fin.castSucc e ∈ pendantEdges a openEdge := he'
    simp only [pendantEdges] at this
    split at this
    · exact map_castSucc_ne_pendant a e (mem_singleton_iff.1 this)
    · exact this.elim
  rw [dif_neg hOld, if_pos he']

private theorem pendantPinnedWeight_eq_zero {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool)
    {e' : Sym2 (Fin (n + 1))}
    (hOld : ¬ ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e')
    (hExtra : e' ∉ pendantEdges a openEdge) :
    pendantPinnedWeight w a openEdge e' = 0 := by
  unfold pendantPinnedWeight
  rw [dif_neg hOld, if_neg hExtra]

private theorem pendantPinnedWeight_comp_map {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool) :
    pendantPinnedWeight w a openEdge ∘ Sym2.map Fin.castSucc = w :=
  funext (pendantPinnedWeight_map_castSucc w a openEdge)

private theorem map_castSucc_mem_pendantConfig_iff {n : ℕ}
    (a : Fin n) (openEdge : Bool) (ω : BondConfig (Fin n))
    (e : Sym2 (Fin n)) :
    Sym2.map Fin.castSucc e ∈ pendantConfig a openEdge ω ↔ e ∈ ω := by
  constructor
  · rintro (⟨e₀, he₀, heq⟩ | hExtra)
    · rwa [Sym2.map.injective (Fin.castSucc_injective n) heq] at he₀
    · simp only [pendantEdges] at hExtra
      split at hExtra
      · exact absurd (mem_singleton_iff.1 hExtra)
          (map_castSucc_ne_pendant a e)
      · exact hExtra.elim
  · intro he
    exact Or.inl ⟨e, he, rfl⟩

/-- Restricting the deterministic augmented law to old pairs gives the old
product law. -/
private theorem map_restrictConfig_pendantPinnedWeight {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool) :
    (prodBernoulli (pendantPinnedWeight w a openEdge)).map
        (restrictConfig Fin.castSucc) = prodBernoulli w := by
  rw [prodBernoulli_map_restrictConfig _ (Fin.castSucc_injective n),
    pendantPinnedWeight_comp_map]

/-- Under the deterministic conditioned weights, all new coordinates agree
almost surely with `pendantConfig`. -/
private theorem ae_pendantConfig_restrictConfig_eq {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool) :
    ∀ᵐ ω' ∂(prodBernoulli (pendantPinnedWeight w a openEdge)),
      pendantConfig a openEdge (restrictConfig Fin.castSucc ω') = ω' := by
  have hall : ∀ e' : Sym2 (Fin (n + 1)),
      ∀ᵐ ω' ∂(prodBernoulli (pendantPinnedWeight w a openEdge)),
        (e' ∈ pendantEdges a openEdge → e' ∈ ω') ∧
          ((¬ ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e') →
            e' ∉ pendantEdges a openEdge → e' ∉ ω') := by
    intro e'
    by_cases hExtra : e' ∈ pendantEdges a openEdge
    · filter_upwards [prodBernoulli_ae_mem_of_eq_one
          (pendantPinnedWeight w a openEdge)
          (pendantPinnedWeight_of_extra w a openEdge hExtra)] with ω' hmem
      exact ⟨fun _ ↦ hmem, fun _ h ↦ absurd hExtra h⟩
    · by_cases hOld : ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e'
      · exact Filter.Eventually.of_forall fun _ ↦
          ⟨fun h ↦ absurd h hExtra, fun h ↦ absurd hOld h⟩
      · filter_upwards [prodBernoulli_ae_notMem
            (pendantPinnedWeight w a openEdge)
            (pendantPinnedWeight_eq_zero w a openEdge hOld hExtra)] with ω' hnot
        exact ⟨fun h ↦ absurd h hExtra, fun _ _ ↦ hnot⟩
  rw [← ae_all_iff] at hall
  filter_upwards [hall] with ω' h
  ext e'
  constructor
  · rintro (⟨e, he, rfl⟩ | hExtra)
    · exact he
    · exact (h e').1 hExtra
  · intro he'
    by_cases hExtra : e' ∈ pendantEdges a openEdge
    · exact Or.inr hExtra
    · by_cases hOld : ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e'
      · obtain ⟨e, rfl⟩ := hOld
        exact Or.inl ⟨e, he', rfl⟩
      · exact absurd he' ((h e').2 hOld hExtra)

/-- The deterministic augmented product law is the image of the old law. -/
private theorem prodBernoulli_pendantPinnedWeight_eq_map {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool) :
    prodBernoulli (pendantPinnedWeight w a openEdge) =
      (prodBernoulli w).map (pendantConfig a openEdge) := by
  have hres : Measurable
      (restrictConfig (Fin.castSucc : Fin n → Fin (n + 1))) :=
    measurable_restrictConfig _
  have haug : Measurable
      (pendantConfig a openEdge : BondConfig (Fin n) →
        BondConfig (Fin (n + 1))) := Measurable.of_discrete
  calc
    prodBernoulli (pendantPinnedWeight w a openEdge) =
        (prodBernoulli (pendantPinnedWeight w a openEdge)).map id :=
      Measure.map_id.symm
    _ = (prodBernoulli (pendantPinnedWeight w a openEdge)).map
        (pendantConfig a openEdge ∘ restrictConfig Fin.castSucc) :=
      Measure.map_congr (by
        filter_upwards [ae_pendantConfig_restrictConfig_eq w a openEdge]
          with ω' hω' using hω'.symm)
    _ = ((prodBernoulli (pendantPinnedWeight w a openEdge)).map
          (restrictConfig Fin.castSucc)).map (pendantConfig a openEdge) :=
      (Measure.map_map haug hres).symm
    _ = (prodBernoulli w).map (pendantConfig a openEdge) := by
      rw [map_restrictConfig_pendantPinnedWeight]

private theorem measureReal_pendantPinned {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (openEdge : Bool)
    (S : Set (BondConfig (Fin (n + 1)))) :
    (prodBernoulli (pendantPinnedWeight w a openEdge)).real S =
      (prodBernoulli w).real (pendantConfig a openEdge ⁻¹' S) := by
  rw [prodBernoulli_pendantPinnedWeight_eq_map,
    map_measureReal_apply (Measurable.of_discrete (f := pendantConfig a openEdge))
      MeasurableSet.of_discrete]

/-- Pinning the random pendant coordinate produces the deterministic augmented
weight above. -/
private theorem pinW_pendant_eq_pinned {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (q : unitInterval)
    (openEdge : Bool) :
    pinW (q8PendantWeight w a q)
        ({q8PendantEdge a} : Set (Sym2 (Fin (n + 1))))
        (pendantEdges a openEdge) =
      pendantPinnedWeight w a openEdge := by
  funext e'
  by_cases hOld : ∃ e : Sym2 (Fin n), Sym2.map Fin.castSucc e = e'
  · obtain ⟨e, rfl⟩ := hOld
    have hnot : Sym2.map Fin.castSucc e ∉
        ({q8PendantEdge a} : Set (Sym2 (Fin (n + 1)))) := by
      simpa only [mem_singleton_iff] using map_castSucc_ne_pendant a e
    rw [pinW_apply_of_not_mem _ _ hnot,
      q8PendantWeight_map_castSucc, pendantPinnedWeight_map_castSucc]
  · by_cases hPendant : e' = q8PendantEdge a
    · subst e'
      rw [pinW_apply]
      cases openEdge <;>
        simp [pendantEdges, pendantPinnedWeight, hOld]
    · have hnot : e' ∉
        ({q8PendantEdge a} : Set (Sym2 (Fin (n + 1)))) := by
        simpa only [mem_singleton_iff]
      have hExtra : e' ∉ pendantEdges a openEdge := by
        cases openEdge <;> simp [pendantEdges, hPendant]
      rw [pinW_apply_of_not_mem _ _ hnot,
        q8PendantWeight_eq_zero w a q hOld hPendant,
        pendantPinnedWeight_eq_zero w a openEdge hOld hExtra]

private theorem pendant_cylinder_open {n : ℕ} (a : Fin n) :
    localCylinder
        (↑({q8PendantEdge a} : Finset (Sym2 (Fin (n + 1)))) :
          Set (Sym2 (Fin (n + 1))))
        ({q8PendantEdge a} : Set (Sym2 (Fin (n + 1)))) =
      { ω : BondConfig (Fin (n + 1)) | q8PendantEdge a ∈ ω } := by
  ext ω
  simp [localCylinder]

private theorem pendant_cylinder_closed {n : ℕ} (a : Fin n) :
    localCylinder
        (↑({q8PendantEdge a} : Finset (Sym2 (Fin (n + 1)))) :
          Set (Sym2 (Fin (n + 1))))
        (∅ : Set (Sym2 (Fin (n + 1)))) =
      { ω : BondConfig (Fin (n + 1)) | q8PendantEdge a ∉ ω } := by
  ext ω
  simp [localCylinder]

/-- Condition on the single pendant coordinate.  This is the common product
measure calculation behind all four pendant identities. -/
private theorem q8Pendant_probability {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (a : Fin n) (q : unitInterval)
    (S : Set (BondConfig (Fin (n + 1)))) :
    (prodBernoulli (q8PendantWeight w a q)).real S =
      (q : ℝ) * (prodBernoulli w).real (pendantConfig a true ⁻¹' S) +
        (1 - (q : ℝ)) *
          (prodBernoulli w).real (pendantConfig a false ⁻¹' S) := by
  let w' := q8PendantWeight w a q
  let μ := prodBernoulli w'
  let e := q8PendantEdge a
  let P : Set (BondConfig (Fin (n + 1))) := {ω | e ∈ ω}
  have hsplit : μ.real (S ∩ P) + μ.real (S \ P) = μ.real S :=
    measureReal_inter_add_sdiff MeasurableSet.of_discrete
  have hOpen : μ.real (S ∩ P) =
      (q : ℝ) * (prodBernoulli w).real (pendantConfig a true ⁻¹' S) := by
    have h := prodBernoulli_real_inter_localCylinder w'
      ({e} : Finset (Sym2 (Fin (n + 1)))) ({e} : Set (Sym2 (Fin (n + 1))))
      (A := S) MeasurableSet.of_discrete
    have hcyl : localCylinder
        (↑({e} : Finset (Sym2 (Fin (n + 1)))) : Set (Sym2 (Fin (n + 1))))
        ({e} : Set (Sym2 (Fin (n + 1)))) = P := by
      simpa only [e, P] using pendant_cylinder_open a
    rw [hcyl, prodBernoulli_real_setOf_mem,
      show w' e = q by simp only [w', e, q8PendantWeight_pendant],
      show pinW w' (↑({e} : Finset (Sym2 (Fin (n + 1)))) :
          Set (Sym2 (Fin (n + 1))))
          ({e} : Set (Sym2 (Fin (n + 1)))) =
          pendantPinnedWeight w a true by
        rw [show (↑({e} : Finset (Sym2 (Fin (n + 1)))) :
            Set (Sym2 (Fin (n + 1)))) =
            ({q8PendantEdge a} : Set (Sym2 (Fin (n + 1)))) by
          ext x
          simp only [Finset.mem_coe, Finset.mem_singleton, mem_singleton_iff, e]]
        simpa only [w', e, pendantEdges, if_true] using
          pinW_pendant_eq_pinned w a q true,
      measureReal_pendantPinned] at h
    exact h
  have hClosed : μ.real (S \ P) =
      (1 - (q : ℝ)) *
        (prodBernoulli w).real (pendantConfig a false ⁻¹' S) := by
    rw [Set.sdiff_eq]
    have h := prodBernoulli_real_inter_localCylinder w'
      ({e} : Finset (Sym2 (Fin (n + 1))))
      (∅ : Set (Sym2 (Fin (n + 1))))
      (A := S) MeasurableSet.of_discrete
    have hcyl : localCylinder
        (↑({e} : Finset (Sym2 (Fin (n + 1)))) : Set (Sym2 (Fin (n + 1))))
        (∅ : Set (Sym2 (Fin (n + 1)))) = Pᶜ := by
      simpa only [e, P, compl_setOf] using pendant_cylinder_closed a
    have hPcompl : Pᶜ =
        { ω : BondConfig (Fin (n + 1)) | e ∉ ω } := by
      ext ω
      simp only [P, mem_compl_iff, mem_setOf_eq]
    rw [hcyl, hPcompl, prodBernoulli_real_setOf_notMem,
      show w' e = q by simp only [w', e, q8PendantWeight_pendant],
      show pinW w' (↑({e} : Finset (Sym2 (Fin (n + 1)))) :
          Set (Sym2 (Fin (n + 1))))
          (∅ : Set (Sym2 (Fin (n + 1)))) =
          pendantPinnedWeight w a false by
        rw [show (↑({e} : Finset (Sym2 (Fin (n + 1)))) :
            Set (Sym2 (Fin (n + 1)))) =
            ({q8PendantEdge a} : Set (Sym2 (Fin (n + 1)))) by
          ext x
          simp only [Finset.mem_coe, Finset.mem_singleton, mem_singleton_iff, e]]
        simpa only [w', e, pendantEdges, Bool.false_eq_true, if_false] using
          pinW_pendant_eq_pinned w a q false,
      measureReal_pendantPinned] at h
    exact h
  rw [← hsplit, hOpen, hClosed]

/-! ## Reachability in the two deterministic pendant configurations -/

/-- Collapse the new last vertex back to its attachment point. -/
private def pendantCollapse {n : ℕ} (a : Fin n) : Fin (n + 1) → Fin n :=
  Fin.lastCases a id

@[simp] private theorem pendantCollapse_last {n : ℕ} (a : Fin n) :
    pendantCollapse a (Fin.last n) = a := by
  simp [pendantCollapse]

@[simp] private theorem pendantCollapse_castSucc {n : ℕ} (a x : Fin n) :
    pendantCollapse a x.castSucc = x := by
  simp [pendantCollapse]

/-- Every old adjacency remains an adjacency after adding the pendant vertex. -/
private theorem pendantConfig_adj_castSucc {n : ℕ} (a : Fin n)
    (openEdge : Bool) (ω : BondConfig (Fin n)) {x y : Fin n}
    (hxy : (openGraph ω).Adj x y) :
    (openGraph (pendantConfig a openEdge ω)).Adj x.castSucc y.castSucc := by
  rw [openGraph_adj] at hxy ⊢
  refine ⟨Or.inl ⟨s(x, y), hxy.1, ?_⟩, ?_⟩
  · rw [Sym2.map_mk]
  · exact fun h ↦ hxy.2 (Fin.castSucc_injective n h)

/-- An augmented adjacency collapses either to an old adjacency or, on the
pendant edge, to equality; in both cases the collapsed old vertices are
reachable. -/
private theorem pendantConfig_adj_collapse_reachable {n : ℕ} (a : Fin n)
    (openEdge : Bool) (ω : BondConfig (Fin n)) {u v : Fin (n + 1)}
    (huv : (openGraph (pendantConfig a openEdge ω)).Adj u v) :
    (openGraph ω).Reachable (pendantCollapse a u) (pendantCollapse a v) := by
  rw [openGraph_adj] at huv
  rcases huv.1 with ⟨e, heω, heq⟩ | hExtra
  · induction e using Sym2.ind with
    | _ x y =>
        rw [Sym2.map_mk, Sym2.eq_iff] at heq
        rcases heq with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
        · subst u
          subst v
          have hxy : (openGraph ω).Adj x y := by
            rw [openGraph_adj]
            exact ⟨heω, fun h ↦ huv.2 (congrArg Fin.castSucc h)⟩
          simpa using hxy.reachable
        · subst v
          subst u
          have hxy : (openGraph ω).Adj x y := by
            rw [openGraph_adj]
            exact ⟨heω, fun h ↦ huv.2 (congrArg Fin.castSucc h).symm⟩
          simpa using hxy.symm.reachable
  · cases openEdge <;> simp only [pendantEdges, Bool.false_eq_true,
        if_false, mem_empty_iff_false, if_true, mem_singleton_iff] at hExtra
    rw [q8PendantEdge, Sym2.eq_iff] at hExtra
    rcases hExtra with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp

/-- Old reachability lifts into either augmented configuration. -/
private theorem pendantConfig_reachable_castSucc {n : ℕ} (a : Fin n)
    (openEdge : Bool) (ω : BondConfig (Fin n)) {x y : Fin n}
    (hxy : (openGraph ω).Reachable x y) :
    (openGraph (pendantConfig a openEdge ω)).Reachable x.castSucc y.castSucc :=
  hxy.map
    { toFun := Fin.castSucc
      map_rel' := fun h ↦ pendantConfig_adj_castSucc a openEdge ω h }

/-- Conversely, collapsing an augmented open walk gives an old reachable
relation. -/
private theorem pendantConfig_reachable_collapse {n : ℕ} (a : Fin n)
    (openEdge : Bool) (ω : BondConfig (Fin n)) {u v : Fin (n + 1)}
    (huv : (openGraph (pendantConfig a openEdge ω)).Reachable u v) :
    (openGraph ω).Reachable (pendantCollapse a u) (pendantCollapse a v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv ⊢
  exact huv.lift' (pendantCollapse a) fun _ _ h ↦
    (SimpleGraph.reachable_iff_reflTransGen _ _).1
      (pendantConfig_adj_collapse_reachable a openEdge ω h)

/-- Adding a pendant edge never changes connectivity between two old
vertices. -/
@[simp] private theorem pendantConfig_reachable_castSucc_iff {n : ℕ}
    (a : Fin n) (openEdge : Bool) (ω : BondConfig (Fin n)) (x y : Fin n) :
    (openGraph (pendantConfig a openEdge ω)).Reachable x.castSucc y.castSucc ↔
      (openGraph ω).Reachable x y := by
  exact ⟨fun h ↦ by simpa using
      pendantConfig_reachable_collapse a openEdge ω h,
    pendantConfig_reachable_castSucc a openEdge ω⟩

/-- When open, the new relay has precisely the old connectivity of `a`. -/
@[simp] private theorem pendantConfig_true_reachable_last_iff {n : ℕ}
    (a x : Fin n) (ω : BondConfig (Fin n)) :
    (openGraph (pendantConfig a true ω)).Reachable (Fin.last n) x.castSucc ↔
      (openGraph ω).Reachable a x := by
  constructor
  · intro h
    simpa using pendantConfig_reachable_collapse a true ω h
  · intro h
    have hla : (openGraph (pendantConfig a true ω)).Adj
        (Fin.last n) a.castSucc := by
      rw [openGraph_adj]
      refine ⟨?_, (Fin.castSucc_ne_last a).symm⟩
      exact Or.inr (by
        simp only [pendantEdges, if_true, mem_singleton_iff, q8PendantEdge]
        exact Sym2.eq_swap)
    exact hla.reachable.trans (pendantConfig_reachable_castSucc a true ω h)

/-- With the pendant edge closed, the new last vertex has no neighbour. -/
private theorem pendantConfig_false_not_adj_last {n : ℕ} (a : Fin n)
    (ω : BondConfig (Fin n)) (v : Fin (n + 1)) :
    ¬ (openGraph (pendantConfig a false ω)).Adj (Fin.last n) v := by
  intro h
  rw [openGraph_adj] at h
  rcases h.1 with ⟨e, -, heq⟩ | hExtra
  · have hlast : Fin.last n ∈ Sym2.map Fin.castSucc e := by
      rw [heq]
      exact Sym2.mem_mk_left _ _
    exact last_not_mem_map_castSucc e hlast
  · simp [pendantEdges] at hExtra

/-- Hence a closed pendant cannot reach an old vertex. -/
@[simp] private theorem pendantConfig_false_not_reachable_last {n : ℕ}
    (a x : Fin n) (ω : BondConfig (Fin n)) :
    ¬ (openGraph (pendantConfig a false ω)).Reachable
      (Fin.last n) x.castSucc := by
  intro h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  have hstay : ∀ {v : Fin (n + 1)},
      Relation.ReflTransGen
          (openGraph (pendantConfig a false ω)).Adj (Fin.last n) v →
        v = Fin.last n := by
    intro v hv
    induction hv with
    | refl => rfl
    | tail hv hadj ih =>
        subst ih
        exact (pendantConfig_false_not_adj_last a ω _ hadj).elim
  exact Fin.castSucc_ne_last x (hstay h)

/-! ## Pull-backs of the connectivity events -/

private theorem preimage_openConn_castSucc {n : ℕ} (a : Fin n)
    (openEdge : Bool) (x y : Fin n) :
    pendantConfig a openEdge ⁻¹'
        (openConn x.castSucc y.castSucc : Set (BondConfig (Fin (n + 1)))) =
      openConn x y := by
  ext ω
  exact pendantConfig_reachable_castSucc_iff a openEdge ω x y

private theorem preimage_openConn_last_true {n : ℕ} (a x : Fin n) :
    pendantConfig a true ⁻¹'
        (openConn (Fin.last n) x.castSucc : Set (BondConfig (Fin (n + 1)))) =
      openConn a x := by
  ext ω
  exact pendantConfig_true_reachable_last_iff a x ω

private theorem preimage_openConn_last_false {n : ℕ} (a x : Fin n) :
    pendantConfig a false ⁻¹'
        (openConn (Fin.last n) x.castSucc : Set (BondConfig (Fin (n + 1)))) =
      ∅ := by
  ext ω
  simp only [mem_preimage, mem_empty_iff_false]
  exact iff_false_intro (pendantConfig_false_not_reachable_last a x ω)

/-- With the pendant open, hitting the replacement relay set is the original
event `{o ↔ A}`. -/
private theorem preimage_U_pendant_true {n : ℕ} (A : Finset (Fin n))
    (o a : Fin n) (ha : a ∈ A) :
    pendantConfig a true ⁻¹' U (q8PendantRelays A a) o.castSucc =
      U A o := by
  ext ω
  constructor
  · intro h
    obtain ⟨y, hy, hoy⟩ := mem_iUnion₂.1 h
    rcases Finset.mem_union.1 hy with hyOld | hyLast
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hyOld
      exact mem_iUnion₂.2 ⟨x, Finset.mem_of_mem_erase hx,
        (pendantConfig_reachable_castSucc_iff a true ω o x).1 hoy⟩
    · have hy' : y = Fin.last n := Finset.mem_singleton.1 hyLast
      subst y
      have hao : (openGraph ω).Reachable a o :=
        (pendantConfig_true_reachable_last_iff a o ω).1 hoy.symm
      exact mem_iUnion₂.2 ⟨a, ha, hao.symm⟩
  · intro h
    obtain ⟨x, hx, hox⟩ := mem_iUnion₂.1 h
    by_cases hxa : x = a
    · subst x
      refine mem_iUnion₂.2 ⟨Fin.last n,
        Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      exact ((pendantConfig_true_reachable_last_iff a o ω).2 hox.symm).symm
    · refine mem_iUnion₂.2 ⟨x.castSucc, Finset.mem_union_left _ ?_, ?_⟩
      · exact Finset.mem_map.2 ⟨x, Finset.mem_erase.2 ⟨hxa, hx⟩, rfl⟩
      · exact (pendantConfig_reachable_castSucc_iff a true ω o x).2 hox

/-- With the pendant closed, only the old relays in `A.erase a` remain
reachable. -/
private theorem preimage_U_pendant_false {n : ℕ} (A : Finset (Fin n))
    (o a : Fin n) :
    pendantConfig a false ⁻¹' U (q8PendantRelays A a) o.castSucc =
      U (A.erase a) o := by
  ext ω
  constructor
  · intro h
    obtain ⟨y, hy, hoy⟩ := mem_iUnion₂.1 h
    rcases Finset.mem_union.1 hy with hyOld | hyLast
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hyOld
      exact mem_iUnion₂.2 ⟨x, hx,
        (pendantConfig_reachable_castSucc_iff a false ω o x).1 hoy⟩
    · have hy' : y = Fin.last n := Finset.mem_singleton.1 hyLast
      subst y
      exact (pendantConfig_false_not_reachable_last a o ω hoy.symm).elim
  · intro h
    obtain ⟨x, hx, hox⟩ := mem_iUnion₂.1 h
    refine mem_iUnion₂.2 ⟨x.castSucc, Finset.mem_union_left _ ?_, ?_⟩
    · exact Finset.mem_map.2 ⟨x, hx, rfl⟩
    · exact (pendantConfig_reachable_castSucc_iff a false ω o x).2 hox

/-! ## The four pendant identities -/

/-- **Equation (pendant-rhoa).**  The score of the new pendant relay is
`q · ρ_a`. -/
theorem q8_pendant_rhoa {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) (q : unitInterval) (ha : a ∈ A) :
    q8Score (q8PendantWeight w a q) (q8PendantRelays A a)
        o.castSucc b.castSucc (Fin.last n) =
      (q : ℝ) * q8Score w A o b a := by
  unfold q8Score
  rw [q8Pendant_probability]
  have hTrue :
      pendantConfig a true ⁻¹'
          (openConn (Fin.last n) b.castSucc ∩
            (U (q8PendantRelays A a) o.castSucc)ᶜ) =
        openConn a b ∩ (U A o)ᶜ := by
    rw [preimage_inter, preimage_compl, preimage_openConn_last_true,
      preimage_U_pendant_true A o a ha]
  have hFalse :
      pendantConfig a false ⁻¹'
          (openConn (Fin.last n) b.castSucc ∩
            (U (q8PendantRelays A a) o.castSucc)ᶜ) = ∅ := by
    rw [preimage_inter, preimage_compl, preimage_openConn_last_false,
      empty_inter]
  rw [hTrue, hFalse, measureReal_empty, mul_zero, add_zero]

/-- **Equation (pendant-rhox).**  An old remaining relay has the stated
two-branch score.  The second component records the useful lower bound by its
old score. -/
theorem q8_pendant_rhox {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a x : Fin n) (q : unitInterval) (ha : a ∈ A)
    (_hx : x ∈ A.erase a) :
    q8Score (q8PendantWeight w a q) (q8PendantRelays A a)
        o.castSucc b.castSucc x.castSucc =
        (q : ℝ) * q8Score w A o b x +
          (1 - (q : ℝ)) *
            (prodBernoulli w).real
              (openConn x b ∩ (U (A.erase a) o)ᶜ) ∧
      q8Score w A o b x ≤
        q8Score (q8PendantWeight w a q) (q8PendantRelays A a)
          o.castSucc b.castSucc x.castSucc := by
  have heq :
      q8Score (q8PendantWeight w a q) (q8PendantRelays A a)
          o.castSucc b.castSucc x.castSucc =
        (q : ℝ) * q8Score w A o b x +
          (1 - (q : ℝ)) *
            (prodBernoulli w).real
              (openConn x b ∩ (U (A.erase a) o)ᶜ) := by
    unfold q8Score
    rw [q8Pendant_probability]
    have hTrue :
        pendantConfig a true ⁻¹'
            (openConn x.castSucc b.castSucc ∩
              (U (q8PendantRelays A a) o.castSucc)ᶜ) =
          openConn x b ∩ (U A o)ᶜ := by
      rw [preimage_inter, preimage_compl, preimage_openConn_castSucc,
        preimage_U_pendant_true A o a ha]
    have hFalse :
        pendantConfig a false ⁻¹'
            (openConn x.castSucc b.castSucc ∩
              (U (q8PendantRelays A a) o.castSucc)ᶜ) =
          openConn x b ∩ (U (A.erase a) o)ᶜ := by
      rw [preimage_inter, preimage_compl, preimage_openConn_castSucc,
        preimage_U_pendant_false]
    rw [hTrue, hFalse]
  refine ⟨heq, ?_⟩
  have hsub :
      (openConn x b ∩ (U A o)ᶜ : Set (BondConfig (Fin n))) ⊆
        openConn x b ∩ (U (A.erase a) o)ᶜ := by
    rintro ω ⟨hxb, hnot⟩
    refine ⟨hxb, ?_⟩
    intro hT
    obtain ⟨y, hy, hoy⟩ := mem_iUnion₂.1 hT
    exact hnot (mem_iUnion₂.2 ⟨y, Finset.mem_of_mem_erase hy, hoy⟩)
  have hprob : q8Score w A o b x ≤
      (prodBernoulli w).real (openConn x b ∩ (U (A.erase a) o)ᶜ) := by
    unfold q8Score
    exact measureReal_mono hsub (measure_ne_top _ _)
  rw [heq]
  have hq₀ : 0 ≤ (q : ℝ) := q.2.1
  have hq₁ : (q : ℝ) ≤ 1 := q.2.2
  nlinarith

/-- **Equation (pendant-L).**  The new relay's left-hand target probability is
`q · L_a`. -/
theorem q8_pendant_L {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) (q : unitInterval) (ha : a ∈ A) :
    q8L (q8PendantWeight w a q) (q8PendantRelays A a)
        o.castSucc b.castSucc (Fin.last n) =
      (q : ℝ) * q8L w A o b a := by
  unfold q8L
  rw [q8Pendant_probability]
  have hTrue :
      pendantConfig a true ⁻¹'
          (openConn (Fin.last n) b.castSucc ∩
            U (q8PendantRelays A a) o.castSucc) =
        openConn a b ∩ U A o := by
    rw [preimage_inter, preimage_openConn_last_true,
      preimage_U_pendant_true A o a ha]
  have hFalse :
      pendantConfig a false ⁻¹'
          (openConn (Fin.last n) b.castSucc ∩
            U (q8PendantRelays A a) o.castSucc) = ∅ := by
    rw [preimage_inter, preimage_openConn_last_false, empty_inter]
  rw [hTrue, hFalse, measureReal_empty, mul_zero, add_zero]

/-- **Equation (pendant-R).**  The observer's target probability splits
according to the state of the pendant edge. -/
theorem q8_pendant_R {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) (q : unitInterval) (ha : a ∈ A) :
    q8R (q8PendantWeight w a q) (q8PendantRelays A a)
        o.castSucc b.castSucc =
      (q : ℝ) * q8R w A o b +
        (1 - (q : ℝ)) *
          (prodBernoulli w).real
            (openConn o b ∩ U (A.erase a) o) := by
  unfold q8R
  rw [q8Pendant_probability]
  have hTrue :
      pendantConfig a true ⁻¹'
          (openConn o.castSucc b.castSucc ∩
            U (q8PendantRelays A a) o.castSucc) =
        openConn o b ∩ U A o := by
    rw [preimage_inter, preimage_openConn_castSucc,
      preimage_U_pendant_true A o a ha]
  have hFalse :
      pendantConfig a false ⁻¹'
          (openConn o.castSucc b.castSucc ∩
            U (q8PendantRelays A a) o.castSucc) =
        openConn o b ∩ U (A.erase a) o := by
    rw [preimage_inter, preimage_openConn_castSucc,
      preimage_U_pendant_false]
  rw [hTrue, hFalse]

/-- The pendant relay is the unique new score minimiser whenever the selected
old relay has positive score and `0 < q < 1`. -/
theorem q8_pendant_strictMin {n : ℕ}
    (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b a : Fin n) (q : unitInterval)
    (hmin : IsQ8Min w A o b a) (hscore : 0 < q8Score w A o b a)
    (_hq₀ : 0 < (q : ℝ)) (hq₁ : (q : ℝ) < 1) :
    IsQ8StrictMin (q8PendantWeight w a q) (q8PendantRelays A a)
      o.castSucc b.castSucc (Fin.last n) := by
  refine ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
  intro x hx hxne
  rcases Finset.mem_union.1 hx with hxOld | hxLast
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hxOld
    calc
      q8Score (q8PendantWeight w a q) (q8PendantRelays A a)
          o.castSucc b.castSucc (Fin.last n) =
          (q : ℝ) * q8Score w A o b a :=
        q8_pendant_rhoa w A o b a q hmin.1
      _ < q8Score w A o b a := by nlinarith
      _ ≤ q8Score w A o b y :=
        hmin.2 y (Finset.mem_of_mem_erase hy)
      _ ≤ q8Score (q8PendantWeight w a q) (q8PendantRelays A a)
          o.castSucc b.castSucc y.castSucc :=
        (q8_pendant_rhox w A o b a y q hmin.1 hy).2
  · exact absurd (Finset.mem_singleton.1 hxLast) hxne

/-- Every probability under a product-Bernoulli law is at most one. -/
private theorem prodBernoulli_real_le_one {V : Type*}
    (w : Sym2 V → unitInterval) (S : Set (BondConfig V)) :
    (prodBernoulli w).real S ≤ 1 := by
  have h := measureReal_mono (μ := prodBernoulli w) (subset_univ S)
    (measure_ne_top _ _)
  simpa only [probReal_univ] using h

/-- **Q8.8.**  The global strict-minimiser form is equivalent to the
every-minimiser form under positive avoidance. -/
theorem q8Strict_iff_q8Positive : Question8Strict ↔ Question8Positive := by
  constructor
  · intro hStrict n w A o b a hD hmin
    by_cases hscore₀ : q8Score w A o b a = 0
    · exact q8_zeroScore w A o b a hmin.1 hD hscore₀
    · have hscore : 0 < q8Score w A o b a :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hscore₀)
      by_contra hconclusion
      have hbad : q8R w A o b < q8L w A o b a := lt_of_not_ge hconclusion
      let Δ : ℝ := q8L w A o b a - q8R w A o b
      have hΔ₀ : 0 < Δ := sub_pos.2 hbad
      have hL₁ : q8L w A o b a ≤ 1 := by
        unfold q8L
        exact prodBernoulli_real_le_one w _
      have hR₀ : 0 ≤ q8R w A o b := measureReal_nonneg
      have hΔ₁ : Δ ≤ 1 := by
        dsimp only [Δ]
        linarith
      let q : unitInterval :=
        ⟨1 - Δ / 4, by linarith, by linarith⟩
      have hq₀ : 0 < (q : ℝ) := by
        change 0 < 1 - Δ / 4
        linarith
      have hq₁ : (q : ℝ) < 1 := by
        change 1 - Δ / 4 < 1
        linarith
      have hnewMin := q8_pendant_strictMin w A o b a q hmin hscore hq₀ hq₁
      have hnew := hStrict (n + 1) (q8PendantWeight w a q)
        (q8PendantRelays A a) o.castSucc b.castSucc (Fin.last n) hnewMin
      rw [q8_pendant_L w A o b a q hmin.1,
        q8_pendant_R w A o b a q hmin.1] at hnew
      have hP₁ : (prodBernoulli w).real
          (openConn o b ∩ U (A.erase a) o) ≤ 1 :=
        prodBernoulli_real_le_one w _
      have hP₀ : 0 ≤ (prodBernoulli w).real
          (openConn o b ∩ U (A.erase a) o) := measureReal_nonneg
      change
        (1 - Δ / 4) * q8L w A o b a ≤
          (1 - Δ / 4) * q8R w A o b +
            (1 - (1 - Δ / 4)) *
              (prodBernoulli w).real
                (openConn o b ∩ U (A.erase a) o) at hnew
      dsimp only [Δ] at hΔ₀ hΔ₁ ⊢
      nlinarith
  · intro hPositive n w A o b a hstrict
    by_cases hD : 0 < (prodBernoulli w).real (U A o)ᶜ
    · apply hPositive n w A o b a hD
      refine ⟨hstrict.1, ?_⟩
      intro x hx
      by_cases hxa : x = a
      · subst x
        exact le_rfl
      · exact (hstrict.2 x hx hxa).le
    · have hD₀ : (prodBernoulli w).real (U A o)ᶜ = 0 :=
        le_antisymm (not_lt.1 hD) measureReal_nonneg
      have hallMin := q8_degenerate_allMin w A o b hD₀
      have hAeq : A = {a} := by
        ext x
        constructor
        · intro hx
          by_contra hxa
          have hxa' : x ≠ a := by simpa only [Finset.mem_singleton] using hxa
          have hlt := hstrict.2 x hx hxa'
          have hle := (hallMin x hx).2 a hstrict.1
          exact (not_lt_of_ge hle hlt)
        · intro hx
          exact (Finset.mem_singleton.1 hx) ▸ hstrict.1
      rw [hAeq]
      exact (q8_singleton w o b a).le

end KNAll

end


#print axioms KNAll.q8PendantWeight_map_castSucc
#print axioms KNAll.q8PendantWeight_pendant
#print axioms KNAll.q8PendantWeight_eq_zero
#print axioms KNAll.q8_pendant_rhoa
#print axioms KNAll.q8_pendant_rhox
#print axioms KNAll.q8_pendant_L
#print axioms KNAll.q8_pendant_R
#print axioms KNAll.q8_pendant_strictMin
#print axioms KNAll.q8Strict_iff_q8Positive
