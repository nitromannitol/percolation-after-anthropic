import Hypergraph.HyperCore

/-!
# Increasing events and positive association in the hyperedge model

The hyperedge analogues of the two properties every application of Harris' inequality needs: the
connection event is increasing in the set of open labels, and over a finite label type it is
measurable.  Feeding them to the product-measure Harris inequality gives positive association of
connection events, which is the correlation input of the gluing argument.

* `isUpperSet_hyperConn` — opening more labels cannot disconnect two vertices, which is that
  monotonicity read as a property of the event.
* `isUpperSet_subset_hyperClusterSet` — the same for the event that a vertex set lies in the cluster
  of a source, since the cluster only grows.
* `measurableSet_hyperConn` — over a finite label type every event is determined by the finite set
  of all labels, hence a finite union of cylinders, as in `measurableSet_clusterEvent`.
* `prodBernoulli_harris_upper` — Harris' inequality for two increasing measurable events under
  `prodBernoulli`, for an arbitrary index type.  The development already had the decreasing form
  `prodBernoulli_harris_lower` and the mixed form `prodBernoulli_harris_upper_lower`; the increasing
  form is obtained here the same way, by transporting `infinitePi_harris` along
  `prodBernoulli_real_eq_infinitePi`.
* `prodBernoulli_hyperConn_harris` — its specialization to two connection events.

## References

* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
* G. R. Grimmett, *Percolation*, 2nd ed., Springer (1999), Thm. (2.4) p. 34.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V E : Type*}

/-! ## The connection event is increasing -/

/-- Opening more labels can only join more vertices.  This repeats `KNAll.Site.openHyperGraph_mono`
of `KN/HyperDefs.lean` under a different name: that module is the skeleton of the later phases and
still carries unproved placeholders, so importing it here would make this module depend on them. -/
theorem openHyperGraph_le_of_subset (H : Hypergraph V E) {ω ω' : Set E} (hsub : ω ⊆ ω') :
    openHyperGraph H ω ≤ openHyperGraph H ω' := by
  intro x y hxy
  rw [openHyperGraph_adj_iff] at hxy ⊢
  obtain ⟨hne, e, he, hx, hy⟩ := hxy
  exact ⟨hne, e, hsub he, hx, hy⟩

/-- **Target 1.**  Opening more labels cannot disconnect two vertices, so the connection event is an
upper set in the configuration order (inclusion of the set of open labels). -/
theorem isUpperSet_hyperConn (H : Hypergraph V E) (x y : V) : IsUpperSet (hyperConn H x y) :=
  fun _ _ hsub h => h.mono (openHyperGraph_le_of_subset H hsub)

/-- The cluster of a source grows when more labels are opened. -/
theorem hyperClusterSet_mono (H : Hypergraph V E) (S : Set V) {ω ω' : Set E} (hsub : ω ⊆ ω') :
    hyperClusterSet H ω S ⊆ hyperClusterSet H ω' S := by
  rintro y ⟨x, hx, hr⟩
  exact ⟨x, hx, hr.mono (openHyperGraph_le_of_subset H hsub)⟩

/-- **Target 2.**  The event that `T` lies in the cluster of `S` is increasing, for the same reason:
the cluster only grows. -/
theorem isUpperSet_subset_hyperClusterSet (H : Hypergraph V E) (S T : Set V) :
    IsUpperSet {ω : Set E | T ⊆ hyperClusterSet H ω S} :=
  fun _ _ hsub h => h.trans (hyperClusterSet_mono H S hsub)

/-! ## Measurability over a finite label type -/

/-- **Target 3.**  Over a finite label type the connection event is measurable: it is determined by
the finite set of all labels, hence a finite union of cylinders.  Same route as
`measurableSet_clusterEvent`. -/
theorem measurableSet_hyperConn [Fintype E] (H : Hypergraph V E) (x y : V) :
    MeasurableSet (hyperConn H x y) := by
  classical
  have h : DeterminedBy (hyperConn H x y) (↑(Finset.univ : Finset E)) := by
    rw [determinedBy_iff]
    intro ω ω' hω
    have hωω : ω = ω' := by simpa using hω
    rw [hωω]
  exact h.measurableSet_of_finset

/-! ## Harris' inequality for two increasing events -/

section Harris

variable {ι : Type*}

/-- **Target 5.  Harris' inequality for two increasing events under `prodBernoulli`**, for an
arbitrary index type: `P(A) P(B) ≤ P(A ∩ B)`.  The development carries the decreasing form
`prodBernoulli_harris_lower` and the mixed form `prodBernoulli_harris_upper_lower` but not this one;
it is proved here exactly as they are, by transporting the product-measure inequality
`infinitePi_harris` along `prodBernoulli_real_eq_infinitePi`, the measurable order isomorphism
`q ↦ {i | q i}` between `ι → Prop` and `Set ι`.
[cite: HarrisPCPS1960, Lemma 4.1] [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem prodBernoulli_harris_upper (p : ι → unitInterval) {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (prodBernoulli p).real A * (prodBernoulli p).real B ≤ (prodBernoulli p).real (A ∩ B) := by
  simp only [prodBernoulli_real_eq_infinitePi, Set.preimage_inter]
  exact infinitePi_harris _ (hA.preimage fun _ _ h => h) (hB.preimage fun _ _ h => h)
    (measurable_setOf hAm) (measurable_setOf hBm)

end Harris

/-- **Target 4.  Positive association of connection events.**  Two connection events in a finite
hyperedge model are positively correlated, by `prodBernoulli_harris_upper` applied to
`isUpperSet_hyperConn` and `measurableSet_hyperConn`.
[cite: HarrisPCPS1960, Lemma 4.1] [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem prodBernoulli_hyperConn_harris [Fintype E] (H : Hypergraph V E) (x y a b : V) :
    (prodBernoulli H.prob).real (hyperConn H x y) *
        (prodBernoulli H.prob).real (hyperConn H a b) ≤
      (prodBernoulli H.prob).real (hyperConn H x y ∩ hyperConn H a b) :=
  prodBernoulli_harris_upper H.prob (isUpperSet_hyperConn H x y) (isUpperSet_hyperConn H a b)
    (measurableSet_hyperConn H x y) (measurableSet_hyperConn H a b)

end KNAll.Site

end
