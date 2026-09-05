import Hypergraph.SiteStatements

/-!
# From a uniform one-arm bound to an infinite cluster

The events `clusterAtLeast G x n`, that the open cluster of `x` contains at least `n` vertices,
decrease in `n` and intersect in the event that the cluster is infinite.  Each of them is
measurable on a countable graph, so continuity from above turns a bound on the finite events that
does not depend on `n` into a bound on the percolation probability.  This is the only place where
the passage from finite to infinite happens, and after it every later argument may work with
finitely many vertices at a time.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set

variable {V : Type*}

/-- The event that the open cluster of `x` has at least `n` vertices. -/
def clusterAtLeast (G : SimpleGraph V) (x : V) (n : ℕ) : Set (Set V) :=
  {ω | ∃ F : Finset V, ↑F ⊆ siteCluster G ω x ∧ n ≤ F.card}

theorem mem_clusterAtLeast (G : SimpleGraph V) (x : V) (n : ℕ) (ω : Set V) :
    ω ∈ clusterAtLeast G x n ↔ ∃ F : Finset V, ↑F ⊆ siteCluster G ω x ∧ n ≤ F.card :=
  Iff.rfl

/-- A vertex lies in the open cluster of `x` exactly when the configuration joins `x` to it. -/
theorem mem_siteCluster_iff (G : SimpleGraph V) (ω : Set V) (x y : V) :
    y ∈ siteCluster G ω x ↔ ω ∈ siteConn G x y := Iff.rfl

/-- Asking for more vertices is asking for more: the one-arm events decrease in `n`. -/
theorem clusterAtLeast_antitone (G : SimpleGraph V) (x : V) :
    Antitone (clusterAtLeast G x) := by
  intro m n hmn ω hω
  obtain ⟨F, hF, hcard⟩ := hω
  exact ⟨F, hF, hmn.trans hcard⟩

/-- A cluster is infinite exactly when it contains a finite set of every size.  The empty cluster of
a closed vertex passes the test for `n = 0`, with the empty set, and fails it for `n = 1`, so the
intersection over all `n` is genuinely the infinite-cluster event. -/
theorem siteInfinite_eq_iInter_clusterAtLeast (G : SimpleGraph V) (x : V) :
    {ω : Set V | (siteCluster G ω x).Infinite} = ⋂ n, clusterAtLeast G x n := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter, mem_clusterAtLeast]
  constructor
  · intro hinf n
    obtain ⟨F, hF, hcard⟩ := hinf.exists_subset_card_eq n
    exact ⟨F, hF, hcard.ge⟩
  · intro h
    have hnot : ¬ (siteCluster G ω x).Finite := by
      intro hfin
      obtain ⟨F, hF, hcard⟩ := h (hfin.toFinset.card + 1)
      have hsub : F ⊆ hfin.toFinset := fun y hy => hfin.mem_toFinset.2 (hF hy)
      have := Finset.card_le_card hsub
      omega
    exact hnot

/-- The one-arm event as a countable union of finite intersections of connection events. -/
theorem clusterAtLeast_eq_iUnion (G : SimpleGraph V) (x : V) (n : ℕ) :
    clusterAtLeast G x n =
      ⋃ F ∈ {F : Finset V | n ≤ F.card}, ⋂ y ∈ (↑F : Set V), siteConn G x y := by
  ext ω
  simp only [mem_clusterAtLeast, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨F, hF, hcard⟩
    exact ⟨F, hcard, fun y hy => hF hy⟩
  · rintro ⟨F, hcard, hF⟩
    exact ⟨F, fun y hy => hF y hy, hcard⟩

/-- The one-arm event is measurable on a countable graph. -/
theorem measurableSet_clusterAtLeast [Countable V] (G : SimpleGraph V) (x : V) (n : ℕ) :
    MeasurableSet (clusterAtLeast G x n) := by
  rw [clusterAtLeast_eq_iUnion]
  refine MeasurableSet.biUnion (Set.to_countable _) fun F _ => ?_
  exact MeasurableSet.biInter F.finite_toSet.countable fun y _ => measurableSet_siteConn G x y

/-- **Continuity from above**: the probability that the cluster of `x` has at least `n` vertices
converges, as `n` grows, to the probability that it is infinite. -/
theorem tendsto_clusterAtLeast [Countable V] (G : SimpleGraph V) (x : V) (p : unitInterval) :
    Filter.Tendsto (fun n => (siteBernoulli (fun _ : V => p)).real (clusterAtLeast G x n))
      Filter.atTop (nhds (thetaSiteOn G x p)) := by
  have h := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := siteBernoulli (fun _ : V => p)) (s := clusterAtLeast G x)
    (fun n => (measurableSet_clusterAtLeast G x n).nullMeasurableSet)
    (clusterAtLeast_antitone G x) ⟨0, measure_ne_top _ _⟩
  rw [← siteInfinite_eq_iInter_clusterAtLeast] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top (siteBernoulli (fun _ : V => p))
    {ω : Set V | (siteCluster G ω x).Infinite})).comp h

/-- **A one-arm bound that does not depend on `n` forces an infinite cluster.** -/
theorem thetaSiteOn_pos_of_forall_le [Countable V] (G : SimpleGraph V) (x : V)
    (p : unitInterval) (c : ℝ) (hc : 0 < c)
    (h : ∀ n, c ≤ (siteBernoulli (fun _ : V => p)).real (clusterAtLeast G x n)) :
    0 < thetaSiteOn G x p :=
  lt_of_lt_of_le hc (ge_of_tendsto' (tendsto_clusterAtLeast G x p) h)

end KNAll.Site

end
