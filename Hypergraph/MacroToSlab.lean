import Hypergraph.SiteOneArm

/-!
# Counting the sites contributed by occupied cells

The renormalisation argument runs on a coarse lattice whose vertices stand for disjoint blocks of
actual sites, and it produces, for each occupied coarse vertex, one genuine site of that block
joined to the origin by an open path.  To read off an infinite cluster one has to convert a supply
of occupied coarse vertices into a supply of distinct sites of the cluster.  Disjointness of the
blocks is exactly what makes the conversion work: two different coarse vertices cannot hand back
the same site, so the chosen sites number as many as the coarse vertices do.

The file carries no geometry.  A cell is any family of sets indexed by an arbitrary type, and the
hypotheses are that the cells are pairwise disjoint and that each occupied index comes with a
representative lying both in its own cell and in the cluster of `x`.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set

variable {V M : Type*}

/-- Representatives chosen from pairwise disjoint cells are pairwise distinct.  If two indices had
the same representative, that site would lie in both of their cells. -/
theorem injOn_of_disjoint_cells (cell : M → Set V)
    (hdisj : ∀ m m' : M, m ≠ m' → Disjoint (cell m) (cell m'))
    (occ : Finset M) (rep : M → V) (hrep : ∀ m ∈ occ, rep m ∈ cell m) :
    Set.InjOn rep ↑occ := by
  intro m hm m' hm' hEq
  by_contra hne
  have h1 : rep m ∈ cell m := hrep m (Finset.mem_coe.1 hm)
  have h2 : rep m ∈ cell m' := by
    rw [hEq]; exact hrep m' (Finset.mem_coe.1 hm')
  exact Set.disjoint_left.1 (hdisj m m' hne) h1 h2

/-- Asking for no vertices asks for nothing: the empty finset witnesses the event. -/
theorem clusterAtLeast_zero (G : SimpleGraph V) (x : V) :
    clusterAtLeast G x 0 = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨∅, by simp, Nat.zero_le _⟩

/-- **The counting step.**  Occupied cells with representatives in the cluster of `x` force the
cluster to have at least as many vertices as there are occupied cells.  For `occ = ∅` the
conclusion is the trivial event `clusterAtLeast G x 0`, witnessed by the empty finset. -/
theorem clusterAtLeast_of_cells (G : SimpleGraph V) (ω : Set V) (x : V)
    (cell : M → Set V) (hdisj : ∀ m m' : M, m ≠ m' → Disjoint (cell m) (cell m'))
    (occ : Finset M) (rep : M → V)
    (hrep : ∀ m ∈ occ, rep m ∈ cell m)
    (hcl : ∀ m ∈ occ, rep m ∈ siteCluster G ω x) :
    ω ∈ clusterAtLeast G x occ.card := by
  classical
  rw [mem_clusterAtLeast]
  refine ⟨occ.image rep, ?_, ?_⟩
  · intro y hy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
    obtain ⟨m, hm, rfl⟩ := hy
    exact hcl m hm
  · exact (Finset.card_image_of_injOn
      (injOn_of_disjoint_cells cell hdisj occ rep hrep)).ge

/-- **The consequence used by the renormalisation construction.**  A lower bound, uniform in `n`,
on the probability of finding `n` occupied cells with representatives in the cluster of `x` makes
the percolation probability positive. -/
theorem thetaSiteOn_pos_of_cells [Countable V] (G : SimpleGraph V) (x : V)
    (p : unitInterval) (cell : M → Set V)
    (hdisj : ∀ m m' : M, m ≠ m' → Disjoint (cell m) (cell m'))
    (c : ℝ) (hc : 0 < c)
    (h : ∀ n : ℕ, c ≤ (siteBernoulli (fun _ : V => p)).real
          {ω | ∃ (occ : Finset M) (rep : M → V), n ≤ occ.card ∧
                (∀ m ∈ occ, rep m ∈ cell m) ∧ (∀ m ∈ occ, rep m ∈ siteCluster G ω x)}) :
    0 < thetaSiteOn G x p := by
  refine thetaSiteOn_pos_of_forall_le G x p c hc fun n => ?_
  refine (h n).trans (measureReal_mono ?_ (measure_ne_top _ _))
  rintro ω ⟨occ, rep, hcard, hrep, hcl⟩
  exact clusterAtLeast_antitone G x hcard
    (clusterAtLeast_of_cells G ω x cell hdisj occ rep hrep hcl)

/-! ## Cells that are single sites

The construction sometimes hands back one distinguished site per coarse vertex rather than a whole
block.  An injection provides such a family, and its singleton images are pairwise disjoint. -/

/-- Singletons taken along an injection form a pairwise disjoint family, in the shape the
hypothesis `hdisj` above asks for. -/
theorem disjoint_singleton_cells {f : M → V} (hf : Function.Injective f) :
    ∀ m m' : M, m ≠ m' → Disjoint ({f m} : Set V) ({f m'} : Set V) := by
  intro m m' hne
  rw [Set.disjoint_singleton_left, Set.mem_singleton_iff]
  exact fun hEq => hne (hf hEq)

/-- The counting step for single-site cells: an injection `f` and a uniform bound on the
probability of finding `n` indices with `f m` in the cluster of `x` make the percolation
probability positive. -/
theorem thetaSiteOn_pos_of_injective_sites [Countable V] (G : SimpleGraph V) (x : V)
    (p : unitInterval) (f : M → V) (hf : Function.Injective f) (c : ℝ) (hc : 0 < c)
    (h : ∀ n : ℕ, c ≤ (siteBernoulli (fun _ : V => p)).real
          {ω | ∃ occ : Finset M, n ≤ occ.card ∧ ∀ m ∈ occ, f m ∈ siteCluster G ω x}) :
    0 < thetaSiteOn G x p := by
  refine thetaSiteOn_pos_of_cells G x p (fun m => ({f m} : Set V))
    (disjoint_singleton_cells hf) c hc fun n => ?_
  refine (h n).trans (measureReal_mono ?_ (measure_ne_top _ _))
  rintro ω ⟨occ, hcard, hcl⟩
  exact ⟨occ, f, hcard, fun m _ => rfl, hcl⟩

end KNAll.Site

end
