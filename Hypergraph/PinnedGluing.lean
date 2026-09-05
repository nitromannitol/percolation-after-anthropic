import Hypergraph.SiteRepresentation

/-!
# The pinned site gluing inequality

`PinnedSiteGluing` is the form of the gluing inequality that the lattice argument consumes: the
observer `o`, the target `b` and every relay of `A` are open with probability one, and no two of
them are assumed distinct.  This module derives it from `HyperedgeGluing`.

The derivation goes through the port representation of `KN/SiteRepresentation.lean`, not through
`SiteGluingUnpinned`.  The reason is that the hyperedge inequality itself carries no distinctness
hypothesis, so the only thing to repair is the dictionary between the two connection events, and
that dictionary fails only on the diagonal: `hyperConn` is reflexive while `siteConn G x x` is the
event that `x` is open.  Each of the three places where the diagonal can appear is handled by an
inequality rather than an identity.

* On the left, a site connection is a chain of open labels, so `siteConnSet G o A` is contained in
  the hyperedge union and each `siteConn G a b` is contained in the corresponding `hyperConn`.
  Both comparisons point the right way and need no pinning at all, the diagonal included.
* On the right, the hyperedge conclusion is an intersection, which is smaller than
  `hyperConn (inl o) (inl b)`.  For `o ≠ b` that set is `siteConn G o b`.  For `o = b` it is
  everything, and there `w o = 1` makes `siteConn G o o` have probability one, so the bound is
  the trivial one.

So `w o = 1` is used once, and only in the degenerate case `o = b`.  The pinning of `b` and of the
relays is never needed.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {V : Type*}

/-- A vertex of probability one is almost surely open, so it is almost surely connected to
itself. -/
theorem siteBernoulli_real_siteConn_self (G : SimpleGraph V) (w : V → unitInterval) {x : V}
    (hx : w x = 1) : (siteBernoulli w).real (siteConn G x x) = 1 := by
  have h : (siteBernoulli w).real {ω : SiteConfig V | x ∈ ω} = (w x : ℝ) :=
    prodBernoulli_real_setOf_mem w x
  rw [siteConn_self, h, hx]
  simp

/-- An open site path is in particular a chain of open labels, so the site connection event is
contained in the hyperedge connection event of the port representation.  This holds on the diagonal
too, where the right-hand side is everything. -/
theorem siteConn_subset_hyperConn (G : SimpleGraph V) (w : V → unitInterval) (x y : V) :
    siteConn G x y ⊆ hyperConn (portHypergraph G w) (Sum.inl x) (Sum.inl y) :=
  fun ω hω => reachable_hyper_of_site G w ω hω.2

/-- **The pinned transfer.**  The finite hyperedge inequality gives the site inequality in the form
used by the lattice argument, with the observer, the target and the relays open with probability
one and no distinctness assumed. -/
theorem pinnedSiteGluing_of_hyperedgeGluing (h : HyperedgeGluing) : PinnedSiteGluing := by
  intro n G w A hA o b ho _hb _hAw
  classical
  set H := portHypergraph G w with hH
  set e : Fin n ↪ PortVertex (Fin n) := ⟨Sum.inl, Sum.inl_injective⟩ with he
  have hA' : (A.map e).Nonempty := hA.map
  have key := h (PortVertex (Fin n)) (Fin n) H (A.map e) hA' (Sum.inl o) (Sum.inl b)
  have hmeas : (prodBernoulli H.prob) = siteBernoulli w := rfl
  rw [hmeas] at key
  -- The site union is contained in the hyperedge union, on the diagonal as well.
  have hsub : siteConnSet G o ↑A ⊆ ⋃ a ∈ A.map e, hyperConn H (Sum.inl o) a := by
    intro ω hω
    simp only [siteConnSet, Set.mem_iUnion, Finset.mem_coe, exists_prop] at hω
    obtain ⟨a, ha, hωa⟩ := hω
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨e a, Finset.mem_map_of_mem e ha, siteConn_subset_hyperConn G w o a hωa⟩
  -- Termwise the site minimum is at most the hyperedge minimum.
  have hinf : A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b))
      ≤ (A.map e).inf' hA' (fun q => (siteBernoulli w).real (hyperConn H q (Sum.inl b))) := by
    refine Finset.le_inf' hA' _ ?_
    intro q hq
    rw [Finset.mem_map] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    exact le_trans (Finset.inf'_le _ ha)
      (measureReal_mono (siteConn_subset_hyperConn G w a b) (measure_ne_top _ _))
  -- The hyperedge conclusion is at most the site connection probability, the diagonal included.
  have hR : (siteBernoulli w).real (hyperConn H (Sum.inl o) (Sum.inl b) ∩
        ⋃ a ∈ A.map e, hyperConn H (Sum.inl o) a) ≤ (siteBernoulli w).real (siteConn G o b) := by
    rcases eq_or_ne o b with rfl | hob
    · rw [siteBernoulli_real_siteConn_self G w ho]
      exact measureReal_le_one
    · refine le_of_le_of_eq (measureReal_mono Set.inter_subset_left (measure_ne_top _ _)) ?_
      rw [hH, hyperConn_eq_siteConn G w hob]
  have hnonneg : (0 : ℝ) ≤ A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b)) :=
    Finset.le_inf' hA _ fun a _ => measureReal_nonneg
  calc (siteBernoulli w).real (siteConnSet G o ↑A) *
        A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b))
      ≤ (siteBernoulli w).real (⋃ a ∈ A.map e, hyperConn H (Sum.inl o) a) *
          (A.map e).inf' hA' (fun q => (siteBernoulli w).real (hyperConn H q (Sum.inl b))) :=
        mul_le_mul (measureReal_mono hsub (measure_ne_top _ _)) hinf hnonneg measureReal_nonneg
    _ ≤ (siteBernoulli w).real (hyperConn H (Sum.inl o) (Sum.inl b) ∩
          ⋃ a ∈ A.map e, hyperConn H (Sum.inl o) a) := key
    _ ≤ (siteBernoulli w).real (siteConn G o b) := hR

end KNAll.Site

end
