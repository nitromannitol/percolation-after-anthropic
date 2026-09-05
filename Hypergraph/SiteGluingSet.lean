import Hypergraph.SiteStatements

/-!
# The site gluing inequality with a set of sources

`SiteGluingUnpinned` glues at a single source vertex `o`.  The lattice arguments need the version
whose source is a set `S`, since otherwise each application has to enlarge the ambient graph by a
wiring vertex and the vertex type changes from one step to the next.  This module derives the
set-source form once and for all, so that everything downstream can stay on a fixed graph.

The device is the one the single-source statement is designed for.  Adjoin one vertex to the graph,
here `Fin.last n` of `Fin (n + 1)`, make it adjacent exactly to the vertices of `S`, and give it
weight `1`, so that it is open almost surely.  A path out of the added vertex leaves it through a
vertex of `S`, so the added vertex is joined to `x` exactly when some open vertex of `S` is
(`measureReal_root_biUnion`).  Applying `SiteGluingUnpinned` on the larger graph, with the added
vertex as source, therefore reads off as the desired inequality once both events are pushed back
along the embedding `Fin.castSucc`.

The added vertex also joins the vertices of `S` to one another, so connection probabilities on the
larger graph are larger than on `G`.  That is the harmless direction: it can only raise the minimum
`min_{a ∈ A} P(a ↔ b)`, which is the factor to be bounded below.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

/-! ## The restriction coupling for inhomogeneous site weights

`siteBernoulli_map_restrictSite` in `KN.SiteStatements` restricts the site measure along an
injection when every vertex carries the same weight.  The added vertex carries weight `1` and the
others carry `w`, so the inhomogeneous statement is needed; the proof is the one given there, and
the one `Percolation.Literature.prodBernoulli_map_restrictConfig` gives for bond percolation. -/

section Restriction

variable {V W : Type*}

/-- **The restriction coupling for inhomogeneous weights**: for injective `f`, restricting a site
configuration pushes site percolation with weights `w` forward to site percolation with weights
`w ∘ f`. -/
theorem siteBernoulli_map_restrictSite' (w : V → unitInterval) {f : W → V}
    (hf : Function.Injective f) :
    (siteBernoulli w).map (restrictSite f) = siteBernoulli (w ∘ f) := by
  have hSV : Measurable fun q : V → Prop => {i | q i} := measurable_setOf
  have hSW : Measurable fun q : W → Prop => {i | q i} := measurable_setOf
  rw [siteBernoulli, siteBernoulli, prodBernoulli_eq_map, prodBernoulli_eq_map,
    Measure.map_map (measurable_restrictSite f) hSV]
  have hcomp : (restrictSite (V := V) f ∘ fun q : V → Prop => {i | q i}) =
      (fun q : W → Prop => {i | q i}) ∘ fun (q : V → Prop) (a : W) => q (f a) := rfl
  rw [hcomp, ← Measure.map_map hSW (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj hf]
  rfl

/-- The probability of a pulled-back event is computed with the restricted weights. -/
theorem siteBernoulli_real_preimage_restrictSite (w : V → unitInterval) {f : W → V}
    (hf : Function.Injective f) {E : Set (SiteConfig W)} (hE : MeasurableSet E) :
    (siteBernoulli w).real (restrictSite f ⁻¹' E) = (siteBernoulli (w ∘ f)).real E := by
  rw [← siteBernoulli_map_restrictSite' w hf, map_measureReal_apply (measurable_restrictSite f) hE]

end Restriction

/-! ## Adjoining a root for the source set -/

section Root

variable {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))

/-- The embedding of the old vertices into the enlarged vertex set. -/
def rootEmb (n : ℕ) : Fin n ↪ Fin (n + 1) := ⟨Fin.castSucc, Fin.castSucc_injective n⟩

@[simp] theorem rootEmb_apply (m : ℕ) (i : Fin m) : rootEmb m i = i.castSucc := rfl

/-- `G` with one vertex adjoined, adjacent exactly to the vertices of `S`.  The added vertex is
`Fin.last n`, and the old vertices sit inside along `Fin.castSucc`. -/
def rootGraph : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel fun x y =>
    (∃ u v : Fin n, x = u.castSucc ∧ y = v.castSucc ∧ G.Adj u v) ∨
      (x = Fin.last n ∧ ∃ v ∈ S, y = v.castSucc)

/-- Old vertices keep exactly their old adjacencies. -/
theorem rootGraph_adj_castSucc (u v : Fin n) :
    (rootGraph G S).Adj u.castSucc v.castSucc ↔ G.Adj u v := by
  rw [rootGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, (⟨u', v', hu, hv, hadj⟩ | ⟨hlast, -⟩) | (⟨u', v', hu, hv, hadj⟩ | ⟨hlast, -⟩)⟩
    · obtain rfl := Fin.castSucc_injective n hu
      obtain rfl := Fin.castSucc_injective n hv
      exact hadj
    · exact absurd hlast (Fin.castSucc_ne_last u)
    · obtain rfl := Fin.castSucc_injective n hu
      obtain rfl := Fin.castSucc_injective n hv
      exact hadj.symm
    · exact absurd hlast (Fin.castSucc_ne_last v)
  · intro hadj
    exact ⟨fun he => hadj.ne (Fin.castSucc_injective n he),
      Or.inl (Or.inl ⟨u, v, rfl, rfl, hadj⟩)⟩

/-- The added vertex is adjacent exactly to the vertices of `S`. -/
theorem rootGraph_adj_last (v : Fin n) :
    (rootGraph G S).Adj (Fin.last n) v.castSucc ↔ v ∈ S := by
  rw [rootGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, (⟨u', -, hu, -, -⟩ | ⟨-, v'', hv'', hv'⟩) | (⟨-, v', -, hv, -⟩ | ⟨hlast, -⟩)⟩
    · exact absurd hu.symm (Fin.castSucc_ne_last u')
    · obtain rfl := Fin.castSucc_injective n hv'
      exact hv''
    · exact absurd hv.symm (Fin.castSucc_ne_last v')
    · exact absurd hlast (Fin.castSucc_ne_last v)
  · intro hv
    exact ⟨fun he => Fin.castSucc_ne_last v he.symm, Or.inl (Or.inr ⟨rfl, v, hv, rfl⟩)⟩

/-- The weights of the enlarged graph: the old ones, and `1` at the added vertex. -/
def rootWeight {m : ℕ} (w : Fin m → unitInterval) : Fin (m + 1) → unitInterval :=
  Fin.snoc w 1

@[simp] theorem rootWeight_castSucc {m : ℕ} (w : Fin m → unitInterval) (i : Fin m) :
    rootWeight w i.castSucc = w i := by
  simp [rootWeight]

@[simp] theorem rootWeight_last {m : ℕ} (w : Fin m → unitInterval) :
    rootWeight w (Fin.last m) = 1 := by
  simp [rootWeight]

theorem rootWeight_comp_castSucc {m : ℕ} (w : Fin m → unitInterval) :
    rootWeight w ∘ Fin.castSucc = w := by
  simp [rootWeight]

/-- An open path of `G` is an open path of the enlarged graph. -/
theorem reachable_castSucc_of_reachable (ω : SiteConfig (Fin (n + 1))) {x y : Fin n}
    (h : (openSiteGraph G (restrictSite Fin.castSucc ω)).Reachable x y) :
    (openSiteGraph (rootGraph G S) ω).Reachable x.castSucc y.castSucc := by
  refine h.map ⟨Fin.castSucc, fun {a b} hab => ?_⟩
  rw [openSiteGraph_adj_iff'] at hab ⊢
  exact ⟨(rootGraph_adj_castSucc G S a b).2 hab.1, hab.2.1, hab.2.2⟩

/-- The invariant carried along an open path out of the added vertex: every old vertex reached is
joined inside `G` to an open vertex of `S`. -/
def RootGood (ω : SiteConfig (Fin (n + 1))) : Fin (n + 1) → Prop := fun q =>
  q = Fin.last n ∨
    ∃ y : Fin n, q = y.castSucc ∧
      restrictSite Fin.castSucc ω ∈ ⋃ s ∈ (S : Set (Fin n)), siteConn G s y

theorem rootGood_step (ω : SiteConfig (Fin (n + 1))) {q q' : Fin (n + 1)}
    (hq : RootGood G S ω q) (hadj : (openSiteGraph (rootGraph G S) ω).Adj q q') :
    RootGood G S ω q' := by
  rcases eq_or_ne q' (Fin.last n) with rfl | hq'
  · exact Or.inl rfl
  obtain ⟨z, rfl⟩ : ∃ z : Fin n, q' = z.castSucc :=
    ⟨q'.castPred hq', (Fin.castSucc_castPred q' hq').symm⟩
  rw [openSiteGraph_adj_iff'] at hadj
  obtain ⟨hGadj, hqmem, hzmem⟩ := hadj
  rcases hq with rfl | ⟨y, rfl, hy⟩
  · refine Or.inr ⟨z, rfl, Set.mem_biUnion ?_ ⟨hzmem, SimpleGraph.Reachable.refl z⟩⟩
    exact Finset.mem_coe.2 ((rootGraph_adj_last G S z).1 hGadj)
  · obtain ⟨s, hs, hconn⟩ := Set.mem_iUnion₂.1 hy
    have hGyz : G.Adj y z := (rootGraph_adj_castSucc G S y z).1 hGadj
    refine Or.inr ⟨z, rfl, Set.mem_biUnion hs ⟨hconn.1, hconn.2.trans ?_⟩⟩
    exact SimpleGraph.Adj.reachable
      ((openSiteGraph_adj_iff' G (restrictSite Fin.castSucc ω) y z).2 ⟨hGyz, hqmem, hzmem⟩)

theorem rootGood_of_walk (ω : SiteConfig (Fin (n + 1))) : ∀ {a q : Fin (n + 1)},
    (openSiteGraph (rootGraph G S) ω).Walk a q → RootGood G S ω a → RootGood G S ω q := by
  intro a q p
  induction p with
  | nil => exact fun hg => hg
  | cons hadj q ih => exact fun hg => ih (rootGood_step G S ω hg hadj)

/-- **A path out of the added vertex leaves it through `S`.**  If the added vertex reaches the old
vertex `x`, then some open vertex of `S` is joined to `x` inside `G`. -/
theorem mem_biUnion_siteConn_of_reachable_root (ω : SiteConfig (Fin (n + 1))) (x : Fin n)
    (h : (openSiteGraph (rootGraph G S) ω).Reachable (Fin.last n) x.castSucc) :
    restrictSite Fin.castSucc ω ∈ ⋃ s ∈ (S : Set (Fin n)), siteConn G s x := by
  obtain ⟨p⟩ := h
  rcases rootGood_of_walk G S ω p (Or.inl rfl) with hlast | ⟨y, hy, hconn⟩
  · exact absurd hlast (Fin.castSucc_ne_last x)
  · obtain rfl := Fin.castSucc_injective n hy
    exact hconn

/-- The converse, when the added vertex is open. -/
theorem mem_siteConn_root (ω : SiteConfig (Fin (n + 1))) (hroot : Fin.last n ∈ ω) (x : Fin n)
    (h : restrictSite Fin.castSucc ω ∈ ⋃ s ∈ (S : Set (Fin n)), siteConn G s x) :
    ω ∈ siteConn (rootGraph G S) (Fin.last n) x.castSucc := by
  obtain ⟨s, hs, hconn⟩ := Set.mem_iUnion₂.1 h
  refine ⟨hroot, ?_⟩
  have hadj : (openSiteGraph (rootGraph G S) ω).Adj (Fin.last n) s.castSucc :=
    (openSiteGraph_adj_iff' _ _ _ _).2
      ⟨(rootGraph_adj_last G S s).2 (Finset.mem_coe.1 hs), hroot, hconn.1⟩
  exact hadj.reachable.trans (reachable_castSucc_of_reachable G S ω hconn.2)

/-- **The event identity, in measure.**  The added vertex reaches some vertex of `T` exactly when
some open vertex of `S` does, up to the null event that the added vertex is closed. -/
theorem measureReal_root_biUnion (w : Fin n → unitInterval) (T : Set (Fin n)) :
    (siteBernoulli (rootWeight w)).real
        (⋃ t ∈ T, siteConn (rootGraph G S) (Fin.last n) t.castSucc) =
      (siteBernoulli w).real (⋃ t ∈ T, ⋃ s ∈ (S : Set (Fin n)), siteConn G s t) := by
  have hE : MeasurableSet (⋃ t ∈ T, ⋃ s ∈ (S : Set (Fin n)), siteConn G s t) :=
    MeasurableSet.biUnion (Set.to_countable T) fun t _ =>
      MeasurableSet.biUnion (Set.to_countable _) fun s _ => measurableSet_siteConn G s t
  have hroot : ∀ᵐ ω ∂(siteBernoulli (rootWeight w)), Fin.last n ∈ ω :=
    prodBernoulli_ae_mem_of_eq_one (rootWeight w) (rootWeight_last w)
  have hmap : (siteBernoulli (rootWeight w)).real (restrictSite Fin.castSucc ⁻¹'
      (⋃ t ∈ T, ⋃ s ∈ (S : Set (Fin n)), siteConn G s t))
      = (siteBernoulli w).real (⋃ t ∈ T, ⋃ s ∈ (S : Set (Fin n)), siteConn G s t) := by
    rw [siteBernoulli_real_preimage_restrictSite (rootWeight w) (Fin.castSucc_injective n) hE,
      rootWeight_comp_castSucc]
  rw [← hmap]
  refine measureReal_congr (Filter.eventuallyEq_set.2 ?_)
  filter_upwards [hroot] with ω hω
  constructor
  · intro hmem
    obtain ⟨t, ht, hconn⟩ := Set.mem_iUnion₂.1 hmem
    exact Set.mem_preimage.2
      (Set.mem_biUnion ht (mem_biUnion_siteConn_of_reachable_root G S ω t hconn.2))
  · intro hmem
    obtain ⟨t, ht, hconn⟩ := Set.mem_iUnion₂.1 (Set.mem_preimage.1 hmem)
    exact Set.mem_biUnion ht (mem_siteConn_root G S ω hω t hconn)

end Root

/-! ## The set-source gluing inequality -/

/-- **The gluing inequality with a set of sources.**  From the single-source form: adjoin a vertex
adjacent exactly to `S` and open almost surely, apply the single-source form there with the added
vertex as observer and the images of `A` and `b` as relay set and target, and push both events back
along `Fin.castSucc`.

Only `b ∉ A` is used.  The two hypotheses on `S` are carried because the statement is the one the
lattice modules ask for; the added vertex is distinct from `Fin.castSucc b` and lies outside the
image of `A` by construction, which is what the distinctness hypotheses of `SiteGluingUnpinned`
require. -/
theorem siteGluingSet_of_unpinned (h : SiteGluingUnpinned) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → unitInterval) (S : Finset (Fin n))
        (A : Finset (Fin n)) (hA : A.Nonempty) (b : Fin n),
      (∀ s ∈ S, s ∉ A) → b ∉ A → (∀ s ∈ S, s ≠ b) →
      (siteBernoulli w).real (⋃ s ∈ (S : Set (Fin n)), siteConnSet G s ↑A) *
          A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b)) ≤
        (siteBernoulli w).real (⋃ s ∈ (S : Set (Fin n)), siteConn G s b) := by
  intro n G w S A hA b _ hbA _
  have hA' : (A.map (rootEmb n)).Nonempty := hA.map
  -- The distinctness hypotheses of the single-source form.
  have hne : Fin.last n ≠ b.castSucc := (Fin.castSucc_ne_last b).symm
  have hoA : Fin.last n ∉ A.map (rootEmb n) := by
    intro hmem
    obtain ⟨a, -, ha⟩ := Finset.mem_map.1 hmem
    exact Fin.castSucc_ne_last a ha
  have hbA' : b.castSucc ∉ A.map (rootEmb n) := by
    intro hmem
    obtain ⟨a, ha, heq⟩ := Finset.mem_map.1 hmem
    have hab : a = b := Fin.castSucc_injective n heq
    exact hbA (hab ▸ ha)
  have key := h (n + 1) (rootGraph G S) (rootWeight w) (A.map (rootEmb n)) hA'
    (Fin.last n) b.castSucc hne hoA hbA'
  -- The source event.
  have hswap : (⋃ t ∈ (↑A : Set (Fin n)), ⋃ s ∈ (S : Set (Fin n)), siteConn G s t)
      = ⋃ s ∈ (S : Set (Fin n)), siteConnSet G s ↑A := by
    simp only [siteConnSet]
    apply Set.Subset.antisymm
    · intro ω hω
      obtain ⟨t, ht, hts⟩ := Set.mem_iUnion₂.1 hω
      obtain ⟨s, hs, hc⟩ := Set.mem_iUnion₂.1 hts
      exact Set.mem_biUnion hs (Set.mem_biUnion ht hc)
    · intro ω hω
      obtain ⟨s, hs, hst⟩ := Set.mem_iUnion₂.1 hω
      obtain ⟨t, ht, hc⟩ := Set.mem_iUnion₂.1 hst
      exact Set.mem_biUnion ht (Set.mem_biUnion hs hc)
  have h1 : (siteBernoulli (rootWeight w)).real
        (siteConnSet (rootGraph G S) (Fin.last n) ↑(A.map (rootEmb n)))
      = (siteBernoulli w).real (⋃ s ∈ (S : Set (Fin n)), siteConnSet G s ↑A) := by
    have hcoe : (↑(A.map (rootEmb n)) : Set (Fin (n + 1))) = Fin.castSucc '' (↑A : Set (Fin n)) := by
      rw [Finset.coe_map]; rfl
    have hset : siteConnSet (rootGraph G S) (Fin.last n) ↑(A.map (rootEmb n))
        = ⋃ t ∈ (↑A : Set (Fin n)), siteConn (rootGraph G S) (Fin.last n) t.castSucc := by
      simp only [siteConnSet, hcoe]
      exact Set.biUnion_image
    rw [hset, measureReal_root_biUnion G S w (↑A : Set (Fin n)), hswap]
  -- The minimum over the relay set can only go up on the larger graph.
  have h2 : A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b))
      ≤ (A.map (rootEmb n)).inf' hA' (fun a => (siteBernoulli (rootWeight w)).real
          (siteConn (rootGraph G S) a b.castSucc)) := by
    refine Finset.le_inf' hA' _ ?_
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 ha'
    refine le_trans (Finset.inf'_le _ ha) ?_
    have hsub : restrictSite Fin.castSucc ⁻¹' (siteConn G a b)
        ⊆ siteConn (rootGraph G S) a.castSucc b.castSucc := by
      intro ω hω
      have hω' : restrictSite Fin.castSucc ω ∈ siteConn G a b := hω
      exact ⟨hω'.1, reachable_castSucc_of_reachable G S ω hω'.2⟩
    calc (siteBernoulli w).real (siteConn G a b)
        = (siteBernoulli (rootWeight w)).real
            (restrictSite Fin.castSucc ⁻¹' (siteConn G a b)) := by
          rw [siteBernoulli_real_preimage_restrictSite (rootWeight w) (Fin.castSucc_injective n)
            (measurableSet_siteConn G a b), rootWeight_comp_castSucc]
      _ ≤ (siteBernoulli (rootWeight w)).real
            (siteConn (rootGraph G S) a.castSucc b.castSucc) :=
          measureReal_mono hsub (measure_ne_top _ _)
  -- The target event.
  have h3 : (siteBernoulli (rootWeight w)).real
        (siteConn (rootGraph G S) (Fin.last n) b.castSucc)
      = (siteBernoulli w).real (⋃ s ∈ (S : Set (Fin n)), siteConn G s b) := by
    have hb := measureReal_root_biUnion G S w ({b} : Set (Fin n))
    rwa [Set.biUnion_singleton, Set.biUnion_singleton] at hb
  calc (siteBernoulli w).real (⋃ s ∈ (S : Set (Fin n)), siteConnSet G s ↑A) *
        A.inf' hA (fun a => (siteBernoulli w).real (siteConn G a b))
      ≤ (siteBernoulli (rootWeight w)).real
            (siteConnSet (rootGraph G S) (Fin.last n) ↑(A.map (rootEmb n))) *
          (A.map (rootEmb n)).inf' hA' (fun a => (siteBernoulli (rootWeight w)).real
            (siteConn (rootGraph G S) a b.castSucc)) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 measureReal_nonneg
    _ ≤ (siteBernoulli (rootWeight w)).real
          (siteConn (rootGraph G S) (Fin.last n) b.castSucc ∩
            siteConnSet (rootGraph G S) (Fin.last n) ↑(A.map (rootEmb n))) := key
    _ ≤ (siteBernoulli (rootWeight w)).real
          (siteConn (rootGraph G S) (Fin.last n) b.castSucc) :=
        measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
    _ = (siteBernoulli w).real (⋃ s ∈ (S : Set (Fin n)), siteConn G s b) := h3

end KNAll.Site

end
