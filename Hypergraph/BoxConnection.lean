import Hypergraph.RenormData

/-!
# Connections confined to a box

`siteConn G x y` is not a cylinder event: an open path from `x` to `y` may use vertices arbitrarily
far away, so no finite set of sites determines whether it occurs.  Every probabilistic estimate the
renormalization argument transports from one parameter to a nearby one has to be a cylinder event,
in the sense of `KNAll.Site.CylinderExperiment`, because that is what makes the probability Lipschitz
in the parameter.

This module supplies the confined form.  `connWithin G S x y` asks for an open path from `x` to `y`
all of whose vertices lie in `S`, which is decided by the states of the sites of `S` alone
(`determinedBy_connWithin`).  When `S` is finite the event is therefore measurable
(`measurableSet_connWithin`), and `cylinderOfConn` packages it as a `CylinderExperiment` on `ℤ^d`.
The event is increasing (`isUpperSet_connWithin`), and it implies the unconfined connection
(`connWithin_subset_siteConn`), which is what lets an estimate proved inside a box be used to draw a
conclusion about the true open cluster.

Note that the confining set enters twice: a vertex counts as open for `connWithin G S x y` only when
it is open *and* in `S`.  This is what makes the event depend on `S` alone; the sites outside `S`
are read as closed.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

section Confined

variable {V : Type*}

/-- The event that `x` and `y` are joined by a path all of whose vertices are open and lie in `S`.
Sites outside `S` are read as closed, so the event depends only on the states of the sites of `S`. -/
def connWithin (G : SimpleGraph V) (S : Set V) (x y : V) : Set (SiteConfig V) :=
  {ω | x ∈ ω ∩ S ∧ (openSiteGraph G (ω ∩ S)).Reachable x y}

theorem mem_connWithin_iff (G : SimpleGraph V) (S : Set V) (x y : V) (ω : SiteConfig V) :
    ω ∈ connWithin G S x y ↔ x ∈ ω ∩ S ∧ (openSiteGraph G (ω ∩ S)).Reachable x y := Iff.rfl

/-- Opening more vertices opens more edges.  A local copy of the monotonicity of `openSiteGraph`,
proved here so that this module depends on nothing beyond `KN.RenormData`. -/
private theorem openSiteGraph_mono_of_subset (G : SimpleGraph V) {ω ω' : SiteConfig V}
    (h : ω ⊆ ω') : openSiteGraph G ω ≤ openSiteGraph G ω' := by
  refine SimpleGraph.le_iff_adj.2 fun a b hab => ?_
  rw [openSiteGraph_adj_iff'] at hab ⊢
  exact ⟨hab.1, h hab.2.1, h hab.2.2⟩

/-- **Target 1.**  The confined connection is a cylinder event on `S`: two configurations with the
same trace on `S` have the same intersection with `S`, and the event mentions the configuration only
through that intersection. -/
theorem determinedBy_connWithin (G : SimpleGraph V) (S : Set V) (x y : V) :
    DeterminedBy (connWithin G S x y) S := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [connWithin, Set.mem_setOf_eq, h]

/-- **Target 2.**  Opening further sites can only create connections, never destroy them. -/
theorem isUpperSet_connWithin (G : SimpleGraph V) (S : Set V) (x y : V) :
    IsUpperSet (connWithin G S x y) := by
  rintro ω ω' hle ⟨hx, hr⟩
  have hsub : ω ∩ S ⊆ ω' ∩ S := Set.inter_subset_inter hle Subset.rfl
  exact ⟨hsub hx, hr.mono (openSiteGraph_mono_of_subset G hsub)⟩

/-- **Target 3.**  Over a finite confining set the event is measurable, being determined by finitely
many sites and hence a finite union of finite-dimensional cylinders. -/
theorem measurableSet_connWithin (G : SimpleGraph V) (S : Finset V) (x y : V) :
    MeasurableSet (connWithin G (↑S : Set V) x y) :=
  (determinedBy_connWithin G (↑S : Set V) x y).measurableSet_of_finset

/-- **Target 5.**  A path inside `S` is a path: the confined connection implies the unconfined one.
No hypothesis on `x` or `y` is needed, because membership in `S` is already part of the confined
event. -/
theorem connWithin_subset_siteConn (G : SimpleGraph V) (S : Set V) (x y : V) :
    connWithin G S x y ⊆ siteConn G x y := by
  rintro ω ⟨hx, hr⟩
  exact ⟨hx.1, hr.mono (openSiteGraph_mono_of_subset G Set.inter_subset_left)⟩

end Confined

/-! ## Packaging as a cylinder experiment on `ℤ^d` -/

variable {d : ℕ}

/-- **Target 4.**  The confined connection inside a finite set of sites of `ℤ^d`, packaged with the
two facts that make it usable by the renormalization argument: it depends on the sites of `S` only,
and it is measurable. -/
def cylinderOfConn (S : Finset (Site d)) (x y : Site d) : CylinderExperiment d where
  support := S
  event := connWithin (zdGraph d) (↑S : Set (Site d)) x y
  determined := determinedBy_connWithin (zdGraph d) (↑S : Set (Site d)) x y
  measurable' := measurableSet_connWithin (zdGraph d) S x y

@[simp] theorem cylinderOfConn_support (S : Finset (Site d)) (x y : Site d) :
    (cylinderOfConn S x y).support = S := rfl

@[simp] theorem cylinderOfConn_event (S : Finset (Site d)) (x y : Site d) :
    (cylinderOfConn S x y).event = connWithin (zdGraph d) (↑S : Set (Site d)) x y := rfl

/-- The probability carried by the packaged event is the probability of the confined connection at
the constant parameter `q`. -/
theorem cylinderOfConn_prob (S : Finset (Site d)) (x y : Site d) (q : unitInterval) :
    (cylinderOfConn S x y).prob q
      = (siteBernoulli (fun _ : Site d => q)).real
          (connWithin (zdGraph d) (↑S : Set (Site d)) x y) := rfl

end KNAll.Site

end
