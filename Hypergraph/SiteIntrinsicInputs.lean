import Hypergraph.BoxConnection
import Hypergraph.RenormStable
import Hypergraph.SiteLocalInputs
import Hypergraph.SiteThetaMono

/-!
# The local inputs of the geometric construction, stated inside a finite box

`SiteLocalInputs d p` of `KN/SiteLocalInputs.lean` carries two hypotheses, `coalescence` and
`faceHit`, and states both with the ambient connectivity of the infinite lattice, `siteConn` and
`siteCluster`.  An ambient connection may be witnessed by an open path leaving every box, so neither
hypothesis is decided by the states of finitely many sites.  That is not a cosmetic matter: the whole
below-parameter route of `KN/RenormStable.lean` moves an estimate from one parameter to a nearby one
through `CylinderExperiment.abs_prob_sub_le`, whose Lipschitz constant is the cardinality of a finite
support, and an event with no finite support has no such constant.

This module states both inputs with connections confined to a named finite box, proves that the
confined events are cylinder events on that box, and proves that the ambient statements imply the
confined ones at the cost of one further finite radius.

The transfer is not a restriction of the ambient statement to a box, and cannot be, because
confinement moves the two halves of each statement in opposite directions.

* Confining makes a connection *harder*.  In `faceHit` the connection is asserted, so the confined
  event is smaller than the ambient one and its probability can only drop; a lower bound on the
  ambient event says nothing about it.
* In `coalescence` the failure of a connection is asserted, so the confined failure event is *larger*
  than the ambient one, and an upper bound on the ambient event again says nothing about it.

In both cases the remedy is the same.  The confined connections inside `box d N` increase, as `N`
grows, to the ambient connection, because an open path has finitely many vertices and so lies in some
box (`iUnion_connWithin_box`).  Continuity of the measure along that increasing family produces a
single finite outer radius `N` at which the confined statement holds with an error as small as
prescribed.  The inner scale that the geometry names, `m` for the faces and `M` for the annulus, is
kept fixed while `N` grows, so the outer box is a thickening of the box the construction cares
about.

The two facts transferred are `exists_localFaceEvent_ge` and `exists_localCoalescenceEvent_le`; they
are collected in the structure `SiteIntrinsicInputs`, which is the interface meant to replace
`SiteLocalInputs`, and the bridge is `siteIntrinsicInputs_of_siteLocalInputs`.  The two bounds are
packaged for the certificate machinery as `faceExperiment` and `coalescenceExperiment`, and
`faceExperiment_abs_prob_sub_le` and `coalescenceExperiment_abs_prob_sub_le` record the Lipschitz
estimate that the ambient statements have no claim to, with the explicit constant `(2N+1)^d`.

Percolation is not used anywhere below.  The ambient statements are hypotheses, exactly as in
`KN/SiteLocalInputs.lean`, and the transfer to a finite box is a statement about measures on the
configuration space that holds at every parameter.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Confined connectivity -/

section Confined

variable {V : Type*}

/-- Enlarging the confining set can only create confined connections. -/
theorem connWithin_mono_set (G : SimpleGraph V) {S S' : Set V} (hS : S ⊆ S') (x y : V) :
    connWithin G S x y ⊆ connWithin G S' x y := by
  rintro ω ⟨hx, hr⟩
  have hsub : ω ∩ S ⊆ ω ∩ S' := Set.inter_subset_inter_right _ hS
  exact ⟨⟨hx.1, hS hx.2⟩, hr.mono (openSiteGraph_mono G hsub)⟩

/-- **A walk that stays inside `S` is a confined connection.**  Every edge of the walk joins two
vertices of its support, hence two vertices of `S`; both are open because the walk runs in the open
site graph.  So the walk transfers to the open site graph of `ω ∩ S`. -/
theorem connWithin_of_walk {G : SimpleGraph V} {ω : SiteConfig V} {S : Set V} {x y : V}
    (hx : x ∈ ω) (p : (openSiteGraph G ω).Walk x y) (hp : ∀ v ∈ p.support, v ∈ S) :
    ω ∈ connWithin G S x y := by
  refine ⟨⟨hx, hp x p.start_mem_support⟩, ⟨p.transfer (openSiteGraph G (ω ∩ S)) ?_⟩⟩
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    have hadj := (openSiteGraph_adj_iff' G ω a b).1 (p.adj_of_mem_edges he)
    exact (openSiteGraph_adj_iff' G (ω ∩ S) a b).2
      ⟨hadj.1, ⟨hadj.2.1, hp a (p.fst_mem_support_of_mem_edges he)⟩,
        ⟨hadj.2.2, hp b (p.snd_mem_support_of_mem_edges he)⟩⟩

/-- Connection to a set, confined to `S`: some vertex of `A` is reached from `x` by an open path
inside `S`. -/
def connWithinSet (G : SimpleGraph V) (S : Set V) (x : V) (A : Set V) : Set (SiteConfig V) :=
  ⋃ a ∈ A, connWithin G S x a

theorem mem_connWithinSet_iff (G : SimpleGraph V) (S : Set V) (x : V) (A : Set V)
    (ω : SiteConfig V) : ω ∈ connWithinSet G S x A ↔ ∃ a ∈ A, ω ∈ connWithin G S x a := by
  simp [connWithinSet]

/-- **A confined connection to a set is a cylinder event on `S`.** -/
theorem determinedBy_connWithinSet (G : SimpleGraph V) (S : Set V) (x : V) (A : Set V) :
    DeterminedBy (connWithinSet G S x A) S :=
  DeterminedBy.iUnion fun a => DeterminedBy.iUnion fun _ => determinedBy_connWithin G S x a

theorem measurableSet_connWithinSet (G : SimpleGraph V) (S : Finset V) (x : V) (A : Set V) :
    MeasurableSet (connWithinSet G (↑S : Set V) x A) :=
  (determinedBy_connWithinSet G (↑S : Set V) x A).measurableSet_of_finset

theorem connWithinSet_mono_set (G : SimpleGraph V) {S S' : Set V} (hS : S ⊆ S') (x : V)
    (A : Set V) : connWithinSet G S x A ⊆ connWithinSet G S' x A :=
  Set.iUnion₂_mono fun a _ => connWithin_mono_set G hS x a

/-- A confined connection to a set is an unconfined one. -/
theorem connWithinSet_subset_siteConnSet (G : SimpleGraph V) (S : Set V) (x : V) (A : Set V) :
    connWithinSet G S x A ⊆ siteConnSet G x A :=
  Set.iUnion₂_mono fun a _ => connWithin_subset_siteConn G S x a

end Confined

/-! ## Exhaustion of the lattice by boxes -/

section Boxes

variable {d : ℕ}

theorem coe_box_mono (d : ℕ) {N N' : ℕ} (h : N ≤ N') :
    (↑(box d N) : Set (Site d)) ⊆ ↑(box d N') :=
  Finset.coe_subset.2 (box_mono d h)

theorem connWithin_box_monotone (d : ℕ) (x y : Site d) :
    Monotone fun N => connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y :=
  fun _ _ h => connWithin_mono_set (zdGraph d) (coe_box_mono d h) x y

theorem connWithinSet_box_monotone (d : ℕ) (x : Site d) (A : Set (Site d)) :
    Monotone fun N => connWithinSet (zdGraph d) (↑(box d N) : Set (Site d)) x A :=
  fun _ _ h => connWithinSet_mono_set (zdGraph d) (coe_box_mono d h) x A

/-- **Every open path lies in a box.**  An unconfined connection on `ℤ^d` is a confined connection
inside some finite box: a walk has finitely many vertices, and a finite set of sites lies in a
box. -/
theorem exists_connWithin_box_of_siteConn {x y : Site d} {ω : SiteConfig (Site d)}
    (h : ω ∈ siteConn (zdGraph d) x y) :
    ∃ N, ω ∈ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y := by
  classical
  obtain ⟨hx, hr⟩ := h
  obtain ⟨p⟩ := hr
  obtain ⟨N, hN⟩ := DCT16.exists_subset_box p.support.toFinset
  exact ⟨N, connWithin_of_walk hx p fun v hv =>
    Finset.mem_coe.2 (hN (List.mem_toFinset.2 hv))⟩

/-- **The confined connections exhaust the unconfined one.**  This is the continuity-from-below
input: the events on the left increase in `N` and their union is the connection event. -/
theorem iUnion_connWithin_box (d : ℕ) (x y : Site d) :
    (⋃ N, connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y) = siteConn (zdGraph d) x y := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun N => connWithin_subset_siteConn _ _ x y) ?_
  intro ω hω
  obtain ⟨N, hN⟩ := exists_connWithin_box_of_siteConn hω
  exact Set.mem_iUnion.2 ⟨N, hN⟩

/-- The same statement for a connection to a set. -/
theorem iUnion_connWithinSet_box (d : ℕ) (x : Site d) (A : Set (Site d)) :
    (⋃ N, connWithinSet (zdGraph d) (↑(box d N) : Set (Site d)) x A) = siteConnSet (zdGraph d) x A := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun N => connWithinSet_subset_siteConnSet _ _ x A) ?_
  rintro ω hω
  rw [siteConnSet, Set.mem_iUnion₂] at hω
  obtain ⟨a, ha, hconn⟩ := hω
  obtain ⟨N, hN⟩ := exists_connWithin_box_of_siteConn hconn
  exact Set.mem_iUnion.2 ⟨N, (mem_connWithinSet_iff _ _ _ _ _).2 ⟨a, ha, hN⟩⟩

/-- The sphere of a box is a finite set of sites. -/
theorem boxSphere_finite (d M : ℕ) : (boxSphere d M).Finite := by
  refine Set.Finite.subset (box d M).finite_toSet ?_
  rintro x ⟨hx, -⟩
  exact Finset.mem_coe.2 (mem_box.2 hx)

/-- A face of a box is a finite set of sites. -/
theorem boxFace_finite (d m : ℕ) (i : Fin d) (b : Bool) : (boxFace d m i b).Finite := by
  refine Set.Finite.subset (box d m).finite_toSet ?_
  rintro x ⟨hx, -⟩
  exact Finset.mem_coe.2 (mem_box.2 hx)

/-- Connection to a countable set of sites is a measurable event. -/
theorem measurableSet_siteConnSet {V : Type*} [Countable V] (G : SimpleGraph V) (x : V)
    {A : Set V} (hA : A.Countable) : MeasurableSet (siteConnSet G x A) :=
  MeasurableSet.biUnion hA fun a _ => measurableSet_siteConn G x a

end Boxes

/-! ## The two confined events -/

section Events

variable {d : ℕ}

/-- **The confined coalescence-failure event.**  Both `x` and `y` reach the sphere of radius `M` by
open paths inside `box d N`, and yet `x` and `y` are not joined by an open path inside `box d N`.

Every connection named here is confined to `box d N`, so the event is decided by the states of the
sites of that box.  Neither half is the restriction to a box of its ambient counterpart: the two arms
are harder to produce inside a box, and the connection between `x` and `y` is harder to produce
inside a box as well, so failing it is easier.  The second effect is why the ambient bound for the
same box says nothing about this event, and why the outer radius `N` has to be sent to infinity. -/
def localCoalescenceEvent (d M N : ℕ) (x y : Site d) : Set (SiteConfig (Site d)) :=
  (connWithinSet (zdGraph d) (↑(box d N) : Set (Site d)) x (boxSphere d M) ∩
      connWithinSet (zdGraph d) (↑(box d N) : Set (Site d)) y (boxSphere d M)) \
    connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y

/-- **The confined face-hitting event.**  Some site of `box d N` is joined, by open paths inside
`box d N`, to every one of the `2d` faces of `box d m`. -/
def localFaceEvent (d m N : ℕ) : Set (SiteConfig (Site d)) :=
  ⋃ x ∈ (↑(box d N) : Set (Site d)), ⋂ q : Fin d × Bool,
    connWithinSet (zdGraph d) (↑(box d N) : Set (Site d)) x (boxFace d m q.1 q.2)

theorem mem_localFaceEvent_iff (d m N : ℕ) (ω : SiteConfig (Site d)) :
    ω ∈ localFaceEvent d m N ↔ ∃ x ∈ box d N, ∀ (i : Fin d) (b : Bool),
      ∃ z ∈ boxFace d m i b, ω ∈ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x z := by
  simp only [localFaceEvent, Set.mem_iUnion₂, Set.mem_iInter, mem_connWithinSet_iff,
    Finset.mem_coe]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, fun i b => h (i, b)⟩,
    fun ⟨x, hx, h⟩ => ⟨x, hx, fun q => h q.1 q.2⟩⟩

/-! ### They are cylinder events on an explicit finite box -/

/-- **The coalescence event is determined by the sites of `box d N`.** -/
theorem determinedBy_localCoalescenceEvent (d M N : ℕ) (x y : Site d) :
    DeterminedBy (localCoalescenceEvent d M N x y) (↑(box d N) : Set (Site d)) := by
  refine DeterminedBy.inter (DeterminedBy.inter ?_ ?_) ?_
  · exact determinedBy_connWithinSet _ _ x _
  · exact determinedBy_connWithinSet _ _ y _
  · exact (determinedBy_connWithin _ _ x y).compl

theorem measurableSet_localCoalescenceEvent (d M N : ℕ) (x y : Site d) :
    MeasurableSet (localCoalescenceEvent d M N x y) :=
  (determinedBy_localCoalescenceEvent d M N x y).measurableSet_of_finset

/-- **The face event is determined by the sites of `box d N`.** -/
theorem determinedBy_localFaceEvent (d m N : ℕ) :
    DeterminedBy (localFaceEvent d m N) (↑(box d N) : Set (Site d)) :=
  DeterminedBy.iUnion fun x => DeterminedBy.iUnion fun _ =>
    DeterminedBy.iInter fun q => determinedBy_connWithinSet _ _ x (boxFace d m q.1 q.2)

theorem measurableSet_localFaceEvent (d m N : ℕ) : MeasurableSet (localFaceEvent d m N) :=
  (determinedBy_localFaceEvent d m N).measurableSet_of_finset

/-- **Both events are cylinder events**, in the sense of `Percolation.Literature.IsLocalEvent`:
each has a finite support, named explicitly, and that support is a box of the lattice. -/
theorem isLocalEvent_localCoalescenceEvent (d M N : ℕ) (x y : Site d) :
    IsLocalEvent (localCoalescenceEvent d M N x y) :=
  ⟨box d N, determinedBy_localCoalescenceEvent d M N x y⟩

theorem isLocalEvent_localFaceEvent (d m N : ℕ) : IsLocalEvent (localFaceEvent d m N) :=
  ⟨box d N, determinedBy_localFaceEvent d m N⟩

/-! ### Comparison with the ambient events -/

/-- The ambient event of the `faceHit` field of `SiteLocalInputs`: some open cluster meets all `2d`
faces of `box d m`. -/
def ambientFaceEvent (d m : ℕ) : Set (SiteConfig (Site d)) :=
  {ω | ∃ x : Site d, ∀ (i : Fin d) (b : Bool),
    (siteCluster (zdGraph d) ω x ∩ boxFace d m i b).Nonempty}

/-- The face event grows with the outer radius. -/
theorem localFaceEvent_monotone (d m : ℕ) : Monotone (localFaceEvent d m) := by
  intro N N' h
  refine Set.iUnion₂_subset fun x hx => ?_
  refine Set.subset_iUnion₂_of_subset x (coe_box_mono d h hx) ?_
  exact Set.iInter_mono fun q => connWithinSet_box_monotone d x _ h

/-- **The confined face event exhausts the ambient one.**  Each open path witnessing the ambient
event is finite, so all `2d` of them, together with their common starting site, lie in one box. -/
theorem iUnion_localFaceEvent (d m : ℕ) :
    (⋃ N, localFaceEvent d m N) = ambientFaceEvent d m := by
  classical
  refine Set.Subset.antisymm (Set.iUnion_subset fun N ω hω => ?_) fun ω hω => ?_
  · rw [mem_localFaceEvent_iff] at hω
    obtain ⟨x, -, h⟩ := hω
    refine ⟨x, fun i b => ?_⟩
    obtain ⟨z, hz, hconn⟩ := h i b
    exact ⟨z, connWithin_subset_siteConn _ _ x z hconn, hz⟩
  · obtain ⟨x, hx⟩ := hω
    have hstep : ∀ q : Fin d × Bool, ∃ N, ∃ z ∈ boxFace d m q.1 q.2,
        ω ∈ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x z := by
      intro q
      obtain ⟨z, hzc, hzf⟩ := hx q.1 q.2
      obtain ⟨N, hN⟩ := exists_connWithin_box_of_siteConn (x := x) (y := z) hzc
      exact ⟨N, z, hzf, hN⟩
    choose f hf using hstep
    obtain ⟨N₀, hN₀⟩ := DCT16.exists_subset_box ({x} : Finset (Site d))
    refine Set.mem_iUnion.2 ⟨max N₀ (Finset.univ.sup f), (mem_localFaceEvent_iff _ _ _ _).2
      ⟨x, box_mono d (le_max_left _ _) (hN₀ (Finset.mem_singleton_self x)), fun i b => ?_⟩⟩
    obtain ⟨z, hzf, hz⟩ := hf (i, b)
    exact ⟨z, hzf, connWithin_box_monotone d x z
      (le_trans (Finset.le_sup (Finset.mem_univ (i, b))) (le_max_right _ _)) hz⟩

/-- The ambient face event is measurable, being the union of the confined ones. -/
theorem measurableSet_ambientFaceEvent (d m : ℕ) : MeasurableSet (ambientFaceEvent d m) := by
  rw [← iUnion_localFaceEvent]
  exact MeasurableSet.iUnion fun N => measurableSet_localFaceEvent d m N

/-- The ambient event of the `coalescence` field of `SiteLocalInputs`: the open clusters of `x` and
of `y` both reach the sphere of radius `M`. -/
def ambientArmsEvent (d M : ℕ) (x y : Site d) : Set (SiteConfig (Site d)) :=
  siteConnSet (zdGraph d) x (boxSphere d M) ∩ siteConnSet (zdGraph d) y (boxSphere d M)

theorem measurableSet_ambientArmsEvent (d M : ℕ) (x y : Site d) :
    MeasurableSet (ambientArmsEvent d M x y) :=
  (measurableSet_siteConnSet _ x (boxSphere_finite d M).countable).inter
    (measurableSet_siteConnSet _ y (boxSphere_finite d M).countable)

/-- The confined coalescence-failure event sits inside the ambient arms event with the *confined*
connection removed.  Confining weakens the arms, which appear positively, and it strengthens the
connection, which appears negatively; only the first of the two changes is in the direction of the
ambient bound. -/
theorem localCoalescenceEvent_subset (d M N : ℕ) (x y : Site d) :
    localCoalescenceEvent d M N x y ⊆
      ambientArmsEvent d M x y \ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y :=
  Set.sdiff_subset_sdiff_left
    (Set.inter_subset_inter (connWithinSet_subset_siteConnSet _ _ x _)
      (connWithinSet_subset_siteConnSet _ _ y _))

end Events

/-! ## From the ambient inputs to the confined ones -/

section Transfer

variable {d : ℕ}

/-- **Continuity from below for the face event.** -/
theorem tendsto_localFaceEvent (d m : ℕ) (p : unitInterval) :
    Filter.Tendsto (fun N => (siteBernoulli (fun _ : Site d => p)).real (localFaceEvent d m N))
      Filter.atTop
      (nhds ((siteBernoulli (fun _ : Site d => p)).real (ambientFaceEvent d m))) := by
  have h := MeasureTheory.tendsto_measure_iUnion_atTop
    (μ := siteBernoulli (fun _ : Site d => p)) (s := localFaceEvent d m)
    (localFaceEvent_monotone d m)
  rw [iUnion_localFaceEvent] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

/-- **Continuity from above for the coalescence-failure event.**  The ambient arms event with the
confined connection removed decreases, as the outer radius grows, to the ambient arms event with the
ambient connection removed, because the confined connections increase to the ambient one. -/
theorem tendsto_ambientArms_diff (d M : ℕ) (p : unitInterval) (x y : Site d) :
    Filter.Tendsto
      (fun N => (siteBernoulli (fun _ : Site d => p)).real
        (ambientArmsEvent d M x y \ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y))
      Filter.atTop
      (nhds ((siteBernoulli (fun _ : Site d => p)).real
        (ambientArmsEvent d M x y \ siteConn (zdGraph d) x y))) := by
  have hmeas : ∀ N : ℕ, NullMeasurableSet
      (ambientArmsEvent d M x y \ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y)
      (siteBernoulli (fun _ : Site d => p)) := fun N =>
    ((measurableSet_ambientArmsEvent d M x y).diff
      (measurableSet_connWithin (zdGraph d) (box d N) x y)).nullMeasurableSet
  have hanti : Antitone fun N : ℕ =>
      ambientArmsEvent d M x y \ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y :=
    fun _ _ hNN => Set.sdiff_subset_sdiff_right (connWithin_box_monotone d x y hNN)
  have h := MeasureTheory.tendsto_measure_iInter_atTop hmeas hanti
    ⟨0, measure_ne_top _ _⟩
  have hinter : (⋂ N : ℕ,
      ambientArmsEvent d M x y \ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) x y) =
      ambientArmsEvent d M x y \ siteConn (zdGraph d) x y := by
    rw [← Set.sdiff_iUnion, iUnion_connWithin_box]
  rw [hinter] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

/-- **The intrinsic face-hitting bound.**  For every error `η` there is a scale `m₀` beyond which
every inner scale `m` admits a finite outer scale `N ≥ m` such that, with probability at least
`1 - η`, some site of `box d N` is joined inside `box d N` to all `2d` faces of `box d m`.

The ambient statement is the hypothesis; the content of the theorem is that the confinement costs an
arbitrarily small amount once the outer box is large enough. -/
theorem exists_localFaceEvent_ge (d : ℕ) (p : unitInterval) (h : SiteLocalInputs d p)
    (η : ℝ) (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ N ≥ m,
      1 - η ≤ (siteBernoulli (fun _ : Site d => p)).real (localFaceEvent d m N) := by
  obtain ⟨m₀, hm₀⟩ := h.faceHit (η / 2) (by linarith)
  refine ⟨m₀, fun m hm => ?_⟩
  have hamb : 1 - η / 2 ≤
      (siteBernoulli (fun _ : Site d => p)).real (ambientFaceEvent d m) := hm₀ m hm
  have hlt : 1 - η < (siteBernoulli (fun _ : Site d => p)).real (ambientFaceEvent d m) := by
    linarith
  obtain ⟨N, hN₁, hN₂⟩ :=
    (((tendsto_localFaceEvent d m p).eventually_const_lt hlt).and
      (Filter.eventually_ge_atTop m)).exists
  exact ⟨N, hN₂, hN₁.le⟩

/-- **The intrinsic coalescence bound.**  For every inner scale `m` and every error `η` there is an
annulus radius `M > m` and a finite outer radius `N ≥ M` such that, uniformly over the pairs of
sites of `box d m`, the probability that both sites reach the sphere of radius `M` inside `box d N`
while remaining unjoined inside `box d N` is at most `η`.

The obstruction the outer radius removes is the second clause: the ambient hypothesis controls the
failure of the *ambient* connection, and a configuration can join `x` to `y` only by leaving
`box d N`.  The confined connections increase to the ambient one as `N` grows, so the extra failures
have probability tending to zero, and finitely many pairs of sites share one radius. -/
theorem exists_localCoalescenceEvent_le (d : ℕ) (p : unitInterval) (h : SiteLocalInputs d p)
    (m : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ M > m, ∃ N ≥ M, ∀ x ∈ box d m, ∀ y ∈ box d m,
      (siteBernoulli (fun _ : Site d => p)).real (localCoalescenceEvent d M N x y) ≤ η := by
  classical
  obtain ⟨M, hMm, hM⟩ := h.coalescence m (η / 2) (by linarith)
  refine ⟨M, hMm, ?_⟩
  have key : ∀ᶠ N : ℕ in Filter.atTop, ∀ q ∈ (box d m) ×ˢ (box d m),
      (siteBernoulli (fun _ : Site d => p)).real
        (ambientArmsEvent d M q.1 q.2 \
          connWithin (zdGraph d) (↑(box d N) : Set (Site d)) q.1 q.2) < η := by
    rw [Filter.eventually_all_finset]
    intro q hq
    rw [Finset.mem_product] at hq
    have hlim : (siteBernoulli (fun _ : Site d => p)).real
        (ambientArmsEvent d M q.1 q.2 \ siteConn (zdGraph d) q.1 q.2) < η :=
      lt_of_le_of_lt (hM q.1 hq.1 q.2 hq.2) (by linarith)
    exact (tendsto_ambientArms_diff d M p q.1 q.2).eventually_lt_const hlim
  obtain ⟨N, hN₁, hN₂⟩ := (key.and (Filter.eventually_ge_atTop M)).exists
  refine ⟨N, hN₂, fun x hx y hy => ?_⟩
  refine le_of_lt (lt_of_le_of_lt ?_ (hN₁ (x, y) (Finset.mem_product.2 ⟨hx, hy⟩)))
  exact measureReal_mono (localCoalescenceEvent_subset d M N x y) (measure_ne_top _ _)

end Transfer

/-! ## The interface, and its packaging for the certificate machinery -/

section Interface

variable {d : ℕ}

/-- **The local inputs of the geometric construction, confined to a finite box.**  Both fields speak
only about connections inside an explicitly named box, so both are cylinder events with the finite
support `box d N`, and `CylinderExperiment.abs_prob_sub_le` applies to them.

`siteIntrinsicInputs_of_siteLocalInputs` proves this from the ambient `SiteLocalInputs d p`, at the
cost of an outer radius `N`, which is exactly the content that the ambient statements do not
have. -/
structure SiteIntrinsicInputs (d : ℕ) (p : unitInterval) : Prop where
  /-- **Two long arms inside a box belong to one cluster inside a larger box.** -/
  coalescence : ∀ m : ℕ, ∀ η : ℝ, 0 < η → ∃ M > m, ∃ N ≥ M, ∀ x ∈ box d m, ∀ y ∈ box d m,
    (siteBernoulli (fun _ : Site d => p)).real (localCoalescenceEvent d M N x y) ≤ η
  /-- **A cluster inside a box reaching every face of an inner box.** -/
  faceHit : ∀ η : ℝ, 0 < η → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ N ≥ m,
    1 - η ≤ (siteBernoulli (fun _ : Site d => p)).real (localFaceEvent d m N)

/-- **The ambient local inputs give the confined ones.**  This is the transfer the renormalization
argument needs and that the ambient statements cannot perform on their own: a connection that leaves
every box is not decided by any finite set of sites. -/
theorem siteIntrinsicInputs_of_siteLocalInputs (d : ℕ) (p : unitInterval)
    (h : SiteLocalInputs d p) : SiteIntrinsicInputs d p where
  coalescence m η hη := exists_localCoalescenceEvent_le d p h m η hη
  faceHit η hη := exists_localFaceEvent_ge d p h η hη

/-- The coalescence bound as a cylinder experiment.  The event carried is the complement of the
failure event, so that the bound reads as a lower bound on a probability, which is the form
`RenormData.ValidAt` asks for. -/
def coalescenceExperiment (d M N : ℕ) (x y : Site d) : CylinderExperiment d where
  support := box d N
  event := (localCoalescenceEvent d M N x y)ᶜ
  determined := (determinedBy_localCoalescenceEvent d M N x y).compl
  measurable' := (measurableSet_localCoalescenceEvent d M N x y).compl

/-- The face-hitting bound as a cylinder experiment. -/
def faceExperiment (d m N : ℕ) : CylinderExperiment d where
  support := box d N
  event := localFaceEvent d m N
  determined := determinedBy_localFaceEvent d m N
  measurable' := measurableSet_localFaceEvent d m N

@[simp] theorem coalescenceExperiment_support (d M N : ℕ) (x y : Site d) :
    (coalescenceExperiment d M N x y).support = box d N := rfl

@[simp] theorem faceExperiment_support (d m N : ℕ) : (faceExperiment d m N).support = box d N := rfl

theorem coalescenceExperiment_prob (d M N : ℕ) (x y : Site d) (q : unitInterval) :
    (coalescenceExperiment d M N x y).prob q
      = 1 - (siteBernoulli (fun _ : Site d => q)).real (localCoalescenceEvent d M N x y) := by
  show (siteBernoulli (fun _ : Site d => q)).real ((localCoalescenceEvent d M N x y)ᶜ) = _
  rw [measureReal_compl (measurableSet_localCoalescenceEvent d M N x y), probReal_univ]

theorem faceExperiment_prob (d m N : ℕ) (q : unitInterval) :
    (faceExperiment d m N).prob q
      = (siteBernoulli (fun _ : Site d => q)).real (localFaceEvent d m N) := rfl

/-- **The bounds are Lipschitz in the parameter**, with constant the number of sites of the box they
are confined to.  This is the property the ambient statements do not have and that the whole
renormalization route depends on; it is `CylinderExperiment.abs_prob_sub_le` with the cardinality of
`box d N` evaluated. -/
theorem coalescenceExperiment_abs_prob_sub_le (d M N : ℕ) (x y : Site d) (p q : unitInterval) :
    |(coalescenceExperiment d M N x y).prob p - (coalescenceExperiment d M N x y).prob q|
      ≤ ((2 * N + 1) ^ d : ℕ) * |(p : ℝ) - (q : ℝ)| := by
  simpa [card_box] using (coalescenceExperiment d M N x y).abs_prob_sub_le p q

theorem faceExperiment_abs_prob_sub_le (d m N : ℕ) (p q : unitInterval) :
    |(faceExperiment d m N).prob p - (faceExperiment d m N).prob q|
      ≤ ((2 * N + 1) ^ d : ℕ) * |(p : ℝ) - (q : ℝ)| := by
  simpa [card_box] using (faceExperiment d m N).abs_prob_sub_le p q

/-- **The coalescence input in certificate form.** -/
theorem exists_coalescenceExperiment_prob_ge (d : ℕ) (p : unitInterval) (h : SiteLocalInputs d p)
    (m : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ M > m, ∃ N ≥ M, ∀ x ∈ box d m, ∀ y ∈ box d m,
      1 - η ≤ (coalescenceExperiment d M N x y).prob p := by
  obtain ⟨M, hMm, N, hNM, hbound⟩ := exists_localCoalescenceEvent_le d p h m η hη
  refine ⟨M, hMm, N, hNM, fun x hx y hy => ?_⟩
  rw [coalescenceExperiment_prob]
  linarith [hbound x hx y hy]

/-- **The face-hitting input in certificate form.** -/
theorem exists_faceExperiment_prob_ge (d : ℕ) (p : unitInterval) (h : SiteLocalInputs d p)
    (η : ℝ) (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ N ≥ m, 1 - η ≤ (faceExperiment d m N).prob p := by
  obtain ⟨m₀, hm₀⟩ := exists_localFaceEvent_ge d p h η hη
  exact ⟨m₀, fun m hm => hm₀ m hm⟩

end Interface

end KNAll.Site

end
