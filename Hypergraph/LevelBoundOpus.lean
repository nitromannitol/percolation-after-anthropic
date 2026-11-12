import Hypergraph.CorridorEstimates
import Hypergraph.ProbInvariant

/-!
# The ordered face crossing and the level event

* `exists_firstEntry` and `orderedFaceCrossing`: the deterministic ordered-face crossing.  A
  confined open path from a source outside `D 0` to a target inside `D K`, for nested regions with
  the gate property, crosses the face `D j \ D (j+1)` for every `j ≤ K`, and its prefix up to that
  crossing stays outside `D j`; `orderedFaceCrossing_prefix_avoids` says the crossings occur in
  order of increasing depth.  This is what allows the per-level conditional failure estimates to
  be iterated against the full-corridor success event.

* `entry_of_levelEvent`, `levelEvent_subset_entryEvent`: the level event forces an entry.  Its
  second disjunct asks for a connection of positive probability from the origin into `E z y`, and
  the origin is not in `E z y`; by the first-entry lemma the connection crosses the boundary of
  `E z y` at a site that the accepted transcript has already recorded open, along a path that never
  enters `E z y` and is therefore entirely pinned.  So the level event is contained in the
  deterministic `EntryEvent`.

* `notMem_M_of_adj_mem_E`, `entry_outside_M`: no site adjacent to `E z y` lies in `M z`, the target
  box of the incoming reservation, so the entry event concerns a target disjoint from the target
  of the reservation clause of `MacroExp.Good`.
-/

noncomputable section

namespace KNAll.Site
namespace LevelOpus

open MeasureTheory Set
open Percolation.Literature Percolation.Literature.LatticeModels

/-! ## Ordered crossing of nested faces -/

section Crossing

variable {V : Type*} {G : SimpleGraph V}

/-- The walk form of the first entry into `D`. -/
private theorem firstEntry_walk {W D : Set V} :
    ∀ {o b : V}, (openSiteGraph G W).Walk o b → o ∉ D → b ∈ D →
      ∃ u v : V, G.Adj u v ∧ u ∉ D ∧ v ∈ D ∧ u ∈ W ∧ v ∈ W ∧
        (openSiteGraph G (W \ D)).Reachable o u := by
  intro o b p
  induction p with
  | nil => intro ho hb; exact absurd hb ho
  | @cons a m b hadj q ih =>
      intro ha hb
      have hadj' := (openSiteGraph_adj_iff' G W a m).1 hadj
      by_cases hm : m ∈ D
      · exact ⟨a, m, hadj'.1, ha, hm, hadj'.2.1, hadj'.2.2, SimpleGraph.Reachable.refl a⟩
      · obtain ⟨u, v, huv, hu, hv, huW, hvW, hreach⟩ := ih hm hb
        refine ⟨u, v, huv, hu, hv, huW, hvW, ?_⟩
        have hstep : (openSiteGraph G (W \ D)).Adj a m :=
          (openSiteGraph_adj_iff' G (W \ D) a m).2 ⟨hadj'.1, ⟨hadj'.2.1, ha⟩, ⟨hadj'.2.2, hm⟩⟩
        exact (SimpleGraph.Adj.reachable hstep).trans hreach

/-- **First entry into a region.**  A confined open path from a source outside `D` to a target in
`D` has a first crossing dart: an open site `u ∉ D` of the confining set adjacent to an open site
`v ∈ D`, and the whole prefix from the source to `u` stays outside `D`. -/
theorem exists_firstEntry {S D : Set V} {o b : V} {ω : SiteConfig V}
    (ho : o ∉ D) (hb : b ∈ D) (hconn : ω ∈ connWithin G S o b) :
    ∃ u v : V, G.Adj u v ∧ u ∉ D ∧ v ∈ D ∧ u ∈ ω ∩ S ∧ v ∈ ω ∩ S ∧
      ω ∈ connWithin G (S \ D) o u := by
  obtain ⟨hoS, hreach⟩ := hconn
  obtain ⟨p⟩ := hreach
  obtain ⟨u, v, huv, hu, hv, huW, hvW, hpre⟩ := firstEntry_walk (G := G) p ho hb
  refine ⟨u, v, huv, hu, hv, huW, hvW, ?_, ?_⟩
  · exact ⟨hoS.1, hoS.2, ho⟩
  · have hset : (ω ∩ S) \ D = ω ∩ (S \ D) := by
      ext x; simp only [Set.mem_diff, Set.mem_inter_iff]; tauto
    rw [← hset]
    exact hpre


/-- A decreasing family of regions is antitone in the level. -/
theorem nested_anti {D : ℕ → Set V} (hmono : ∀ j, D (j + 1) ⊆ D j) {i j : ℕ} (hij : i ≤ j) :
    D j ⊆ D i := by
  induction j with
  | zero => simpa [Nat.le_zero.1 hij] using Set.Subset.refl (D 0)
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (hmono j).trans (ih (Nat.lt_succ_iff.1 h))
      · have : i = j + 1 := le_antisymm hij h
        subst this
        exact Set.Subset.refl _

/-- **Ordered face crossing.**  Let `D 0 ⊇ D 1 ⊇ ⋯` be nested regions with the gate property: a
site of `D j` entered from outside `D j` is not in `D (j+1)`.  Then a confined open path from a
source outside `D 0` to a target inside `D K` crosses, for every level `j ≤ K`, the face
`D j \ D (j+1)`, and its prefix up to that crossing lies outside `D j` -- hence inside the region
that defines the previous level.

This is the deterministic input that a per-level conditional failure estimate needs before it can
be iterated: without it the events "level `j` is bad" carry no information about the full-corridor
success event. -/
theorem orderedFaceCrossing {S : Set V} {D : ℕ → Set V} {o b : V} {ω : SiteConfig V}
    (hmono : ∀ j, D (j + 1) ⊆ D j)
    (hgate : ∀ j, ∀ x y : V, x ∉ D j → y ∈ D j → G.Adj x y → y ∉ D (j + 1))
    (ho : o ∉ D 0) {K : ℕ} (hb : b ∈ D K) (hconn : ω ∈ connWithin G S o b)
    {j : ℕ} (hj : j ≤ K) :
    ∃ u v : V, G.Adj u v ∧ u ∉ D j ∧ v ∈ D j ∧ v ∉ D (j + 1) ∧
      u ∈ ω ∩ S ∧ v ∈ ω ∩ S ∧ ω ∈ connWithin G (S \ D j) o u := by
  have hoj : o ∉ D j := fun hc => ho (nested_anti hmono (Nat.zero_le j) hc)
  have hbj : b ∈ D j := nested_anti hmono hj hb
  obtain ⟨u, v, huv, hu, hv, huS, hvS, hpre⟩ := exists_firstEntry hoj hbj hconn
  exact ⟨u, v, huv, hu, hv, hgate j u v hu hv huv, huS, hvS, hpre⟩

/-- Every site the prefix reaches lies in its own confining set. -/
theorem mem_of_reachable_of_connWithin {S' : Set V} {o u x : V} {ω : SiteConfig V}
    (hpre : ω ∈ connWithin G S' o u)
    (hx : (openSiteGraph G (ω ∩ S')).Reachable o x) : x ∈ ω ∩ S' :=
  mem_of_mem_siteCluster G (ω ∩ S') ⟨hpre.1, hx⟩

/-- **The crossings happen in order.**  Every site reached by the prefix that ends at the first
entry into `D i` avoids every deeper level `D j`, `j ≥ i`.  So the first entries into
`D 0, D 1, …` occur along the path in this order. -/
theorem orderedFaceCrossing_prefix_avoids {S : Set V} {D : ℕ → Set V} {o u : V} {ω : SiteConfig V}
    (hmono : ∀ j, D (j + 1) ⊆ D j) {i j : ℕ} (hij : i ≤ j)
    (hpre : ω ∈ connWithin G (S \ D i) o u) {x : V}
    (hx : (openSiteGraph G (ω ∩ (S \ D i))).Reachable o x) : x ∉ D j := fun hxj =>
  (mem_of_reachable_of_connWithin hpre hx).2.2 (nested_anti hmono hij hxj)

end Crossing

/-! ## The level event and the entry it forces -/

section Level

variable {d : ℕ} [NeZero d]

/-- The event `Assembly.levelEvent` of `KN/AssemblyCheck.lean`, repeated verbatim (that
declaration is `private`).  For a fixed prospective direction `y`, an examination is usable if `y`
is no longer pending, or if some inner target lies in every certificate level and is reached from
the origin with the source probability the acquisition theorem needs. -/
def LevelEvent (d n : ℕ) (C : LeftImp2.Certificate2 d)
    (q : unitInterval) (h : MacroExp.Tr d) (y : Site 2) :
    Set (SiteConfig (Site d)) :=
  {omega | y ∉ MacroExp.pending d
      (MacroExp.accepted d C.corridor C.halfWidth n h omega)
      (MacroExp.pendZ d n h) ∨
    ∃ B : Set (Site d),
      (∀ i < C.levels, B ⊆
        ↑(Corridor.Dbox (Corridor.scalesOf C)
          (MacroExp.ctr d C.corridor y) i)) ∧
      1 - C.eps / 8 <
        (MacroExp.accepted d C.corridor C.halfWidth n h omega).prob
          (fun _ : Site d => q)
          (connWithinSet (zdGraph d)
            (↑((MacroExp.accepted d C.corridor C.halfWidth n h omega).inspected ∪
              MacroExp.E d C.corridor C.halfWidth (MacroExp.pendZ d n h) y) :
                Set (Site d))
            (MacroExp.emb 0) B)}

/-- The deterministic event that, after the examination has been accepted, the recorded open
cluster of the origin reaches a site adjacent to the outgoing corridor `E z y`, along a path that
never enters that corridor. -/
def EntryEvent (d r t n : ℕ) (h : MacroExp.Tr d) (y : Site 2) :
    Set (SiteConfig (Site d)) :=
  {omega | ∃ u : Site d,
      (∃ v ∈ MacroExp.E d r t (MacroExp.pendZ d n h) y, (zdGraph d).Adj u v) ∧
      (↑(MacroExp.accepted d r t n h omega).openSites : Set (Site d)) ∈
        connWithin (zdGraph d)
          ((↑(MacroExp.accepted d r t n h omega).inspected : Set (Site d)) \
            (↑(MacroExp.E d r t (MacroExp.pendZ d n h) y) : Set (Site d)))
          (MacroExp.emb 0) u}

/-- A well-formed certificate has a positive corridor radius. -/
theorem corridor_pos {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) : 0 < C.corridor := by
  have h1 := hwf.levels_pos
  have h2 := hwf.corridor_ge
  have : 0 < C.levels * (2 * C.faceTarget + 2) := by positivity
  omega

theorem scalesOf_rho_le {C : LeftImp2.Certificate2 d} (u : Fin d) :
    (Corridor.scalesOf C).ρ₀ u ≤ MacroExp.rad (5 * C.corridor) C.halfWidth u := by
  simp only [Corridor.scalesOf]
  unfold MacroExp.rad
  split_ifs <;> omega

/-- **The level event forces an entry into the outgoing corridor.**  The second disjunct of the
level event asks for a connection of positive probability from the origin to a set inside every
certificate level of `y`; all those levels lie in the fresh corridor `E z y`, which the origin does
not.  By the first-entry lemma the connection has a crossing dart whose tail is recorded open, is
adjacent to `E z y`, and is joined to the origin by a path that stays out of `E z y`; that path is
therefore pinned by the accepted transcript, so the entry is a deterministic property of the
configuration read during the examination. -/
theorem entry_of_levelEvent (hd : 2 ≤ d)
    (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) (q : unitInterval)
    (n : ℕ) (h : MacroExp.Tr d) {y : Site 2}
    (hzy : (zdGraph 2).Adj (MacroExp.pendZ d n h) y)
    (h0 : MacroExp.emb 0 ∉
      MacroExp.E d C.corridor C.halfWidth (MacroExp.pendZ d n h) y)
    {omega : SiteConfig (Site d)}
    (hpend : y ∈ MacroExp.pending d
      (MacroExp.accepted d C.corridor C.halfWidth n h omega) (MacroExp.pendZ d n h))
    (hlv : omega ∈ LevelEvent d n C q h y) :
    omega ∈ EntryEvent d C.corridor C.halfWidth n h y := by
  classical
  set z := MacroExp.pendZ d n h with hz
  set hp := MacroExp.accepted d C.corridor C.halfWidth n h omega with hhp
  obtain ⟨B, hB, hprob⟩ := hlv.resolve_left (not_not_intro hpend)
  set Dset : Set (Site d) :=
    (↑(MacroExp.E d C.corridor C.halfWidth z y) : Set (Site d)) with hD
  set S : Set (Site d) :=
    (↑(hp.inspected ∪ MacroExp.E d C.corridor C.halfWidth z y) : Set (Site d)) with hS
  set A : Set (SiteConfig (Site d)) :=
    connWithinSet (zdGraph d) S (MacroExp.emb 0) B with hA
  -- the source estimate is strictly positive, so the event is not empty under the pinned law
  have heps1 : C.eps ≤ 1 := hwf.eps_le_one
  have hpos : 0 < hp.prob (fun _ : Site d => q) A := by linarith
  have hne : (substitute (↑hp.inspected : Set (Site d)) hp.state ⁻¹' A).Nonempty := by
    rcases Set.eq_empty_or_nonempty
      (substitute (↑hp.inspected : Set (Site d)) hp.state ⁻¹' A) with hemp | hne
    · exfalso
      rw [FRDom.Transcript.prob_eq, pinnedProb, hemp] at hpos
      simp at hpos
    · exact hne
  obtain ⟨omega', homega'⟩ := hne
  set sigma : SiteConfig (Site d) :=
    substitute (↑hp.inspected : Set (Site d)) hp.state omega' with hsigma
  have hsig : sigma ∈ A := homega'
  obtain ⟨b, hbB, hconn⟩ := (mem_connWithinSet_iff (zdGraph d) S (MacroExp.emb 0) B sigma).1 hsig
  -- the inner target lies in the corridor
  have hr : 0 < C.corridor := corridor_pos hwf
  have hplace : Corridor.Dbox (Corridor.scalesOf C) (MacroExp.ctr d C.corridor y) 0 ⊆
      MacroExp.E d C.corridor C.halfWidth z y :=
    Corridor.Dbox_subset_E hd C.corridor C.halfWidth hr hzy.ne (Corridor.scalesOf C)
      (fun u => scalesOf_rho_le u) 0
  have hbD : b ∈ Dset := by
    have := hB 0 hwf.levels_pos hbB
    exact Finset.mem_coe.2 (hplace (Finset.mem_coe.1 this))
  obtain ⟨u, v, huv, hu, hv, huS, hvS, hpre⟩ := exists_firstEntry h0 hbD hconn
  -- the prefix is confined to the inspected sites, where the accepted transcript pins the states
  have hSD : S \ Dset = (↑hp.inspected : Set (Site d)) \ Dset := by
    rw [hS, hD, Finset.coe_union]
    ext x
    simp only [Set.mem_diff, Set.mem_union]
    tauto
  have hagree : sigma ∩ (S \ Dset) = (↑hp.openSites : Set (Site d)) ∩ (S \ Dset) := by
    ext x
    constructor
    · rintro ⟨hxs, hxSD⟩
      have hxI : x ∈ (↑hp.inspected : Set (Site d)) := by
        rw [hSD] at hxSD; exact hxSD.1
      refine ⟨?_, hxSD⟩
      have := (mem_substitute_of_mem (R := (↑hp.inspected : Set (Site d))) hp.state hxI).1 hxs
      exact this
    · rintro ⟨hxo, hxSD⟩
      have hxI : x ∈ (↑hp.inspected : Set (Site d)) := by
        rw [hSD] at hxSD; exact hxSD.1
      exact ⟨(mem_substitute_of_mem (R := (↑hp.inspected : Set (Site d))) hp.state hxI).2 hxo,
        hxSD⟩
  have hpre' : (↑hp.openSites : Set (Site d)) ∈
      connWithin (zdGraph d) (S \ Dset) (MacroExp.emb 0) u :=
    ((determinedBy_iff _ _).1
      (determinedBy_connWithin (zdGraph d) (S \ Dset) (MacroExp.emb 0) u) _ _ hagree).1 hpre
  refine ⟨u, ⟨v, Finset.mem_coe.1 hv, huv⟩, ?_⟩
  rw [← hSD]
  exact hpre'

/-- Adjacent sites differ by at most one in every coordinate. -/
theorem abs_sub_le_one_of_adj {u v : Site d} (hadj : (zdGraph d).Adj u v) (j : Fin d) :
    |v j - u j| ≤ 1 := by
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff u v).1 hadj
  · have hval := congrFun hi j
    simp only [Pi.add_apply, Pi.single_apply] at hval
    split_ifs at hval <;> rw [abs_le] <;> omega
  · have hval := congrFun hi j
    simp only [Pi.add_apply, Pi.single_apply] at hval
    split_ifs at hval <;> rw [abs_le] <;> omega

/-- **The target box of the incoming reservation does not touch the outgoing corridor.**  A site of
`M z` is at graph distance at least two from `E z y`: the corridor leaves the central box `Q z`,
whose planar radius is `5 r`, while `M z` has planar radius `3 r`, and in the transverse
coordinates the corridor is contained in the same slab as `Q z`.

This is the exact form of the budget mismatch.  The invariant `MacroExp.Good` bounds only the
failure of the connection to `M z`, with budget `(1 - density)/4`; the level event needs the origin
to reach a site adjacent to `E z y`, and by this lemma no such site lies in `M z`.  The two events
have disjoint targets, so the target inequality, whose budget `(1 - density)/16` is four times
smaller, is not a consequence of the invariant. -/
theorem notMem_M_of_adj_mem_E (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r) {z y : Site 2}
    {u v : Site d} (hv : v ∈ MacroExp.E d r t z y) (huv : (zdGraph d).Adj u v) :
    u ∉ MacroExp.M d r t z := by
  classical
  intro hu
  rw [MacroExp.E, Finset.mem_sdiff, MacroExp.mem_hbox] at hv
  obtain ⟨hhull, hQ⟩ := hv
  apply hQ
  rw [MacroExp.Q, MacroExp.mem_abox]
  intro j
  rw [MacroExp.M, MacroExp.mem_abox] at hu
  have huj := hu j
  have hstep := abs_sub_le_one_of_adj (d := d) huv j
  rw [abs_le] at hstep
  by_cases hj : j.val < 2
  · have h3 : MacroExp.rad (3 * r) t j = 3 * (r : ℤ) := by
      unfold MacroExp.rad; rw [if_pos hj]; push_cast; ring
    have h5 : MacroExp.rad (5 * r) t j = 5 * (r : ℤ) := by
      unfold MacroExp.rad; rw [if_pos hj]; push_cast; ring
    rw [h3] at huj
    rw [h5]
    have hrz : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    omega
  · have hcz : MacroExp.ctr d r z j = 0 := by
      simp [MacroExp.ctr, MacroExp.emb_apply_of_not_lt z hj]
    have hcy : MacroExp.ctr d r y j = 0 := by
      simp [MacroExp.ctr, MacroExp.emb_apply_of_not_lt y hj]
    have hhj := hhull j
    rw [hcz, hcy] at hhj
    rw [hcz]
    simpa using hhj

/-- **What the level event really asks for.**  It forces the accepted transcript to join the origin
to a recorded open site outside the target box `M z` of the incoming reservation, along a path that
never enters the outgoing corridor. -/
theorem entry_outside_M (hd : 2 ≤ d)
    (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) (q : unitInterval)
    (n : ℕ) (h : MacroExp.Tr d) {y : Site 2}
    (hzy : (zdGraph 2).Adj (MacroExp.pendZ d n h) y)
    (h0 : MacroExp.emb 0 ∉
      MacroExp.E d C.corridor C.halfWidth (MacroExp.pendZ d n h) y)
    {omega : SiteConfig (Site d)}
    (hpend : y ∈ MacroExp.pending d
      (MacroExp.accepted d C.corridor C.halfWidth n h omega) (MacroExp.pendZ d n h))
    (hlv : omega ∈ LevelEvent d n C q h y) :
    ∃ u : Site d,
      u ∉ MacroExp.M d C.corridor C.halfWidth (MacroExp.pendZ d n h) ∧
      (↑(MacroExp.accepted d C.corridor C.halfWidth n h omega).openSites : Set (Site d)) ∈
        connWithin (zdGraph d)
          ((↑(MacroExp.accepted d C.corridor C.halfWidth n h omega).inspected : Set (Site d)) \
            (↑(MacroExp.E d C.corridor C.halfWidth (MacroExp.pendZ d n h) y) : Set (Site d)))
          (MacroExp.emb 0) u := by
  obtain ⟨u, ⟨v, hvE, huv⟩, hconn⟩ :=
    entry_of_levelEvent (d := d) hd C hwf q n h hzy h0 hpend hlv
  exact ⟨u, notMem_M_of_adj_mem_E (d := d) hd C.corridor C.halfWidth (corridor_pos hwf)
    hvE huv, hconn⟩

/-- A direction undetermined before the examination is still pending after it. -/
theorem pending_accepted_of_notMem (r t n : ℕ) (h : MacroExp.Tr d)
    {y : Site 2} (hy : y ∈ MacroExp.nbrs (MacroExp.pendZ d n h))
    (hyz : y ≠ MacroExp.pendZ d n h) (hyu : y ∉ h.openV ∪ h.closedV)
    (omega : SiteConfig (Site d)) :
    y ∈ MacroExp.pending d (MacroExp.accepted d r t n h omega) (MacroExp.pendZ d n h) := by
  classical
  rw [MacroExp.mem_pending]
  refine ⟨hy, ?_⟩
  rw [MacroExp.accepted, FRDom.Transcript.step_determined]
  intro hcon
  rcases Finset.mem_insert.1 hcon with h1 | h1
  · exact hyz h1
  · exact hyu h1

/-- **The level event is contained in the entry event.** -/
theorem levelEvent_subset_entryEvent (hd : 2 ≤ d)
    (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) (q : unitInterval)
    (n : ℕ) (h : MacroExp.Tr d) {y : Site 2}
    (hy : y ∈ MacroExp.nbrs (MacroExp.pendZ d n h))
    (hyu : y ∉ h.openV ∪ h.closedV)
    (h0 : MacroExp.emb 0 ∉
      MacroExp.E d C.corridor C.halfWidth (MacroExp.pendZ d n h) y) :
    LevelEvent d n C q h y ⊆ EntryEvent d C.corridor C.halfWidth n h y := by
  have hzy : (zdGraph 2).Adj (MacroExp.pendZ d n h) y := MacroExp.adj_of_mem_nbrs hy
  intro omega homega
  exact entry_of_levelEvent (d := d) hd C hwf q n h hzy h0
    (pending_accepted_of_notMem (d := d) C.corridor C.halfWidth n h hy hzy.ne' hyu omega) homega

end Level

/-! ## Indices of the plane embedding -/

section Index

variable {d : ℕ} [NeZero d]

theorem val_one (hd : 2 ≤ d) : (1 : Fin d).val = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]

theorem zero_ne_one_fin (hd : 2 ≤ d) : (0 : Fin d) ≠ (1 : Fin d) := by
  intro hcon
  have h0 : (0 : Fin d).val = 0 := Fin.val_zero d
  have h1 := val_one (d := d) hd
  rw [hcon] at h0
  omega

end Index

#print axioms KNAll.Site.LevelOpus.exists_firstEntry
#print axioms KNAll.Site.LevelOpus.orderedFaceCrossing
#print axioms KNAll.Site.LevelOpus.entry_of_levelEvent
#print axioms KNAll.Site.LevelOpus.notMem_M_of_adj_mem_E

end LevelOpus
end KNAll.Site

end
