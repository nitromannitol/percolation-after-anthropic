import Hypergraph.CorridorEstimates
import Hypergraph.ProbInvariant

/-!
# The directional level bound: the ordered face crossing, and where the budget runs out

`Assembly.site_no_percolation_at_criticality` in `KN/AssemblyCheck.lean` takes as its second
hypothesis, for every well-formed certificate `C` valid at `q`, every `n`, every transcript `h`
with `MacroExp.Good d C.corridor C.halfWidth h q ((1 - C.density)/4)` and
`¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n)`, and every
`y ∈ MacroExp.nbrs (MacroExp.pendZ d n h)`,

  `h.prob (fun _ => q) (Assembly.levelEvent d n C q h y)ᶜ ≤ (1 - C.density)/16`.

`Assembly.levelEvent d n C q h y` is the event, in the configuration `omega` read on the fresh
incoming corridor, that either `y` is no longer a pending macro-neighbour of the examined vertex
`z = MacroExp.pendZ d n h` after the examination is accepted, or else some set `B` contained in
*every* certificate level box about `y` is reached from the origin, inside the accepted
transcript's inspected sites together with the outgoing corridor `E z y`, with pinned probability
larger than `1 - C.eps/8`.  The event `Assembly.levelEvent` is `private`; `LevelOpus.LevelEvent`
below repeats it character for character.

## What this file contains

* `exists_firstEntry` and `orderedFaceCrossing`: the deterministic ordered-face crossing.  A
  confined open path from a source outside `D 0` to a target inside `D K`, for nested regions with
  the gate property, crosses the face `D j \ D (j+1)` for every `j ≤ K`, and its prefix up to that
  crossing stays outside `D j`; `orderedFaceCrossing_prefix_avoids` says the crossings occur in
  order of increasing depth.  Without this the per-level conditional failure estimates cannot be
  iterated against the full-corridor success event.

* `entry_of_levelEvent`, `levelEvent_subset_entryEvent`: the level event forces an entry.  Its
  second disjunct asks for a connection of positive probability from the origin into `E z y`, and
  the origin is not in `E z y`; by the first-entry lemma the connection crosses the boundary of
  `E z y` at a site that the accepted transcript has already recorded open, along a path that never
  enters `E z y` and is therefore entirely pinned.  So the level event is contained in the
  deterministic `EntryEvent`.

* `notMem_M_of_adj_mem_E`, `entry_outside_M`, `entryBound_of_directional`: the budget mismatch.  No
  site adjacent to `E z y` lies in `M z`, the target box of the incoming reservation, so the
  hypothesis above demands a failure budget `(1 - density)/16` for an event whose target is
  disjoint from the target of the only probabilistic clause of `MacroExp.Good`, whose budget is
  `(1 - density)/4`, four times larger.

* `not_hDirectionalNoCover`: the hypothesis is false once `MacroExp.Good.cover` is dropped.  The
  transcript `badTr` records a straight open segment from the origin to the centre of `M zdir` and
  a closed wall across the incoming corridor at transverse level `5r`.  It satisfies `zero_mem`,
  `inspected_thin`, `cert` and `reserve` -- the last with probability exactly `1` -- and it is not
  terminal, yet the level event of the pending direction `ydir` is empty, so the left-hand side of
  the target inequality is `1` and the right-hand side at most `1/16`.

## The reading of that refutation

`MacroExp.Good` has five fields and `cover` is the only one `badTr` violates.  `cover` is a
deterministic inclusion: it says the inspected sites lie in the central box of the origin together
with the edge regions of already-examined macro-edges, whence
`MacroExp.inspected_disjoint_pending_E`, that the incoming corridor is unread.  It carries no
probability.  So a proof of the target inequality must obtain the improvement from `(1-density)/4`
to `(1-density)/16` from `reserve` and the freshness that `cover` supplies -- and freshness is
exactly what makes the entry into `E z y` a random event about which `Good` records nothing:
`M z` has planar radius `3r`, the entry sites sit on the boundary of `Q z` at planar radius `5r`,
and by `notMem_M_of_adj_mem_E` the two are never adjacent.

The manuscript (`v14/gapclosed.pdf`, Lemma 7.9) carries its invariant at tolerance
`δ_c = min{δ₁, ρ/4, 1/2}`, where `δ₁` is the input tolerance of its corridor-move lemma 7.5 chosen
so that the *output* error is `ρ/32`; the per-direction bound is then `ρ/32 + (1-δ₂)^K ≤ ρ/16`.
The Lean assembly instead instantiates the invariant at the largest tolerance `MacroExp.StepBound`
allows, `δ = (1 - density)/4`, and so keeps only the `ρ/4` half of `δ_c`.  Nothing in
`MacroExp.Good` at that tolerance can produce a `ρ/32` corridor bound.
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

/-- **What the target inequality really asserts.**  The hypothesis `hdirectional` of
`Assembly.site_no_percolation_at_criticality`, stated inline, forces at every good non-terminal
transcript an estimate with failure budget `(1 - density)/16` for the *entry* event: after the
examination the origin must be joined, without entering the outgoing corridor, to a recorded open
site adjacent to it, and by `notMem_M_of_adj_mem_E` no such site lies in the target box `M z` of
the incoming reservation.

The only probabilistic clause of `MacroExp.Good`, its `reserve` field, bounds the failure of the
connection to `M z` by `(1 - density)/4`.  So the hypothesis demands, on a different event, a
budget four times smaller than the invariant supplies; `not_hDirectionalNoCover` shows that the
`reserve` field together with the other non-`cover` clauses does not supply it. -/
theorem entryBound_of_directional (hd : 2 ≤ d)
    (hdir : ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval),
      C.WellFormed → C.ValidAt2 q →
      ∀ (n : ℕ) (h : MacroExp.Tr d),
        MacroExp.Good d C.corridor C.halfWidth (q := q)
          (δ := (1 - (C.density : ℝ)) / 4) h →
        ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
        ∀ y ∈ MacroExp.nbrs (MacroExp.pendZ d n h),
          h.prob (fun _ : Site d => q) (LevelEvent d n C q h y)ᶜ ≤
            (1 - (C.density : ℝ)) / 16)
    (C : LeftImp2.Certificate2 d) (q : unitInterval) (hwf : C.WellFormed) (hv : C.ValidAt2 q)
    (n : ℕ) (h : MacroExp.Tr d)
    (hg : MacroExp.Good d C.corridor C.halfWidth (q := q)
      (δ := (1 - (C.density : ℝ)) / 4) h)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    {y : Site 2} (hy : y ∈ MacroExp.nbrs (MacroExp.pendZ d n h))
    (hyu : y ∉ h.openV ∪ h.closedV)
    (h0 : MacroExp.emb 0 ∉
      MacroExp.E d C.corridor C.halfWidth (MacroExp.pendZ d n h) y) :
    h.prob (fun _ : Site d => q)
        (EntryEvent d C.corridor C.halfWidth n h y)ᶜ ≤ (1 - (C.density : ℝ)) / 16 := by
  refine le_trans (ProbInv.prob_mono h (fun _ : Site d => q) ?_)
    (hdir C q hwf hv n h hg hT y hy)
  exact Set.compl_subset_compl.2
    (levelEvent_subset_entryEvent (d := d) hd C hwf q n h hy hyu h0)

end Level

/-! ## The geometry of one incoming and one outgoing corridor -/

section Geometry

variable {d : ℕ} [NeZero d]

/-- The macro-vertex examined in the counterexample below. -/
def zdir : Site 2 := MacroExp.mvUnit 0 true

/-- The pending direction out of `zdir`. -/
def ydir : Site 2 := zdir + MacroExp.mvUnit 1 true

theorem val_one (hd : 2 ≤ d) : (1 : Fin d).val = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]

theorem zero_ne_one_fin (hd : 2 ≤ d) : (0 : Fin d) ≠ (1 : Fin d) := by
  intro hcon
  have h0 : (0 : Fin d).val = 0 := Fin.val_zero d
  have h1 := val_one (d := d) hd
  rw [hcon] at h0
  omega

theorem emb_zdir_apply_zero : (MacroExp.emb zdir : Site d) (0 : Fin d) = 1 := by
  have hlt : ((0 : Fin d)).val < 2 := by simp
  rw [MacroExp.emb_apply_of_lt zdir hlt]
  have : (⟨((0 : Fin d)).val, hlt⟩ : Fin 2) = (0 : Fin 2) := by
    apply Fin.ext; simp
  rw [this]
  simp [zdir, MacroExp.mvUnit]

theorem emb_zdir_apply_one (hd : 2 ≤ d) : (MacroExp.emb zdir : Site d) (1 : Fin d) = 0 := by
  have hv := val_one (d := d) hd
  have hd1 : d ≠ 1 := by omega
  have hmod : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
  have hlt : ((1 : Fin d)).val < 2 := by omega
  rw [MacroExp.emb_apply_of_lt zdir hlt]
  have hne : (⟨((1 : Fin d)).val, hlt⟩ : Fin 2) ≠ (0 : Fin 2) := by
    intro hcon
    have hval := congrArg Fin.val hcon
    simp at hval
    omega
  simp [zdir, MacroExp.mvUnit, Pi.single_apply, hne, hd1]

theorem emb_ydir_apply_one (hd : 2 ≤ d) : (MacroExp.emb ydir : Site d) (1 : Fin d) = 1 := by
  have hv := val_one (d := d) hd
  have hd1 : d ≠ 1 := by omega
  have hmod : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
  have hlt : ((1 : Fin d)).val < 2 := by omega
  rw [MacroExp.emb_apply_of_lt ydir hlt]
  rw [ydir]
  simp [MacroExp.mvUnit, zdir, Pi.single_apply, hd1, hmod]

theorem emb_ydir_apply_of_ne (hd : 2 ≤ d) {j : Fin d} (hj : j ≠ (1 : Fin d)) :
    (MacroExp.emb ydir : Site d) j = MacroExp.emb zdir j := by
  by_cases hlt : j.val < 2
  · rw [MacroExp.emb_apply_of_lt ydir hlt, MacroExp.emb_apply_of_lt zdir hlt]
    have hne : (⟨j.val, hlt⟩ : Fin 2) ≠ (1 : Fin 2) := by
      intro hcon
      apply hj
      apply Fin.ext
      have := congrArg Fin.val hcon
      simp at this
      rw [this, val_one (d := d) hd]
    simp [ydir, MacroExp.mvUnit, Pi.single_apply, hne]
  · rw [MacroExp.emb_apply_of_not_lt ydir hlt, MacroExp.emb_apply_of_not_lt zdir hlt]

/-- **The outgoing corridor lies strictly beyond the transverse level `5r`.**  Every site of
`E zdir ydir` has second planar coordinate larger than `5 r`. -/
theorem lt_coord_one_of_mem_E_out (hd : 2 ≤ d) (r t : ℕ) {v : Site d}
    (hv : v ∈ MacroExp.E d r t zdir ydir) : 5 * (r : ℤ) < v (1 : Fin d) := by
  classical
  rw [MacroExp.E, Finset.mem_sdiff, MacroExp.mem_hbox] at hv
  obtain ⟨hhull, hQ⟩ := hv
  have hone : ((1 : Fin d)).val < 2 := by have := val_one (d := d) hd; omega
  have hradone : MacroExp.rad (5 * r) t (1 : Fin d) = 5 * (r : ℤ) := by
    unfold MacroExp.rad; rw [if_pos hone]; push_cast; ring
  have hcz : MacroExp.ctr d r zdir (1 : Fin d) = 0 := by
    simp [MacroExp.ctr, emb_zdir_apply_one (d := d) hd]
  have hcy : MacroExp.ctr d r ydir (1 : Fin d) = 20 * (r : ℤ) := by
    simp [MacroExp.ctr, emb_ydir_apply_one (d := d) hd]
  -- off the direction of the move the two centres agree, so the hull gives the box condition
  by_contra hcon
  push_neg at hcon
  apply hQ
  rw [MacroExp.Q, MacroExp.mem_abox]
  intro j
  by_cases hj : j = (1 : Fin d)
  · subst hj
    have h1 := hhull (1 : Fin d)
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := Int.ofNat_nonneg r
    have hmin : min (MacroExp.ctr d r zdir (1 : Fin d)) (MacroExp.ctr d r ydir (1 : Fin d))
        = 0 := by rw [hcz, hcy]; exact min_eq_left (by omega)
    rw [hmin, hradone] at h1
    rw [hcz, hradone]
    omega
  · have h1 := hhull j
    have hceq : MacroExp.ctr d r ydir j = MacroExp.ctr d r zdir j := by
      simp [MacroExp.ctr, emb_ydir_apply_of_ne (d := d) hd hj]
    rw [hceq] at h1
    simpa using h1

end Geometry

/-! ## A transcript with the reservation and without the entry -/

section Bad

variable {d : ℕ} [NeZero d]

theorem emb_zdir_apply_of_ne (hd : 2 ≤ d) {j : Fin d} (hj : j ≠ (0 : Fin d)) :
    (MacroExp.emb zdir : Site d) j = 0 := by
  by_cases hlt : j.val < 2
  · rw [MacroExp.emb_apply_of_lt zdir hlt]
    have hne : (⟨j.val, hlt⟩ : Fin 2) ≠ (0 : Fin 2) := by
      intro hcon
      apply hj
      apply Fin.ext
      have hval := congrArg Fin.val hcon
      simpa using hval
    simp [zdir, MacroExp.mvUnit, Pi.single_apply, hne]
  · rw [MacroExp.emb_apply_of_not_lt zdir hlt]

theorem emb_zero_eq : (MacroExp.emb (0 : Site 2) : Site d) = 0 := by
  funext j
  by_cases hj : j.val < 2
  · rw [MacroExp.emb_apply_of_lt _ hj]; rfl
  · rw [MacroExp.emb_apply_of_not_lt _ hj]; rfl

theorem ctr_zdir (hd : 2 ≤ d) (r : ℕ) :
    (MacroExp.ctr d r zdir : Site d) = Pi.single (0 : Fin d) (20 * (r : ℤ)) := by
  funext j
  by_cases hj : j = (0 : Fin d)
  · subst hj
    simp [MacroExp.ctr, emb_zdir_apply_zero]
  · simp [MacroExp.ctr, emb_zdir_apply_of_ne (d := d) hd hj, Pi.single_apply, hj]

/-- The straight segment of recorded open sites from the origin to the centre of the target box of
`zdir`. -/
def lineL (d r : ℕ) [NeZero d] : Finset (Site d) :=
  (Finset.range (20 * r + 1)).image (fun k : ℕ => (Pi.single (0 : Fin d) (k : ℤ) : Site d))

theorem mem_lineL {r : ℕ} {x : Site d} :
    x ∈ lineL d r ↔ ∃ k : ℕ, k ≤ 20 * r ∧ x = Pi.single (0 : Fin d) (k : ℤ) := by
  classical
  simp only [lineL, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩

theorem coord_one_lineL (hd : 2 ≤ d) {r : ℕ} {x : Site d} (hx : x ∈ lineL d r) :
    x (1 : Fin d) = 0 := by
  obtain ⟨k, -, rfl⟩ := mem_lineL.1 hx
  have hne : (1 : Fin d) ≠ (0 : Fin d) := (zero_ne_one_fin (d := d) hd).symm
  simp [Pi.single_apply, hne]

theorem lineL_subset_thin (hd : 2 ≤ d) (r t : ℕ) :
    (↑(lineL d r) : Set (Site d)) ⊆ MacroExp.thin d t := by
  intro x hx
  obtain ⟨k, -, rfl⟩ := mem_lineL.1 (Finset.mem_coe.1 hx)
  intro j hj0 hj1
  simp [Pi.single_apply, hj0]

/-- The recorded closed wall inside the incoming corridor: every site of that corridor that could
be adjacent to the outgoing one. -/
def blockN (d r t : ℕ) [NeZero d] : Finset (Site d) :=
  (MacroExp.E d r t 0 zdir).filter (fun x => 5 * (r : ℤ) ≤ x (1 : Fin d))

theorem mem_blockN {r t : ℕ} {x : Site d} :
    x ∈ blockN d r t ↔ x ∈ MacroExp.E d r t 0 zdir ∧ 5 * (r : ℤ) ≤ x (1 : Fin d) := by
  classical
  simp [blockN]

theorem lineL_disjoint_blockN (hd : 2 ≤ d) {r t : ℕ} (hr : 0 < r) :
    Disjoint (lineL d r) (blockN d r t) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  have h1 := coord_one_lineL (d := d) hd hx
  have h2 := (mem_blockN.1 hx').2
  have : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  omega

/-- **The counterexample transcript.**  One macro-vertex is occupied, three of its neighbours are
determined closed, and the fourth, `zdir`, is the pending frontier vertex.  The recorded sites are
a straight open segment from the origin to the centre of the target box of `zdir`, together with a
recorded closed wall at transverse level `5r` of the incoming corridor. -/
def badTr (d r t : ℕ) [NeZero d] : MacroExp.Tr d where
  inspected := lineL d r ∪ blockN d r t
  openSites := lineL d r
  openSites_subset := Finset.subset_union_left
  openV := {0}
  closedV := (MacroExp.nbrs (0 : Site 2)).erase zdir

@[simp] theorem badTr_inspected (r t : ℕ) :
    (badTr d r t).inspected = lineL d r ∪ blockN d r t := rfl

@[simp] theorem badTr_openSites (r t : ℕ) : (badTr d r t).openSites = lineL d r := rfl

@[simp] theorem badTr_openV (r t : ℕ) : (badTr d r t).openV = {0} := rfl

@[simp] theorem badTr_closedV (r t : ℕ) :
    (badTr d r t).closedV = (MacroExp.nbrs (0 : Site 2)).erase zdir := rfl

theorem zdir_mem_nbrs_zero : zdir ∈ MacroExp.nbrs (0 : Site 2) :=
  MacroExp.mem_nbrs_iff.2 ⟨0, true, by simp [zdir]⟩

theorem zdir_ne_zero : zdir ≠ (0 : Site 2) := by
  intro hcon
  have := congrFun hcon (0 : Fin 2)
  simp [zdir, MacroExp.mvUnit] at this

theorem ydir_mem_nbrs_zdir : ydir ∈ MacroExp.nbrs zdir :=
  MacroExp.mem_nbrs_iff.2 ⟨1, true, rfl⟩

theorem ydir_ne_zdir : ydir ≠ zdir := by
  intro hcon
  have := congrFun hcon (1 : Fin 2)
  simp [ydir, MacroExp.mvUnit] at this

theorem ydir_notMem_nbrs_zero : ydir ∉ MacroExp.nbrs (0 : Site 2) := by
  intro hcon
  obtain ⟨i, b, hb⟩ := MacroExp.mem_nbrs_iff.1 hcon
  have h0 := congrFun hb (0 : Fin 2)
  have h1 := congrFun hb (1 : Fin 2)
  fin_cases i <;> cases b <;>
    simp [ydir, zdir, MacroExp.mvUnit, Pi.single_apply] at h0 h1

theorem badTr_explored (r t : ℕ) {u : Site 2}
    (hu : u ∈ (badTr d r t).explored (zdGraph 2) 0) : u = 0 := by
  have h := mem_of_mem_siteCluster (zdGraph 2)
    (↑((badTr d r t).openV) : Set (Site 2)) hu
  simpa using h

theorem badTr_zero_mem_explored (r t : ℕ) :
    (0 : Site 2) ∈ (badTr d r t).explored (zdGraph 2) 0 :=
  mem_siteCluster_self _ _ (by simp)

theorem badTr_boundary (r t : ℕ) :
    (badTr d r t).boundary (zdGraph 2) (box 2 1) 0 = {zdir} := by
  classical
  ext v
  constructor
  · rintro ⟨hvA, hvo, hvc, hor⟩
    have hv0 : v ≠ 0 := by
      intro hcon; exact hvo (by simp [hcon])
    obtain ⟨u, hu, hadj⟩ := hor.resolve_left hv0
    rw [badTr_explored (d := d) r t hu] at hadj
    have hvn : v ∈ MacroExp.nbrs (0 : Site 2) := MacroExp.mem_nbrs_of_adj hadj
    have : v = zdir := by
      by_contra hne
      exact hvc (by simpa using Finset.mem_erase.2 ⟨hne, hvn⟩)
    simpa using this
  · intro hv
    have hv' : v = zdir := by simpa using hv
    subst hv'
    refine ⟨?_, ?_, ?_, Or.inr ⟨0, badTr_zero_mem_explored (d := d) r t,
      MacroExp.adj_of_mem_nbrs zdir_mem_nbrs_zero⟩⟩
    · rw [mem_box]
      intro j
      fin_cases j <;> simp [zdir, MacroExp.mvUnit, Pi.single_apply]
    · simpa using zdir_ne_zero
    · simpa using Finset.notMem_erase zdir (MacroExp.nbrs (0 : Site 2))

theorem badTr_not_terminal (r t : ℕ) :
    ¬ (badTr d r t).Terminal (zdGraph 2) (box 2 1) 0 (MacroExp.tgt 1) := by
  rintro (hR | hB)
  · obtain ⟨v, hvt, hvex⟩ := hR
    have hv0 : v = 0 := badTr_explored (d := d) r t hvex
    subst hv0
    obtain ⟨i, hi⟩ :=
      MacroExp.exists_coord_of_mem_innerBoundary (Finset.mem_coe.1 hvt)
    simp at hi
  · have : zdir ∈ (badTr d r t).boundary (zdGraph 2) (box 2 1) 0 := by
      rw [badTr_boundary]; rfl
    rw [hB] at this
    exact this

theorem badTr_pendZ (r t : ℕ) : MacroExp.pendZ d 1 (badTr d r t) = zdir := by
  have hT := badTr_not_terminal (d := d) r t
  have hmem := MacroExp.pendZ_mem d 1
    (MacroExp.boundary_nonempty_of_not_terminal d 1 hT)
  rw [badTr_boundary] at hmem
  simpa using hmem

theorem badTr_pendW (r t : ℕ) : MacroExp.pendW d 1 (badTr d r t) = 0 := by
  unfold MacroExp.pendW
  split_ifs with hex
  · exact badTr_explored (d := d) r t hex.choose_spec.1
  · rfl

theorem badTr_pending_zero (r t : ℕ) : MacroExp.pending d (badTr d r t) 0 = {zdir} := by
  classical
  ext v
  rw [MacroExp.mem_pending, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hnd⟩
    by_contra hne
    have hmem : v ∈ (MacroExp.nbrs (0 : Site 2)).erase zdir := Finset.mem_erase.2 ⟨hne, hv⟩
    exact hnd (Finset.mem_union_right _ hmem)
  · rintro rfl
    refine ⟨zdir_mem_nbrs_zero, ?_⟩
    intro hcon
    rcases Finset.mem_union.1 hcon with h | h
    · exact zdir_ne_zero (by simpa using h)
    · have h' : zdir ∈ (MacroExp.nbrs (0 : Site 2)).erase zdir := h
      exact (Finset.mem_erase.1 h').1 rfl

/-- The straight segment is connected whenever all its sites are open. -/
theorem line_reachable (W : Set (Site d)) :
    ∀ m : ℕ, (∀ k : ℕ, k ≤ m → (Pi.single (0 : Fin d) (k : ℤ) : Site d) ∈ W) →
      (openSiteGraph (zdGraph d) W).Reachable
        (Pi.single (0 : Fin d) ((0 : ℕ) : ℤ)) (Pi.single (0 : Fin d) ((m : ℕ) : ℤ)) := by
  intro m
  induction m with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ m ih =>
      intro hmem
      have hprev := ih (fun k hk => hmem k (by omega))
      have hstepAdj : (zdGraph d).Adj (Pi.single (0 : Fin d) ((m : ℕ) : ℤ))
          (Pi.single (0 : Fin d) (((m + 1 : ℕ)) : ℤ)) := by
        rw [zdGraph_adj_iff]
        refine ⟨(0 : Fin d), Or.inl ?_⟩
        rw [← Pi.single_add]
        congr 1
      have hadj : (openSiteGraph (zdGraph d) W).Adj
          (Pi.single (0 : Fin d) ((m : ℕ) : ℤ))
          (Pi.single (0 : Fin d) (((m + 1 : ℕ)) : ℤ)) :=
        (openSiteGraph_adj_iff' _ _ _ _).2
          ⟨hstepAdj, hmem m (by omega), hmem (m + 1) (by omega)⟩
      exact hprev.trans hadj.reachable

theorem emb_zero_eq_single : (MacroExp.emb (0 : Site 2) : Site d)
    = Pi.single (0 : Fin d) ((0 : ℕ) : ℤ) := by
  rw [emb_zero_eq]
  simp

/-- **The transcript carries the incoming reservation with probability one.**  The recorded open
segment already joins the origin to the centre of the target box of `zdir` inside the inspected
sites, so the reservation event holds for every configuration. -/
theorem badTr_reservation_eq_one (hd : 2 ≤ d) (r t : ℕ) (q : unitInterval) :
    (badTr d r t).prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d)
        (↑((badTr d r t).inspected ∪ MacroExp.E d r t 0 zdir) : Set (Site d))
        (MacroExp.emb 0) (↑(MacroExp.M d r t zdir) : Set (Site d))) = 1 := by
  classical
  set h := badTr d r t with hh
  set S : Set (Site d) := (↑(h.inspected ∪ MacroExp.E d r t 0 zdir) : Set (Site d)) with hS
  have hpre : substitute (↑h.inspected : Set (Site d)) h.state ⁻¹'
      (connWithinSet (zdGraph d) S (MacroExp.emb 0)
        (↑(MacroExp.M d r t zdir) : Set (Site d))) = Set.univ := by
    ext omega'
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    set sigma : SiteConfig (Site d) :=
      substitute (↑h.inspected : Set (Site d)) h.state omega' with hsigma
    have hline : ∀ x ∈ lineL d r, x ∈ sigma ∩ S := by
      intro x hx
      have hxI : x ∈ (↑h.inspected : Set (Site d)) := by
        simp only [hh, badTr_inspected, Finset.coe_union]
        exact Or.inl (Finset.mem_coe.2 hx)
      refine ⟨?_, ?_⟩
      · rw [hsigma, mem_substitute_of_mem h.state hxI]
        show x ∈ h.openSites
        simpa [hh] using hx
      · rw [hS, Finset.coe_union]
        exact Or.inl hxI
    have hmem : ∀ k : ℕ, k ≤ 20 * r →
        (Pi.single (0 : Fin d) (k : ℤ) : Site d) ∈ sigma ∩ S := by
      intro k hk
      exact hline _ (mem_lineL.2 ⟨k, hk, rfl⟩)
    have hreach := line_reachable (sigma ∩ S) (20 * r) hmem
    refine (mem_connWithinSet_iff (zdGraph d) S (MacroExp.emb 0)
      (↑(MacroExp.M d r t zdir) : Set (Site d)) sigma).2
      ⟨MacroExp.ctr d r zdir, Finset.mem_coe.2 (MacroExp.ctr_mem_M r t zdir), ?_, ?_⟩
    · rw [emb_zero_eq_single]
      exact hmem 0 (by omega)
    · rw [emb_zero_eq_single, ctr_zdir (d := d) hd r]
      have hcast : ((20 * r : ℕ) : ℤ) = 20 * (r : ℤ) := by push_cast; ring
      rw [← hcast]
      exact hreach
  rw [FRDom.Transcript.prob_eq, pinnedProb, hpre]
  simp

theorem ydir_ne_zero : ydir ≠ (0 : Site 2) := by
  intro hcon
  have := congrFun hcon (1 : Fin 2)
  simp [ydir, zdir, MacroExp.mvUnit, Pi.single_apply] at this

/-- Adjacent sites differ by one in every coordinate. -/
theorem coord_ge_of_adj {u v : Site d} (hadj : (zdGraph d).Adj u v) (j : Fin d) :
    v j - 1 ≤ u j := by
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff u v).1 hadj
  · have := congrFun hi j
    simp only [Pi.add_apply, Pi.single_apply] at this
    split_ifs at this <;> omega
  · have := congrFun hi j
    simp only [Pi.add_apply, Pi.single_apply] at this
    split_ifs at this <;> omega

/-- **The level event is empty at this transcript.**  The recorded closed wall `blockN` occupies
every site of the incoming corridor at transverse level `5r`, and the recorded open segment stays
at transverse level `0`; so after the examination no open site of the origin's cluster is adjacent
to the outgoing corridor, and the source estimate of the level event is unattainable. -/
theorem badTr_levelEvent_eq_empty (hd : 2 ≤ d) (C : LeftImp2.Certificate2 d)
    (hwf : C.WellFormed) (q : unitInterval) :
    LevelEvent d 1 C q (badTr d C.corridor C.halfWidth) ydir = ∅ := by
  classical
  have hr : 0 < C.corridor := corridor_pos hwf
  have hrz : (1 : ℤ) ≤ (C.corridor : ℤ) := by exact_mod_cast hr
  have hzdir : MacroExp.pendZ d 1 (badTr d C.corridor C.halfWidth) = zdir :=
    badTr_pendZ C.corridor C.halfWidth
  have hpendW : MacroExp.pendW d 1 (badTr d C.corridor C.halfWidth) = 0 :=
    badTr_pendW C.corridor C.halfWidth
  have hregion : MacroExp.region d C.corridor C.halfWidth 1
      (badTr d C.corridor C.halfWidth)
      = MacroExp.E d C.corridor C.halfWidth 0 zdir \
        (lineL d C.corridor ∪ blockN d C.corridor C.halfWidth) := by
    rw [MacroExp.region, hpendW, hzdir]
    rfl
  rw [Set.eq_empty_iff_forall_notMem]
  intro omega homega
  set hp := MacroExp.accepted d C.corridor C.halfWidth 1
    (badTr d C.corridor C.halfWidth) omega with hhp
  have hpend : ydir ∈ MacroExp.pending d hp
      (MacroExp.pendZ d 1 (badTr d C.corridor C.halfWidth)) := by
    rw [MacroExp.mem_pending, hzdir]
    refine ⟨ydir_mem_nbrs_zdir, ?_⟩
    intro hcon
    rcases Finset.mem_union.1 hcon with hop | hcl
    · have hop' : ydir ∈ insert zdir ({0} : Finset (Site 2)) := by
        simpa [hhp, MacroExp.accepted, hzdir] using hop
      rcases Finset.mem_insert.1 hop' with h1 | h1
      · exact ydir_ne_zdir h1
      · exact ydir_ne_zero (by simpa using h1)
    · have hcl' : ydir ∈ (MacroExp.nbrs (0 : Site 2)).erase zdir := by
        simpa [hhp, MacroExp.accepted] using hcl
      exact ydir_notMem_nbrs_zero (Finset.mem_erase.1 hcl').2
  -- the outgoing corridor is beyond level `5r`, the origin is not
  have h0 : MacroExp.emb 0 ∉
      MacroExp.E d C.corridor C.halfWidth
        (MacroExp.pendZ d 1 (badTr d C.corridor C.halfWidth)) ydir := by
    rw [hzdir]
    intro hcon
    have := lt_coord_one_of_mem_E_out (d := d) hd C.corridor C.halfWidth hcon
    rw [emb_zero_eq] at this
    simp at this
    omega
  have hzy : (zdGraph 2).Adj (MacroExp.pendZ d 1 (badTr d C.corridor C.halfWidth)) ydir := by
    rw [hzdir]; exact MacroExp.adj_of_mem_nbrs ydir_mem_nbrs_zdir
  obtain ⟨u, ⟨v, hvE, huv⟩, hconn⟩ :=
    entry_of_levelEvent (d := d) hd C hwf q 1 (badTr d C.corridor C.halfWidth) hzy h0 hpend homega
  -- the entry site sits at transverse level at least `5r`
  have hvcoord : 5 * (C.corridor : ℤ) < v (1 : Fin d) := by
    rw [hzdir] at hvE
    exact lt_coord_one_of_mem_E_out (d := d) hd C.corridor C.halfWidth hvE
  have hucoord : 5 * (C.corridor : ℤ) ≤ u (1 : Fin d) := by
    have := coord_ge_of_adj (d := d) huv (1 : Fin d)
    omega
  -- but every recorded open site of the accepted transcript sits below it
  have humem : u ∈ (↑hp.openSites : Set (Site d)) :=
    (mem_of_reachable_of_connWithin hconn hconn.2).1
  have huopen : (badTr d C.corridor C.halfWidth).state u ∨
      (u ∈ MacroExp.region d C.corridor C.halfWidth 1 (badTr d C.corridor C.halfWidth) ∧
        u ∈ omega) := by
    have h1 : hp.state u := Finset.mem_coe.1 humem
    rw [hhp, MacroExp.accepted, FRDom.Transcript.step_state] at h1
    exact h1
  rcases huopen with hL | hR
  · have hL' : u ∈ lineL d C.corridor := hL
    have := coord_one_lineL (d := d) hd hL'
    omega
  · rw [hregion] at hR
    have hRE : u ∈ MacroExp.E d C.corridor C.halfWidth 0 zdir :=
      (Finset.mem_sdiff.1 hR.1).1
    have hRnot : u ∉ lineL d C.corridor ∪ blockN d C.corridor C.halfWidth :=
      (Finset.mem_sdiff.1 hR.1).2
    exact hRnot (Finset.mem_union_right _ (mem_blockN.2 ⟨hRE, hucoord⟩))

theorem prob_univ (h : MacroExp.Tr d) (q : unitInterval) :
    h.prob (fun _ : Site d => q) (Set.univ : Set (SiteConfig (Site d))) = 1 := by
  rw [FRDom.Transcript.prob_eq, pinnedProb]
  simp

theorem badTr_inspected_thin (hd : 2 ≤ d) (r t : ℕ) :
    (↑((badTr d r t).inspected) : Set (Site d)) ⊆ MacroExp.thin d t := by
  rw [badTr_inspected, Finset.coe_union]
  refine Set.union_subset (lineL_subset_thin hd r t) ?_
  intro x hx
  have hxE : x ∈ MacroExp.E d r t 0 zdir := (mem_blockN.1 (Finset.mem_coe.1 hx)).1
  exact MacroExp.E_subset_thin hd r t 0 zdir (Finset.mem_coe.2 hxE)

theorem badTr_cert (r t : ℕ) :
    ∀ z ∈ (badTr d r t).openV, ∃ a ∈ MacroExp.M d r t z,
      (↑((badTr d r t).openSites) : Set (Site d)) ∈
        connWithin (zdGraph d) (↑((badTr d r t).inspected) : Set (Site d))
          (MacroExp.emb 0) a := by
  intro z hz
  have hz0 : z = 0 := by simpa using hz
  subst hz0
  refine ⟨MacroExp.emb 0, MacroExp.emb_zero_mem_M r t, ?_⟩
  have hmem : (MacroExp.emb 0 : Site d) ∈ lineL d r := by
    rw [emb_zero_eq_single]
    exact mem_lineL.2 ⟨0, by omega, rfl⟩
  refine ⟨⟨?_, ?_⟩, SimpleGraph.Reachable.refl _⟩
  · exact Finset.mem_coe.2 hmem
  · rw [badTr_inspected, Finset.coe_union]
    exact Or.inl (Finset.mem_coe.2 hmem)

end Bad

/-! ## The refutation -/

section Refutation

/-- **The hypothesis `hdirectional` of `Assembly.site_no_percolation_at_criticality`, with the
invariant `MacroExp.Good` replaced by its four clauses other than `cover`.**

`MacroExp.Good` has exactly five fields: `zero_mem`, `inspected_thin`, `cert`, `reserve` and
`cover`.  The first four are listed here verbatim; the conclusion is the target inequality,
verbatim.  Only `cover`, a deterministic inclusion of the inspected sites in the union of the
central box of the origin and the edge regions of already-examined macro-edges, is omitted. -/
def HDirectionalNoCover (d : ℕ) [NeZero d] : Prop :=
  ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval),
    C.WellFormed → C.ValidAt2 q →
    ∀ (n : ℕ) (h : MacroExp.Tr d),
      (0 : Site 2) ∈ h.openV →
      (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d C.halfWidth →
      (∀ z ∈ h.openV, ∃ a ∈ MacroExp.M d C.corridor C.halfWidth z,
        (↑h.openSites : Set (Site d)) ∈
          connWithin (zdGraph d) (↑h.inspected : Set (Site d)) (MacroExp.emb 0) a) →
      (∀ z ∈ h.openV, ∀ y ∈ MacroExp.pending d h z,
        MacroExp.reservationBound d C.corridor C.halfWidth q
          ((1 - (C.density : ℝ)) / 4) h z y) →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ MacroExp.nbrs (MacroExp.pendZ d n h),
        h.prob (fun _ : Site d => q) (LevelEvent d n C q h y)ᶜ ≤ (1 - (C.density : ℝ)) / 16

/-- **The directional level bound does not follow from the probabilistic content of the
invariant.**

At the transcript `badTr` the incoming reservation of `MacroExp.Good` holds with probability one,
the origin is occupied, everything inspected lies in the slab and every occupied macro-vertex
carries its certificate; the exploration has not terminated and `ydir` is a pending direction of
the vertex examined next.  Yet the level event for that direction is empty, so the left-hand side
of the target inequality is `1` while its right-hand side is at most `1/16`.

The transcript violates only `MacroExp.Good.cover`, which is a deterministic inclusion carrying no
probability.  So a proof of the target inequality has to extract the improvement from `ρ/4` to
`ρ/16` out of `cover` alone -- and `cover` says only that the incoming corridor is unread, which is
precisely what makes the entry into the outgoing corridor a random event about which the invariant
records nothing. -/
theorem not_hDirectionalNoCover (d : ℕ) [NeZero d] (hd : 3 ≤ d) : ¬ HDirectionalNoCover d := by
  classical
  intro hdir
  have hd2 : 2 ≤ d := by omega
  obtain ⟨q, hq1, hqpos⟩ := exists_thetaSite_pos d (by omega)
  obtain ⟨C, hwf, hv, -⟩ := LeftImp2.exists_wellFormed2_validAt2 d q hq1 hqpos
  have hrho : 0 < 1 - (C.density : ℝ) := by
    have h1 := hwf.eps_pos
    have h2 := hwf.eps_le
    linarith
  have hrho1 : 1 - (C.density : ℝ) ≤ 1 := by
    have := C.density.2.1
    linarith
  have hres : ∀ z ∈ (badTr d C.corridor C.halfWidth).openV,
      ∀ y ∈ MacroExp.pending d (badTr d C.corridor C.halfWidth) z,
        MacroExp.reservationBound d C.corridor C.halfWidth q ((1 - (C.density : ℝ)) / 4)
          (badTr d C.corridor C.halfWidth) z y := by
    intro z hz y hy
    have hz0 : z = 0 := by simpa using hz
    subst hz0
    rw [badTr_pending_zero] at hy
    have hy' : y = zdir := by simpa using hy
    subst hy'
    unfold MacroExp.reservationBound MacroExp.reservationEvent
    rw [badTr_reservation_eq_one (d := d) hd2 C.corridor C.halfWidth q]
    linarith
  have hy : ydir ∈ MacroExp.nbrs (MacroExp.pendZ d 1 (badTr d C.corridor C.halfWidth)) := by
    rw [badTr_pendZ]
    exact ydir_mem_nbrs_zdir
  have hb := hdir C q hwf hv 1 (badTr d C.corridor C.halfWidth) (by simp)
    (badTr_inspected_thin (d := d) hd2 C.corridor C.halfWidth)
    (badTr_cert (d := d) C.corridor C.halfWidth) hres
    (badTr_not_terminal (d := d) C.corridor C.halfWidth) ydir hy
  rw [badTr_levelEvent_eq_empty (d := d) hd2 C hwf q, Set.compl_empty,
    prob_univ (d := d)] at hb
  linarith

end Refutation

#print axioms KNAll.Site.LevelOpus.exists_firstEntry
#print axioms KNAll.Site.LevelOpus.orderedFaceCrossing
#print axioms KNAll.Site.LevelOpus.entry_of_levelEvent
#print axioms KNAll.Site.LevelOpus.notMem_M_of_adj_mem_E
#print axioms KNAll.Site.LevelOpus.entryBound_of_directional
#print axioms KNAll.Site.LevelOpus.badTr_levelEvent_eq_empty
#print axioms KNAll.Site.LevelOpus.not_hDirectionalNoCover

end LevelOpus
end KNAll.Site

end
