import Hypergraph.CoreStopped

/-!
# Freshness of the next core head

The stopped stub from `z` towards an adjacent head `y` begins on the outgoing face of `Q z`.
If its additional depth is strictly less than `10r`, it ends before the incoming face of `Q y`:
the two macro centres are `20r` apart and both central boxes have radius `5r`.

This strict separation is needed by the recursive core exploration.  The older bound
`10 * s * K ≤ 13 * r` is enough for ordered-face crossing, but is not enough to keep the next
head box unread.
-/

noncomputable section

namespace KNAll.Site.CoreFresh

open Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- The unread part owned by an oriented frontier edge.  Its head box is excluded because that
box is read when the head is first examined. -/
def liveRegion (d r t : Nat) (w z : Site 2) : Finset (Site d) :=
  MacroExp.E d r t w z \ MacroExp.Q d r t z

/-- A stopped prefix of extra depth `< 10r` is disjoint from the next head's central box. -/
theorem stub_disjoint_headQ {r t a : Nat} {z y : Site 2} {i : Fin d} {sigma : Int}
    (ha : a < 10 * r) (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma) :
    Disjoint (Stopped.stub (MacroExp.ctr d r z) i sigma r t a) (MacroExp.Q d r t y) := by
  rw [Finset.disjoint_left]
  intro x hxstub hxQ
  have hstub := (Stopped.mem_stub hsigma).1 hxstub
  have hQi := (MacroExp.mem_abox.1 (show x ∈ MacroExp.abox (MacroExp.ctr d r y) (5 * r) t from hxQ)) i
  have hi2 : i.val < 2 := Stopped.dir_planar hsigma hemb
  have hrad : MacroExp.rad (5 * r) t i = (5 * (r : Nat) : Int) := by
    unfold MacroExp.rad
    rw [if_pos hi2]
    rfl
  rw [hrad] at hQi
  have hctr := Stopped.ctr_sub_apply (d := d) r y z i
  rw [hemb, Pi.single_eq_same] at hctr
  have ha' : ((a : Nat) : Int) < 10 * (r : Int) := by exact_mod_cast ha
  rcases hsigma with hsig | hsig
  · subst sigma
    norm_num [Stopped.lam] at hctr hstub
    omega
  · subst sigma
    norm_num [Stopped.lam] at hctr hstub
    omega

/-- Every level that can be selected by `CoreStopped.stopLevel` has a prefix disjoint from `Q y`
under the recursive depth budget `10*s*K ≤ 10*r`. -/
theorem stopLevel_stub_disjoint_headQ {r t s K : Nat} {h : MacroExp.Tr d}
    {z y : Site 2} {i : Fin d} {sigma : Int} {q : unitInterval} {deltaC : Real}
    {omega : SiteConfig (Site d)}
    (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hsuccess : omega ∉ CoreStopped.noGoodLevel r t s h z y i sigma q deltaC K) :
    Disjoint
      (Stopped.stub (MacroExp.ctr d r z) i sigma r t
        (10 * s * CoreStopped.stopLevel r t s h z y i sigma q deltaC K omega))
      (MacroExp.Q d r t y) := by
  apply stub_disjoint_headQ (hsigma := hsigma) (hemb := hemb)
  have hj := CoreStopped.stopLevel_lt hsuccess
  have hlt : 10 * s * CoreStopped.stopLevel r t s h z y i sigma q deltaC K omega <
      10 * s * K := Nat.mul_lt_mul_of_pos_left hj (by omega)
  omega

/-- A successful stopped reveal preserves freshness of the next head box.  This is the form used
by the recursive macro exploration: the old transcript was fresh at `Q y`, and the only newly
inspected sites are the selected stopped stub. -/
theorem levelTr_inspected_disjoint_headQ {r t s K : Nat} {h : MacroExp.Tr d}
    {z y : Site 2} {i : Fin d} {sigma : Int} {q : unitInterval} {deltaC : Real}
    {omega : SiteConfig (Site d)}
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hfresh : Disjoint h.inspected (MacroExp.Q d r t y))
    (hsuccess : omega ∉ CoreStopped.noGoodLevel r t s h z y i sigma q deltaC K) :
    Disjoint
      (Stopped.levelTr d r t s h z i sigma
        (CoreStopped.stopLevel r t s h z y i sigma q deltaC K omega) omega).inspected
      (MacroExp.Q d r t y) := by
  rw [Stopped.levelTr_inspected, Finset.disjoint_left]
  intro x hx hxQ
  rcases Finset.mem_union.1 hx with hxOld | hxStub
  · exact Finset.disjoint_left.1 hfresh hxOld hxQ
  · exact Finset.disjoint_left.1
      (stopLevel_stub_disjoint_headQ hs hbudget hsigma hemb hsuccess) hxStub hxQ

/-- Once the tail box has already been inspected, the fresh part of a short stub lies in the
owned live region `E(z,y) \ Q(y)`. -/
theorem freshStub_subset_liveRegion {r t a : Nat} {h : MacroExp.Tr d}
    {z y : Site 2} {i : Fin d} {sigma : Int}
    (hr : 0 < r) (hrt : 2 * r ≤ t) (ha : a < 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected) :
    Stopped.stub (MacroExp.ctr d r z) i sigma r t a \ h.inspected ⊆
      liveRegion d r t z y := by
  intro x hx
  rw [Finset.mem_sdiff] at hx
  change x ∈ MacroExp.E d r t z y \ MacroExp.Q d r t y
  rw [Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · have hprotected := Stopped.stub_subset_Q_union_E (d := d) (t := t) hr
      (show a ≤ 17 * r by omega) hrt hsigma hemb hx.1
    rcases Finset.mem_union.1 hprotected with hxQ | hxE
    · exact absurd (hQ hxQ) hx.2
    · exact hxE
  · exact fun hxQy => Finset.disjoint_left.1
      (stub_disjoint_headQ ha hsigma hemb) hx.1 hxQy

/-- The reveal set at the selected successful level is contained in its owner's live region. -/
theorem stopLevel_revealSet_subset_liveRegion {r t s K : Nat} {h : MacroExp.Tr d}
    {z y : Site 2} {i : Fin d} {sigma : Int} {q : unitInterval} {deltaC : Real}
    {omega : SiteConfig (Site d)}
    (hr : 0 < r) (hrt : 2 * r ≤ t) (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (hsuccess : omega ∉ CoreStopped.noGoodLevel r t s h z y i sigma q deltaC K) :
    Stopped.revealSet d r t s h z i sigma
        (CoreStopped.stopLevel r t s h z y i sigma q deltaC K omega) ⊆
      liveRegion d r t z y := by
  apply freshStub_subset_liveRegion hr hrt _ hsigma hemb hQ
  have hj := CoreStopped.stopLevel_lt hsuccess
  have hlt : 10 * s * CoreStopped.stopLevel r t s h z y i sigma q deltaC K omega <
      10 * s * K := Nat.mul_lt_mul_of_pos_left hj (by omega)
  omega

#print axioms KNAll.Site.CoreFresh.stub_disjoint_headQ
#print axioms KNAll.Site.CoreFresh.stopLevel_stub_disjoint_headQ
#print axioms KNAll.Site.CoreFresh.levelTr_inspected_disjoint_headQ
#print axioms KNAll.Site.CoreFresh.freshStub_subset_liveRegion
#print axioms KNAll.Site.CoreFresh.stopLevel_revealSet_subset_liveRegion

end KNAll.Site.CoreFresh

end
