import Hypergraph.CoreDirectionNoGluing
import Hypergraph.TargetAwareWindow

/-!
# Support-owned post-entry windows

The original `CorePostWindowBound` fixes both the support and the relay region to the rectangular
middle box `PostFam.tailO`.  The target-aware window from the proof of the target lemma naturally
has two finite pieces instead: a local coalescence/face box `Q x` and a target-hit box `P x`.
Only their union has to belong to one fresh owner `O`; neither piece has to equal the old
rectangular `tailO`.

`WindowLevel` records exactly that interface.  The local box lies in the shell part of the owner,
the full support `Q x ∪ P x` lies in the owner, and the owner lies strictly inside the fresh tail
level.  The strict inclusion records the unused outer collar.  Its `relay` field has precisely the
pattern-stability form supplied by the target-aware three-factor event: agreement on `Q x` fixes
the canonical face relay, while the other configuration is separately assumed to lie in the
window event and may use `P x` to reach the target.

The resulting `TargetExt.LevelGeometry` uses the original product-independence proof.  In
particular this module does not use `PinnedSiteGluing` or `TargetExt.LevelGeometryD`.
-/

noncomputable section

namespace KNAll.Site.CorePostSupport

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.Corridor

variable {d : Nat} [NeZero d]

/-- A support-owned reliability window for one longitudinal tail level.

`Q x` is the local coalescence/face support and `P x` is the target-hit support.  The common
`owner` may be their union over all contacts.  `interior` is the portion withheld from the shell
pattern used to select the canonical relay. -/
structure WindowLevel (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (c : Site d) (i : Fin d) (sigma : Int) (r t s j m : Nat)
    (Dom : Finset (Site d)) (T : Set (Site d)) where
  owner : Finset (Site d)
  interior : Finset (Site d)
  Q : Site d → Finset (Site d)
  P : Site d → Finset (Site d)
  event : Site d → Set (SiteConfig (Site d))
  interior_subset_owner : interior ⊆ owner
  owner_ssubset_tail : owner ⊂ PostFam.tailD C c i sigma r t s j m
  face_subset_shell : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
    face (PostFam.tailScales C i r t s j m) (PostFam.tailCentre c i sigma r s j) 0 x ⊆
      owner \ interior
  seed_outside_owner : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
    ∀ v ∈ seed (PostFam.tailScales C i r t s j m)
      (PostFam.tailCentre c i sigma r s j) 0 x, v ∉ owner
  Q_subset_shell : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), Q x ⊆ owner \ interior
  P_subset_owner : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), P x ⊆ owner
  determined : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
    DeterminedBy (event x) (↑(Q x ∪ P x) : Set (Site d))
  relay : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), ∀ omega ∈ event x,
    ∃ u ∈ face (PostFam.tailScales C i r t s j m)
        (PostFam.tailCentre c i sigma r s j) 0 x,
      u ∈ omega ∧ ∀ omega' ∈ event x,
        omega' ∩ (↑(Q x) : Set (Site d)) = omega ∩ ↑(Q x) →
          omega' ∈ TargetExt.toTarget (zdGraph d) owner T u
  reliable : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
    1 - 3 * C.delta ^ 2 ≤
      (siteBernoulli (fun _ : Site d => q)).real (event x)

/-- Translation adapter for the target-aware three-factor theorem.  That theorem naturally
returns a connection inside its full finite support `Q x ∪ P x`; this constructor enlarges the
allowed path to the common owner.  No probability or correlation argument occurs in the
translation. -/
def WindowLevel.ofTargetAware
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {T : Set (Site d)}
    (owner interior : Finset (Site d))
    (Q P : Site d → Finset (Site d))
    (event : Site d → Set (SiteConfig (Site d)))
    (hIntO : interior ⊆ owner)
    (hOTail : owner ⊂ PostFam.tailD C c i sigma r t s j m)
    (hface : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      face (PostFam.tailScales C i r t s j m)
        (PostFam.tailCentre c i sigma r s j) 0 x ⊆ owner \ interior)
    (hseed : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      ∀ v ∈ seed (PostFam.tailScales C i r t s j m)
        (PostFam.tailCentre c i sigma r s j) 0 x, v ∉ owner)
    (hQ : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), Q x ⊆ owner \ interior)
    (hP : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), P x ⊆ owner)
    (hdet : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      DeterminedBy (event x) (↑(Q x ∪ P x) : Set (Site d)))
    (hrelaySupport : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), ∀ omega ∈ event x,
      ∃ u ∈ face (PostFam.tailScales C i r t s j m)
          (PostFam.tailCentre c i sigma r s j) 0 x,
        u ∈ omega ∧ ∀ omega' ∈ event x,
          omega' ∩ (↑(Q x) : Set (Site d)) = omega ∩ ↑(Q x) →
            omega' ∈ TargetExt.toTarget (zdGraph d) (Q x ∪ P x) T u)
    (hreliable : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      1 - 3 * C.delta ^ 2 ≤
        (siteBernoulli (fun _ : Site d => q)).real (event x)) :
    WindowLevel C q c i sigma r t s j m Dom T where
  owner := owner
  interior := interior
  Q := Q
  P := P
  event := event
  interior_subset_owner := hIntO
  owner_ssubset_tail := hOTail
  face_subset_shell := hface
  seed_outside_owner := hseed
  Q_subset_shell := hQ
  P_subset_owner := hP
  determined := hdet
  relay := by
    intro x hx omega homega
    obtain ⟨u, hu, huopen, hrelay⟩ := hrelaySupport x hx omega homega
    refine ⟨u, hu, huopen, ?_⟩
    intro omega' homega' hagree
    exact connWithinSet_mono_set (zdGraph d)
      (Finset.coe_subset.2 (Finset.union_subset
        ((hQ x hx).trans Finset.sdiff_subset) (hP x hx))) u T
      (hrelay omega' homega' hagree)
  reliable := hreliable

/-- Direct specialization of `ofTargetAware` to the proved Problem-A event.  The only probability
premises are the three finite component estimates displayed at the end of the argument.  The
finite target `target x` may depend on the contact and is enlarged to the common downstream target
`T` after the deterministic relay has been built. -/
def WindowLevel.ofProblemA
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {T : Set (Site d)}
    (owner interior : Finset (Site d))
    (A Q P target : Site d → Finset (Site d)) {beta : Real}
    (hIntO : interior ⊆ owner)
    (hOTail : owner ⊂ PostFam.tailD C c i sigma r t s j m)
    (hseed : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      ∀ v ∈ seed (PostFam.tailScales C i r t s j m)
        (PostFam.tailCentre c i sigma r s j) 0 x, v ∉ owner)
    (hAQ : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), A x ⊆ Q x)
    (hfaceBoundary : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      face (PostFam.tailScales C i r t s j m)
        (PostFam.tailCentre c i sigma r s j) 0 x ⊆
          innerBoundary (zdGraph d) (Q x))
    (htargetQ : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), Disjoint (target x) (Q x))
    (hQ : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), Q x ⊆ owner \ interior)
    (hP : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), P x ⊆ owner)
    (htarget : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m), (↑(target x) : Set (Site d)) ⊆ T)
    (hbeta : 0 ≤ beta)
    (hcoal : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      1 - TargetAware.componentTolerance C.delta beta <
        (siteBernoulli (fun _ : Site d => q)).real
          (TargetAware.finiteCoalescenceGood (zdGraph d) (A x) (Q x)))
    (hface : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      1 - TargetAware.componentTolerance C.delta beta <
        (siteBernoulli (fun _ : Site d => q)).real
          (TargetAware.finiteHit (zdGraph d) (Q x) (A x)
            (face (PostFam.tailScales C i r t s j m)
              (PostFam.tailCentre c i sigma r s j) 0 x)))
    (htargetHit : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m),
      1 - TargetAware.componentTolerance C.delta beta <
        (siteBernoulli (fun _ : Site d => q)).real
          (TargetAware.finiteHit (zdGraph d) (P x) (A x) (target x))) :
    WindowLevel C q c i sigma r t s j m Dom T := by
  let U : Site d → Finset (Site d) := fun x =>
    face (PostFam.tailScales C i r t s j m)
      (PostFam.tailCentre c i sigma r s j) 0 x
  let event : Site d → Set (SiteConfig (Site d)) := fun x =>
    TargetAware.window (zdGraph d) (A x) (Q x) (P x) (U x) (target x)
  apply WindowLevel.ofTargetAware owner interior Q P event hIntO hOTail
  · intro x hx u hu
    apply hQ x hx
    exact (mem_innerBoundary_iff.1 (hfaceBoundary x hx hu)).1
  · exact hseed
  · exact hQ
  · exact hP
  · intro x hx
    exact TargetAware.determinedBy_window_support (zdGraph d)
      (A x) (Q x) (P x) (U x) (target x)
  · intro x hx omega homega
    obtain ⟨hu, huopen, hrelay⟩ :=
      TargetAware.canonicalRelay_toTarget (zdGraph d) (hAQ x hx)
        (hfaceBoundary x hx) (htargetQ x hx) Finset.subset_union_left
        Finset.subset_union_right omega homega
    refine ⟨TargetAware.canonicalRelay (zdGraph d) (A x) (Q x) (U x) omega,
      hu, huopen, ?_⟩
    intro omega' homega' hagree
    have hconn := hrelay omega' homega' hagree
    obtain ⟨v, hv, huv⟩ :=
      (mem_connWithinSet_iff (zdGraph d) (↑(Q x ∪ P x) : Set (Site d))
        (TargetAware.canonicalRelay (zdGraph d) (A x) (Q x) (U x) omega)
        (↑(target x) : Set (Site d)) omega').1 hconn
    change omega' ∈ connWithinSet (zdGraph d) (↑(Q x ∪ P x) : Set (Site d))
      (TargetAware.canonicalRelay (zdGraph d) (A x) (Q x) (U x) omega) T
    exact (mem_connWithinSet_iff (zdGraph d) (↑(Q x ∪ P x) : Set (Site d))
      (TargetAware.canonicalRelay (zdGraph d) (A x) (Q x) (U x) omega) T omega').2
        ⟨v, htarget x hx hv, huv⟩
  · intro x hx
    exact (TargetAware.one_sub_three_sq_lt_prob_window (zdGraph d)
      (fun _ : Site d => q) (A x) (Q x) (P x) (U x) (target x) hbeta
      (hcoal x hx) (hface x hx) (htargetHit x hx)).le

/-- The complete finite support of a target-aware contact window. -/
def WindowLevel.support {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T) (x : Site d) : Finset (Site d) :=
  W.Q x ∪ W.P x

/-- Every full `Q x ∪ P x` support belongs to its declared owner. -/
theorem WindowLevel.support_subset_owner
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T)
    {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m)) :
    W.support x ⊆ W.owner := by
  rw [WindowLevel.support]
  exact Finset.union_subset
    ((W.Q_subset_shell x hx).trans Finset.sdiff_subset) (W.P_subset_owner x hx)

/-- The strict owner inclusion exposes a genuine unused collar in the fresh tail. -/
theorem WindowLevel.exists_unused_collar
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T) :
    ∃ v ∈ PostFam.tailD C c i sigma r t s j m, v ∉ W.owner :=
  (Finset.ssubset_iff_of_subset W.owner_ssubset_tail.le).1 W.owner_ssubset_tail

/-- Ownership plus freshness of the tail makes the complete `Q x ∪ P x` support fresh. -/
theorem WindowLevel.support_fresh
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom inspected : Finset (Site d)} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T)
    (hfresh : Disjoint (PostFam.tailD C c i sigma r t s j m) inspected)
    {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m)) :
    Disjoint (W.support x) inspected :=
  hfresh.mono_left ((W.support_subset_owner hx).trans W.owner_ssubset_tail.le)

/-- Under the certificate's actual tolerance range, reliability forces every contact window to
be nonempty.  This rules out the vacuous empty-event implementation independently of the collar
witness above. -/
theorem WindowLevel.event_nonempty
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T)
    {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (PostFam.tailD C c i sigma r t s j m)) :
    (W.event x).Nonempty := by
  have heprod : 0 ≤ C.eps * (1 - C.eps) :=
    mul_nonneg hwf.eps_pos.le (sub_nonneg.2 hwf.eps_le_one)
  have hepssq : C.eps ^ 2 ≤ 1 := by nlinarith
  have ha0 : 0 ≤ C.eps ^ 2 / 96 := by positivity
  have hale : C.eps ^ 2 / 96 ≤ (1 : Real) / 96 := by nlinarith
  have hsquare : 0 ≤ ((1 : Real) / 96 - C.eps ^ 2 / 96) *
      ((1 : Real) / 96 + C.eps ^ 2 / 96) :=
    mul_nonneg (sub_nonneg.2 hale) (add_nonneg (by positivity) ha0)
  have hpositive : 0 < 1 - 3 * C.delta ^ 2 := by
    rw [hwf.delta_eq]
    nlinarith
  have hprob : 0 < (siteBernoulli (fun _ : Site d => q)).real (W.event x) :=
    lt_of_lt_of_le hpositive (W.reliable x hx)
  exact nonempty_of_measureReal_ne_zero hprob.ne'

/-- A support-owned window level supplies the shell-supported geometry used by the gluing-free
target extension theorem. -/
def WindowLevel.toLevelGeometry
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {o : Site d} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T)
    (hfit : Fits (PostFam.tailScales C i r t s j m) 0)
    (hDDom : PostFam.tailD C c i sigma r t s j m ⊆ Dom)
    (ho : o ∉ PostFam.tailD C c i sigma r t s j m) :
    TargetExt.LevelGeometry (zdGraph d) Dom o T where
  D := PostFam.tailD C c i sigma r t s j m
  O := W.owner
  Int := W.interior
  U := face (PostFam.tailScales C i r t s j m)
    (PostFam.tailCentre c i sigma r s j) 0
  J := seed (PostFam.tailScales C i r t s j m)
    (PostFam.tailCentre c i sigma r s j) 0
  sel := selC (PostFam.tailScales C i r t s j m)
    (PostFam.tailCentre c i sigma r s j) 0
  Gx := W.event
  hIntO := W.interior_subset_owner
  hOD := W.owner_ssubset_tail.le
  hDDom := hDDom
  ho := ho
  hU := W.face_subset_shell
  hJD := by
    intro x hx
    exact seed_subset_Dbox hfit
      (isContact_of_mem_outerBoundary _ _ _ Dom (by simpa only [PostFam.tailD] using hx))
  hJO := W.seed_outside_owner
  hW3 := by
    intro x hx u hu
    exact connWithin_seed hfit
      (isContact_of_mem_outerBoundary _ _ _ Dom (by simpa only [PostFam.tailD] using hx)) hu
  hsel_sub := fun K => selC_subset _ _ _ K
  hsel_disj := fun K => selC_pairwiseDisjoint_seed _ _ _ hfit K
  hGdet := by
    intro x hx
    exact (W.determined x hx).mono
      (Finset.coe_subset.2 (W.support_subset_owner hx))
  hrelay := by
    intro x hx omega homega
    obtain ⟨u, hu, huopen, hrelay⟩ := W.relay x hx omega homega
    refine ⟨u, hu, huopen, ?_⟩
    intro omega' homega' hagree
    apply hrelay omega' homega'
    ext v
    by_cases hvQ : v ∈ W.Q x
    · have hvShell : v ∈ W.owner \ W.interior := W.Q_subset_shell x hx hvQ
      have hvEq := Set.ext_iff.1 hagree v
      simpa only [Set.mem_inter_iff, Finset.mem_coe, hvQ, hvShell, and_true] using hvEq
    · simp only [Set.mem_inter_iff, Finset.mem_coe, hvQ, and_false]

@[simp] theorem WindowLevel.toLevelGeometry_D
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {o : Site d} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T) (hfit) (hDDom)
    (ho : o ∉ PostFam.tailD C c i sigma r t s j m) :
    (W.toLevelGeometry hfit hDDom ho).D = PostFam.tailD C c i sigma r t s j m := rfl

@[simp] theorem WindowLevel.toLevelGeometry_Gx
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {o : Site d} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T) (hfit) (hDDom)
    (ho : o ∉ PostFam.tailD C c i sigma r t s j m)
    (x : Site d) : (W.toLevelGeometry hfit hDDom ho).Gx x = W.event x := rfl

@[simp] theorem WindowLevel.toLevelGeometry_sel
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {o : Site d} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T) (hfit) (hDDom)
    (ho : o ∉ PostFam.tailD C c i sigma r t s j m)
    (L : Finset (Site d)) :
    (W.toLevelGeometry hfit hDDom ho).sel L =
      selC (PostFam.tailScales C i r t s j m) (PostFam.tailCentre c i sigma r s j) 0 L := rfl

@[simp] theorem WindowLevel.toLevelGeometry_J
    {C : LeftImp2.Certificate2 d} {q : unitInterval}
    {c : Site d} {i : Fin d} {sigma : Int} {r t s j m : Nat}
    {Dom : Finset (Site d)} {o : Site d} {T : Set (Site d)}
    (W : WindowLevel C q c i sigma r t s j m Dom T) (hfit) (hDDom)
    (ho : o ∉ PostFam.tailD C c i sigma r t s j m)
    (x : Site d) :
    (W.toLevelGeometry hfit hDDom ho).J x =
      seed (PostFam.tailScales C i r t s j m) (PostFam.tailCentre c i sigma r s j) 0 x := rfl

/-! ## All-level interface and the downstream bridge -/

/-- The flexible replacement for `CorePost.CorePostWindowBound` at one stopped level.  It owns
one target-aware window datum for every target-extension level. -/
structure CorePostWindowBound (C : LeftImp2.Certificate2 d) (q : unitInterval)
    (c : Site d) (i : Fin d) (sigma : Int) (r t s j : Nat)
    (Dom : Finset (Site d)) (T : Set (Site d)) where
  window : ∀ m, m < C.levels → WindowLevel C q c i sigma r t s j m Dom T

/-- A support-owned bound gives the complete deterministic/probabilistic family at one stopped
level.  This is the direct replacement for the strict
`CorePostNoGluing.familyAt_of_corePostWindowBound` bridge. -/
noncomputable def familyAt_of_corePostWindowBound
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    {j : Nat} {omega : SiteConfig (Site d)}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t) (hj : j < K)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hthin : (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh : Disjoint h.inspected (MacroExp.E d r t z y))
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
      (CorePost.levelDom r t s h z y i sigma j omega)
      (↑(CoreRes.target (d := d) r y) : Set (Site d))) :
    CorePostNoGluing.FamilyAt C q r t s h z y i sigma j omega := by
  let Dom := CorePost.levelDom r t s h z y i sigma j omega
  let T : Set (Site d) := ↑(CoreRes.target (d := d) r y)
  have hiplanar : i.val < 2 := Stopped.dir_planar hsigma hemb
  have hthinDom : (↑Dom : Set (Site d)) ⊆ MacroExp.thin d t := by
    intro x hx
    simp only [Finset.mem_coe, Dom, CorePost.levelDom, Finset.mem_union,
      Stopped.levelTr_inspected] at hx
    rcases hx with (hx | hx) | hx
    · exact hthin (Finset.mem_coe.2 hx)
    · exact PostFam.stub_subset_thin hd hiplanar hsigma hrt (Finset.mem_coe.2 hx)
    · exact MacroExp.E_subset_thin hd r t z y (Finset.mem_coe.2 hx)
  have hfitAll : ∀ m,
      Fits (PostFam.tailScales C i r t s j (PostFam.clipLevel C m)) 0 := by
    intro m
    exact PostFam.tail_fits C hj (PostFam.clipLevel_lt C hwf m)
      hlong hplanar htrans i
  have hsubAll : ∀ m,
      PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j
          (PostFam.clipLevel C m) ⊆ Dom := by
    intro m x hx
    apply Finset.mem_union_right
    exact PostFam.tailD_subset_E (t := t) hd C hsigma hemb hj
      (PostFam.clipLevel_lt C hwf m) (by omega) hlong hx
  have hfreshAll : ∀ m,
      Disjoint
        (PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j
          (PostFam.clipLevel C m))
        (Stopped.levelTr d r t s h z i sigma j omega).inspected := by
    intro m
    have hDE :
        PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j
            (PostFam.clipLevel C m) ⊆ MacroExp.E d r t z y :=
      PostFam.tailD_subset_E (t := t) hd C hsigma hemb hj
        (PostFam.clipLevel_lt C hwf m) (by omega) hlong
    rw [Stopped.levelTr_inspected, Finset.disjoint_union_right]
    exact ⟨hfresh.symm.mono_left hDE,
      PostFam.tailD_disjoint_stub C hsigma hj (PostFam.clipLevel_lt C hwf m) hlong⟩
  have hoAll : ∀ m,
      (MacroExp.emb 0 : Site d) ∉
        PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j
          (PostFam.clipLevel C m) := by
    intro m hom
    exact Finset.disjoint_left.1 (hfreshAll m) hom
      (by
        rw [Stopped.levelTr_inspected]
        exact Finset.mem_union_left _ (h.openSites_subset horigin))
  let W : ∀ m, WindowLevel C q (MacroExp.ctr d r z) i sigma r t s j
      (PostFam.clipLevel C m) Dom T := fun m =>
    hwindow.window (PostFam.clipLevel C m) (PostFam.clipLevel_lt C hwf m)
  let lv : Nat → TargetExt.LevelGeometry (zdGraph d) Dom (MacroExp.emb 0) T := fun m =>
    (W m).toLevelGeometry (hfitAll m) (hsubAll m) (hoAll m)
  refine
    { lv := lv
      nest := ?_
      gateRel := ?_
      source := ?_
      fresh := ?_
      select := ?_
      seed := ?_
      reliable := ?_ }
  · intro m hm
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    simpa only [lv, WindowLevel.toLevelGeometry_D, PostFam.clipLevel_eq C hm,
      PostFam.clipLevel_eq C hm0] using
      (PostFam.tailD_succ_subset C (MacroExp.ctr d r z) i sigma r t s j m)
  · intro m hm x hxDom hxout v hv hadj
    have hm0 : m < C.levels := lt_trans (Nat.lt_succ_self m) hm
    have hxout' :
        x ∉ PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j m := by
      simpa only [lv, WindowLevel.toLevelGeometry_D, PostFam.clipLevel_eq C hm0] using hxout
    have hv' : v ∈ PostFam.tailD C (MacroExp.ctr d r z) i sigma r t s j m := by
      simpa only [lv, WindowLevel.toLevelGeometry_D, PostFam.clipLevel_eq C hm0] using hv
    have hout := PostFam.tail_gate_rel (z := z) C hiplanar (sigma := sigma)
      (r := r) (s := s) (j := j) (m := m) (Dom := Dom) hthinDom
      x hxDom hxout' v hv' hadj
    simpa only [lv, WindowLevel.toLevelGeometry_D, PostFam.clipLevel_eq C hm] using hout
  · intro m hm x hx
    rw [Finset.mem_coe] at hx ⊢
    simpa only [lv, WindowLevel.toLevelGeometry_D, PostFam.clipLevel_eq C hm] using
      (PostFam.stubFace_subset_tailD C hsigma hj hm (by omega) hrt (by omega) (by omega)
        hlong hx)
  · intro m hm
    simpa only [lv, WindowLevel.toLevelGeometry_D, PostFam.clipLevel_eq C hm] using
      hfreshAll m
  · intro m hm L hL hcard
    simp only [lv, WindowLevel.toLevelGeometry_sel, PostFam.clipLevel_eq C hm]
    simp only [lv, WindowLevel.toLevelGeometry_D, PostFam.clipLevel_eq C hm] at hL
    apply le_card_selC_of_subset_outerBoundary
      (PostFam.tailScales C i r t s j m)
      (PostFam.tailCentre (MacroExp.ctr d r z) i sigma r s j) 0 Dom L
      (k := C.seedCount) (N := C.contacts)
    · simpa only [PostFam.tailD] using hL
    · have heq : 4 * (1 + 2 * C.faceTarget) + 1 = 8 * C.faceTarget + 5 := by omega
      simpa only [PostFam.tailScales, heq] using hwf.contacts_ge
    · exact hcard
  · intro m hm x hx
    simp only [lv, WindowLevel.toLevelGeometry_J, PostFam.clipLevel_eq C hm]
    simp only [lv, WindowLevel.toLevelGeometry_D, PostFam.clipLevel_eq C hm] at hx
    refine (MacroExp.card_seed_le
      (Sc := PostFam.tailScales C i r t s j m) rfl
      (PostFam.tail_fits C hj hm hlong hplanar htrans i) ?_).trans ?_
    · exact isContact_of_mem_outerBoundary _ _ _ Dom
        (by simpa only [PostFam.tailD] using hx)
    · simpa only [PostFam.tailScales] using hwf.seedSize_ge
  · intro m hm x hx
    simp only [lv, WindowLevel.toLevelGeometry_Gx, PostFam.clipLevel_eq C hm]
    exact (W m).reliable x (by
      simpa only [PostFam.clipLevel_eq C hm, lv, WindowLevel.toLevelGeometry_D] using hx)

/-- The exact existential family consumed by `CorePerLevelNoGluing.hone_of_postEntry`. -/
theorem hpost_of_corePostWindowBound
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hthin : (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh : Disjoint h.inspected (MacroExp.E d r t z y))
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
        (CorePost.levelDom r t s h z y i sigma j omega)
        (↑(CoreRes.target (d := d) r y) : Set (Site d))) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      ∃ lv : Nat → TargetExt.LevelGeometry (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
          (MacroExp.emb 0) (↑(CoreRes.target (d := d) r y) : Set (Site d)),
        (∀ m, m + 1 < C.levels → (lv (m + 1)).D ⊆ (lv m).D) ∧
        (∀ m, m + 1 < C.levels →
          ∀ x ∈ ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪
            MacroExp.E d r t z y), x ∉ (lv m).D →
          ∀ v ∈ (lv m).D, (zdGraph d).Adj x v → v ∉ (lv (m + 1)).D) ∧
        (∀ m < C.levels,
          (↑(Stopped.stubFace (MacroExp.ctr d r z) i sigma r t (10 * s * (j + 1))) :
            Set (Site d)) ⊆ ↑(lv m).D) ∧
        (∀ m < C.levels,
          Disjoint (lv m).D (Stopped.levelTr d r t s h z i sigma j omega).inspected) ∧
        (∀ m < C.levels, ∀ L ⊆ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
          (lv m).D, C.contacts ≤ L.card → C.seedCount ≤ ((lv m).sel L).card) ∧
        (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
          (lv m).D, ((lv m).J x).card ≤ C.seedSize) ∧
        (∀ m < C.levels, ∀ x ∈ TargetExt.outerBoundary (zdGraph d)
          ((Stopped.levelTr d r t s h z i sigma j omega).inspected ∪ MacroExp.E d r t z y)
          (lv m).D, 1 - 3 * C.delta ^ 2 ≤
            (siteBernoulli (fun _ : Site d => q)).real ((lv m).Gx x)) := by
  intro j hj omega
  let F := familyAt_of_corePostWindowBound hwf hd hr hrt hj hsigma hemb hthin hfresh horigin
    hfar hclear hwidth hlong hplanar htrans (hwindow j hj omega)
  exact ⟨F.lv, F.nest, F.gateRel, F.source, F.fresh, F.select, F.seed, F.reliable⟩

/-- Direct bridge from support-owned target-aware windows to the gluing-free stopped-level
estimate used by the incoming-atom tower. -/
theorem hone_of_corePostWindowBound
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q)
    {r t s K : Nat} {h : MacroExp.Tr d} {z y : Site 2} {i : Fin d} {sigma : Int}
    (hd : 2 ≤ d) (hr : 0 < r) (hrt : 2 * r ≤ t)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hQ : MacroExp.Q d r t z ⊆ h.inspected)
    (hthin : (↑h.inspected : Set (Site d)) ⊆ MacroExp.thin d t)
    (hfresh : Disjoint h.inspected (MacroExp.E d r t z y))
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfar : 10 * s * K ≤ 13 * r)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (hlong : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
        (CorePost.levelDom r t s h z y i sigma j omega)
        (↑(CoreRes.target (d := d) r y) : Set (Site d))) :
    ∀ j, j < K → ∀ omega : SiteConfig (Site d),
      substitute (↑h.inspected : Set (Site d)) h.state omega ∈
          CoreStopped.levelBad r t s h z y i sigma q C.eps j →
      (Stopped.levelTr d r t s h z i sigma j omega).prob (fun _ : Site d => q)
          (Stopped.crossEvent d r t s h z i sigma j) ≤ 1 - C.delta := by
  apply CorePerLevelNoGluing.hone_of_postEntry hwf hv hwf.delta_eq hr hrt hfar hsigma hemb hQ
  exact hpost_of_corePostWindowBound hwf hd hr hrt hsigma hemb hthin hfresh horigin hfar hclear
    hwidth hlong hplanar htrans hwindow

/-! ## One-direction consumer -/

/-- The complete incoming-atom direction estimate with support-owned target-aware windows.  Its
statement is identical to `CoreDirectionNoGluing.prob_directionFailure_le_of_postWindow` except
for replacing the strict `CorePost.CorePostWindowBound` premise by the flexible structure above
and making the target set explicit. -/
theorem prob_directionFailure_le_of_corePostWindow
    {C : LeftImp2.Certificate2 d} (hwf : C.WellFormed) {q : unitInterval}
    (hv : C.ValidAt2 q) (hd : 3 ≤ d) {r t R s K : Nat} {h : MacroExp.Tr d}
    {w z y : Site 2} {i : Fin d} {sigma : Int} {rho : Real}
    (hr : 0 < r) (ht : 5 * r ≤ t) (h44 : 44 ≤ r) (hR1 : 1 ≤ R)
    (hscale : 100 * (d + 1) * (R + 1) < r)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (hemb : (MacroExp.emb (y - z) : Site d) = Pi.single i sigma)
    (hy : y ≠ 0) (hwz : w ≠ z)
    (horigin : (MacroExp.emb 0 : Site d) ∈ h.openSites)
    (hfresh : Disjoint h.inspected (MacroExp.Q d r t z ∪ MacroExp.E d r t z y))
    (hzero : (MacroExp.emb 0 : Site d) ∉
      MacroExp.Q d r t z ∪ MacroExp.E d r t z y)
    (hthin : (↑(h.inspected ∪ MacroExp.E d r t w z) : Set (Site d)) ⊆
      MacroExp.thin d t)
    (hfresh_out : Disjoint (h.inspected ∪ MacroExp.E d r t w z)
      (MacroExp.E d r t z y))
    (hface : CoreRes.FaceInputs (d := d) R h q
      (h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)))
    (hlong : CoreRes.LongInputs (d := d) R h q
      (h.inspected ∪ MacroExp.E d r t w z ∪
        Stopped.stub (MacroExp.ctr d r z) i sigma r t (17 * r)) i sigma)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (he_beta : C.eps ≤ AtomTower.beta rho d)
    (hpow : (1 - AtomTower.f C.eps) ^ K ≤ rho / 32)
    (hincoming : CoreRes.Bound (d := d) r t q C.eps h w z)
    (hclear : C.levels + 1 ≤ 10 * s)
    (hwidth : C.levels + 1 ≤ 3 * r)
    (htail : 5 * s * K + C.levels + C.faceTarget + 2 ≤ 8 * r)
    (hplanar : C.faceTarget + 1 ≤ 2 * r)
    (htrans : C.faceTarget + 1 ≤ t)
    (hwindow : ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
        CorePostWindowBound C q (MacroExp.ctr d r z) i sigma r t s j
          (CorePost.levelDom r t s (AtomTower.incomingTr d r t h w z outer)
            z y i sigma j xi)
          (↑(CoreRes.target (d := d) r y) : Set (Site d))) :
    h.prob (fun _ : Site d => q)
      {outer | outer ∉ CoreStopped.directionEvent r t s
        (AtomTower.incomingTr d r t h w z outer) z y i sigma q C.eps K} ≤
      rho / 16 := by
  have hd2 : 2 ≤ d := by omega
  have hfar : 10 * s * K ≤ 13 * r := by omega
  have hone : ∀ outer : SiteConfig (Site d), ∀ j, j < K →
      ∀ xi : SiteConfig (Site d),
      substitute
          (↑(AtomTower.incomingTr d r t h w z outer).inspected : Set (Site d))
          (AtomTower.incomingTr d r t h w z outer).state xi ∈
        CoreStopped.levelBad r t s (AtomTower.incomingTr d r t h w z outer)
          z y i sigma q C.eps j →
      (Stopped.levelTr d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma j xi).prob (fun _ : Site d => q)
        (Stopped.crossEvent d r t s (AtomTower.incomingTr d r t h w z outer)
          z i sigma j) ≤ 1 - AtomTower.f C.eps := by
    intro outer
    let h' := AtomTower.incomingTr d r t h w z outer
    have hQ : MacroExp.Q d r t z ⊆ h'.inspected := by
      intro x hx
      change x ∈ (AtomTower.incomingTr d r t h w z outer).inspected
      rw [AtomTower.incomingTr_inspected]
      exact Finset.mem_union_right _ (CorrMove.Q_subset_E hd2 r t hr hwz hx)
    have horigin' : (MacroExp.emb 0 : Site d) ∈ h'.openSites := by
      dsimp only [h', AtomTower.incomingTr, FRDom.Transcript.step]
      exact Finset.mem_union_left _ horigin
    have hthin' : (↑h'.inspected : Set (Site d)) ⊆ MacroExp.thin d t := by
      simpa only [h', AtomTower.incomingTr_inspected] using hthin
    have hfresh' : Disjoint h'.inspected (MacroExp.E d r t z y) := by
      simpa only [h', AtomTower.incomingTr_inspected] using hfresh_out
    have hlevel := hone_of_corePostWindowBound hwf hv hd2 hr (by omega) hsigma hemb
      hQ hthin' hfresh' horigin' hfar hclear hwidth htail hplanar htrans
      (fun j hj xi => hwindow outer j hj xi)
    simpa only [h', hwf.delta_eq, AtomTower.f] using hlevel
  exact CoreDirection.prob_directionFailure_le hd hr ht h44 hR1 hscale hs hbudget hsigma
    hemb hy hwz hfresh hzero hthin hfresh_out hface hlong hrho0 hrho1 hwf.eps_pos he_beta
    hpow hincoming hone

#print axioms KNAll.Site.CorePostSupport.WindowLevel.toLevelGeometry
#print axioms KNAll.Site.CorePostSupport.familyAt_of_corePostWindowBound
#print axioms KNAll.Site.CorePostSupport.hpost_of_corePostWindowBound
#print axioms KNAll.Site.CorePostSupport.hone_of_corePostWindowBound
#print axioms KNAll.Site.CorePostSupport.prob_directionFailure_le_of_corePostWindow

end KNAll.Site.CorePostSupport

end
