import Hypergraph.SelectionPacking
import Hypergraph.ReinforcedTargetBridge

/-!
# Reinforced shell levels and exact contact selection

This file is the deterministic geometry used by the reinforced-window branch of manuscript v15.
The shells are scanned from outside to inside.  On each shell we greedily separate contacts at
scale `4m` and then deterministically truncate the greedy set to `k` points.  The packing factor is
exactly the cardinality of the radius-`8m` lattice cube.

There are no probability estimates here.  The final API records precisely the geometric and
finite-support hypotheses consumed by the seed, selected-bad, and reliable-relay bounds.
-/

noncomputable section

namespace KNAll.Site.ReinforcedLevel

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

/-! ## The outer-to-inner shell list -/

/-- The `n`th offset in the outer-to-inner scan.  For `n < L` these are
`2m+L+1, ..., 2m+2`. -/
def offset (m L n : Nat) : Int := 2 * (m : Int) + (L : Int) + 1 - (n : Int)

def radius (rho0 : Fin d → Int) (m L n : Nat) : Fin d → Int :=
  fun a => rho0 a + offset m L n

def shell (c : Site d) (rho0 : Fin d → Int) (m L n : Nat) : Finset (Site d) :=
  Corridor.rbox c (radius rho0 m L n)

theorem offset_first (m L : Nat) : offset m L 0 = 2 * (m : Int) + L + 1 := by
  simp [offset]

theorem offset_last (m L : Nat) (hL : 0 < L) :
    offset m L (L - 1) = 2 * (m : Int) + 2 := by
  simp only [offset]
  omega

theorem offset_succ (m L n : Nat) : offset m L (n + 1) = offset m L n - 1 := by
  simp [offset]
  ring

theorem thickness_le_offset (m L n : Nat) (hn : n < L) :
    ReinforcedShell.thickness m ≤ offset m L n := by
  simp only [ReinforcedShell.thickness, offset]
  omega

/-- Later scan indices are inner shells. -/
theorem shell_anti (c : Site d) (rho0 : Fin d → Int) (m L : Nat) {n n' : Nat}
    (hnn' : n ≤ n') : shell c rho0 m L n' ⊆ shell c rho0 m L n := by
  apply Corridor.rbox_mono
  intro a
  simp only [radius, offset]
  omega

theorem shell_succ_subset (c : Site d) (rho0 : Fin d → Int) (m L n : Nat) :
    shell c rho0 m L (n + 1) ⊆ shell c rho0 m L n :=
  shell_anti c rho0 m L (Nat.le_succ n)

/-- The requested scan gate.  An edge entering scan shell `n` from its exterior can only hit its
outermost lattice layer, and hence does not reach the next (one-unit smaller) shell.  Membership
of `x` in `Dom` is retained in the signature used by the exterior exploration. -/
theorem scan_gate (c : Site d) (rho0 : Fin d → Int) (m L n : Nat)
    (_hn : n + 1 < L) {Dom : Finset (Site d)} {x y : Site d}
    (_hxDom : x ∈ Dom) (hx : x ∉ shell c rho0 m L n)
    (hy : y ∈ shell c rho0 m L n) (hadj : (zdGraph d).Adj x y) :
    y ∉ shell c rho0 m L (n + 1) := by
  have hgate := Corridor.notMem_rbox_sub_one_of_adj hx hy hadj
  have heq : shell c rho0 m L (n + 1) =
      Corridor.rbox c (fun a => radius rho0 m L n a - 1) := by
    unfold shell
    congr 1
    funext a
    simp only [radius, offset]
    push_cast
    ring
  rw [heq]
  exact hgate

/-- At every genuine scan index the nonnegative base radii make the centered shell nonempty. -/
theorem centre_mem_shell (c : Site d) (rho0 : Fin d → Int) (m L n : Nat)
    (hrho0 : ∀ a, 0 ≤ rho0 a) (hn : n < L) : c ∈ shell c rho0 m L n := by
  rw [shell, Corridor.mem_rbox]
  intro a
  have hbase := hrho0 a
  have hrad : 0 ≤ rho0 a + offset m L n := by
    simp only [offset]
    omega
  simp only [radius]
  constructor <;> omega

/-- The original centered box is contained in every valid expanded shell.  The nonnegative-base
premise is the same concrete hypothesis that also proves the shells nonempty. -/
theorem baseBox_subset_shell (c : Site d) (rho0 : Fin d → Int) (m L n : Nat)
    (hrho0 : ∀ a, 0 ≤ rho0 a) (hn : n < L) :
    Corridor.rbox c rho0 ⊆ shell c rho0 m L n := by
  apply Corridor.rbox_mono
  intro a
  have hbase := hrho0 a
  have hoff := thickness_le_offset m L n hn
  have hthick : 0 ≤ ReinforcedShell.thickness m := by
    simp only [ReinforcedShell.thickness]
    positivity
  have hoff0 : 0 ≤ offset m L n := hthick.trans hoff
  simp only [radius]
  omega

theorem shell_nonempty (c : Site d) (rho0 : Fin d → Int) (m L n : Nat)
    (hrho0 : ∀ a, 0 ≤ rho0 a) (hn : n < L) :
    (shell c rho0 m L n).Nonempty :=
  ⟨c, centre_mem_shell c rho0 m L n hrho0 hn⟩

/-- Every member of the finite scan lies inside its outermost shell. -/
theorem shell_subset_outer (c : Site d) (rho0 : Fin d → Int) (m L n : Nat) :
    shell c rho0 m L n ⊆ shell c rho0 m L 0 :=
  shell_anti c rho0 m L (Nat.zero_le n)

/-- A single containment assumption for the outermost scan shell puts every later shell in the
active domain. -/
theorem shell_subset_active (c : Site d) (rho0 : Fin d → Int) (m L n : Nat)
    {D : Finset (Site d)} (houter : shell c rho0 m L 0 ⊆ D) :
    shell c rho0 m L n ⊆ D :=
  (shell_subset_outer c rho0 m L n).trans houter

/-- Under the same single outer-shell assumption, every reinforced collar in the scan is active. -/
theorem collar_subset_active (c : Site d) (rho0 : Fin d → Int) (m L n : Nat)
    {D : Finset (Site d)} (houter : shell c rho0 m L 0 ⊆ D) :
    ReinforcedShell.collar m c (radius rho0 m L n) ⊆ D :=
  fun _ hz => shell_subset_active c rho0 m L n houter (Finset.mem_sdiff.1 hz).1

/-- Removing the reinforced collar from scan level `n` leaves the explicitly smaller centered
box. -/
theorem innerBox_eq (c : Site d) (rho0 : Fin d → Int) (m L n : Nat) :
    ReinforcedShell.innerBox m c (radius rho0 m L n) =
      Corridor.rbox c (fun a => rho0 a + (L : Int) - (n : Int) - 1) := by
  unfold ReinforcedShell.innerBox radius offset ReinforcedShell.thickness
  congr 1
  funext a
  ring

/-! ## Exact truncation of the greedy packing -/

/-- A deterministic choice of `k` members when possible, and the whole set otherwise. -/
def truncate {V : Type*} [DecidableEq V] (k : Nat) (S : Finset V) : Finset V :=
  if h : k ≤ S.card then (Finset.exists_subset_card_eq h).choose else S

theorem truncate_subset {V : Type*} [DecidableEq V] (k : Nat) (S : Finset V) :
    truncate k S ⊆ S := by
  classical
  unfold truncate
  split_ifs with h
  · exact (Finset.exists_subset_card_eq h).choose_spec.1
  · exact Finset.Subset.refl S

theorem card_truncate_le {V : Type*} [DecidableEq V] (k : Nat) (S : Finset V) :
    (truncate k S).card ≤ k := by
  classical
  unfold truncate
  split_ifs with h
  · rw [(Finset.exists_subset_card_eq h).choose_spec.2]
  · exact Nat.le_of_lt (Nat.lt_of_not_ge h)

theorem card_truncate_eq {V : Type*} [DecidableEq V] (k : Nat) (S : Finset V)
    (h : k ≤ S.card) : (truncate k S).card = k := by
  classical
  simp only [truncate, dif_pos h]
  exact (Finset.exists_subset_card_eq h).choose_spec.2

/-- Keep only contacts, greedily separate them at scale `4m`, and truncate to `k`.  Filtering
makes the pairwise-window statement valid for every input finset, not merely boundary subsets. -/
def selected (m k : Nat) (c : Site d) (rho : Fin d → Int)
    (K : Finset (Site d)) : Finset (Site d) :=
  truncate k (Corridor.sel ((4 * m : Nat) : Int) (K.filter (Corridor.IsContact c rho)))

theorem selected_subset (m k : Nat) (c : Site d) (rho : Fin d → Int) (K : Finset (Site d)) :
    selected m k c rho K ⊆ K := by
  exact (truncate_subset k _).trans
    ((Corridor.sel_subset _ _).trans (Finset.filter_subset _ _))

theorem card_selected_le (m k : Nat) (c : Site d) (rho : Fin d → Int)
    (K : Finset (Site d)) : (selected m k c rho K).card ≤ k :=
  card_truncate_le k _

theorem selected_isContact (m k : Nat) (c : Site d) (rho : Fin d → Int)
    {K : Finset (Site d)} {x : Site d} (hx : x ∈ selected m k c rho K) :
    Corridor.IsContact c rho x := by
  have hx' := truncate_subset k _ hx
  have hx'' := Corridor.sel_subset ((4 * m : Nat) : Int) _ hx'
  exact (Finset.mem_filter.1 hx'').2

theorem selected_far (m k : Nat) (c : Site d) (rho : Fin d → Int)
    (K : Finset (Site d)) {x y : Site d}
    (hx : x ∈ selected m k c rho K) (hy : y ∈ selected m k c rho K) (hxy : x ≠ y) :
    Corridor.Far ((4 * m : Nat) : Int) x y := by
  exact Corridor.sel_far _ _ x (truncate_subset k _ hx) y (truncate_subset k _ hy) hxy

theorem selected_pairwiseDisjoint_window (m k : Nat) (hm : 1 ≤ m)
    (c : Site d) (rho : Fin d → Int) (K : Finset (Site d)) :
    (↑(selected m k c rho K) : Set (Site d)).PairwiseDisjoint
      (ReinforcedShell.window m c rho) := by
  intro x hx y hy hxy
  apply ReinforcedShell.disjoint_window_of_far m hm c rho
    (selected_isContact m k c rho hx) (selected_isContact m k c rho hy)
  obtain ⟨a, ha⟩ := selected_far m k c rho K hx hy hxy
  exact ⟨a, by omega⟩

/-! ## The exact `|Λ₈ₘ|` packing threshold -/

theorem card_cube_eight (m : Nat) (z : Site d) :
    (CorrMove.cube z (8 * (m : Int))).card = (16 * m + 1) ^ d := by
  change (Corridor.rbox z (fun _ => 8 * (m : Int))).card = _
  rw [Corridor.card_rbox_const]
  congr 1
  omega

theorem isContact_of_mem_outerBoundary_rbox (Dom : Finset (Site d))
    (c : Site d) (rho : Fin d → Int) {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho)) :
    Corridor.IsContact c rho x := by
  classical
  simp only [TargetExt.outerBoundary, Finset.mem_filter, Finset.mem_sdiff] at hx
  exact ⟨hx.1.2, hx.2⟩

theorem card_selected_eq_of_contacts (m k N : Nat) (c : Site d) (rho : Fin d → Int)
    (K : Finset (Site d)) (hcontacts : ∀ x ∈ K, Corridor.IsContact c rho x)
    (hpack : k * (16 * m + 1) ^ d ≤ N) (hK : N ≤ K.card) :
    (selected m k c rho K).card = k := by
  have hfilter : K.filter (Corridor.IsContact c rho) = K :=
    Finset.filter_eq_self.2 hcontacts
  have hbound := Corridor.card_le_card_sel_mul (d := d) (4 * m) K
  have hpos : 0 < (16 * m + 1) ^ d := by positivity
  have hkgreedy : k ≤ (Corridor.sel ((4 * m : Nat) : Int) K).card := by
    apply Nat.le_of_mul_le_mul_right _ hpos
    have hbound' : K.card ≤
        (Corridor.sel ((4 * m : Nat) : Int) K).card * (16 * m + 1) ^ d := by
      simpa only [show 4 * (4 * m) + 1 = 16 * m + 1 by ring] using hbound
    exact hpack.trans (hK.trans hbound')
  unfold selected
  rw [hfilter]
  exact card_truncate_eq k _ hkgreedy

/-- Packing stated literally with `|Λ₈ₘ|`. -/
theorem card_selected_eq_of_boundary (m k N : Nat) (c : Site d) (rho : Fin d → Int)
    (Dom K : Finset (Site d))
    (hKsub : K ⊆ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho))
    (hpack : k * (CorrMove.cube (0 : Site d) (8 * (m : Int))).card ≤ N)
    (hK : N ≤ K.card) : (selected m k c rho K).card = k := by
  apply card_selected_eq_of_contacts m k N c rho K
  · intro x hx
    exact isContact_of_mem_outerBoundary_rbox Dom c rho (hKsub hx)
  · simpa only [card_cube_eight] using hpack
  · exact hK

/-! ## One level, in the form consumed by the analytic interfaces -/

abbrev J (m : Nat) (c : Site d) (rho : Fin d → Int) : Site d → Finset (Site d) :=
  ReinforcedShell.window m c rho

abbrev relay (m : Nat) (c : Site d) (rho : Fin d → Int) : Site d → Site d :=
  ReinforcedShell.centre m c rho

theorem collar_subset_shell (m : Nat) (c : Site d) (rho : Fin d → Int) :
    ReinforcedShell.collar m c rho ⊆ Corridor.rbox c rho := by
  intro z hz
  exact (Finset.mem_sdiff.1 hz).1

theorem window_subset_collar_of_boundary (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, ReinforcedShell.thickness m ≤ rho a) (Dom : Finset (Site d))
    {x : Site d} (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho)) :
    J m c rho x ⊆ ReinforcedShell.collar m c rho :=
  ReinforcedShell.window_subset_collar m c rho hrho
    (isContact_of_mem_outerBoundary_rbox Dom c rho hx)

theorem relay_mem_collar_of_boundary (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, ReinforcedShell.thickness m ≤ rho a) (Dom : Finset (Site d))
    {x : Site d} (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho)) :
    relay m c rho x ∈ ReinforcedShell.collar m c rho := by
  have hcontact := isContact_of_mem_outerBoundary_rbox Dom c rho hx
  apply ReinforcedShell.window_subset_collar m c rho hrho hcontact
  apply ReinforcedShell.sourceCube_subset_window m c rho hcontact
  exact CorrMove.centre_mem_cube (by positivity)

theorem bridge_of_boundary (m : Nat) (hm : 1 ≤ m) (c : Site d) (rho : Fin d → Int)
    (Dom : Finset (Site d)) {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho))
    (omega : SiteConfig (Site d)) (hxopen : x ∈ omega)
    (hopen : omega ∈ ReinforcedTarget.openWindow (J m c rho x)) :
    omega ∈ connWithin (zdGraph d)
      (insert x (↑(J m c rho x) : Set (Site d))) x (relay m c rho x) := by
  apply ReinforcedShell.allOpen_connects_source m c rho hm
    (isContact_of_mem_outerBoundary_rbox Dom c rho hx) hxopen
  · exact hopen
  · exact CorrMove.centre_mem_cube (by positivity)

theorem card_window_of_boundary (m : Nat) (c : Site d) (rho : Fin d → Int)
    (Dom : Finset (Site d)) {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho)) :
    (J m c rho x).card = ReinforcedShell.seedSize d m :=
  ReinforcedShell.card_window m c rho
    (isContact_of_mem_outerBoundary_rbox Dom c rho hx)

/-- The bad event used by the selected-bad estimate.  Both factors are determined by the complete
collar; this is the freshness statement needed by `real_rich_inter_selectedBad_le`. -/
def unreliableAt (w : Site d → unitInterval) (m : Nat) (c : Site d)
    (rho : Fin d → Int) (D : Finset (Site d)) (T : Set (Site d)) (δ : Real)
    (x : Site d) : Set (SiteConfig (Site d)) :=
  ReinforcedTarget.openWindow (J m c rho x) ∩
    ReinforcedTarget.lowRelay (zdGraph d) w (ReinforcedShell.collar m c rho)
      D T δ (relay m c rho x)

theorem determinedBy_unreliableAt_of_boundary (w : Site d → unitInterval)
    (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, ReinforcedShell.thickness m ≤ rho a) (Dom D : Finset (Site d))
    (T : Set (Site d)) (δ : Real) {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho)) :
    DeterminedBy (unreliableAt w m c rho D T δ x)
      (↑(ReinforcedShell.collar m c rho) : Set (Site d)) := by
  apply DeterminedBy.inter
  · exact (ReinforcedTarget.determinedBy_openWindow (J m c rho x)).mono
      (fun z hz => Finset.mem_coe.2
        (window_subset_collar_of_boundary m c rho hrho Dom hx (Finset.mem_coe.1 hz)))
  · exact ReinforcedTarget.determinedBy_lowRelay (zdGraph d) w
      (ReinforcedShell.collar m c rho) D T δ (relay m c rho x)

theorem innerBox_subset_shell (m : Nat) (c : Site d) (rho : Fin d → Int) :
    ReinforcedShell.innerBox m c rho ⊆ Corridor.rbox c rho := by
  apply Corridor.rbox_mono
  intro a
  simp only [ReinforcedShell.innerBox, ReinforcedShell.thickness]
  omega

/-- Direct deterministic instantiation of the bridge hypotheses in
`ReinforcedTarget.selectedReliable_subset_reachRelayD`.  The only remaining assumptions are the
ambient-domain inclusions required by that theorem itself. -/
theorem selectedReliable_subset_reachRelayD
    (w : Site d → unitInterval) (m k : Nat) (hm : 1 ≤ m)
    (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, ReinforcedShell.thickness m ≤ rho a)
    {Dom D : Finset (Site d)} (hOD : Corridor.rbox c rho ⊆ D) (hDDom : D ⊆ Dom)
    (o : Site d) (T : Set (Site d)) (δ : Real) :
    ReinforcedTarget.selectedReliable (zdGraph d) w Dom D (Corridor.rbox c rho)
        (ReinforcedShell.innerBox m c rho) o T δ (selected m k c rho)
        (J m c rho) (relay m c rho) ⊆
      TargetExt.reachRelayD (zdGraph d) w Dom D (Corridor.rbox c rho)
        (ReinforcedShell.innerBox m c rho) o T δ := by
  apply ReinforcedTarget.selectedReliable_subset_reachRelayD
    (zdGraph d) w (innerBox_subset_shell m c rho) hOD hDDom o T δ
      (selected m k c rho) (J m c rho) (relay m c rho)
  · exact selected_subset m k c rho
  · intro x hx
    exact window_subset_collar_of_boundary m c rho hrho Dom hx
  · intro x hx
    exact relay_mem_collar_of_boundary m c rho hrho Dom hx
  · intro x hx
    exact bridge_of_boundary m hm c rho Dom hx

/-- Bundle of all deterministic hypotheses required at one reinforced level. -/
structure Facts (m k : Nat) (c : Site d) (rho : Fin d → Int)
    (Dom : Finset (Site d)) : Prop where
  sel_subset : ∀ K, selected m k c rho K ⊆ K
  sel_card_le : ∀ K, (selected m k c rho K).card ≤ k
  sel_disjoint : ∀ K, (↑(selected m k c rho K) : Set (Site d)).PairwiseDisjoint (J m c rho)
  collar_subset : ReinforcedShell.collar m c rho ⊆ Corridor.rbox c rho
  window_subset : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho),
    J m c rho x ⊆ ReinforcedShell.collar m c rho
  relay_mem : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho),
    relay m c rho x ∈ ReinforcedShell.collar m c rho
  bridge : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho),
    ∀ omega : SiteConfig (Site d), x ∈ omega →
      omega ∈ ReinforcedTarget.openWindow (J m c rho x) →
      omega ∈ connWithin (zdGraph d) (insert x (↑(J m c rho x) : Set (Site d)))
        x (relay m c rho x)
  window_card : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox c rho),
    (J m c rho x).card = ReinforcedShell.seedSize d m

theorem facts (m k : Nat) (hm : 1 ≤ m) (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, ReinforcedShell.thickness m ≤ rho a) (Dom : Finset (Site d)) :
    Facts m k c rho Dom where
  sel_subset := selected_subset m k c rho
  sel_card_le := card_selected_le m k c rho
  sel_disjoint := selected_pairwiseDisjoint_window m k hm c rho
  collar_subset := collar_subset_shell m c rho
  window_subset := fun x hx => window_subset_collar_of_boundary m c rho hrho Dom hx
  relay_mem := fun x hx => relay_mem_collar_of_boundary m c rho hrho Dom hx
  bridge := fun x hx => bridge_of_boundary m hm c rho Dom hx
  window_card := fun x hx => card_window_of_boundary m c rho Dom hx

/-! The same bundle instantiated on scan level `n`. -/
theorem scan_facts (m k L n : Nat) (hm : 1 ≤ m) (hn : n < L)
    (c : Site d) (rho0 : Fin d → Int) (hrho0 : ∀ a, 0 ≤ rho0 a)
    (Dom : Finset (Site d)) : Facts m k c (radius rho0 m L n) Dom := by
  apply facts m k hm c (radius rho0 m L n)
  intro a
  have hbase := hrho0 a
  have hoff := thickness_le_offset m L n hn
  simp only [radius]
  omega

#print axioms KNAll.Site.ReinforcedLevel.card_selected_eq_of_boundary
#print axioms KNAll.Site.ReinforcedLevel.scan_gate
#print axioms KNAll.Site.ReinforcedLevel.baseBox_subset_shell
#print axioms KNAll.Site.ReinforcedLevel.shell_subset_active
#print axioms KNAll.Site.ReinforcedLevel.facts
#print axioms KNAll.Site.ReinforcedLevel.scan_facts
#print axioms KNAll.Site.ReinforcedLevel.determinedBy_unreliableAt_of_boundary
#print axioms KNAll.Site.ReinforcedLevel.selectedReliable_subset_reachRelayD

end KNAll.Site.ReinforcedLevel

end
