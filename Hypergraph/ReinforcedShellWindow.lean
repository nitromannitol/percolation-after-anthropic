import Hypergraph.CorridorMove
import Hypergraph.CorridorGeometry
import Hypergraph.RenormData

/-!
# Reinforced all-open shell windows

This is the deterministic geometry of Manuscript v15, Lemma `shell-windows`, specialized to the
anisotropic integer boxes `Corridor.rbox` used by the concrete corridor plans.  It does not use
local uniqueness.  A contact receives a rectangular all-open window of fixed cardinality; the
window contains a translated radius-`m` source cube, lies in a collar, and is local to the
contact.  The last section packages the window as a finite cylinder leaf.
-/

noncomputable section

namespace KNAll.Site.ReinforcedShell

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat} [NeZero d]

def thickness (m : Nat) : Int := 2 * (m : Int) + 2

def transverseCentre (m : Nat) (c : Site d) (rho : Fin d → Int)
    (x : Site d) (a : Fin d) : Int :=
  max (c a - rho a + 2 * (m : Int))
    (min (c a + rho a - 2 * (m : Int)) (x a))

def centre (m : Nat) (c : Site d) (rho : Fin d → Int)
    (x : Site d) : Site d := fun a =>
  if a = Corridor.dirI c rho x then
    c a + Corridor.dirσ c rho x * (rho a - (m : Int) - 1)
  else transverseCentre m c rho x a

def lower (m : Nat) (c : Site d) (rho : Fin d → Int)
    (x : Site d) : Fin d → Int := fun a =>
  if a = Corridor.dirI c rho x then
    min (c a + Corridor.dirσ c rho x * (rho a - 2 * (m : Int) - 1))
      (c a + Corridor.dirσ c rho x * rho a)
  else transverseCentre m c rho x a - 2 * (m : Int)

def upper (m : Nat) (c : Site d) (rho : Fin d → Int)
    (x : Site d) : Fin d → Int := fun a =>
  if a = Corridor.dirI c rho x then
    max (c a + Corridor.dirσ c rho x * (rho a - 2 * (m : Int) - 1))
      (c a + Corridor.dirσ c rho x * rho a)
  else transverseCentre m c rho x a + 2 * (m : Int)

def window (m : Nat) (c : Site d) (rho : Fin d → Int)
    (x : Site d) : Finset (Site d) :=
  Corridor.ibox (lower m c rho x) (upper m c rho x)

def sourceCube (m : Nat) (c : Site d) (rho : Fin d → Int)
    (x : Site d) : Finset (Site d) :=
  CorrMove.cube (centre m c rho x) (m : Int)

def innerBox (m : Nat) (c : Site d) (rho : Fin d → Int) : Finset (Site d) :=
  Corridor.rbox c (fun a => rho a - thickness m)

def collar (m : Nat) (c : Site d) (rho : Fin d → Int) : Finset (Site d) :=
  Corridor.rbox c rho \ innerBox m c rho

def inward (c : Site d) (rho : Fin d → Int) (x : Site d) : Site d :=
  Function.update x (Corridor.dirI c rho x)
    (x (Corridor.dirI c rho x) - Corridor.dirσ c rho x)

def allOpen (F : Finset (Site d)) : Set (SiteConfig (Site d)) :=
  {omega | (↑F : Set (Site d)) ⊆ omega}

def seedSize (d m : Nat) : Nat := (2 * m + 2) * (4 * m + 1) ^ (d - 1)

theorem transverseCentre_bounds (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, 2 * (m : Int) + 2 ≤ rho a) (x : Site d) (a : Fin d) :
    c a - rho a + 2 * (m : Int) ≤ transverseCentre m c rho x a ∧
      transverseCentre m c rho x a ≤ c a + rho a - 2 * (m : Int) := by
  unfold transverseCentre
  constructor
  · exact le_max_left _ _
  · apply max_le
    · linarith [hrho a]
    · exact min_le_left _ _

theorem sourceCube_subset_window (m : Nat) (c : Site d) (rho : Fin d → Int)
    {x : Site d} (hx : Corridor.IsContact c rho x) :
    sourceCube m c rho x ⊆ window m c rho x := by
  intro z hz
  rw [sourceCube, CorrMove.mem_cube] at hz
  rw [window, Corridor.mem_ibox]
  intro a
  have ha := hz a
  rw [abs_le] at ha
  by_cases hai : a = Corridor.dirI c rho x
  · subst a
    simp only [lower, upper, if_pos]
    simp only [centre, if_pos] at ha
    obtain ⟨hsigma, -, -⟩ := Corridor.dir_spec hx
    rcases hsigma with hs | hs <;> rw [hs] at ha ⊢ <;>
      simp only [one_mul, neg_one_mul, min_def, max_def] at ha ⊢ <;>
      split_ifs <;> constructor <;> omega
  · simp only [lower, upper, if_neg hai]
    simp only [centre, if_neg hai] at ha
    constructor <;> linarith

/-- W1, exact size: one coordinate has `2m+2` sites and each transverse coordinate has
`4m+1` sites. -/
theorem card_window (m : Nat) (c : Site d) (rho : Fin d → Int)
    {x : Site d} (hx : Corridor.IsContact c rho x) :
    (window m c rho x).card = seedSize d m := by
  classical
  let i := Corridor.dirI c rho x
  have hprod : (window m c rho x).card =
      ∏ a : Fin d, (Finset.Icc (lower m c rho x a) (upper m c rho x a)).card := by
    show (Fintype.piFinset fun a =>
      Finset.Icc (lower m c rho x a) (upper m c rho x a)).card = _
    rw [Fintype.card_piFinset]
  have hi : (Finset.Icc (lower m c rho x i) (upper m c rho x i)).card =
      2 * m + 2 := by
    rw [Int.card_Icc]
    simp only [lower, upper, i, if_pos]
    obtain ⟨hsigma, -, -⟩ := Corridor.dir_spec hx
    rcases hsigma with hs | hs <;> rw [hs] <;>
      simp only [one_mul, neg_one_mul, min_def, max_def] <;>
      split_ifs <;> norm_num <;> omega
  have htrans : ∀ a : Fin d, a ≠ i →
      (Finset.Icc (lower m c rho x a) (upper m c rho x a)).card = 4 * m + 1 := by
    intro a hai
    rw [Int.card_Icc]
    simp only [lower, upper, i] at hai ⊢
    rw [if_neg hai]
    norm_num
    omega
  rw [hprod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hi]
  have hrest : ∏ a ∈ Finset.univ.erase i,
      (Finset.Icc (lower m c rho x a) (upper m c rho x a)).card =
        (4 * m + 1) ^ (d - 1) := by
    calc
      ∏ a ∈ Finset.univ.erase i,
          (Finset.Icc (lower m c rho x a) (upper m c rho x a)).card =
          ∏ _a ∈ Finset.univ.erase i, (4 * m + 1) := by
            apply Finset.prod_congr rfl
            intro a ha
            exact htrans a (Finset.ne_of_mem_erase ha)
      _ = (4 * m + 1) ^ (Finset.univ.erase i).card := Finset.prod_const _
      _ = (4 * m + 1) ^ (d - 1) := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
          Fintype.card_fin]
  rw [hrest]
  rfl

theorem window_subset_outer (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, 2 * (m : Int) + 2 ≤ rho a) {x : Site d}
    (hx : Corridor.IsContact c rho x) :
    window m c rho x ⊆ Corridor.rbox c rho := by
  intro z hz
  rw [window, Corridor.mem_ibox] at hz
  rw [Corridor.mem_rbox]
  intro a
  by_cases hai : a = Corridor.dirI c rho x
  · subst a
    have ha := hz (Corridor.dirI c rho x)
    have hri := hrho (Corridor.dirI c rho x)
    simp only [lower, upper, if_pos] at ha
    obtain ⟨hsigma, -, -⟩ := Corridor.dir_spec hx
    rcases hsigma with hs | hs <;> rw [hs] at ha <;>
      simp only [one_mul, neg_one_mul, min_def, max_def] at ha <;>
      split_ifs at ha <;> constructor <;> omega
  · have ha := hz a
    simp only [lower, upper, if_neg hai] at ha
    have hc := transverseCentre_bounds m c rho hrho x a
    constructor <;> linarith

theorem window_disjoint_inner (m : Nat) (c : Site d) (rho : Fin d → Int)
    {x : Site d} (hx : Corridor.IsContact c rho x) :
    Disjoint (window m c rho x) (innerBox m c rho) := by
  rw [Finset.disjoint_left]
  intro z hzW hzI
  rw [window, Corridor.mem_ibox] at hzW
  rw [innerBox, Corridor.mem_rbox] at hzI
  have hw := hzW (Corridor.dirI c rho x)
  have hi := hzI (Corridor.dirI c rho x)
  simp only [lower, upper, if_pos] at hw
  simp only [thickness] at hi
  obtain ⟨hsigma, -, -⟩ := Corridor.dir_spec hx
  rcases hsigma with hs | hs <;> rw [hs] at hw <;>
    simp only [one_mul, neg_one_mul, min_def, max_def] at hw <;>
    split_ifs at hw <;> omega

theorem window_subset_collar (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, 2 * (m : Int) + 2 ≤ rho a) {x : Site d}
    (hx : Corridor.IsContact c rho x) :
    window m c rho x ⊆ collar m c rho := by
  intro z hz
  rw [collar, Finset.mem_sdiff]
  exact ⟨window_subset_outer m c rho hrho hx hz,
    fun hzI => Finset.disjoint_left.1 (window_disjoint_inner m c rho hx) hz hzI⟩

theorem inward_mem_window (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hm : 1 ≤ m) {x : Site d} (hx : Corridor.IsContact c rho x) :
    inward c rho x ∈ window m c rho x := by
  rw [window, Corridor.mem_ibox]
  obtain ⟨hsigma, hxi, hxq⟩ := Corridor.dir_spec hx
  intro a
  by_cases hai : a = Corridor.dirI c rho x
  · subst a
    simp only [inward, Function.update_self, lower, upper, if_pos]
    rcases hsigma with hs | hs <;> rw [hs] at hxi ⊢ <;>
      simp only [one_mul, neg_one_mul, min_def, max_def] at hxi ⊢ <;>
      split_ifs <;> constructor <;> omega
  · simp only [inward, Function.update_of_ne hai, lower, upper, if_neg hai]
    have hxrange := hxq a hai
    unfold transverseCentre
    simp only [min_def, max_def]
    split_ifs <;> constructor <;> omega

theorem inward_adj (c : Site d) (rho : Fin d → Int) {x : Site d}
    (hx : Corridor.IsContact c rho x) : (zdGraph d).Adj x (inward c rho x) := by
  obtain ⟨hsigma, -, -⟩ := Corridor.dir_spec hx
  unfold inward
  have heq : x (Corridor.dirI c rho x) - Corridor.dirσ c rho x =
      x (Corridor.dirI c rho x) + (-Corridor.dirσ c rho x) := by ring
  rw [heq]
  apply Corridor.adj_of_update
  rcases hsigma with hs | hs <;> rw [hs] <;> simp

theorem window_subset_contactCube (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hm : 1 ≤ m) {x : Site d} (hx : Corridor.IsContact c rho x) :
    window m c rho x ⊆ CorrMove.cube x (4 * (m : Int)) := by
  intro z hz
  rw [window, Corridor.mem_ibox] at hz
  rw [CorrMove.mem_cube]
  intro a
  rw [abs_le]
  by_cases hai : a = Corridor.dirI c rho x
  · subst a
    have ha := hz (Corridor.dirI c rho x)
    simp only [lower, upper, if_pos] at ha
    obtain ⟨hsigma, hxi, -⟩ := Corridor.dir_spec hx
    rcases hsigma with hs | hs <;> rw [hs] at ha hxi <;>
      simp only [one_mul, neg_one_mul, min_def, max_def] at ha <;>
      split_ifs at ha <;> constructor <;> omega
  · have ha := hz a
    simp only [lower, upper, if_neg hai] at ha
    obtain ⟨-, -, hxq⟩ := Corridor.dir_spec hx
    have hxrange := hxq a hai
    unfold transverseCentre at ha
    simp only [min_def, max_def] at ha
    split_ifs at ha <;> constructor <;> omega

/-- W3: contacts separated by more than `8m` in some coordinate have disjoint windows. -/
theorem disjoint_window_of_far (m : Nat) (hm : 1 ≤ m)
    (c : Site d) (rho : Fin d → Int) {x x' : Site d}
    (hx : Corridor.IsContact c rho x) (hx' : Corridor.IsContact c rho x')
    (hfar : ∃ a, 8 * (m : Int) < |x a - x' a|) :
    Disjoint (window m c rho x) (window m c rho x') := by
  rw [Finset.disjoint_left]
  intro z hzx hzx'
  obtain ⟨a, ha⟩ := hfar
  have hz1 := window_subset_contactCube m c rho hm hx hzx
  have hz2 := window_subset_contactCube m c rho hm hx' hzx'
  rw [CorrMove.mem_cube] at hz1 hz2
  have h1 := hz1 a
  have h2 := hz2 a
  rw [abs_le] at h1 h2
  have hle : |x a - x' a| ≤ 8 * (m : Int) := by
    rw [abs_le]
    constructor <;> linarith
  exact (not_lt_of_ge hle) ha

/-- If the contact and its whole window are open, the contact reaches every point of the embedded
source cube inside `insert x window`. -/
theorem allOpen_connects_source (m : Nat) (c : Site d) (rho : Fin d → Int)
    (hm : 1 ≤ m) {x : Site d} (hx : Corridor.IsContact c rho x)
    {omega : SiteConfig (Site d)} (hxopen : x ∈ omega)
    (hopen : omega ∈ allOpen (window m c rho x)) :
    ∀ u ∈ sourceCube m c rho x,
      omega ∈ connWithin (zdGraph d)
        (insert x (↑(window m c rho x) : Set (Site d))) x u := by
  intro u hu
  have hy := inward_mem_window m c rho hm hx
  have huW := sourceCube_subset_window m c rho hx hu
  have hWopen : (↑(window m c rho x) : Set (Site d)) ⊆ omega := hopen
  have hconn := Corridor.connWithin_ibox_of_allOpen hWopen
    (Corridor.dist1 (inward c rho x) u) (inward c rho x) u hy huW le_rfl
  exact TargetExt.connWithin_of_adj_of_connWithin (zdGraph d) (inward_adj c rho hx)
    ⟨hxopen, Set.mem_insert _ _⟩
    ⟨hWopen (Finset.mem_coe.2 hy), Set.mem_insert_of_mem _ (Finset.mem_coe.2 hy)⟩
    (connWithin_mono_set (zdGraph d) (Set.subset_insert x _) _ _ hconn)

/-- An open reinforced window connects its centre to every site of its embedded source cube.
Unlike `allOpen_connects_source`, this statement does not assume that the exterior contact is
open.  This is the form needed before conditioning on which contacts are actually reached. -/
theorem allOpen_connects_centre (m : Nat) (c : Site d) (rho : Fin d → Int)
    {x : Site d} (hx : Corridor.IsContact c rho x)
    {omega : SiteConfig (Site d)}
    (hopen : omega ∈ allOpen (window m c rho x)) :
    ∀ u ∈ sourceCube m c rho x,
      omega ∈ connWithin (zdGraph d)
        (↑(window m c rho x) : Set (Site d)) (centre m c rho x) u := by
  intro u hu
  have hcW : centre m c rho x ∈ window m c rho x :=
    sourceCube_subset_window m c rho hx (CorrMove.centre_mem_cube (by positivity))
  have huW : u ∈ window m c rho x := sourceCube_subset_window m c rho hx hu
  exact Corridor.connWithin_ibox_of_allOpen hopen
    (Corridor.dist1 (centre m c rho x) u) (centre m c rho x) u hcW huW le_rfl

/-- The complete deterministic `shell-windows` conclusion for one contact. -/
structure Facts (m : Nat) (c : Site d) (rho : Fin d → Int) (x : Site d) : Prop where
  source_subset : sourceCube m c rho x ⊆ window m c rho x
  window_subset_collar : window m c rho x ⊆ collar m c rho
  card_eq : (window m c rho x).card = seedSize d m
  inward_mem : inward c rho x ∈ window m c rho x
  inward_adjacent : (zdGraph d).Adj x (inward c rho x)
  local_subset : window m c rho x ⊆ CorrMove.cube x (4 * (m : Int))
  connects : ∀ (omega : SiteConfig (Site d)), x ∈ omega →
    omega ∈ allOpen (window m c rho x) →
      ∀ u ∈ sourceCube m c rho x,
        omega ∈ connWithin (zdGraph d)
          (insert x (↑(window m c rho x) : Set (Site d))) x u
  far_disjoint : ∀ x', Corridor.IsContact c rho x' →
    (∃ a, 8 * (m : Int) < |x a - x' a|) →
      Disjoint (window m c rho x) (window m c rho x')

/-- Reinforced shell windows, in a single API matching W1--W3. -/
theorem facts (m : Nat) (hm : 1 ≤ m) (c : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, 2 * (m : Int) + 2 ≤ rho a)
    {x : Site d} (hx : Corridor.IsContact c rho x) : Facts m c rho x where
  source_subset := sourceCube_subset_window m c rho hx
  window_subset_collar := window_subset_collar m c rho hrho hx
  card_eq := card_window m c rho hx
  inward_mem := inward_mem_window m c rho hm hx
  inward_adjacent := inward_adj c rho hx
  local_subset := window_subset_contactCube m c rho hm hx
  connects := fun omega hxopen hopen =>
    allOpen_connects_source m c rho hm hx hxopen hopen
  far_disjoint := fun x' hx' hfar => disjoint_window_of_far m hm c rho hx hx' hfar

/-- The all-open window is a finite cylinder leaf with its literal support. -/
def windowExperiment (m : Nat) (c : Site d) (rho : Fin d → Int)
    (x : Site d) : CylinderExperiment d where
  support := window m c rho x
  event := allOpen (window m c rho x)
  determined := determinedBy_allOpen (↑(window m c rho x) : Set (Site d))
  measurable' :=
    (determinedBy_allOpen (↑(window m c rho x) : Set (Site d))).measurableSet_of_finset

theorem windowExperiment_prob (p : unitInterval) (m : Nat) (c : Site d)
    (rho : Fin d → Int) (x : Site d) :
    (windowExperiment m c rho x).prob p = (p : Real) ^ (window m c rho x).card := by
  change (siteBernoulli (fun _ : Site d => p)).real
      {omega | (↑(window m c rho x) : Set (Site d)) ⊆ omega} = _
  rw [siteBernoulli, prodBernoulli_real_subset, Finset.prod_const]

theorem windowExperiment_prob_fixed (p : unitInterval) (m : Nat) (c : Site d)
    (rho : Fin d → Int) {x : Site d} (hx : Corridor.IsContact c rho x) :
    (windowExperiment m c rho x).prob p = (p : Real) ^ seedSize d m := by
  rw [windowExperiment_prob, card_window m c rho hx]

#print axioms KNAll.Site.ReinforcedShell.sourceCube_subset_window
#print axioms KNAll.Site.ReinforcedShell.card_window
#print axioms KNAll.Site.ReinforcedShell.window_subset_collar
#print axioms KNAll.Site.ReinforcedShell.inward_mem_window
#print axioms KNAll.Site.ReinforcedShell.window_subset_contactCube
#print axioms KNAll.Site.ReinforcedShell.disjoint_window_of_far
#print axioms KNAll.Site.ReinforcedShell.allOpen_connects_source
#print axioms KNAll.Site.ReinforcedShell.allOpen_connects_centre
#print axioms KNAll.Site.ReinforcedShell.facts
#print axioms KNAll.Site.ReinforcedShell.windowExperiment_prob
#print axioms KNAll.Site.ReinforcedShell.windowExperiment_prob_fixed

end KNAll.Site.ReinforcedShell

end
