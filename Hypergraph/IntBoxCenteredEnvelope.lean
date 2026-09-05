import Hypergraph.ExactTargetPlan
import Hypergraph.ReinforcedLevelGeometry

/-!
# A one-unit centered envelope for exact-plan integer boxes

An `ExactTargetPlan.IntBox` need not be centered and its two side lengths may have different
parity.  Taking the lower integer midpoint in each coordinate and the larger half-width gives a
centered `Corridor.rbox`.  The parity discrepancy costs at most one lattice unit, so the centered
box lies in `B.inflate 1`.  This file also absorbs the reinforced outer-to-inner shell scan into
the plan radius inequality.
-/

noncomputable section

namespace KNAll.Site.IntBoxCenteredEnvelope

open Set Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {d : Nat}

abbrev IntBox := ExactTargetPlan.IntBox

/-- The nonnegative coordinate gap, without requiring orderedness in the definition. -/
def gap (B : IntBox d) (a : Fin d) : Nat := (B.upper a - B.lower a).toNat

/-- The lower integer midpoint. -/
def centre (B : IntBox d) : Site d :=
  fun a => B.lower a + (gap B a / 2 : Nat)

/-- The larger of the two integer half-widths. -/
def rho (B : IntBox d) : Fin d → Int :=
  fun a => max ((gap B a / 2 : Nat) : Int) ((gap B a - gap B a / 2 : Nat) : Int)

theorem gap_cast {B : IntBox d} (hB : B.Ordered) (a : Fin d) :
    (gap B a : Int) = B.upper a - B.lower a := by
  simp only [gap]
  exact Int.toNat_of_nonneg (sub_nonneg.mpr (hB a))

theorem half_balance (g : Nat) :
    g - g / 2 ≤ g / 2 + 1 ∧ g / 2 ≤ (g - g / 2) + 1 := by
  omega

theorem rho_nonneg (B : IntBox d) (a : Fin d) : 0 ≤ rho B a := by
  simp only [rho]
  positivity

theorem centre_sub_lower {B : IntBox d} (a : Fin d) :
    centre B a - B.lower a = ((gap B a / 2 : Nat) : Int) := by
  simp only [centre]
  ring

theorem upper_sub_centre {B : IntBox d} (hB : B.Ordered) (a : Fin d) :
    B.upper a - centre B a = ((gap B a - gap B a / 2 : Nat) : Int) := by
  have hg := gap_cast hB a
  have hhalf : gap B a / 2 ≤ gap B a := Nat.div_le_self _ _
  simp only [centre]
  omega

/-- The centered radius reaches both original faces. -/
theorem envelope_bounds {B : IntBox d} (hB : B.Ordered) (a : Fin d) :
    centre B a - rho B a ≤ B.lower a ∧
      B.upper a ≤ centre B a + rho B a := by
  have hl := centre_sub_lower (B := B) a
  have hu := upper_sub_centre hB a
  simp only [rho]
  constructor
  · have hm : ((gap B a / 2 : Nat) : Int) ≤
        max ((gap B a / 2 : Nat) : Int) ((gap B a - gap B a / 2 : Nat) : Int) :=
      le_max_left _ _
    omega
  · have hm : ((gap B a - gap B a / 2 : Nat) : Int) ≤
        max ((gap B a / 2 : Nat) : Int) ((gap B a - gap B a / 2 : Nat) : Int) :=
      le_max_right _ _
    omega

/-- The two rounded half-widths differ by at most one, giving the reverse envelope bounds. -/
theorem envelope_bounds_inflate_one {B : IntBox d} (hB : B.Ordered) (a : Fin d) :
    B.lower a - 1 ≤ centre B a - rho B a ∧
      centre B a + rho B a ≤ B.upper a + 1 := by
  have hl := centre_sub_lower (B := B) a
  have hu := upper_sub_centre hB a
  have hbal := half_balance (gap B a)
  simp only [rho]
  rcases le_total ((gap B a / 2 : Nat) : Int)
      ((gap B a - gap B a / 2 : Nat) : Int) with hle | hle
  · rw [max_eq_right hle]
    norm_cast at hle ⊢
    omega
  · rw [max_eq_left hle]
    norm_cast at hle ⊢
    omega

/-- The original exact-plan box lies in its centered envelope. -/
theorem sites_subset_rbox {B : IntBox d} (hB : B.Ordered) :
    B.sites ⊆ Corridor.rbox (centre B) (rho B) := by
  intro x hx
  rw [ExactTargetPlan.IntBox.mem_sites] at hx
  rw [Corridor.mem_rbox]
  intro a
  have he := envelope_bounds hB a
  exact ⟨he.1.trans (hx a).1, (hx a).2.trans he.2⟩

/-- Max-sanity adapter: centering costs at most one inflation unit. -/
theorem rbox_subset_inflate_one {B : IntBox d} (hB : B.Ordered) :
    Corridor.rbox (centre B) (rho B) ⊆ (B.inflate 1).sites := by
  intro x hx
  rw [Corridor.mem_rbox] at hx
  rw [ExactTargetPlan.IntBox.mem_sites]
  intro a
  have he := envelope_bounds_inflate_one hB a
  have hxa := hx a
  dsimp [ExactTargetPlan.IntBox.inflate]
  exact ⟨he.1.trans hxa.1, hxa.2.trans he.2⟩

/-- The expanded centered envelope at radius increment `j` fits in `B.inflate (j+1)`. -/
theorem rbox_add_subset_inflate {B : IntBox d} (hB : B.Ordered) (j : Nat) :
    Corridor.rbox (centre B) (fun a => rho B a + (j : Int)) ⊆
      (B.inflate (j + 1)).sites := by
  intro x hx
  rw [Corridor.mem_rbox] at hx
  rw [ExactTargetPlan.IntBox.mem_sites]
  intro a
  have he := envelope_bounds_inflate_one hB a
  have hxa := hx a
  dsimp [ExactTargetPlan.IntBox.inflate]
  constructor <;> omega

/-! ## Reinforced scan inside one exact-plan inflation -/

theorem shell_subset_inflate {B : IntBox d} (hB : B.Ordered)
    (m L R n : Nat) (_hn : n < L) (hR : 2 * m + L + 2 ≤ R) :
    ReinforcedLevel.shell (centre B) (rho B) m L n ⊆ (B.inflate R).sites := by
  intro x hx
  rw [ReinforcedLevel.shell, Corridor.mem_rbox] at hx
  rw [ExactTargetPlan.IntBox.mem_sites]
  intro a
  have he := envelope_bounds_inflate_one hB a
  have hxa := hx a
  dsimp [ExactTargetPlan.IntBox.inflate]
  simp only [ReinforcedLevel.radius, ReinforcedLevel.offset] at hxa
  constructor <;> omega

/-- The source box is present in every reinforced scan shell. -/
theorem sites_subset_shell {B : IntBox d} (hB : B.Ordered)
    (m L n : Nat) (hn : n < L) :
    B.sites ⊆ ReinforcedLevel.shell (centre B) (rho B) m L n := by
  intro x hx
  have hx' := sites_subset_rbox hB hx
  rw [Corridor.mem_rbox] at hx'
  rw [ReinforcedLevel.shell, Corridor.mem_rbox]
  intro a
  have hxa := hx' a
  have hoff : 0 ≤ ReinforcedLevel.offset m L n := by
    simp only [ReinforcedLevel.offset]
    omega
  simp only [ReinforcedLevel.radius]
  constructor <;> omega

#print axioms KNAll.Site.IntBoxCenteredEnvelope.rho_nonneg
#print axioms KNAll.Site.IntBoxCenteredEnvelope.sites_subset_rbox
#print axioms KNAll.Site.IntBoxCenteredEnvelope.rbox_subset_inflate_one
#print axioms KNAll.Site.IntBoxCenteredEnvelope.rbox_add_subset_inflate
#print axioms KNAll.Site.IntBoxCenteredEnvelope.shell_subset_inflate
#print axioms KNAll.Site.IntBoxCenteredEnvelope.sites_subset_shell

end KNAll.Site.IntBoxCenteredEnvelope

end
