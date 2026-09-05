import Hypergraph.ProbInvariant
import Hypergraph.TargetExtension
import Hypergraph.LeftImprovement
import Hypergraph.SiteSlabGeometry
import Hypergraph.SiteFiniteEnergy

/-!
# The macro exploration of a slab

The renormalisation of the manuscript (Section 8.5, Lemma 8.12 and Proposition 8.13) explores the
macro lattice `ℤ²` embedded in the two free coordinates of a slab of `ℤ^d`, one macro-vertex at a
time, from an occupied predecessor.  This module builds the deterministic part of that exploration
as an instance of `KNAll.Site.FRDom.Exploration`, and proves the whole chain from a one-step bound
to percolation in a slab of `ℤ^d`.

* The macro lattice is `Site 2` with `zdGraph 2`; the macro-vertex `z` sits at the centre
  `ctr r z = 20 r z` in the planar coordinates.  Boxes are anisotropic, of planar radius `R` and
  transverse half-width `t` (`abox`), so that every region lies in the slab `thin t`.
* `Q r t z` is the central box, `M r t z` the target box, and `E r t w z` the edge region revealed
  when `z` is examined from `w`: the convex hull of the two central boxes with `Q r t w` removed.
* A transcript is admissible (`Good`) when the origin is occupied, everything inspected lies in the
  slab, every occupied macro-vertex carries an actual recorded-open path certificate, and every
  pending direction carries a near-one pinned probability of reaching the next target box through
  its protected edge region.  The success event `succ` realizes the incoming reservation and
  acquires such a probabilistic reservation in every outgoing pending direction.  It never demands
  an open connection from a designated gateway.
* The start transcript has the central box `Q r t 0` read and recorded open, and the origin
  occupied.  `Q r t 0` is paid for once, by `prod_mul_real_preimage_openSites_le`.
* `thetaSiteOn_thin_pos_of_stepBound`: if every examination succeeds with pinned probability at
  least `a`, with `θ_2(a) > 0`, then the slab `thin t` percolates; `exists_slab_pos_of_stepBound`
  moves this to the family `slabGraph d k`.

What is not proved is the one-step bound itself, `StepBound`; see the final section.
-/

noncomputable section

namespace KNAll.Site.MacroExp

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

/-! ## The geometry -/

section Geometry

variable {d : ℕ}

/-- The planar embedding: a macro-vertex read in the first two coordinates of `ℤ^d`. -/
def emb (z : Site 2) : Site d := fun j => if h : j.val < 2 then z ⟨j.val, h⟩ else 0

theorem emb_apply_of_lt (z : Site 2) {j : Fin d} (h : j.val < 2) : emb z j = z ⟨j.val, h⟩ := by
  simp [emb, h]

theorem emb_apply_of_not_lt (z : Site 2) {j : Fin d} (h : ¬ j.val < 2) : emb z j = 0 := by
  simp [emb, h]

@[simp] theorem emb_zero : (emb (0 : Site 2) : Site d) = 0 := by
  funext j
  by_cases h : j.val < 2
  · rw [emb_apply_of_lt _ h]; rfl
  · rw [emb_apply_of_not_lt _ h]; rfl

/-- The centre of the macro-vertex `z` at spacing `20 r`. -/
def ctr (d r : ℕ) (z : Site 2) : Site d := fun j => 20 * (r : ℤ) * emb z j

theorem ctr_apply_of_lt (r : ℕ) (z : Site 2) {j : Fin d} (h : j.val < 2) :
    ctr d r z j = 20 * (r : ℤ) * z ⟨j.val, h⟩ := by
  simp [ctr, emb_apply_of_lt z h]

theorem ctr_apply_of_not_lt (r : ℕ) (z : Site 2) {j : Fin d} (h : ¬ j.val < 2) : ctr d r z j = 0 := by
  simp [ctr, emb_apply_of_not_lt z h]

/-- The radius in the coordinate `j`: `R` in the two planar coordinates and `t` elsewhere. -/
def rad (R t : ℕ) (j : Fin d) : ℤ := if j.val < 2 then R else t

/-- The anisotropic box: planar radius `R`, transverse half-width `t`, centre `c`. -/
def abox (c : Site d) (R t : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun j => Finset.Icc (c j - rad R t j) (c j + rad R t j)

theorem mem_abox {c x : Site d} {R t : ℕ} :
    x ∈ abox c R t ↔ ∀ j, c j - rad R t j ≤ x j ∧ x j ≤ c j + rad R t j := by
  simp [abox, Fintype.mem_piFinset]

/-- The box between two centres: coordinatewise from the smaller centre minus the radius to the
larger centre plus the radius. -/
def hbox (c c' : Site d) (R t : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun j => Finset.Icc (min (c j) (c' j) - rad R t j) (max (c j) (c' j) + rad R t j)

theorem mem_hbox {c c' x : Site d} {R t : ℕ} :
    x ∈ hbox c c' R t ↔
      ∀ j, min (c j) (c' j) - rad R t j ≤ x j ∧ x j ≤ max (c j) (c' j) + rad R t j := by
  simp [hbox, Fintype.mem_piFinset]

/-- The central box of the macro-vertex `z`. -/
def Q (d r t : ℕ) (z : Site 2) : Finset (Site d) := abox (ctr d r z) (5 * r) t

/-- The target box of the macro-vertex `z`. -/
def M (d r t : ℕ) (z : Site 2) : Finset (Site d) := abox (ctr d r z) (3 * r) t

/-- The edge region revealed when `z` is examined from `w`: the box spanned by the two central
boxes, with the central box of `w` removed. -/
def E (d r t : ℕ) (w z : Site 2) : Finset (Site d) :=
  hbox (ctr d r w) (ctr d r z) (5 * r) t \ Q d r t w

/-- The slab thin in every coordinate other than the two planar ones. -/
def thin (d t : ℕ) [NeZero d] : Set (Site d) := {x | ∀ j, j ≠ 0 → j ≠ 1 → |x j| ≤ (t : ℤ)}

theorem zero_mem_thin [NeZero d] (t : ℕ) : (0 : Site d) ∈ thin d t := fun j _ _ => by simp

/-- A coordinate other than `0` and `1` has index at least `2`. -/
theorem two_le_val_of_ne [NeZero d] {j : Fin d} (h0 : j ≠ 0) (h1 : j ≠ 1) (hd : 2 ≤ d) :
    ¬ j.val < 2 := by
  intro hlt
  have hv0 : (0 : Fin d).val = 0 := Fin.val_zero d
  have hv1 : (1 : Fin d).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rcases Nat.lt_succ_iff.1 hlt |>.lt_or_eq with h | h
  · exact h0 (Fin.ext (by omega))
  · exact h1 (Fin.ext (by omega))

theorem M_subset_Q (r t : ℕ) (z : Site 2) : M d r t z ⊆ Q d r t z := by
  intro x hx
  rw [M, mem_abox] at hx
  rw [Q, mem_abox]
  intro j
  have := hx j
  unfold rad at this ⊢
  split_ifs at this ⊢ <;> omega

theorem ctr_mem_M (r t : ℕ) (z : Site 2) : ctr d r z ∈ M d r t z := by
  rw [M, mem_abox]
  intro j
  unfold rad
  split_ifs <;> omega

theorem emb_zero_mem_M (r t : ℕ) : (emb 0 : Site d) ∈ M d r t 0 := by
  have h : (ctr d r (0 : Site 2) : Site d) = emb 0 := by
    funext j
    by_cases hj : j.val < 2
    · rw [ctr_apply_of_lt r _ hj, emb_apply_of_lt _ hj]; simp
    · rw [ctr_apply_of_not_lt r _ hj, emb_apply_of_not_lt _ hj]
  rw [← h]
  exact ctr_mem_M r t 0

/-- Every anisotropic box centred on the plane lies in the slab. -/
theorem abox_subset_thin [NeZero d] (hd : 2 ≤ d) (r : ℕ) (z : Site 2) (R t : ℕ) :
    (↑(abox (ctr d r z) R t) : Set (Site d)) ⊆ thin d t := by
  intro x hx
  rw [Finset.mem_coe, mem_abox] at hx
  intro j hj0 hj1
  have hlt := two_le_val_of_ne hj0 hj1 hd
  have := hx j
  rw [ctr_apply_of_not_lt r z hlt] at this
  unfold rad at this
  rw [if_neg hlt] at this
  rw [abs_le]
  omega

theorem Q_subset_thin [NeZero d] (hd : 2 ≤ d) (r t : ℕ) (z : Site 2) :
    (↑(Q d r t z) : Set (Site d)) ⊆ thin d t := abox_subset_thin hd r z _ t

/-- The edge region lies in the slab. -/
theorem E_subset_thin [NeZero d] (hd : 2 ≤ d) (r t : ℕ) (w z : Site 2) :
    (↑(E d r t w z) : Set (Site d)) ⊆ thin d t := by
  intro x hx
  rw [Finset.mem_coe, E, Finset.mem_sdiff, mem_hbox] at hx
  intro j hj0 hj1
  have hlt := two_le_val_of_ne hj0 hj1 hd
  have := hx.1 j
  rw [ctr_apply_of_not_lt r w hlt, ctr_apply_of_not_lt r z hlt] at this
  unfold rad at this
  rw [if_neg hlt] at this
  rw [abs_le]
  simp only [min_self, max_self] at this
  omega

/-- The target box of a macro-vertex lies in the edge region leading to it, since the central boxes
of distinct macro-vertices are disjoint. -/
theorem M_subset_E (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r) {w z : Site 2} (hwz : w ≠ z) :
    M d r t z ⊆ E d r t w z := by
  intro x hx
  rw [M, mem_abox] at hx
  rw [E, Finset.mem_sdiff, mem_hbox, Q, mem_abox]
  constructor
  · intro j
    have := hx j
    unfold rad at this ⊢
    split_ifs at this ⊢ with hj
    · constructor
      · have := min_le_right (ctr d r w j) (ctr d r z j); omega
      · have := le_max_right (ctr d r w j) (ctr d r z j); omega
    · constructor
      · have := min_le_right (ctr d r w j) (ctr d r z j); omega
      · have := le_max_right (ctr d r w j) (ctr d r z j); omega
  · intro hQ
    -- some planar coordinate of `w` and `z` differ, and there the two boxes are far apart
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, w i ≠ z i := by
      by_contra h
      push Not at h
      exact hwz (funext h)
    have hid : i.val < d := lt_of_lt_of_le i.isLt hd
    have h1 := hx ⟨i.val, hid⟩
    have h2 := hQ ⟨i.val, hid⟩
    have hjlt : (⟨i.val, hid⟩ : Fin d).val < 2 := i.isLt
    rw [ctr_apply_of_lt r z hjlt] at h1
    rw [ctr_apply_of_lt r w hjlt] at h2
    unfold rad at h1 h2
    rw [if_pos hjlt] at h1 h2
    have hi' : w i ≠ z i := hi
    have hr' : (0 : ℤ) ≤ 20 * (r : ℤ) := by positivity
    have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
    rcases lt_or_gt_of_ne hi' with hlt | hlt
    · have hle : w i + 1 ≤ z i := hlt
      have := mul_le_mul_of_nonneg_left hle hr'
      push_cast at h1 h2
      nlinarith
    · have hle : z i + 1 ≤ w i := hlt
      have := mul_le_mul_of_nonneg_left hle hr'
      push_cast at h1 h2
      nlinarith

end Geometry

/-! ## An all-open box is connected

`KN/CorridorGeometry.lean` proves this for its own boxes, but that module imports this one, so the
argument is repeated here for the boxes of the macro geometry. -/

section BoxConnected

variable {d : ℕ}

/-- The `ℓ¹` distance between two sites. -/
def dist1 (x y : Site d) : ℕ := ∑ j, (x j - y j).natAbs

/-- One coordinate of `x` moved one step towards `y`. -/
def stepTo (x y : Site d) (i : Fin d) : Site d :=
  Function.update x i (x i + if x i < y i then 1 else -1)

theorem stepTo_apply_self (x y : Site d) (i : Fin d) :
    stepTo x y i i = x i + if x i < y i then 1 else -1 := by
  simp [stepTo]

theorem stepTo_apply_of_ne (x y : Site d) {i j : Fin d} (h : j ≠ i) : stepTo x y i j = x j := by
  simp [stepTo, h]

theorem adj_stepTo (x y : Site d) (i : Fin d) : (zdGraph d).Adj x (stepTo x y i) := by
  rw [zdGraph_adj_iff]
  refine ⟨i, ?_⟩
  by_cases h : x i < y i
  · left
    funext j
    by_cases hj : j = i
    · subst hj; simp [stepTo, h]
    · simp [stepTo, hj]
  · right
    funext j
    by_cases hj : j = i
    · subst hj; simp [stepTo, h]
    · simp [stepTo, hj]

theorem dist1_stepTo {x y : Site d} {i : Fin d} (hne : x i ≠ y i) :
    dist1 (stepTo x y i) y + 1 = dist1 x y := by
  classical
  unfold dist1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i, (stepTo x y i j - y j).natAbs
      = ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [stepTo_apply_of_ne x y (Finset.ne_of_mem_erase hj)]
  rw [hrest, stepTo_apply_self]
  split_ifs with h <;> omega

theorem stepTo_mem_abox {c x y : Site d} {R t : ℕ} (hx : x ∈ abox c R t) (hy : y ∈ abox c R t)
    {i : Fin d} (hne : x i ≠ y i) : stepTo x y i ∈ abox c R t := by
  rw [mem_abox] at hx hy ⊢
  intro j
  by_cases hj : j = i
  · rw [hj, stepTo_apply_self]
    have h1 := hx i; have h2 := hy i
    split_ifs <;> omega
  · rw [stepTo_apply_of_ne x y hj]
    exact hx j

/-- **An all-open box is connected.** -/
theorem connWithin_abox_of_allOpen {c : Site d} {R t : ℕ} {ω : SiteConfig (Site d)}
    (hopen : (↑(abox c R t) : Set (Site d)) ⊆ ω) :
    ∀ (n : ℕ) (x y : Site d), x ∈ abox c R t → y ∈ abox c R t → dist1 x y ≤ n →
      ω ∈ connWithin (zdGraph d) (↑(abox c R t) : Set (Site d)) x y := by
  intro n
  induction n with
  | zero =>
    intro x y hx hy hd
    have hxy : x = y := by
      funext j
      have h0 : dist1 x y = 0 := Nat.le_zero.1 hd
      unfold dist1 at h0
      have := (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ j)
      omega
    subst hxy
    exact ⟨⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩, SimpleGraph.Reachable.refl _⟩
  | succ n ih =>
    intro x y hx hy hd
    by_cases hxy : x = y
    · subst hxy
      exact ⟨⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩, SimpleGraph.Reachable.refl _⟩
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra h
        push Not at h
        exact hxy (funext h)
      have hstep := dist1_stepTo hi
      have hmem := stepTo_mem_abox hx hy hi
      have hrec := ih (stepTo x y i) y hmem hy (by omega)
      refine ⟨⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩, ?_⟩
      refine (SimpleGraph.Adj.reachable ?_).trans hrec.2
      exact (openSiteGraph_adj_iff' (zdGraph d) _ x _).2
        ⟨adj_stepTo x y i, ⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩,
          ⟨hopen (Finset.mem_coe.2 hmem), Finset.mem_coe.2 hmem⟩⟩

/-- Any two sites of a box are within `ℓ¹` distance of the box's diameter, so the connectivity
statement applies with the step count `dist1 x y` itself. -/
theorem connWithin_abox {c : Site d} {R t : ℕ} {ω : SiteConfig (Site d)}
    (hopen : (↑(abox c R t) : Set (Site d)) ⊆ ω) {x y : Site d} (hx : x ∈ abox c R t)
    (hy : y ∈ abox c R t) : ω ∈ connWithin (zdGraph d) (↑(abox c R t) : Set (Site d)) x y :=
  connWithin_abox_of_allOpen hopen (dist1 x y) x y hx hy le_rfl

end BoxConnected

/-! ## Macro neighbours and stub tips -/

section Tips

variable {d : ℕ}

/-- The planar unit step in coordinate `i`, forward when `b`. -/
def mvUnit (i : Fin 2) (b : Bool) : Site 2 := Pi.single i (if b then 1 else -1)

/-- The four macro-neighbours of `z`. -/
def nbrs (z : Site 2) : Finset (Site 2) :=
  (Finset.univ : Finset (Fin 2 × Bool)).image fun p => z + mvUnit p.1 p.2

theorem mem_nbrs_iff {z z' : Site 2} :
    z' ∈ nbrs z ↔ ∃ (i : Fin 2) (b : Bool), z' = z + mvUnit i b := by
  simp only [nbrs, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  exact ⟨fun ⟨i, b, h⟩ => ⟨i, b, h.symm⟩, fun ⟨i, b, h⟩ => ⟨i, b, h.symm⟩⟩

theorem adj_of_mem_nbrs {z z' : Site 2} (h : z' ∈ nbrs z) : (zdGraph 2).Adj z z' := by
  obtain ⟨i, b, rfl⟩ := mem_nbrs_iff.1 h
  rw [zdGraph_adj_iff]
  refine ⟨i, ?_⟩
  cases b
  · right
    funext j
    simp only [mvUnit, Pi.add_apply, Pi.single_apply, Bool.false_eq_true, if_false]
    split_ifs <;> omega
  · left
    funext j
    simp only [mvUnit, Pi.add_apply, Pi.single_apply, if_true]

theorem mem_nbrs_of_adj {z z' : Site 2} (h : (zdGraph 2).Adj z z') : z' ∈ nbrs z := by
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff z z').1 h
  · refine mem_nbrs_iff.2 ⟨i, true, ?_⟩
    rw [hi]
    funext j
    simp [mvUnit]
  · refine mem_nbrs_iff.2 ⟨i, false, ?_⟩
    funext j
    have := congrFun hi j
    simp only [mvUnit, Pi.add_apply, Pi.single_apply, Bool.false_eq_true, if_false] at *
    split_ifs at * <;> omega

/-- The difference of a macro-neighbour is a planar unit vector, so its embedding has entries in
`{-1, 0, 1}` and vanishes off the plane. -/
theorem abs_emb_sub_le_one {z z' : Site 2} (h : z' ∈ nbrs z) (j : Fin d) :
    |emb (z' - z) j| ≤ 1 := by
  obtain ⟨i, b, rfl⟩ := mem_nbrs_iff.1 h
  by_cases hj : j.val < 2
  · rw [emb_apply_of_lt _ hj]
    have hval : (z + mvUnit i b - z) (⟨j.val, hj⟩ : Fin 2) = mvUnit i b ⟨j.val, hj⟩ := by
      simp
    rw [hval]
    simp only [mvUnit, Pi.single_apply]
    by_cases hk : (⟨j.val, hj⟩ : Fin 2) = i
    · rw [if_pos hk]
      cases b <;> simp
    · rw [if_neg hk]
      simp
  · rw [emb_apply_of_not_lt _ hj]
    simp

theorem emb_sub_eq_zero {z z' : Site 2} {j : Fin d} (hj : ¬ j.val < 2) : emb (z' - z) j = 0 :=
  emb_apply_of_not_lt _ hj

/-- **The stub tip** of the macro-vertex `z` towards its neighbour `z'`: the centre of the face of
the central box `Q z` facing `z'`. -/
def tip (d r : ℕ) (z z' : Site 2) : Site d := fun j => ctr d r z j + 5 * r * emb (z' - z) j

theorem tip_apply (r : ℕ) (z z' : Site 2) (j : Fin d) :
    tip d r z z' j = ctr d r z j + 5 * r * emb (z' - z) j := rfl

/-- **The tip lies on the central box of its own macro-vertex.** -/
theorem tip_mem_Q (r t : ℕ) {z z' : Site 2} (h : z' ∈ nbrs z) : tip d r z z' ∈ Q d r t z := by
  rw [Q, mem_abox]
  intro j
  rw [tip_apply]
  have habs := abs_emb_sub_le_one (d := d) h j
  rw [abs_le] at habs
  unfold rad
  by_cases hj : j.val < 2
  · rw [if_pos hj]
    have hr : (0 : ℤ) ≤ r := Nat.cast_nonneg r
    push_cast
    constructor <;> nlinarith [habs.1, habs.2]
  · rw [if_neg hj, emb_sub_eq_zero hj]
    simp

/-- The embedded planar step towards a macro-neighbour is a unit coordinate vector of `ℤ^d`. -/
theorem exists_single_emb_sub (hd : 2 ≤ d) {z z' : Site 2} (h : z' ∈ nbrs z) :
    ∃ (j₀ : Fin d) (σ : ℤ), (σ = 1 ∨ σ = -1) ∧ (emb (z' - z) : Site d) = Pi.single j₀ σ := by
  obtain ⟨i, b, rfl⟩ := mem_nbrs_iff.1 h
  set j₀ : Fin d := ⟨i.val, lt_of_lt_of_le i.isLt hd⟩ with hj₀
  refine ⟨j₀, if b then 1 else -1, by cases b <;> simp, ?_⟩
  funext j
  by_cases hj : j.val < 2
  · rw [emb_apply_of_lt _ hj]
    have hval : (z + mvUnit i b - z) (⟨j.val, hj⟩ : Fin 2) = mvUnit i b ⟨j.val, hj⟩ := by simp
    rw [hval]
    simp only [mvUnit, Pi.single_apply]
    by_cases hk : (⟨j.val, hj⟩ : Fin 2) = i
    · have hv : (⟨j.val, hj⟩ : Fin 2).val = i.val := congrArg Fin.val hk
      have hjj : j = j₀ := by
        refine Fin.ext ?_
        rw [hj₀]
        exact hv
      rw [if_pos hk, if_pos hjj]
    · have hjj : ¬ (j = j₀) := by
        intro hc
        have hv : (j : Fin d).val = j₀.val := congrArg Fin.val hc
        rw [hj₀] at hv
        exact hk (Fin.ext hv)
      rw [if_neg hk, if_neg hjj]
  · rw [emb_apply_of_not_lt _ hj, Pi.single_apply, if_neg]
    intro hc
    rw [hj₀] at hc
    exact hj (by rw [hc]; exact i.isLt)

/-- **The corridor entrance**: the site one step beyond the tip, in the direction of the
neighbour. -/
def tipOut (d r : ℕ) (z z' : Site 2) : Site d := fun j => tip d r z z' j + emb (z' - z) j

theorem adj_tip_tipOut (hd : 2 ≤ d) (r : ℕ) {z z' : Site 2} (h : z' ∈ nbrs z) :
    (zdGraph d).Adj (tip d r z z') (tipOut d r z z') := by
  obtain ⟨j₀, σ, hσ, hemb⟩ := exists_single_emb_sub hd h
  have hout : (tipOut d r z z' : Site d) = tip d r z z' + Pi.single j₀ σ := by
    funext j
    show tip d r z z' j + emb (z' - z) j = _
    rw [hemb]
    rfl
  rw [zdGraph_adj_iff]
  refine ⟨j₀, ?_⟩
  rcases hσ with rfl | rfl
  · exact Or.inl hout
  · refine Or.inr ?_
    rw [hout]
    funext j
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> omega

/-- **The corridor entrance lies in the corridor.**  So the tip left by an occupied macro-vertex is
an inspected open site adjacent to the fresh region revealed at the next examination; this is
exactly what the refuted design lacked. -/
theorem tipOut_mem_E (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r) {z z' : Site 2} (h : z' ∈ nbrs z) :
    tipOut d r z z' ∈ E d r t z z' := by
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  obtain ⟨j₀, σ, hσ, hemb⟩ := exists_single_emb_sub (d := d) hd h
  have hval : ∀ j : Fin d, (tipOut d r z z' : Site d) j
      = ctr d r z j + (5 * r + 1) * emb (z' - z) j := by
    intro j
    show tip d r z z' j + emb (z' - z) j = _
    rw [tip_apply]
    ring
  -- the centre of the neighbour differs by `20 r` in the direction of the step
  have hctr : ∀ j : Fin d, ctr d r z' j = ctr d r z j + 20 * r * emb (z' - z) j := by
    intro j
    by_cases hj : j.val < 2
    · rw [ctr_apply_of_lt r z' hj, ctr_apply_of_lt r z hj, emb_apply_of_lt _ hj]
      simp only [Pi.sub_apply]
      ring
    · rw [ctr_apply_of_not_lt r z' hj, ctr_apply_of_not_lt r z hj, emb_apply_of_not_lt _ hj]
      simp
  rw [E, Finset.mem_sdiff, mem_hbox, Q, mem_abox]
  constructor
  · intro j
    have habs := abs_emb_sub_le_one (d := d) h j
    rw [abs_le] at habs
    have hc := hctr j
    have hv := hval j
    unfold rad
    by_cases hj : j.val < 2
    · rw [if_pos hj]
      push_cast
      rcases le_or_gt 0 (emb (z' - z) j) with hs | hs
      · have hmin : min (ctr d r z j) (ctr d r z' j) = ctr d r z j := by
          rw [min_eq_left]; nlinarith
        have hmax : max (ctr d r z j) (ctr d r z' j) = ctr d r z' j := by
          rw [max_eq_right]; nlinarith
        rw [hmin, hmax, hv, hc]
        constructor <;> nlinarith
      · have hmin : min (ctr d r z j) (ctr d r z' j) = ctr d r z' j := by
          rw [min_eq_right]; nlinarith
        have hmax : max (ctr d r z j) (ctr d r z' j) = ctr d r z j := by
          rw [max_eq_left]; nlinarith
        rw [hmin, hmax, hv, hc]
        constructor <;> nlinarith
    · rw [emb_sub_eq_zero (d := d) hj] at hv hc
      rw [if_neg hj, hc, hv]
      simp
  · intro hQ
    -- in the direction of the step the entrance is one beyond the face of the central box
    have hj₀ : emb (z' - z) j₀ = σ := by rw [hemb]; simp
    have hcQ := hQ j₀
    have hv := hval j₀
    unfold rad at hcQ
    have hj₀lt : j₀.val < 2 := by
      by_contra hc
      rw [emb_sub_eq_zero (d := d) hc] at hj₀
      rcases hσ with rfl | rfl <;> omega
    rw [if_pos hj₀lt, hv, hj₀] at hcQ
    push_cast at hcQ
    rcases hσ with rfl | rfl <;> [nlinarith [hcQ.2]; nlinarith [hcQ.1]]

theorem tip_mem_thin [NeZero d] (hd : 2 ≤ d) (r t : ℕ) {z z' : Site 2} (h : z' ∈ nbrs z) :
    tip d r z z' ∈ thin d t :=
  Q_subset_thin hd r t z (Finset.mem_coe.2 (tip_mem_Q r t h))

end Tips

/-! ## The corridor of an outgoing direction is disjoint from the incoming one

This is the separation that the revised manuscript keeps apart from the other three facts about the
stopped target subbox: for `w ≠ y`, the corridor `E w z` revealed when `z` is examined and the
corridor `E z y` of an outgoing direction of `z` do not meet.  It is proved by normalized interval
arithmetic in the planar coordinate of the outgoing direction. -/

section Separation

variable {d : ℕ}

/-- The embedding of a planar vector is injective once `d ≥ 2`. -/
theorem emb_injective (hd : 2 ≤ d) : Function.Injective (emb (d := d)) := by
  intro v v' hvv
  funext i
  have hid : i.val < d := lt_of_lt_of_le i.isLt hd
  have h := congrFun hvv ⟨i.val, hid⟩
  have hlt : (⟨i.val, hid⟩ : Fin d).val < 2 := i.isLt
  rw [emb_apply_of_lt _ hlt, emb_apply_of_lt _ hlt] at h
  simpa using h

/-- **The outgoing corridor lies beyond the face of the central box.**  Off the direction of the
step the corridor keeps the cross-section of the central box, so a site of the corridor can leave
that box only in the direction of the step, and then by at least one lattice unit. -/
theorem le_of_mem_E_out (r t : ℕ) {z y : Site 2} (h : y ∈ nbrs z) {j₀ : Fin d} {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hemb : (emb (y - z) : Site d) = Pi.single j₀ σ)
    {x : Site d} (hx : x ∈ E d r t z y) :
    5 * (r : ℤ) + 1 ≤ σ * (x j₀ - ctr d r z j₀) := by
  rw [E, Finset.mem_sdiff, mem_hbox, Q, mem_abox] at hx
  obtain ⟨hbox, hQ⟩ := hx
  -- the centres agree off the direction of the step
  have hctr : ∀ j : Fin d, ctr d r y j = ctr d r z j + 20 * r * emb (y - z) j := by
    intro j
    by_cases hj : j.val < 2
    · rw [ctr_apply_of_lt r y hj, ctr_apply_of_lt r z hj, emb_apply_of_lt _ hj]
      simp only [Pi.sub_apply]
      ring
    · rw [ctr_apply_of_not_lt r y hj, ctr_apply_of_not_lt r z hj, emb_apply_of_not_lt _ hj]
      simp
  have hoff : ∀ j : Fin d, j ≠ j₀ → ctr d r y j = ctr d r z j := by
    intro j hj
    rw [hctr j, hemb, Pi.single_apply, if_neg hj]
    simp
  -- so the box condition fails in the direction of the step
  have hfail : ¬ (ctr d r z j₀ - rad (5 * r) t j₀ ≤ x j₀ ∧
      x j₀ ≤ ctr d r z j₀ + rad (5 * r) t j₀) := by
    intro hc
    refine hQ fun j => ?_
    by_cases hj : j = j₀
    · rw [hj]; exact hc
    · have hb := hbox j
      rw [hoff j hj] at hb
      simpa using hb
  have hj₀lt : j₀.val < 2 := by
    by_contra hc
    have : (emb (y - z) : Site d) j₀ = 0 := emb_sub_eq_zero (d := d) hc
    rw [hemb, Pi.single_eq_same] at this
    rcases hσ with rfl | rfl <;> omega
  have hrad : rad (5 * r) t j₀ = 5 * (r : ℤ) := by
    unfold rad; rw [if_pos hj₀lt]; push_cast; ring
  rw [hrad] at hfail
  have hb := hbox j₀
  rw [hctr j₀, hemb, Pi.single_eq_same, hrad] at hb
  push_cast at hb hfail ⊢
  have hr0 : (0 : ℤ) ≤ r := Nat.cast_nonneg r
  rcases hσ with rfl | rfl
  · simp only [one_mul, mul_one] at hb ⊢
    rcases hb with ⟨hb1, hb2⟩
    have hmin : min (ctr d r z j₀) (ctr d r z j₀ + 20 * (r : ℤ)) = ctr d r z j₀ := by
      rw [min_eq_left]; linarith
    rw [hmin] at hb1
    omega
  · rcases hb with ⟨hb1, hb2⟩
    have hmax : max (ctr d r z j₀) (ctr d r z j₀ + 20 * (r : ℤ) * (-1)) = ctr d r z j₀ := by
      rw [max_eq_left]; linarith
    rw [hmax] at hb2
    have : (-1 : ℤ) * (x j₀ - ctr d r z j₀) = ctr d r z j₀ - x j₀ := by ring
    rw [this]
    omega

end Separation

/-! ## Separation of protected directional regions

`KN.CorridorFreshness` proves the more general classification used by later corridor modules, but
that module imports this one.  The following local form is therefore proved here, before the
probability invariant is constructed: two oriented nearest-neighbour edge regions with different
heads, which are not opposite orientations of the same edge, are disjoint. -/

section ProtectedSeparation

private theorem reserveMacroCell_le {r a b : ℤ} (hr : 0 < r)
    (h : 20 * r * a - 5 * r ≤ 20 * r * b + 5 * r) : a ≤ b := by
  by_contra h'
  push Not at h'
  have hgap : b + 1 ≤ a := h'
  have hscale := mul_le_mul_of_nonneg_left hgap (show (0 : ℤ) ≤ 20 * r by positivity)
  nlinarith

private theorem reserveMacroCell_lt {r a b : ℤ} (hr : 0 < r)
    (h : 20 * r * a - 5 * r < 20 * r * b - 5 * r) : a < b := by
  by_contra h'
  push Not at h'
  have hscale := mul_le_mul_of_nonneg_left h' (show (0 : ℤ) ≤ 20 * r by positivity)
  nlinarith

private theorem reserveHead_between {r : ℤ} (hr : 0 < r) {w z a b X : ℤ}
    (hwz : z = w ∨ z = w + 1 ∨ z = w - 1)
    (h1 : min (20 * r * w) (20 * r * z) - 5 * r ≤ X)
    (h2 : X ≤ max (20 * r * w) (20 * r * z) + 5 * r)
    (h3 : min (20 * r * a) (20 * r * b) - 5 * r ≤ X)
    (h4 : X ≤ max (20 * r * a) (20 * r * b) + 5 * r)
    (hside : z = w ∨ X < 20 * r * w - 5 * r ∨ 20 * r * w + 5 * r < X) :
    min a b ≤ z ∧ z ≤ max a b := by
  have hr0 : (0 : ℤ) ≤ 20 * r := by positivity
  have hab : min (20 * r * a) (20 * r * b) = 20 * r * min a b ∧
      max (20 * r * a) (20 * r * b) = 20 * r * max a b := by
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab,
        min_eq_left (mul_le_mul_of_nonneg_left hab hr0),
        max_eq_right (mul_le_mul_of_nonneg_left hab hr0)]
      exact ⟨rfl, rfl⟩
    · rw [min_eq_right hab, max_eq_left hab,
        min_eq_right (mul_le_mul_of_nonneg_left hab hr0),
        max_eq_left (mul_le_mul_of_nonneg_left hab hr0)]
      exact ⟨rfl, rfl⟩
  rw [hab.1] at h3
  rw [hab.2] at h4
  rcases hwz with hz | hz | hz
  · subst hz
    rw [min_self] at h1
    rw [max_self] at h2
    exact ⟨reserveMacroCell_le hr (h3.trans h2), reserveMacroCell_le hr (h1.trans h4)⟩
  · subst hz
    have hmin : min (20 * r * w) (20 * r * (w + 1)) = 20 * r * w :=
      min_eq_left (mul_le_mul_of_nonneg_left (by linarith) hr0)
    have hmax : max (20 * r * w) (20 * r * (w + 1)) = 20 * r * (w + 1) :=
      max_eq_right (mul_le_mul_of_nonneg_left (by linarith) hr0)
    rw [hmin] at h1
    rw [hmax] at h2
    rcases hside with hside | hside | hside
    · omega
    · linarith
    · refine ⟨reserveMacroCell_le hr (h3.trans h2), ?_⟩
      have : w < max a b := reserveMacroCell_lt hr (by linarith)
      omega
  · subst hz
    have hmin : min (20 * r * w) (20 * r * (w - 1)) = 20 * r * (w - 1) :=
      min_eq_right (mul_le_mul_of_nonneg_left (by linarith) hr0)
    have hmax : max (20 * r * w) (20 * r * (w - 1)) = 20 * r * w :=
      max_eq_left (mul_le_mul_of_nonneg_left (by linarith) hr0)
    rw [hmin] at h1
    rw [hmax] at h2
    rcases hside with hside | hside | hside
    · omega
    · refine ⟨?_, reserveMacroCell_le hr (h1.trans h4)⟩
      have : min a b < w := reserveMacroCell_lt hr (by linarith)
      omega
    · linarith

private def reservePlanarCoord {d : ℕ} (hd : 2 ≤ d) (i : Fin 2) : Fin d :=
  ⟨i.val, lt_of_lt_of_le i.isLt hd⟩

private theorem reservePlanarCoord_val_lt {d : ℕ} (hd : 2 ≤ d) (i : Fin 2) :
    (reservePlanarCoord hd i).val < 2 := i.isLt

private theorem ctr_reservePlanarCoord {d : ℕ} (hd : 2 ≤ d) (r : ℕ)
    (z : Site 2) (i : Fin 2) :
    ctr d r z (reservePlanarCoord hd i) = 20 * (r : ℤ) * z i := by
  rw [ctr_apply_of_lt r z (reservePlanarCoord_val_lt hd i)]
  rfl

private theorem rad_reservePlanarCoord {d : ℕ} (hd : 2 ≤ d) (R t : ℕ) (i : Fin 2) :
    rad R t (reservePlanarCoord hd i) = R := by
  unfold rad
  rw [if_pos (reservePlanarCoord_val_lt hd i)]

private theorem reserveHbox_planar_bounds {d : ℕ} (hd : 2 ≤ d) (r t : ℕ)
    (a b : Site 2) {x : Site d}
    (hx : x ∈ hbox (ctr d r a) (ctr d r b) (5 * r) t) (i : Fin 2) :
    min (20 * (r : ℤ) * a i) (20 * (r : ℤ) * b i) - 5 * r ≤
        x (reservePlanarCoord hd i) ∧
      x (reservePlanarCoord hd i) ≤
        max (20 * (r : ℤ) * a i) (20 * (r : ℤ) * b i) + 5 * r := by
  have h := (mem_hbox.1 hx) (reservePlanarCoord hd i)
  rw [ctr_reservePlanarCoord hd r a i, ctr_reservePlanarCoord hd r b i,
    rad_reservePlanarCoord hd (5 * r) t i] at h
  push_cast at h
  exact h

private theorem exists_reservePlanar_outside_tail {d : ℕ} (hd : 2 ≤ d) (r t : ℕ)
    {w z : Site 2} {x : Site d} (hx : x ∈ E d r t w z) :
    ∃ i : Fin 2, x (reservePlanarCoord hd i) < 20 * (r : ℤ) * w i - 5 * r ∨
      20 * (r : ℤ) * w i + 5 * r < x (reservePlanarCoord hd i) := by
  rw [E, Finset.mem_sdiff] at hx
  obtain ⟨hxh, hxQ⟩ := hx
  rw [Q, mem_abox] at hxQ
  push Not at hxQ
  obtain ⟨j, hj⟩ := hxQ
  by_cases hjlt : j.val < 2
  · refine ⟨⟨j.val, hjlt⟩, ?_⟩
    have hpl : reservePlanarCoord hd ⟨j.val, hjlt⟩ = j := Fin.ext rfl
    rw [hpl]
    rw [ctr_apply_of_lt r w hjlt] at hj
    unfold rad at hj
    rw [if_pos hjlt] at hj
    push_cast at hj
    rcases lt_or_ge (x j) (20 * (r : ℤ) * w ⟨j.val, hjlt⟩ - 5 * r) with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · exfalso
    have h := (mem_hbox.1 hxh) j
    rw [ctr_apply_of_not_lt r w hjlt, ctr_apply_of_not_lt r z hjlt] at h
    rw [ctr_apply_of_not_lt r w hjlt] at hj
    unfold rad at h hj
    rw [if_neg hjlt] at h hj
    simp only [min_self, max_self] at h
    omega

private theorem reserveAdjacent_coord {w z : Site 2} (h : (zdGraph 2).Adj w z) (i : Fin 2) :
    z i = w i ∨ z i = w i + 1 ∨ z i = w i - 1 := by
  obtain ⟨k, hk | hk⟩ := (zdGraph_adj_iff w z).1 h
  · rw [hk]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik]
  · rw [hk]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [hik]

private theorem reserveHead_mem_hull {d : ℕ} (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z a b : Site 2} (hwz : (zdGraph 2).Adj w z) {x : Site d}
    (hx : x ∈ E d r t w z)
    (hab : x ∈ hbox (ctr d r a) (ctr d r b) (5 * r) t) (i : Fin 2) :
    min (a i) (b i) ≤ z i ∧ z i ≤ max (a i) (b i) := by
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have hxh : x ∈ hbox (ctr d r w) (ctr d r z) (5 * r) t :=
    (Finset.mem_sdiff.1 hx).1
  obtain ⟨i₀, hi₀⟩ := exists_reservePlanar_outside_tail hd r t hx
  have h1 := reserveHbox_planar_bounds hd r t w z hxh i
  have h2 := reserveHbox_planar_bounds hd r t a b hab i
  by_cases hii : i = i₀
  · subst hii
    exact reserveHead_between hr' (reserveAdjacent_coord hwz i)
      h1.1 h1.2 h2.1 h2.2 (Or.inr hi₀)
  · have hwi : z i = w i := by
      obtain ⟨k, hk | hk⟩ := (zdGraph_adj_iff w z).1 hwz
      · have hik : i ≠ k := by
          intro hik
          subst hik
          have h0 := reserveHbox_planar_bounds hd r t w z hxh i₀
          have hz0 : z i₀ = w i₀ := by rw [hk]; simp [Ne.symm hii]
          rw [hz0, min_self, max_self] at h0
          omega
        rw [hk]
        simp [hik]
      · have hik : i ≠ k := by
          intro hik
          subst hik
          have h0 := reserveHbox_planar_bounds hd r t w z hxh i₀
          have hz0 : z i₀ = w i₀ := by rw [hk]; simp [Ne.symm hii]
          rw [hz0, min_self, max_self] at h0
          omega
        rw [hk]
        simp [hik]
    exact reserveHead_between hr' (Or.inl hwi) h1.1 h1.2 h2.1 h2.2 (Or.inl hwi)

private theorem reserveEq_endpoint_of_hull {a b z : Site 2} (hab : (zdGraph 2).Adj a b)
    (h : ∀ i, min (a i) (b i) ≤ z i ∧ z i ≤ max (a i) (b i)) : z = a ∨ z = b := by
  obtain ⟨k, hk | hk⟩ := (zdGraph_adj_iff a b).1 hab
  · have hother : ∀ i, i ≠ k → z i = a i := by
      intro i hik
      have hi := h i
      rw [hk] at hi
      simp [hik] at hi
      omega
    have hk' := h k
    rw [hk] at hk'
    simp at hk'
    rcases (show z k = a k ∨ z k = a k + 1 by omega) with hz | hz
    · left
      funext i
      by_cases hik : i = k
      · subst hik
        exact hz
      · exact hother i hik
    · right
      funext i
      by_cases hik : i = k
      · subst hik
        rw [hk]
        simp [hz]
      · rw [hk]
        simp [hik, hother i hik]
  · have hother : ∀ i, i ≠ k → z i = b i := by
      intro i hik
      have hi := h i
      rw [hk] at hi
      simp [hik] at hi
      omega
    have hk' := h k
    rw [hk] at hk'
    simp at hk'
    rcases (show z k = b k ∨ z k = b k + 1 by omega) with hz | hz
    · right
      funext i
      by_cases hik : i = k
      · subst hik
        exact hz
      · exact hother i hik
    · left
      funext i
      by_cases hik : i = k
      · subst hik
        rw [hk]
        simp [hz]
      · rw [hk]
        simp [hik, hother i hik]

private theorem reserveHead_eq_endpoint_of_inter {d : ℕ} (hd : 2 ≤ d) (r t : ℕ)
    (hr : 0 < r) {w z w' z' : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hwz' : (zdGraph 2).Adj w' z') {x : Site d}
    (hx : x ∈ E d r t w z) (hx' : x ∈ E d r t w' z') : z = w' ∨ z = z' := by
  have hxH : x ∈ hbox (ctr d r w') (ctr d r z') (5 * r) t :=
    (Finset.mem_sdiff.1 hx').1
  exact reserveEq_endpoint_of_hull hwz'
    (reserveHead_mem_hull hd r t hr hwz hx hxH)

private theorem reserveQ_eq_hbox_self {d : ℕ} (r t : ℕ) (z : Site 2) :
    Q d r t z = hbox (ctr d r z) (ctr d r z) (5 * r) t := by
  ext x
  rw [Q, mem_abox, mem_hbox]
  simp only [min_self, max_self]

/-- An oriented protected edge is disjoint from every central box except its head box. -/
theorem protectedEdge_disjoint_Q {d : ℕ} (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z z' : Site 2} (hwz : (zdGraph 2).Adj w z) (hz' : z' ≠ z) :
    Disjoint (E d r t w z) (Q d r t z') := by
  rw [Finset.disjoint_left]
  intro x hxE hxQ
  rw [reserveQ_eq_hbox_self] at hxQ
  have hz : z = z' := by
    funext i
    have hi := reserveHead_mem_hull hd r t hr hwz hxE hxQ i
    simp only [min_self, max_self] at hi
    omega
  exact hz' hz.symm

/-- Protected regions with distinct, non-reversed oriented macro-edges are disjoint. -/
theorem protectedEdges_disjoint {d : ℕ} (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z w' z' : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hwz' : (zdGraph 2).Adj w' z') (hheads : z ≠ z')
    (hrev : ¬ (w = z' ∧ z = w')) : Disjoint (E d r t w z) (E d r t w' z') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rcases reserveHead_eq_endpoint_of_inter hd r t hr hwz hwz' hx hx' with hzw' | hzz'
  · have hz'w : z' = w ∨ z' = z :=
      reserveHead_eq_endpoint_of_inter hd r t hr hwz' hwz hx' hx
    rcases hz'w with hz'w | hz'z
    · exact hrev ⟨hz'w.symm, hzw'⟩
    · exact hheads hz'z.symm
  · exact hheads hzz'

end ProtectedSeparation

/-! ## The exploration -/

section Explore

variable (d : ℕ) [NeZero d] (r t n : ℕ)

/-- A transcript of the macro exploration: sites of `ℤ^d` are read, macro-vertices of `ℤ²` are
determined. -/
abbrev Tr := FRDom.Transcript (Site d) (Site 2)

/-- The target of the exploration of radius `n`: the inner boundary of the macro box. -/
def tgt : Set (Site 2) := ↑(innerBoundary (zdGraph 2) (box 2 n))

theorem boundary_nonempty_of_not_terminal {h : Tr d}
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    (h.boundary (zdGraph 2) (box 2 n) 0).Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun he => hT (Or.inr he)

open Classical in
/-- The macro-vertex examined next: a frontier vertex, when there is one. -/
def pendZ (h : Tr d) : Site 2 :=
  if hne : (h.boundary (zdGraph 2) (box 2 n) 0).Nonempty then hne.choose else 0

theorem pendZ_mem {h : Tr d} (hne : (h.boundary (zdGraph 2) (box 2 n) 0).Nonempty) :
    pendZ d n h ∈ h.boundary (zdGraph 2) (box 2 n) 0 := by
  unfold pendZ
  rw [dif_pos hne]
  exact hne.choose_spec

open Classical in
/-- An occupied predecessor of the macro-vertex examined next, when there is one. -/
def pendW (h : Tr d) : Site 2 :=
  if hex : ∃ u ∈ h.explored (zdGraph 2) 0, (zdGraph 2).Adj u (pendZ d n h) then hex.choose else 0

/-- The fresh part of the edge region leading to the macro-vertex examined next. -/
def region (h : Tr d) : Finset (Site d) := E d r t (pendW d n h) (pendZ d n h) \ h.inspected

/-- The recorded states together with the states read on the fresh region: the configuration on
which the incoming event is decided. -/
def rec (h : Tr d) (ω : SiteConfig (Site d)) : SiteConfig (Site d) :=
  (↑h.openSites : Set (Site d)) ∪ (ω ∩ ↑(region d r t n h))

open Classical in
/-- The macro-neighbours of `z` still undetermined by the transcript. -/
def pending (h : Tr d) (z : Site 2) : Finset (Site 2) :=
  (nbrs z).filter fun z' => z' ∉ h.openV ∪ h.closedV

theorem mem_pending {h : Tr d} {z z' : Site 2} :
    z' ∈ pending d h z ↔ z' ∈ nbrs z ∧ z' ∉ h.openV ∪ h.closedV := by
  classical
  simp [pending]

/-- Determining more macro-vertices leaves fewer pending directions. -/
theorem pending_subset_of_subset {h h' : Tr d} {z : Site 2}
    (hsub : h.openV ∪ h.closedV ⊆ h'.openV ∪ h'.closedV) :
    pending d h' z ⊆ pending d h z := by
  intro z' hz'
  rw [mem_pending] at hz' ⊢
  exact ⟨hz'.1, fun hc => hz'.2 (hsub hc)⟩

/-- The old deterministic stub source.  It remains useful as a geometric point, but the corrected
exploration does not demand a connection from it: doing so incurs an unavoidable factor `q`. -/
def src (h : Tr d) : Site d := tip d r (pendW d n h) (pendZ d n h)

/-- The event protected by the directional reservation `z → y`.  The history already inspected is
allowed, and the only unread coordinates on which the event depends are in its own edge region.
This is equation (69) of the corrected macro examination. -/
def reservationEvent (h : Tr d) (z y : Site 2) : Set (SiteConfig (Site d)) :=
  connWithinSet (zdGraph d) (↑(h.inspected ∪ E d r t z y) : Set (Site d))
    (emb 0) (↑(M d r t y) : Set (Site d))

/-- A directional reservation is a near-one pinned conditional probability, not a realized path
to a designated gateway.  The sites exposed through the first good level are part of
`h.inspected`; the unread remainder is protected inside `E z y`. -/
def reservationBound (q : unitInterval) (δ : ℝ) (h : Tr d) (z y : Site 2) : Prop :=
  1 - δ < h.prob (fun _ : Site d => q) (reservationEvent d r t h z y)

/-- The transcript obtained if the current examination is accepted.  Naming it makes the outgoing
postcondition in `succ` unambiguous: its probability is evaluated after the newly read states have
been pinned. -/
def accepted (h : Tr d) (ω : SiteConfig (Site d)) : Tr d :=
  h.step (pendZ d n h) (region d r t n h) true ω

/-- **The corrected invariant-level success postcondition.**  The incoming reservation is realized as an actual connection
from the origin to the new target box.  For every still-pending direction of the new vertex, the
post-examination transcript must acquire a near-one directional reservation.  No deterministic
connection to a tip, face, or other designated target is requested. -/
def succ (q : unitInterval) (δ : ℝ) (h : Tr d) : Set (SiteConfig (Site d)) :=
  {ω | (∃ a ∈ M d r t (pendZ d n h), rec d r t n h ω ∈
        connWithin (zdGraph d) (↑(h.inspected ∪ region d r t n h) : Set (Site d))
          (emb 0) a) ∧
      ∀ y ∈ pending d (accepted d r t n h ω) (pendZ d n h),
        reservationBound d r t q δ (accepted d r t n h ω) (pendZ d n h) y}

/-- **The invariant.**  The origin is occupied, everything inspected lies in the slab, and every
occupied macro-vertex has a certificate: a site of its target box joined to the origin of `ℤ^d`
by a path of sites recorded open. -/
structure Good (h : Tr d) (q : unitInterval := 1) (δ : ℝ := 2) : Prop where
  zero_mem : (0 : Site 2) ∈ h.openV
  inspected_thin : (↑h.inspected : Set (Site d)) ⊆ thin d t
  cert : ∀ z ∈ h.openV, ∃ a ∈ M d r t z,
    (↑h.openSites : Set (Site d)) ∈ connWithin (zdGraph d) (↑h.inspected : Set (Site d)) (emb 0) a
  /-- **The probabilistic directional invariant.**  Each pending neighbour of each occupied
  macro-vertex has a protected near-one connection event under the pinned transcript law. -/
  reserve : ∀ z ∈ h.openV, ∀ y ∈ pending d h z,
    reservationBound d r t q δ h z y
  /-- **The cover.**  Every inspected site lies in `Q₀` or in the edge region of an examined
  edge: a macro-edge whose tail is occupied and whose head is determined. -/
  cover : ∃ edges : Finset (Site 2 × Site 2),
    (∀ e ∈ edges, e.1 ∈ h.openV ∧ e.2 ∈ h.openV ∪ h.closedV ∧ (zdGraph 2).Adj e.1 e.2) ∧
    (↑h.inspected : Set (Site d)) ⊆ ↑(Q d r t 0) ∪ ⋃ e ∈ edges, (↑(E d r t e.1 e.2) : Set (Site d))

theorem measurable_rec (h : Tr d) : Measurable (rec d r t n h) := by
  refine measurable_set_iff.2 fun i => ?_
  have hfun : (fun ω : SiteConfig (Site d) => i ∈ rec d r t n h ω)
      = fun ω : SiteConfig (Site d) => i ∈ h.openSites ∨ (i ∈ ω ∧ i ∈ region d r t n h) := by
    funext ω
    simp [rec]
  rw [hfun]
  exact Measurable.or measurable_const (Measurable.and (measurable_set_mem i) measurable_const)

theorem rec_congr (h : Tr d) {ω ω' : SiteConfig (Site d)}
    (hagree : ω ∩ (↑(region d r t n h) : Set (Site d)) = ω' ∩ ↑(region d r t n h)) :
    rec d r t n h ω = rec d r t n h ω' := by
  simp only [rec, hagree]

theorem determinedBy_succ (q : unitInterval) (δ : ℝ) (h : Tr d) :
    DeterminedBy (succ d r t n q δ h)
      (↑(h.inspected ∪ region d r t n h) : Set (Site d)) := by
  rw [determinedBy_iff]
  intro ω ω' hωω'
  have hsub : (↑(region d r t n h) : Set (Site d)) ⊆ ↑(h.inspected ∪ region d r t n h) := by
    rw [Finset.coe_union]; exact Set.subset_union_right
  have hagree : ω ∩ (↑(region d r t n h) : Set (Site d)) = ω' ∩ ↑(region d r t n h) := by
    have key : ∀ ω₀ : SiteConfig (Site d), ω₀ ∩ (↑(region d r t n h) : Set (Site d))
        = (ω₀ ∩ ↑(h.inspected ∪ region d r t n h)) ∩ ↑(region d r t n h) := fun ω₀ => by
      rw [Set.inter_assoc, Set.inter_eq_self_of_subset_right hsub]
    rw [key ω, key ω', hωω']
  have hpoint : ∀ x ∈ region d r t n h, (x ∈ ω ↔ x ∈ ω') := by
    intro x hx
    have hx' := Set.ext_iff.1 hωω' x
    simpa [hx] using hx'
  have hstep : accepted d r t n h ω = accepted d r t n h ω' := by
    exact FRDom.Transcript.step_congr h hpoint
  simp only [succ, Set.mem_setOf_eq, rec_congr d r t n h hagree, hstep]

theorem measurableSet_succ (q : unitInterval) (δ : ℝ) (h : Tr d) :
    MeasurableSet (succ d r t n q δ h) :=
  (determinedBy_succ d r t n q δ h).measurableSet_of_finset

/-- The vertex examined next is not the origin, which is occupied at every good transcript. -/
theorem pendZ_ne_zero {q : unitInterval} {δ : ℝ} {h : Tr d}
    (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) : pendZ d n h ≠ 0 := by
  intro h0
  obtain ⟨-, hzo, -, -⟩ := pendZ_mem d n (boundary_nonempty_of_not_terminal d n hT)
  rw [h0] at hzo
  exact hzo hg.zero_mem

theorem exists_pred {q : unitInterval} {δ : ℝ} {h : Tr d}
    (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    ∃ u ∈ h.explored (zdGraph 2) 0, (zdGraph 2).Adj u (pendZ d n h) := by
  obtain ⟨-, -, -, hor⟩ := pendZ_mem d n (boundary_nonempty_of_not_terminal d n hT)
  rcases hor with h0 | hex
  · exact absurd h0 (pendZ_ne_zero d r t n hg hT)
  · exact hex

/-- The predecessor is a macro-neighbour of the vertex examined next, so it is distinct from it. -/
theorem pendW_ne_pendZ {q : unitInterval} {δ : ℝ} {h : Tr d}
    (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) : pendW d n h ≠ pendZ d n h := by
  have hex := exists_pred d r t n hg hT
  unfold pendW
  rw [dif_pos hex]
  exact hex.choose_spec.2.ne

/-- The predecessor is occupied and macro-adjacent to the vertex examined next. -/
theorem pendW_spec {q : unitInterval} {δ : ℝ} {h : Tr d}
    (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    pendW d n h ∈ h.openV ∧ (zdGraph 2).Adj (pendW d n h) (pendZ d n h) := by
  have hex := exists_pred d r t n hg hT
  unfold pendW
  rw [dif_pos hex]
  exact ⟨Finset.mem_coe.1 (mem_of_mem_siteCluster _ _ hex.choose_spec.1), hex.choose_spec.2⟩

/-- `Good.cover` makes the complete incoming edge region fresh.  This is the local dependency-safe
form of `Corridor.inspected_disjoint_pending_E`; the latter module imports this one, so the proof is
repeated here at the point where `step_good` needs it. -/
theorem inspected_disjoint_pending_E {q : unitInterval} {δ : ℝ} {h : Tr d}
    (hd : 2 ≤ d) (hr : 0 < r) (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    Disjoint h.inspected (E d r t (pendW d n h) (pendZ d n h)) := by
  classical
  obtain ⟨edges, hedges, hcover⟩ := hg.cover
  obtain ⟨-, hzo, hzc, -⟩ :=
    pendZ_mem d n (boundary_nonempty_of_not_terminal d n hT)
  have hnewAdj := (pendW_spec d r t n hg hT).2
  have hpzUndet : pendZ d n h ∉ h.openV ∪ h.closedV := by
    intro hpz
    rcases Finset.mem_union.1 hpz with hpz | hpz
    · exact hzo hpz
    · exact hzc hpz
  have hpzZero : (0 : Site 2) ≠ pendZ d n h := by
    intro h0
    apply hzo
    rw [← h0]
    exact hg.zero_mem
  rw [Finset.disjoint_left]
  intro x hxI hxNew
  rcases hcover (Finset.mem_coe.2 hxI) with hxQ | hxEdges
  · have hdis := protectedEdge_disjoint_Q hd r t hr hnewAdj hpzZero
    exact Finset.disjoint_left.1 hdis hxNew (Finset.mem_coe.1 hxQ)
  · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxEdges
    have he' : e ∈ edges := Finset.mem_coe.1 he
    obtain ⟨heOpen, heDet, heAdj⟩ := hedges e he'
    have hheads : e.2 ≠ pendZ d n h := by
      intro heq
      apply hpzUndet
      rw [← heq]
      exact heDet
    have hreverse : ¬ (e.1 = pendZ d n h ∧ e.2 = pendW d n h) := by
      rintro ⟨heq, -⟩
      apply hpzUndet
      rw [← heq]
      exact Finset.mem_union_left _ heOpen
    have hdis := protectedEdges_disjoint hd r t hr heAdj hnewAdj hheads hreverse
    exact Finset.disjoint_left.1 hdis (Finset.mem_coe.1 hxe) hxNew

/-- At a good nonterminal transcript the exploration's fresh part is the entire incoming edge
region. -/
theorem region_eq_pending_E {q : unitInterval} {δ : ℝ} {h : Tr d}
    (hd : 2 ≤ d) (hr : 0 < r) (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    region d r t n h = E d r t (pendW d n h) (pendZ d n h) := by
  exact Finset.sdiff_eq_self_of_disjoint
    (inspected_disjoint_pending_E d r t n hd hr hg hT).symm

/-- Confined connections compose inside one confining set. -/
theorem connWithin_trans' {S : Set (Site d)} {ω : SiteConfig (Site d)} {x y z : Site d}
    (h₁ : ω ∈ connWithin (zdGraph d) S x y) (h₂ : ω ∈ connWithin (zdGraph d) S y z) :
    ω ∈ connWithin (zdGraph d) S x z := ⟨h₁.1, h₁.2.trans h₂.2⟩

/-- A pending direction after the current step was already pending before it, unless its tail is the
newly accepted vertex. -/
theorem pending_before_step {h : Tr d} (b : Bool) (ω : SiteConfig (Site d))
    {z y : Site 2}
    (hy : y ∈ pending d (h.step (pendZ d n h) (region d r t n h) b ω) z) :
    y ∈ pending d h z := by
  apply pending_subset_of_subset d (h' := h.step (pendZ d n h) (region d r t n h) b ω) _ hy
  rw [FRDom.Transcript.step_determined]
  exact Finset.subset_insert _ _

theorem step_good {q : unitInterval} {δ : ℝ} {h : Tr d} (hd : 2 ≤ d) (hr : 0 < r)
    (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) (b : Bool) (ω : SiteConfig (Site d))
    (hb : b = true ↔ ω ∈ succ d r t n q δ h) :
    Good d r t (h.step (pendZ d n h) (region d r t n h) b ω) q δ where
  zero_mem := by
    rw [FRDom.Transcript.step_openV]
    cases b
    · simpa using hg.zero_mem
    · simp only [if_true]
      exact Finset.mem_insert_of_mem hg.zero_mem
  inspected_thin := by
    rw [FRDom.Transcript.step_inspected, Finset.coe_union]
    refine Set.union_subset hg.inspected_thin ?_
    refine Set.Subset.trans ?_ (E_subset_thin hd r t (pendW d n h) (pendZ d n h))
    rw [Finset.coe_subset]
    exact Finset.sdiff_subset
  cert := by
    intro z hz
    -- the recorded states after the examination
    have hopen : (↑(h.step (pendZ d n h) (region d r t n h) b ω).openSites : Set (Site d))
        = rec d r t n h ω := by
      classical
      show (↑(h.openSites ∪ (region d r t n h).filter (fun x => x ∈ ω)) : Set (Site d)) = _
      rw [Finset.coe_union, Finset.coe_filter, rec]
      congr 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_coe]
      exact and_comm
    have hinsp : (↑(h.step (pendZ d n h) (region d r t n h) b ω).inspected : Set (Site d))
        = ↑(h.inspected ∪ region d r t n h) := by
      rw [FRDom.Transcript.step_inspected]
    rw [hopen, hinsp]
    have hold : ∀ z' ∈ h.openV, ∃ a ∈ M d r t z', rec d r t n h ω ∈
        connWithin (zdGraph d) (↑(h.inspected ∪ region d r t n h) : Set (Site d)) (emb 0) a := by
      intro z' hz'
      obtain ⟨a, ha, hpath⟩ := hg.cert z' hz'
      refine ⟨a, ha, ?_⟩
      have h1 := connWithin_mono_set (zdGraph d) (S' := (↑(h.inspected ∪ region d r t n h) : Set (Site d)))
        (by rw [Finset.coe_union]; exact Set.subset_union_left) (emb 0) a hpath
      exact isUpperSet_connWithin (zdGraph d) _ (emb 0) a (Set.subset_union_left) h1
    rw [FRDom.Transcript.step_openV] at hz
    cases b with
    | false => exact hold z (by simpa using hz)
    | true =>
      simp only [if_true, Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · obtain ⟨a, ha, hconn⟩ := (hb.1 rfl).1
        exact ⟨a, ha, hconn⟩
      · exact hold z hz
  reserve := by
    classical
    intro z hz y hy
    have hold : ∀ z₀ ∈ h.openV,
        ∀ y₀ ∈ pending d (h.step (pendZ d n h) (region d r t n h) b ω) z₀,
          reservationBound d r t q δ
            (h.step (pendZ d n h) (region d r t n h) b ω) z₀ y₀ := by
      intro z₀ hz₀ y₀ hy₀
      have hyOld : y₀ ∈ pending d h z₀ := pending_before_step d r t n b ω hy₀
      have hOld := hg.reserve z₀ hz₀ y₀ hyOld
      have hadjNow : (zdGraph 2).Adj (pendW d n h) (pendZ d n h) :=
        (pendW_spec d r t n hg hT).2
      have hadjProtected : (zdGraph 2).Adj z₀ y₀ :=
        adj_of_mem_nbrs ((mem_pending d).1 hyOld).1
      have hhead : pendZ d n h ≠ y₀ := by
        intro heq
        have hyUndet := ((mem_pending d).1 hy₀).2
        apply hyUndet
        rw [← heq, FRDom.Transcript.step_determined]
        exact Finset.mem_insert_self _ _
      have hpzOld : pendZ d n h ∉ h.openV :=
        (pendZ_mem d n (boundary_nonempty_of_not_terminal d n hT)).2.1
      have hreverse : ¬ (pendW d n h = y₀ ∧ pendZ d n h = z₀) := by
        rintro ⟨-, hpz⟩
        apply hpzOld
        rw [hpz]
        exact hz₀
      have hEdges : Disjoint
          (E d r t (pendW d n h) (pendZ d n h)) (E d r t z₀ y₀) :=
        protectedEdges_disjoint hd r t hr hadjNow hadjProtected hhead hreverse
      have hRegEdge : Disjoint (region d r t n h) (E d r t z₀ y₀) :=
        hEdges.mono_left Finset.sdiff_subset
      have hFresh : Disjoint (region d r t n h) h.inspected :=
        (inspected_disjoint_pending_E d r t n hd hr hg hT).symm.mono_left
          Finset.sdiff_subset
      have hSupportDisj : Disjoint (↑(region d r t n h) : Set (Site d))
          (↑(h.inspected ∪ E d r t z₀ y₀) : Set (Site d)) := by
        rw [Set.disjoint_left]
        intro x hxR hxS
        rw [Finset.mem_coe] at hxR hxS
        rw [Finset.mem_union] at hxS
        rcases hxS with hxI | hxE
        · exact Finset.disjoint_left.1 hFresh hxR hxI
        · exact Finset.disjoint_left.1 hRegEdge hxR hxE
      have hEventDet : DeterminedBy (reservationEvent d r t h z₀ y₀)
          (↑(h.inspected ∪ E d r t z₀ y₀) : Set (Site d)) := by
        exact determinedBy_connWithinSet (zdGraph d)
          (↑(h.inspected ∪ E d r t z₀ y₀) : Set (Site d))
          (emb 0) (↑(M d r t y₀) : Set (Site d))
      have hProbEq := ProbInv.prob_step_eq_of_disjoint h
        (fun _ : Site d => q) (pendZ d n h) (region d r t n h) b ω
        hFresh hEventDet hSupportDisj
      have hDom : (↑(h.inspected ∪ E d r t z₀ y₀) : Set (Site d)) ⊆
          ↑((h.step (pendZ d n h) (region d r t n h) b ω).inspected ∪
            E d r t z₀ y₀) := by
        rw [FRDom.Transcript.step_inspected]
        intro x hx
        simp only [Finset.mem_coe, Finset.mem_union] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx
      have hEventMono : reservationEvent d r t h z₀ y₀ ⊆
          reservationEvent d r t
            (h.step (pendZ d n h) (region d r t n h) b ω) z₀ y₀ :=
        connWithinSet_mono_set (zdGraph d) hDom (emb 0) (↑(M d r t y₀) : Set (Site d))
      unfold reservationBound at hOld ⊢
      calc
        1 - δ < h.prob (fun _ : Site d => q) (reservationEvent d r t h z₀ y₀) := hOld
        _ = (h.step (pendZ d n h) (region d r t n h) b ω).prob
            (fun _ : Site d => q) (reservationEvent d r t h z₀ y₀) := hProbEq.symm
        _ ≤ (h.step (pendZ d n h) (region d r t n h) b ω).prob
            (fun _ : Site d => q)
            (reservationEvent d r t
              (h.step (pendZ d n h) (region d r t n h) b ω) z₀ y₀) :=
          ProbInv.prob_mono _ _ hEventMono
    rw [FRDom.Transcript.step_openV] at hz
    cases b with
    | false => exact hold z (by simpa using hz) y hy
    | true =>
      simp only [if_true, Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · simpa [accepted] using (hb.1 rfl).2 y hy
      · exact hold z hz y hy
  cover := by
    classical
    obtain ⟨edges, hedges, hcov⟩ := hg.cover
    obtain ⟨hwV, hadj⟩ := pendW_spec d r t n hg hT
    refine ⟨insert (pendW d n h, pendZ d n h) edges, ?_, ?_⟩
    · intro e he
      rw [Finset.mem_insert] at he
      have hdet : (h.step (pendZ d n h) (region d r t n h) b ω).openV ∪
          (h.step (pendZ d n h) (region d r t n h) b ω).closedV
            = insert (pendZ d n h) (h.openV ∪ h.closedV) := FRDom.Transcript.step_determined h
      have hopenV : h.openV ⊆ (h.step (pendZ d n h) (region d r t n h) b ω).openV := by
        rw [FRDom.Transcript.step_openV]
        cases b
        · simp
        · simp only [if_true]; exact Finset.subset_insert _ _
      rcases he with rfl | he
      · refine ⟨hopenV hwV, ?_, hadj⟩
        rw [hdet]
        exact Finset.mem_insert_self _ _
      · obtain ⟨h1, h2, h3⟩ := hedges e he
        refine ⟨hopenV h1, ?_, h3⟩
        rw [hdet]
        exact Finset.mem_insert_of_mem h2
    · rw [FRDom.Transcript.step_inspected, Finset.coe_union]
      refine Set.union_subset (hcov.trans (Set.union_subset_union_right _ ?_)) ?_
      · exact Set.biUnion_subset_biUnion_left (Finset.coe_subset.2 (Finset.subset_insert _ _))
      · intro x hx
        have hxE : x ∈ E d r t (pendW d n h) (pendZ d n h) :=
          (Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)).1
        refine Or.inr ?_
        exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_self _ _)) (Finset.mem_coe.2 hxE)

/-- **The macro exploration** of radius `n`, at spacing `r`, transverse half-width `t`, density
`q`: an instance of `FRDom.Exploration` on the arena `box 2 n` with root `0` and target the inner
boundary of the arena. -/
def macroExp (hd : 2 ≤ d) (hr : 0 < r) (q : unitInterval) (δ : ℝ) :
    FRDom.Exploration (Site d) (zdGraph 2) (box 2 n) (0 : Site 2) (tgt n) where
  density _ := q
  Admissible := fun h => Good d r t h q δ
  next := pendZ d n
  region := region d r t n
  succ := succ d r t n q δ
  succ_measurable := measurableSet_succ d r t n q δ
  next_mem_boundary _ _ hT := pendZ_mem d n (boundary_nonempty_of_not_terminal d n hT)
  region_fresh _ _ _ := Finset.sdiff_disjoint
  succ_determinedBy h _ _ := determinedBy_succ d r t n q δ h
  step_admissible _ hg hT b ω hb := step_good d r t n hd hr hg hT b ω hb

/-- The start transcript: the central box of the origin read and recorded open, the origin
occupied. -/
def start : Tr d :=
  ⟨Q d r t 0, Q d r t 0, Finset.Subset.refl _, {0}, ∅⟩

/-- Build the corrected initial invariant from the four initial long-box bounds. -/
theorem start_good_of_reservations (hd : 2 ≤ d) (q : unitInterval) (δ : ℝ)
    (hreserve : ∀ y ∈ pending d (start d r t) 0,
      reservationBound d r t q δ (start d r t) 0 y) :
    Good d r t (start d r t) q δ where
  zero_mem := Finset.mem_singleton_self _
  inspected_thin := Q_subset_thin hd r t 0
  cert := by
    intro z hz
    have hz' : z ∈ ({0} : Finset (Site 2)) := hz
    rw [Finset.mem_singleton] at hz'
    subst hz'
    refine ⟨emb 0, emb_zero_mem_M r t, ?_⟩
    have h0 : (emb 0 : Site d) ∈ Q d r t 0 := M_subset_Q r t 0 (emb_zero_mem_M r t)
    exact ⟨⟨Finset.mem_coe.2 h0, Finset.mem_coe.2 h0⟩, SimpleGraph.Reachable.refl _⟩
  reserve := by
    intro z hz y hy
    have hz' : z ∈ ({0} : Finset (Site 2)) := hz
    rw [Finset.mem_singleton] at hz'
    subst z
    exact hreserve y hy
  cover := ⟨∅, fun e he => absurd he (Finset.notMem_empty e), by
    show (↑(Q d r t 0) : Set (Site d)) ⊆ _
    simp⟩

/-- A loose-tolerance inhabitant used only to record unconditional non-vacuity of `Good`.  Useful
applications use `start_good_of_reservations` (or the initial field of `StepBound`) with
`δ ≤ (1-a)/4`. -/
theorem start_good (hd : 2 ≤ d) (q : unitInterval) {δ : ℝ} (hδ : 1 < δ) :
    Good d r t (start d r t) q δ := by
  apply start_good_of_reservations d r t hd q δ
  intro y hy
  unfold reservationBound
  have hp := FRDom.Transcript.prob_nonneg (start d r t)
    (fun _ : Site d => q) (reservationEvent d r t (start d r t) 0 y)
  linarith

end Explore

/-! ### Boundary of the present transcript interface

The probability invariant and its persistence are represented exactly above.  The
`FRDom.Exploration` interface, however, has one configuration-independent `region h`, and its only
transition both reads all of that region and commits the Boolean verdict.  Thus it cannot itself
represent the manuscript's configuration-dependent stopping set obtained by revealing
`H⁰, H¹, ...` until the first good level.  Here `succ` states the required postcondition, while
`StepBound` remains the contract that an implementation of that stopped examination must prove.

A literal layer-by-layer implementation needs either (i) transcript substeps which enlarge
`inspected` without changing `openV` or `closedV`, together with an examination phase and current
level, or (ii) a stopping-time transition whose recorded finite region may depend measurably on the
states read so far.  In either version the reserved parent edge and its protected unread region
must remain recorded until the final commit. -/

/-! ## From a one-step bound to percolation in the slab -/

section Conclusion

variable (d : ℕ) [NeZero d] (r t : ℕ)

/-- **The corrected one-step contract.**  It includes the initial four reservations and chooses a
positive directional tolerance small enough for the failure budget.  At every resulting good
nonterminal transcript, the corrected usable event has pinned probability at least `a`. -/
def StepBound (q a : unitInterval) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ (1 - (a : ℝ)) / 4 ∧ δ ≤ 1 / 2 ∧
    Good d r t (start d r t) q δ ∧
    ∀ (n : ℕ) (h : Tr d), Good d r t h q δ →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n) →
      (a : ℝ) ≤ h.prob (fun _ : Site d => q) (succ d r t n q δ h)

variable {d r t}

/-- Every transcript reached by a run from a good transcript is good. -/
theorem good_run (hd : 2 ≤ d) (hr : 0 < r) {n : ℕ} (q : unitInterval) (δ : ℝ) :
    ∀ (m : ℕ) (h : Tr d), Good d r t h q δ →
      ∀ ω : SiteConfig (Site d),
      Good d r t ((macroExp d r t n hd hr q δ).run m h ω) q δ := by
  intro m
  induction m with
  | zero => intro h hg ω; simpa using hg
  | succ m ih =>
    intro h hg ω
    by_cases hT : h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)
    · rw [(macroExp d r t n hd hr q δ).run_succ_of_terminal hT]
      exact hg
    · rw [(macroExp d r t n hd hr q δ).run_succ_of_not_terminal hT]
      exact ih _ (step_good d r t n hd hr hg hT _ ω
        ((macroExp d r t n hd hr q δ).bit_eq_true_iff h ω)) ω

/-- Along a run, the recorded open sites are open in the configuration read, provided this was so
at the start. -/
theorem openSites_run_subset (hd : 2 ≤ d) (hr : 0 < r) {n : ℕ}
    (q : unitInterval) (δ : ℝ) :
    ∀ (m : ℕ) (h : Tr d) (ω : SiteConfig (Site d)), (↑h.openSites : Set (Site d)) ⊆ ω →
      (↑((macroExp d r t n hd hr q δ).run m h ω).openSites : Set (Site d)) ⊆ ω := by
  intro m
  induction m with
  | zero => intro h ω hω; simpa using hω
  | succ m ih =>
    intro h ω hω
    by_cases hT : h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)
    · rw [(macroExp d r t n hd hr q δ).run_succ_of_terminal hT]
      exact hω
    · rw [(macroExp d r t n hd hr q δ).run_succ_of_not_terminal hT]
      refine ih _ ω ?_
      classical
      show (↑(h.openSites ∪ (region d r t n h).filter (fun x => x ∈ ω)) : Set (Site d)) ⊆ ω
      rw [Finset.coe_union]
      refine Set.union_subset hω ?_
      intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      exact hx.2

/-- A macro-vertex of the inner boundary of the macro box of radius `n` has a coordinate of
absolute value `n`. -/
theorem exists_coord_of_mem_innerBoundary {n : ℕ} {z : Site 2}
    (hz : z ∈ innerBoundary (zdGraph 2) (box 2 n)) : ∃ i : Fin 2, |z i| = n := by
  rw [mem_innerBoundary_iff] at hz
  obtain ⟨hzbox, y, hy, hadj⟩ := hz
  rw [mem_box] at hzbox
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff z y).1 hadj
  · refine ⟨i, ?_⟩
    have hyi : ¬ (-(n : ℤ) ≤ y i ∧ y i ≤ n) := by
      intro hcon
      exact hy (mem_box.2 fun j => by
        by_cases hj : j = i
        · subst hj; exact hcon
        · have := hzbox j
          rw [hi]
          simpa [Pi.single_apply, hj] using this)
    have hzi := hzbox i
    have hrel : y i = z i + 1 := by
      rw [hi]; simp
    rw [abs_eq (Nat.cast_nonneg n)]
    omega
  · refine ⟨i, ?_⟩
    have hyi : ¬ (-(n : ℤ) ≤ y i ∧ y i ≤ n) := by
      intro hcon
      exact hy (mem_box.2 fun j => by
        by_cases hj : j = i
        · subst hj; exact hcon
        · have := hzbox j
          rw [hi] at this
          simpa [Pi.single_apply, hj] using this)
    have hzi := hzbox i
    have hrel : z i = y i + 1 := by
      rw [hi]; simp
    rw [abs_eq (Nat.cast_nonneg n)]
    omega

/-- **The certificate at a reaching transcript.**  If a good transcript has reached the inner
boundary of the macro box of radius `n`, then some site at planar distance at least `20 r n - 3 r`
from the origin is joined to it by a path of sites recorded open. -/
theorem exists_far_of_reaches (hd : 2 ≤ d) {q : unitInterval} {δ : ℝ}
    {n : ℕ} {h : Tr d} (hg : Good d r t h q δ)
    (hR : h.Reaches (zdGraph 2) 0 (tgt n)) :
    ∃ a : Site d, (∃ j : Fin d, 20 * (r : ℤ) * n - 3 * r ≤ |a j|) ∧
      (↑h.openSites : Set (Site d)) ∈ connWithin (zdGraph d) (↑h.inspected : Set (Site d)) (emb 0) a := by
  obtain ⟨z, hz, hzex⟩ := hR
  have hzV : z ∈ h.openV := Finset.mem_coe.1 (mem_of_mem_siteCluster _ _ hzex)
  obtain ⟨a, ha, hpath⟩ := hg.cert z hzV
  refine ⟨a, ?_, hpath⟩
  obtain ⟨i, hi⟩ := exists_coord_of_mem_innerBoundary (Finset.mem_coe.1 hz)
  have hid : i.val < d := lt_of_lt_of_le i.isLt hd
  refine ⟨⟨i.val, hid⟩, ?_⟩
  rw [M, mem_abox] at ha
  have h1 := ha ⟨i.val, hid⟩
  have hjlt : (⟨i.val, hid⟩ : Fin d).val < 2 := i.isLt
  rw [ctr_apply_of_lt r z hjlt] at h1
  unfold rad at h1
  rw [if_pos hjlt] at h1
  have hzi : z ⟨(⟨i.val, hid⟩ : Fin d).val, hjlt⟩ = z i := rfl
  rw [hzi] at h1
  push_cast at h1
  rcases (abs_eq (Nat.cast_nonneg n)).1 hi with hz' | hz'
  · rw [hz'] at h1
    linarith [le_abs_self (a ⟨i.val, hid⟩)]
  · rw [hz'] at h1
    have h2 : 20 * (r : ℤ) * (-(n : ℤ)) = -(20 * r * n) := by ring
    rw [h2] at h1
    linarith [neg_le_abs (a ⟨i.val, hid⟩)]

/-- **The far-arm event.**  Some site at planar distance at least `20 r n - 3 r` from the origin is
joined to the origin of `ℤ^d` by an open path inside the slab. -/
def far (d : ℕ) [NeZero d] (r t n : ℕ) : Set (SiteConfig (Site d)) :=
  {ω | ∃ a : Site d, (∃ j : Fin d, 20 * (r : ℤ) * n - 3 * r ≤ |a j|) ∧
    ω ∈ connWithin (zdGraph d) (thin d t) (emb 0) a}

/-- A confined connection is the preimage of the unconfined one under intersection with the
confining set, which is measurable whatever the confining set. -/
theorem measurableSet_connWithin_of_countable {V : Type*} [Countable V] (G : SimpleGraph V)
    (S : Set V) (x y : V) : MeasurableSet (connWithin G S x y) := by
  have hmeas : Measurable fun ω : SiteConfig V => ω ∩ S := by
    refine measurable_set_iff.2 fun i => ?_
    have hfun : (fun ω : SiteConfig V => i ∈ ω ∩ S) = fun ω : SiteConfig V => i ∈ ω ∧ i ∈ S := by
      funext ω; rfl
    rw [hfun]
    exact Measurable.and (measurable_set_mem i) measurable_const
  have hset : connWithin G S x y = (fun ω : SiteConfig V => ω ∩ S) ⁻¹' siteConn G x y := by
    ext ω; rfl
  rw [hset]
  exact hmeas (measurableSet_siteConn G x y)

theorem measurableSet_far (d : ℕ) [NeZero d] (r t n : ℕ) : MeasurableSet (far d r t n) := by
  have hset : far d r t n = ⋃ a : Site d, ⋃ _ : (∃ j : Fin d, 20 * (r : ℤ) * n - 3 * r ≤ |a j|),
      connWithin (zdGraph d) (thin d t) (emb 0) a := by
    ext ω; simp [far]
  rw [hset]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun _ =>
    measurableSet_connWithin_of_countable _ _ _ _

theorem far_antitone (d : ℕ) [NeZero d] (r t : ℕ) : Antitone (far d r t) := by
  refine antitone_nat_of_succ_le fun n ω hω => ?_
  obtain ⟨a, ⟨j, hj⟩, hconn⟩ := hω
  refine ⟨a, ⟨j, ?_⟩, hconn⟩
  have hr : (0 : ℤ) ≤ r := Nat.cast_nonneg r
  have : 20 * (r : ℤ) * ((n + 1 : ℕ) : ℤ) = 20 * r * n + 20 * r := by push_cast; ring
  rw [this] at hj
  linarith

/-- **A reaching run has a far arm.**  Read on a configuration in which the central box of the
origin is open, a run of the exploration that reaches the inner boundary of the macro box of radius
`n` exhibits an open path inside the slab from the origin to a site at planar distance at least
`20 r n - 3 r`. -/
theorem far_of_run_reaches (hd : 2 ≤ d) (hr : 0 < r) {n : ℕ}
    (q : unitInterval) (δ : ℝ)
    (hstart : Good d r t (start d r t) q δ) (m : ℕ)
    {ω : SiteConfig (Site d)} (hQ : (↑(Q d r t 0) : Set (Site d)) ⊆ ω)
    (hR : ((macroExp d r t n hd hr q δ).run m (start d r t) ω).Reaches
      (zdGraph 2) 0 (tgt n)) :
    ω ∈ far d r t n := by
  have hg := good_run hd hr (n := n) q δ m (start d r t) hstart ω
  obtain ⟨a, hfar, hpath⟩ := exists_far_of_reaches hd hg hR
  refine ⟨a, hfar, ?_⟩
  have hsub : (↑((macroExp d r t n hd hr q δ).run m (start d r t) ω).openSites :
      Set (Site d)) ⊆ ω :=
    openSites_run_subset hd hr (n := n) q δ m (start d r t) ω hQ
  exact isUpperSet_connWithin (zdGraph d) _ (emb 0) a hsub
    (connWithin_mono_set (zdGraph d) hg.inspected_thin (emb 0) a hpath)

/-- Pinning the central box open is opening its sites. -/
theorem substitute_Q_eq_openSites (ω : SiteConfig (Site d)) :
    substitute (↑(Q d r t 0) : Set (Site d)) (fun x => x ∈ Q d r t 0) ω
      = openSites (↑(Q d r t 0) : Set (Site d)) ω := by
  ext i
  by_cases hi : i ∈ (↑(Q d r t 0) : Set (Site d))
  · rw [mem_substitute_of_mem _ hi]
    simp only [mem_openSites, Finset.mem_coe] at hi ⊢
    exact ⟨fun _ => Or.inr hi, fun _ => hi⟩
  · rw [mem_substitute_of_notMem _ hi, mem_openSites]
    exact ⟨fun h => Or.inl h, fun h => h.resolve_right hi⟩

/-- The number of macro-vertices of the arena bounds the number of undetermined ones. -/
theorem undetermined_start_le (n : ℕ) :
    (start d r t).undetermined (box 2 n) ≤ (box 2 n).card :=
  Finset.card_le_card Finset.sdiff_subset

/-- **The uniform lower bound.**  Under the one-step bound at density `a`, the far-arm event of
every radius has probability at least `q ^ |Q_0| · θ_2(a)`. -/
theorem le_real_far (hd : 2 ≤ d) (hr : 0 < r) (q a : unitInterval)
    (hs : StepBound d r t q a) (n : ℕ) :
    (q : ℝ) ^ (Q d r t 0).card * thetaSite 2 a
      ≤ (siteBernoulli (fun _ : Site d => q)).real (far d r t n) := by
  classical
  obtain ⟨δ, hδ0, hδa, hδhalf, hstart, hstep⟩ := hs
  set E := macroExp d r t n hd hr q δ with hE
  set m := (box 2 n).card with hm
  -- the domination at the start transcript
  have hdom := E.bern_le_prob_run (a := a)
    (fun h hg hT => hstep n h hg hT) m (start d r t) hstart (undetermined_start_le n)
  -- the Bernoulli value of the start is the pinned box connection probability
  have hbern : thetaSite 2 a ≤ (start d r t).bern a (zdGraph 2) (box 2 n) 0 (tgt n) := by
    refine (FRDom.thetaSite_le_pinnedProb_box n a).trans (le_of_eq ?_)
    unfold FRDom.Transcript.bern
    show pinnedProb (fun _ : Site 2 => a) {0} (fun _ => True) _
      = pinnedProb (fun _ : Site 2 => a) (↑({0} ∪ ∅ : Finset (Site 2))) (fun v => v ∈ ({0} : Finset (Site 2))) _
    rw [Finset.union_empty, Finset.coe_singleton]
    refine pinnedProb_congr_val _ _ (fun v hv => ?_) _
    rw [Set.mem_singleton_iff] at hv
    simp [hv]
  -- the pinned run probability, read as opening the central box
  have hrun : (start d r t).prob (fun _ : Site d => q) {ω | (E.run m (start d r t) ω).Reaches (zdGraph 2) 0 (tgt n)}
      ≤ (siteBernoulli (fun _ : Site d => q)).real
          (openSites (↑(Q d r t 0) : Set (Site d)) ⁻¹' far d r t n) := by
    rw [FRDom.Transcript.prob_eq, pinnedProb]
    refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
    simp only [Set.mem_preimage] at hω ⊢
    have hsub : substitute (↑(start d r t).inspected : Set (Site d)) (start d r t).state ω
        = openSites (↑(Q d r t 0) : Set (Site d)) ω := substitute_Q_eq_openSites ω
    rw [hsub] at hω
    refine far_of_run_reaches hd hr q δ hstart m ?_ hω
    intro x hx
    exact Or.inr hx
  have hins := prod_mul_real_preimage_openSites_le (fun _ : Site d => q) (Q d r t 0)
    (measurableSet_far d r t n)
  rw [Finset.prod_const] at hins
  have hq0 : (0 : ℝ) ≤ (q : ℝ) ^ (Q d r t 0).card := pow_nonneg q.2.1 _
  calc (q : ℝ) ^ (Q d r t 0).card * thetaSite 2 a
      ≤ (q : ℝ) ^ (Q d r t 0).card *
          (siteBernoulli (fun _ : Site d => q)).real
            (openSites (↑(Q d r t 0) : Set (Site d)) ⁻¹' far d r t n) :=
        mul_le_mul_of_nonneg_left (hbern.trans (hdom.trans hrun)) hq0
    _ ≤ (siteBernoulli (fun _ : Site d => q)).real (far d r t n) := hins

/-! ### From far arms of every radius to an infinite cluster of the slab -/

/-- A walk in the open site graph of `ω ∩ S` lifts to the induced graph on `S`. -/
theorem reachable_induce {V : Type*} (G : SimpleGraph V) (S : Set V) (ω : SiteConfig V) :
    ∀ {u v : V} (_ : (openSiteGraph G (ω ∩ S)).Walk u v) (hu : u ∈ S) (hv : v ∈ S),
      (openSiteGraph (G.comap (Subtype.val : S → V)) (restrictSite Subtype.val ω)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  intro u v p
  induction p with
  | nil => intro _ _; exact SimpleGraph.Reachable.refl _
  | @cons a c _ hac _ ih =>
    intro ha hv
    obtain ⟨hGac, haω, hcω⟩ := (openSiteGraph_adj_iff' G (ω ∩ S) a c).1 hac
    refine (SimpleGraph.Adj.reachable ?_).trans (ih hcω.2 hv)
    exact (openSiteGraph_adj_iff' (G.comap (Subtype.val : S → V)) _ ⟨a, ha⟩ ⟨c, hcω.2⟩).2
      ⟨SimpleGraph.comap_adj.2 hGac, haω.1, hcω.1⟩

/-- A confined connection puts its endpoint into the open cluster of the induced graph. -/
theorem mem_siteCluster_induce_of_connWithin {V : Type*} (G : SimpleGraph V) (S : Set V)
    {ω : SiteConfig V} {x y : V} (h : ω ∈ connWithin G S x y) (hx : x ∈ S) :
    ∃ hy : y ∈ S, (⟨y, hy⟩ : S) ∈
      siteCluster (G.comap (Subtype.val : S → V)) (restrictSite Subtype.val ω) ⟨x, hx⟩ := by
  have hy : y ∈ S := (mem_of_mem_siteCluster G (ω ∩ S) ⟨h.1, h.2⟩).2
  obtain ⟨p⟩ := h.2
  exact ⟨hy, h.1.1, reachable_induce G S ω p hx hy⟩

/-- **Far arms of every radius give an infinite cluster in the slab.** -/
theorem infinite_of_forall_far (hr : 0 < r) {ω : SiteConfig (Site d)}
    (hω : ∀ n, ω ∈ far d r t n) :
    (siteCluster ((zdGraph d).comap (Subtype.val : thin d t → Site d))
      (restrictSite Subtype.val ω) ⟨0, zero_mem_thin t⟩).Infinite := by
  set C := siteCluster ((zdGraph d).comap (Subtype.val : thin d t → Site d))
    (restrictSite Subtype.val ω) ⟨0, zero_mem_thin t⟩ with hC
  intro hfin
  -- the coordinates of the sites of the cluster are bounded
  have hT : (⋃ y ∈ C, Set.range fun j : Fin d => |(y : Site d) j|).Finite :=
    hfin.biUnion fun _ _ => Set.finite_range _
  obtain ⟨B, hB⟩ := hT.bddAbove
  set n : ℕ := B.toNat + 1 with hn
  obtain ⟨a, ⟨j, hj⟩, hconn⟩ := hω n
  have h0 : (emb 0 : Site d) = 0 := emb_zero
  rw [h0] at hconn
  obtain ⟨ha, hmem⟩ := mem_siteCluster_induce_of_connWithin (zdGraph d) (thin d t) hconn
    (zero_mem_thin t)
  have hle : |a j| ≤ B := hB (Set.mem_biUnion hmem ⟨j, rfl⟩)
  have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
  have hnB : (B : ℤ) < n := by
    rw [hn]; push_cast
    exact lt_of_le_of_lt (Int.self_le_toNat B) (by linarith)
  have hn1 : (1 : ℤ) ≤ n := by
    rw [hn]; push_cast
    linarith [(Nat.cast_nonneg B.toNat : (0 : ℤ) ≤ B.toNat)]
  have : 17 * (n : ℤ) ≤ 20 * (r : ℤ) * n - 3 * r := by nlinarith
  linarith

/-- **Percolation of the slab from a one-step bound.**  If every examination succeeds with pinned
probability at least `a`, with `θ_2(a) > 0`, then site percolation at `q` percolates in the slab
`thin d t`, from the origin. -/
theorem thetaSiteOn_thin_pos_of_stepBound (hd : 2 ≤ d) (hr : 0 < r) (q a : unitInterval)
    (hq : 0 < (q : ℝ)) (ha : 0 < thetaSite 2 a) (hs : StepBound d r t q a) :
    0 < thetaSiteOn ((zdGraph d).induce (thin d t)) ⟨0, zero_mem_thin t⟩ q := by
  set c : ℝ := (q : ℝ) ^ (Q d r t 0).card * thetaSite 2 a with hc
  have hcpos : 0 < c := mul_pos (pow_pos hq _) ha
  -- the induced graph as a pull-back
  have hG : (zdGraph d).induce (thin d t) = (zdGraph d).comap (Subtype.val : thin d t → Site d) := by
    ext a b; rfl
  rw [hG, thetaSiteOn_comap_eq (zdGraph d) Subtype.val_injective]
  -- continuity from above along the far-arm events
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := siteBernoulli (fun _ : Site d => q)) (s := far d r t)
    (fun n => (measurableSet_far d r t n).nullMeasurableSet) (far_antitone d r t) ⟨0, measure_ne_top _ _⟩
  have hlim' := (ENNReal.tendsto_toReal (measure_ne_top (siteBernoulli (fun _ : Site d => q))
    (⋂ n, far d r t n))).comp hlim
  have hge : c ≤ (siteBernoulli (fun _ : Site d => q)).real (⋂ n, far d r t n) :=
    ge_of_tendsto' hlim' fun n => le_real_far hd hr q a hs n
  refine lt_of_lt_of_le hcpos (hge.trans (measureReal_mono ?_ (measure_ne_top _ _)))
  intro ω hω
  rw [Set.mem_iInter] at hω
  exact infinite_of_forall_far hr hω

/-- **Percolation in the slab family of the endgame, from a one-step bound.**  For `d ≥ 3`,
`exists_slab_pos_of_thin` carries the percolation of `thin d t` to one of the slabs `slab d k`. -/
theorem exists_slab_pos_of_stepBound (hd : 3 ≤ d) (hr : 0 < r) (q a : unitInterval)
    (hq : 0 < (q : ℝ)) (ha : 0 < thetaSite 2 a) (hs : StepBound d r t q a) :
    ∃ k : ℕ, 0 < thetaSiteOn (slabGraph d k) (slabOrigin d k) q :=
  exists_slab_pos_of_thin d hd t q
    (thetaSiteOn_thin_pos_of_stepBound (by omega) hr q a hq ha hs)

/-! ### The slab of the certificate -/

/-- **The slab bridge with its width made explicit.**  This is `exists_slab_pos_of_thin` of
`KN/SiteSlabGeometry.lean` with the witness `k = 2 t` displayed; the proof is the same. -/
theorem slab_two_pos_of_thin (hd : 3 ≤ d) (t : ℕ) (p : unitInterval)
    (h : 0 < thetaSiteOn ((zdGraph d).induce (thin d t)) ⟨0, zero_mem_thin t⟩ p) :
    0 < thetaSiteOn (slabGraph d (2 * t)) (slabOrigin d (2 * t)) p := by
  classical
  obtain ⟨i, hi0, hi1⟩ : ∃ i : Fin d, i ≠ 0 ∧ i ≠ 1 := by
    refine ⟨⟨2, by omega⟩, ?_, ?_⟩
    · simp
    · refine Fin.ne_of_val_ne ?_
      rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < d by omega)]
      simp
  set Th : Set (Site d) := thin d t with hThdef
  have h0Th : (0 : Site d) ∈ Th := zero_mem_thin t
  set v : Site d := Pi.single i (t : ℤ) with hvdef
  set e : Fin d ≃ Fin d := Equiv.swap 0 i with hedef
  set S : Set (Site d) := {z : Site d | (shiftPermSite v e).symm z ∈ Th} with hSdef
  have hmem : ∀ x : Site d, x ∈ Th ↔ shiftPermSite v e x ∈ S := by
    intro x
    rw [hSdef]
    show x ∈ Th ↔ (shiftPermSite v e).symm (shiftPermSite v e x) ∈ Th
    rw [Equiv.symm_apply_apply]
  have he0 : e 0 = i := by rw [hedef]; exact Equiv.swap_apply_left 0 i
  have hei0 : e i = 0 := by rw [hedef]; exact Equiv.swap_apply_right 0 i
  have hei : ∀ j : Fin d, e j = i ↔ j = 0 := by
    intro j
    refine ⟨fun hj => ?_, fun hj => by rw [hj]; exact he0⟩
    have hswap : e (e j) = 0 := by rw [hj]; exact hei0
    rw [hedef, Equiv.swap_apply_self] at hswap
    exact hswap
  have hΦ0 : shiftPermSite v e (0 : Site d) = Pi.single (0 : Fin d) (t : ℤ) := by
    funext j
    show ((0 : Site d) + v) (e j) = (Pi.single (0 : Fin d) (t : ℤ) : Site d) j
    rw [zero_add, hvdef]
    simp only [Pi.single_apply]
    by_cases hj : j = 0
    · rw [if_pos ((hei j).2 hj), if_pos hj]
    · rw [if_neg fun hc => hj ((hei j).1 hc), if_neg hj]
  have hSslab : S ⊆ slab d (2 * t) := by
    intro z hz
    have hx : (shiftPermSite v e).symm z ∈ Th := hz
    have habs : |(shiftPermSite v e).symm z i| ≤ (t : ℤ) := hx i hi0 hi1
    have hz0 : z 0 = (shiftPermSite v e).symm z i + (t : ℤ) := by
      conv_lhs => rw [← (shiftPermSite v e).apply_symm_apply z]
      show ((shiftPermSite v e).symm z + v) (e 0) = (shiftPermSite v e).symm z i + (t : ℤ)
      rw [he0]
      show (shiftPermSite v e).symm z i + v i = (shiftPermSite v e).symm z i + (t : ℤ)
      rw [hvdef]
      simp
    rw [abs_le] at habs
    simp only [slab, Set.mem_setOf_eq]
    constructor
    · rw [hz0]; linarith [habs.1]
    · rw [hz0]; push_cast; linarith [habs.2]
  have hsingleS : (Pi.single (0 : Fin d) (t : ℤ) : Site d) ∈ S := by
    rw [← hΦ0]
    exact (hmem 0).1 h0Th
  have hiso := thetaSiteOn_iso (induceShiftPermIso v e hmem) ⟨(0 : Site d), h0Th⟩ p
  have hroot : (induceShiftPermIso v e hmem ⟨(0 : Site d), h0Th⟩) =
      (⟨Pi.single (0 : Fin d) (t : ℤ), hsingleS⟩ : S) := Subtype.ext hΦ0
  rw [hroot] at hiso
  have hposS : 0 < thetaSiteOn ((zdGraph d).induce S)
      ⟨Pi.single (0 : Fin d) (t : ℤ), hsingleS⟩ p := by
    rw [hiso]
    exact h
  have hmono := thetaSiteOn_induce_mono (zdGraph d) hSslab
    (Pi.single (0 : Fin d) (t : ℤ)) hsingleS p
  refine thetaSiteOn_slabOrigin_pos_of_axis d p t (by omega) ?_
  exact lt_of_lt_of_le hposS hmono

/-- Percolation in a slab persists in every wider slab. -/
theorem thetaSiteOn_slab_mono {k k' : ℕ} (hk : k ≤ k') (p : unitInterval) :
    thetaSiteOn (slabGraph d k) (slabOrigin d k) p ≤ thetaSiteOn (slabGraph d k') (slabOrigin d k') p := by
  have hsub : slab d k ⊆ slab d k' := fun x hx => ⟨hx.1, hx.2.trans (by exact_mod_cast hk)⟩
  exact thetaSiteOn_induce_mono (zdGraph d) hsub (0 : Site d) (zero_mem_slab d k) p

/-- **The soundness of the certificate, conditionally on the one-step bound.**  If for every
well-formed certificate valid at `q` there are a spacing `r`, a transverse half-width `t` with
`2 t ≤ width`, and a planar density `a` with `θ_2(a) > 0` at which the one-step bound holds, then
`CertificateSound d` holds for `d ≥ 3`.  The positivity of `q` is supplied by
`Certificate.not_validAt_of_coe_eq_zero`. -/
theorem certificateSound_of_stepBound (hd : 3 ≤ d)
    (hs : ∀ (C : LeftImp.Certificate d) (q : unitInterval), C.WellFormed → C.ValidAt q →
      ∃ (r t : ℕ) (a : unitInterval), 0 < r ∧ 2 * t ≤ C.width ∧ 0 < thetaSite 2 a ∧
        StepBound d r t q a) :
    LeftImp.CertificateSound d := by
  intro C q hwf hv
  obtain ⟨r, t, a, hr, ht, ha, hstep⟩ := hs C q hwf hv
  have hq : 0 < (q : ℝ) := by
    rcases lt_or_eq_of_le q.2.1 with hq | hq
    · exact hq
    · exact absurd hv (C.not_validAt_of_coe_eq_zero hwf hq.symm)
  have hthin := thetaSiteOn_thin_pos_of_stepBound (r := r) (t := t) (by omega) hr q a hq ha hstep
  exact lt_of_lt_of_le (slab_two_pos_of_thin hd t q hthin) (thetaSiteOn_slab_mono ht q)

end Conclusion

/-! ## The incoming reservation

The old deterministic stub theorems are intentionally absent.  At a good nonterminal transcript,
the occupied predecessor instead supplies the pinned near-one event for the edge that is about to
be examined. -/

section IncomingReservation

variable {d : ℕ} [NeZero d] {r t n : ℕ} {q : unitInterval} {δ : ℝ}

/-- The edge selected for the next examination already carries the probabilistic invariant. -/
theorem incoming_reservation {h : Tr d} (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    reservationBound d r t q δ h (pendW d n h) (pendZ d n h) := by
  obtain ⟨hw, hadj⟩ := pendW_spec d r t n hg hT
  obtain ⟨-, hzo, hzc, -⟩ :=
    pendZ_mem d n (boundary_nonempty_of_not_terminal d n hT)
  apply hg.reserve (pendW d n h) hw (pendZ d n h)
  rw [mem_pending]
  exact ⟨mem_nbrs_of_adj hadj, by simp [hzo, hzc]⟩

/-- The protected event is exactly the incoming connection event after replacing the edge by its
fresh part.  Thus the incoming half of `succ` realizes the reservation rather than paying for a
designated source site. -/
theorem incoming_reservation_region {h : Tr d}
    (hg : Good d r t h q δ)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    1 - δ < h.prob (fun _ : Site d => q)
      (connWithinSet (zdGraph d) (↑(h.inspected ∪ region d r t n h) : Set (Site d))
        (emb 0) (↑(M d r t (pendZ d n h)) : Set (Site d))) := by
  have hbound := incoming_reservation hg hT
  unfold reservationBound reservationEvent at hbound
  have hset : h.inspected ∪ region d r t n h =
      h.inspected ∪ E d r t (pendW d n h) (pendZ d n h) := by
    ext x
    simp [region]
  rwa [hset]

end IncomingReservation

/-! ## Non-vacuity of the geometry, at `d = 3`, `r = 1`, `t = 1` -/

section NonVacuity

/-- The origin of `ℤ³` lies in the edge region leading from the macro-vertex `e₀` to the origin:
it is inside the box spanned by the two central boxes and outside the central box of `e₀`. -/
example : (0 : Site 3) ∈ E 3 1 1 (Pi.single 0 1) 0 := by
  rw [E, Finset.mem_sdiff, mem_hbox, Q, mem_abox]
  refine ⟨fun j => ?_, fun h => ?_⟩
  · fin_cases j <;> simp [ctr, emb, rad]
  · have := h ⟨0, by norm_num⟩
    simp [ctr, emb, rad] at this

/-- The centre of the macro-vertex `e₀` at spacing `20` is `(20, 0, 0)`. -/
example : (ctr 3 1 (Pi.single 0 1) : Site 3) = Pi.single 0 20 := by
  funext j
  fin_cases j <;> simp [ctr, emb]

/-- The origin belongs to the central box of the origin, which is read at the start. -/
example : (emb 0 : Site 3) ∈ Q 3 1 1 0 := M_subset_Q 1 1 0 (emb_zero_mem_M 1 1)

/-- The target box of a macro-vertex lies in the edge region leading to it, at these scales. -/
example : M 3 1 1 (Pi.single 0 1) ⊆ E 3 1 1 0 (Pi.single 0 1) :=
  M_subset_E (by norm_num) 1 1 Nat.one_pos (by
    intro h
    have := congrFun h 0
    simp at this)

/-- The corrected invariant itself is nonempty; a tolerance above one makes its probability clause
automatic.  The useful small tolerance is supplied by `StepBound`. -/
example : Good 3 1 1 (start 3 1 1) (1 : unitInterval) 2 :=
  start_good 3 1 1 (by norm_num) 1 (by norm_num)

/-! ### The recorded state at the stub tip

`Good` fixes the occupied macro-vertices, the location of the inspected set, a recorded path from
the origin into each occupied target box, the pending reservations and the cover.  It says nothing
about the recorded state at `src`, the stub tip of the pending edge, because the corrected
exploration asks for no connection out of that tip: such a request costs a factor `q`.  The three
modules `KN/EntranceBound.lean`, `KN/PinnedEntrance.lean` and `KN/LongBoxHit.lean` still need that
tip recorded open and take it as an explicit hypothesis.  The two theorems here exhibit a
transcript at which that hypothesis, `Good`, and non-terminality all hold at once, so the
hypothesis is satisfiable and the theorems above it are not vacuous.
-/

/-- The radius-one exploration has not terminated at the start transcript: the origin is not on the
inner boundary of `box 2 1`, and the macro-neighbour `e₀` of the origin is an undetermined frontier
vertex. -/
theorem start_notTerminal_one (d : ℕ) [NeZero d] (r t : ℕ) :
    ¬ (start d r t).Terminal (zdGraph 2) (box 2 1) 0 (tgt 1) := by
  intro hT
  rcases hT with hR | hB
  · obtain ⟨z, hzt, hzex⟩ := hR
    have hzV : z ∈ (start d r t).openV :=
      Finset.mem_coe.1 (mem_of_mem_siteCluster _ _ hzex)
    have hz0 : z = 0 := by simpa [start] using hzV
    subst z
    obtain ⟨i, hi⟩ := exists_coord_of_mem_innerBoundary (Finset.mem_coe.1 hzt)
    simp at hi
  · let e : Site 2 := Pi.single 0 1
    have heA : e ∈ box 2 1 := by
      rw [mem_box]
      intro j
      fin_cases j <;> simp [e]
    have he0 : e ≠ 0 := by
      intro he
      have hc := congrFun he (0 : Fin 2)
      simp [e] at hc
    have heOpen : e ∉ (start d r t).openV := by
      simpa [start] using he0
    have heClosed : e ∉ (start d r t).closedV := by
      simp [start]
    have h0exp : (0 : Site 2) ∈ (start d r t).explored (zdGraph 2) 0 :=
      mem_siteCluster_self _ _ (by simp [start])
    have hadj : (zdGraph 2).Adj (0 : Site 2) e := by
      rw [zdGraph_adj_iff]
      exact ⟨0, Or.inl (by simp [e])⟩
    have heb : e ∈ (start d r t).boundary (zdGraph 2) (box 2 1) 0 :=
      ⟨heA, heOpen, heClosed, Or.inr ⟨0, h0exp, hadj⟩⟩
    rw [hB] at heb
    exact heb

/-- **The stub tip is recorded open at the start transcript.**  `start` reads the whole central box
of the origin and records all of it open, and `tip_mem_Q` places the tip of every pending edge of
the origin in that box.  Nothing here is assumed: the transcript is the one `start_good` certifies
good. -/
theorem src_mem_openSites_start (d : ℕ) [NeZero d] (r t n : ℕ) (hd : 2 ≤ d)
    (hT : ¬ (start d r t).Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    src d r n (start d r t) ∈ (start d r t).openSites := by
  have hg : Good d r t (start d r t) 1 2 := start_good d r t hd 1 (by norm_num)
  obtain ⟨hW, hadj⟩ := pendW_spec d r t n hg hT
  have hW0 : pendW d n (start d r t) = 0 := by
    have hW' : pendW d n (start d r t) ∈ ({0} : Finset (Site 2)) := hW
    simpa using hW'
  show tip d r (pendW d n (start d r t)) (pendZ d n (start d r t)) ∈ Q d r t 0
  rw [hW0] at hadj ⊢
  exact tip_mem_Q r t (mem_nbrs_of_adj hadj)

/-- The three conditions that the entrance modules impose on a transcript hold together at radius
one: the start transcript is good, is not terminal, and records its pending stub tip open. -/
theorem good_notTerminal_src_open_start (d : ℕ) [NeZero d] (r t : ℕ) (hd : 2 ≤ d) :
    Good d r t (start d r t) ∧
      ¬ (start d r t).Terminal (zdGraph 2) (box 2 1) 0 (tgt 1) ∧
      src d r 1 (start d r t) ∈ (start d r t).openSites :=
  ⟨start_good d r t hd 1 (by norm_num), start_notTerminal_one d r t,
    src_mem_openSites_start d r t 1 hd (start_notTerminal_one d r t)⟩

/-- The far-arm bound at radius `n = 2`: planar distance at least `37`. -/
example : (20 : ℤ) * 1 * 2 - 3 * 1 = 37 := by norm_num

end NonVacuity

end KNAll.Site.MacroExp

end

/-! ## Co-import check

All the modules named in the brief imported together, with all the relevant namespaces opened at
once; the names below are the ones consumed. -/

noncomputable section CoImportCheck

open KNAll.Site KNAll.Site.MacroExp KNAll.Site.FRDom KNAll.Site.TargetExt KNAll.Site.LeftImp
open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

-- the finite-radius domination consumed
example (d : ℕ) [NeZero d] (r t n : ℕ) (hd : 2 ≤ d) (hr : 0 < r)
    (q : unitInterval) (δ : ℝ) :
    FRDom.Exploration (Site d) (zdGraph 2) (box 2 n) (0 : Site 2) (MacroExp.tgt n) :=
  macroExp d r t n hd hr q δ

-- the target extension available for the one-step bound
#check @KNAll.Site.TargetExt.targetExtension_eps

-- the certificate whose soundness is the target
example (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (hs : ∀ (C : Certificate d) (q : unitInterval), C.WellFormed → C.ValidAt q →
      ∃ (r t : ℕ) (a : unitInterval), 0 < r ∧ 2 * t ≤ C.width ∧ 0 < thetaSite 2 a ∧
        StepBound d r t q a) :
    CertificateSound d :=
  certificateSound_of_stepBound hd hs

#print axioms KNAll.Site.MacroExp.macroExp
#print axioms KNAll.Site.MacroExp.start_good
#print axioms KNAll.Site.MacroExp.exists_far_of_reaches
#print axioms KNAll.Site.MacroExp.le_real_far
#print axioms KNAll.Site.MacroExp.thetaSiteOn_thin_pos_of_stepBound
#print axioms KNAll.Site.MacroExp.exists_slab_pos_of_stepBound
#print axioms KNAll.Site.MacroExp.slab_two_pos_of_thin
#print axioms KNAll.Site.MacroExp.certificateSound_of_stepBound
#print axioms KNAll.Site.MacroExp.incoming_reservation
#print axioms KNAll.Site.MacroExp.incoming_reservation_region
#print axioms KNAll.Site.MacroExp.tip_mem_Q
#print axioms KNAll.Site.MacroExp.start_notTerminal_one
#print axioms KNAll.Site.MacroExp.src_mem_openSites_start
#print axioms KNAll.Site.MacroExp.good_notTerminal_src_open_start
#print axioms KNAll.Site.MacroExp.tipOut_mem_E
#print axioms KNAll.Site.MacroExp.connWithin_abox
#print axioms KNAll.Site.MacroExp.le_of_mem_E_out
#print axioms KNAll.Site.MacroExp.emb_injective
#print axioms KNAll.Site.MacroExp.step_good

end CoImportCheck
