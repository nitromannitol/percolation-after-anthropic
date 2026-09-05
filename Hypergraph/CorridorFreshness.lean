import Hypergraph.CorridorGeometry

/-!
# Freshness of deterministic lattice corridors

The edge region `E d r t w z` is oriented: it is the box spanned by the central boxes at
`w` and `z`, with the tail box `Q d r t w` removed.  This file records the exact deterministic
separation consequences of that convention.

For adjacent planar macro-vertices and positive spacing, two oriented edge regions can meet only
in either of the following cases:

* they have the same head (both regions contain the central box of that head), or
* they are the two opposite orientations of the same unoriented edge (they meet in the bridge
  between the two endpoint boxes).

In particular, merely asking for distinct ordered pairs and distinct heads is not enough: reversed
edges are the exceptional case.  The final results turn the `Good.cover` field into freshness of
the entire pending corridor, not only freshness of the set-difference called `region`.
-/

noncomputable section

namespace KNAll.Site.Corridor

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.MacroExp

/-! ## One-dimensional separation at macro scale -/

/-- At spacing `20 r`, closed intervals of radius `5 r` around distinct integral macro-cells do
not touch. -/
private theorem macroCell_le {r a b : ℤ} (hr : 0 < r)
    (h : 20 * r * a - 5 * r ≤ 20 * r * b + 5 * r) : a ≤ b := by
  by_contra h'
  push Not at h'
  have hgap : b + 1 ≤ a := h'
  have hscale := mul_le_mul_of_nonneg_left hgap (show (0 : ℤ) ≤ 20 * r by positivity)
  nlinarith

/-- A strict comparison of the inner faces of two macro-cells detects the strict comparison of
their integral indices. -/
private theorem macroCell_lt {r a b : ℤ} (hr : 0 < r)
    (h : 20 * r * a - 5 * r < 20 * r * b - 5 * r) : a < b := by
  by_contra h'
  push Not at h'
  have hscale := mul_le_mul_of_nonneg_left h' (show (0 : ℤ) ≤ 20 * r by positivity)
  nlinarith

/-- The one-dimensional cell calculation used below.  The point `X` lies in the thickened unit
segment from `w` to `z`, outside the radius-`5r` cell at `w`, and also in the thickened segment
from `a` to `b`; therefore `z` is between `a` and `b`. -/
private theorem head_between {r : ℤ} (hr : 0 < r) {w z a b X : ℤ}
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
    exact ⟨macroCell_le hr (h3.trans h2), macroCell_le hr (h1.trans h4)⟩
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
    · refine ⟨macroCell_le hr (h3.trans h2), ?_⟩
      have : w < max a b := macroCell_lt hr (by linarith)
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
    · refine ⟨?_, macroCell_le hr (h1.trans h4)⟩
      have : min a b < w := macroCell_lt hr (by linarith)
      omega
    · linarith

/-! ## Planar coordinates and the head-cell lemma -/

variable {d : ℕ}

/-- Embed a planar coordinate into `Fin d`, given `d ≥ 2`. -/
private def planarCoord (hd : 2 ≤ d) (i : Fin 2) : Fin d :=
  ⟨i.val, lt_of_lt_of_le i.isLt hd⟩

private theorem planarCoord_val_lt (hd : 2 ≤ d) (i : Fin 2) :
    (planarCoord hd i).val < 2 := i.isLt

private theorem ctr_planarCoord (hd : 2 ≤ d) (r : ℕ) (z : Site 2) (i : Fin 2) :
    ctr d r z (planarCoord hd i) = 20 * (r : ℤ) * z i := by
  rw [ctr_apply_of_lt r z (planarCoord_val_lt hd i)]
  rfl

private theorem rad_planarCoord (hd : 2 ≤ d) (R t : ℕ) (i : Fin 2) :
    rad R t (planarCoord hd i) = R := by
  unfold rad
  rw [if_pos (planarCoord_val_lt hd i)]

private theorem hbox_planar_bounds (hd : 2 ≤ d) (r t : ℕ) (a b : Site 2) {x : Site d}
    (hx : x ∈ hbox (ctr d r a) (ctr d r b) (5 * r) t) (i : Fin 2) :
    min (20 * (r : ℤ) * a i) (20 * (r : ℤ) * b i) - 5 * r ≤ x (planarCoord hd i) ∧
      x (planarCoord hd i) ≤
        max (20 * (r : ℤ) * a i) (20 * (r : ℤ) * b i) + 5 * r := by
  have h := (mem_hbox.1 hx) (planarCoord hd i)
  rw [ctr_planarCoord hd r a i, ctr_planarCoord hd r b i,
    rad_planarCoord hd (5 * r) t i] at h
  push_cast at h
  exact h

/-- Membership in an oriented edge region leaves the tail box in a planar coordinate. -/
private theorem exists_planar_outside_tail (hd : 2 ≤ d) (r t : ℕ)
    {w z : Site 2} {x : Site d} (hx : x ∈ E d r t w z) :
    ∃ i : Fin 2, x (planarCoord hd i) < 20 * (r : ℤ) * w i - 5 * r ∨
      20 * (r : ℤ) * w i + 5 * r < x (planarCoord hd i) := by
  rw [E, Finset.mem_sdiff] at hx
  obtain ⟨hxh, hxQ⟩ := hx
  rw [Q, mem_abox] at hxQ
  push Not at hxQ
  obtain ⟨j, hj⟩ := hxQ
  by_cases hjlt : j.val < 2
  · refine ⟨⟨j.val, hjlt⟩, ?_⟩
    have hpl : planarCoord hd ⟨j.val, hjlt⟩ = j := Fin.ext rfl
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

/-- Adjacent macro-vertices differ by at most one in each coordinate. -/
private theorem adjacent_coord {w z : Site 2} (h : (zdGraph 2).Adj w z) (i : Fin 2) :
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

/-- **Head-cell lemma.**  If a point of the oriented region `w → z` also lies in the box
spanned by the adjacent macro-vertices `a,b`, then the head `z` lies in the coordinate hull of
`a,b`. -/
theorem head_mem_hull_of_mem_E_of_mem_hbox (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z a b : Site 2} (hwz : (zdGraph 2).Adj w z) {x : Site d}
    (hx : x ∈ E d r t w z)
    (hab : x ∈ hbox (ctr d r a) (ctr d r b) (5 * r) t) (i : Fin 2) :
    min (a i) (b i) ≤ z i ∧ z i ≤ max (a i) (b i) := by
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  have hxh : x ∈ hbox (ctr d r w) (ctr d r z) (5 * r) t :=
    (Finset.mem_sdiff.1 hx).1
  obtain ⟨i₀, hi₀⟩ := exists_planar_outside_tail hd r t hx
  have h1 := hbox_planar_bounds hd r t w z hxh i
  have h2 := hbox_planar_bounds hd r t a b hab i
  by_cases hii : i = i₀
  · subst hii
    exact head_between hr' (adjacent_coord hwz i) h1.1 h1.2 h2.1 h2.2 (Or.inr hi₀)
  · have hwi : z i = w i := by
      obtain ⟨k, hk | hk⟩ := (zdGraph_adj_iff w z).1 hwz
      · have hik : i ≠ k := by
          intro hik
          subst hik
          have h0 := hbox_planar_bounds hd r t w z hxh i₀
          have hz0 : z i₀ = w i₀ := by rw [hk]; simp [Ne.symm hii]
          rw [hz0, min_self, max_self] at h0
          omega
        rw [hk]
        simp [hik]
      · have hik : i ≠ k := by
          intro hik
          subst hik
          have h0 := hbox_planar_bounds hd r t w z hxh i₀
          have hz0 : z i₀ = w i₀ := by rw [hk]; simp [Ne.symm hii]
          rw [hz0, min_self, max_self] at h0
          omega
        rw [hk]
        simp [hik]
    exact head_between hr' (Or.inl hwi) h1.1 h1.2 h2.1 h2.2 (Or.inl hwi)

/-- An integral point in the coordinate hull of a nearest-neighbour macro-edge is one of its two
endpoints. -/
theorem eq_endpoint_of_mem_adjacent_hull {a b z : Site 2} (hab : (zdGraph 2).Adj a b)
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

/-- A central box is the degenerate two-centre hull box. -/
theorem Q_eq_hbox_self (r t : ℕ) (z : Site 2) :
    Q d r t z = hbox (ctr d r z) (ctr d r z) (5 * r) t := by
  ext x
  rw [Q, mem_abox, mem_hbox]
  simp only [min_self, max_self]

/-! ## Exact separation from central boxes -/

variable [NeZero d]

/-- An oriented edge region is disjoint from every central box except the box at its head. -/
theorem E_disjoint_Q_of_ne_head (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z z' : Site 2} (hwz : (zdGraph 2).Adj w z) (hz' : z' ≠ z) :
    Disjoint (E d r t w z) (Q d r t z') := by
  rw [Finset.disjoint_left]
  intro x hxE hxQ
  rw [Q_eq_hbox_self] at hxQ
  have hz : z = z' := by
    funext i
    have hi := head_mem_hull_of_mem_E_of_mem_hbox hd r t hr hwz hxE hxQ i
    simp only [min_self, max_self] at hi
    omega
  exact hz' hz.symm

/-- The tail-box case is definitional and needs no adjacency or scale assumption. -/
theorem E_disjoint_Q_tail (d r t : ℕ) (w z : Site 2) :
    Disjoint (E d r t w z) (Q d r t w) := by
  simpa only [E] using
    (Finset.sdiff_disjoint :
      Disjoint (hbox (ctr d r w) (ctr d r z) (5 * r) t \ Q d r t w) (Q d r t w))

/-- The preceding statement is exact: the head box is contained in the edge region. -/
theorem E_disjoint_Q_iff (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z z' : Site 2} (hwz : (zdGraph 2).Adj w z) :
    Disjoint (E d r t w z) (Q d r t z') ↔ z' ≠ z := by
  constructor
  · intro hdis hzz'
    subst z'
    have hcQ : ctr d r z ∈ Q d r t z :=
      M_subset_Q r t z (ctr_mem_M r t z)
    have hcE : ctr d r z ∈ E d r t w z :=
      Q_subset_E hd r t hr hwz.ne hcQ
    exact Finset.disjoint_left.1 hdis hcE hcQ
  · exact E_disjoint_Q_of_ne_head hd r t hr hwz

/-! ## Classification of intersections of oriented edges -/

/-- A common site forces the head of the first oriented edge to be an endpoint of the second. -/
theorem head_eq_endpoint_of_mem_E_inter_E (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z w' z' : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hwz' : (zdGraph 2).Adj w' z') {x : Site d}
    (hx : x ∈ E d r t w z) (hx' : x ∈ E d r t w' z') : z = w' ∨ z = z' := by
  have hxH : x ∈ hbox (ctr d r w') (ctr d r z') (5 * r) t :=
    (Finset.mem_sdiff.1 hx').1
  exact eq_endpoint_of_mem_adjacent_hull hwz'
    (head_mem_hull_of_mem_E_of_mem_hbox hd r t hr hwz hx hxH)

/-- Thus two oriented nearest-neighbour corridors can intersect only when their heads agree or
when the ordered pairs are reversals of one another. -/
theorem pair_classification_of_mem_E_inter_E (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z w' z' : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hwz' : (zdGraph 2).Adj w' z') {x : Site d}
    (hx : x ∈ E d r t w z) (hx' : x ∈ E d r t w' z') :
    z = z' ∨ (w = z' ∧ z = w') := by
  rcases head_eq_endpoint_of_mem_E_inter_E hd r t hr hwz hwz' hx hx' with hzw' | hzz'
  · have hz'w : z' = w ∨ z' = z :=
      head_eq_endpoint_of_mem_E_inter_E hd r t hr hwz' hwz hx' hx
    rcases hz'w with hz'w | hz'z
    · exact Or.inr ⟨hz'w.symm, hzw'⟩
    · exact Or.inl hz'z.symm
  · exact Or.inl hzz'

/-- A convenient sufficient form: the first head is not either endpoint of the second edge. -/
theorem E_disjoint_E_of_head_ne_endpoints (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z w' z' : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hwz' : (zdGraph 2).Adj w' z') (hzw' : z ≠ w') (hzz' : z ≠ z') :
    Disjoint (E d r t w z) (E d r t w' z') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rcases head_eq_endpoint_of_mem_E_inter_E hd r t hr hwz hwz' hx hx' with h | h
  · exact hzw' h
  · exact hzz' h

/-- The formulation closest to the edge-pair question: distinct heads suffice after excluding the
reversed ordered pair. -/
theorem E_disjoint_E_of_heads_ne_of_not_reverse (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z w' z' : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hwz' : (zdGraph 2).Adj w' z') (hheads : z ≠ z')
    (hrev : ¬ (w = z' ∧ z = w')) : Disjoint (E d r t w z) (E d r t w' z') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rcases pair_classification_of_mem_E_inter_E hd r t hr hwz hwz' hx hx' with h | h
  · exact hheads h
  · exact hrev h

/-! ## The reversed-edge bridge really is nonempty -/

/-- The integral midpoint of two macro-centres.  The factor `10 r` makes division by two
unnecessary. -/
def edgeMidpoint (d r : ℕ) (w z : Site 2) : Site d :=
  fun j => 10 * (r : ℤ) * (emb w j + emb z j)

@[simp] theorem edgeMidpoint_comm (d r : ℕ) (w z : Site 2) :
    edgeMidpoint d r w z = edgeMidpoint d r z w := by
  funext j
  simp only [edgeMidpoint]
  ring

/-- The midpoint lies in the (unoriented) hull box. -/
theorem edgeMidpoint_mem_hbox (r t : ℕ) (w z : Site 2) :
    edgeMidpoint d r w z ∈ hbox (ctr d r w) (ctr d r z) (5 * r) t := by
  rw [mem_hbox]
  intro j
  by_cases hj : j.val < 2
  · rw [ctr_apply_of_lt r w hj, ctr_apply_of_lt r z hj]
    unfold rad
    rw [if_pos hj]
    simp only [edgeMidpoint, emb_apply_of_lt _ hj]
    push_cast
    have hr0 : (0 : ℤ) ≤ r := by positivity
    rcases le_total (w ⟨j.val, hj⟩) (z ⟨j.val, hj⟩) with hwz | hzw
    · rw [min_eq_left (mul_le_mul_of_nonneg_left hwz (by positivity)),
        max_eq_right (mul_le_mul_of_nonneg_left hwz (by positivity))]
      constructor <;> nlinarith
    · rw [min_eq_right (mul_le_mul_of_nonneg_left hzw (by positivity)),
        max_eq_left (mul_le_mul_of_nonneg_left hzw (by positivity))]
      constructor <;> nlinarith
  · rw [ctr_apply_of_not_lt r w hj, ctr_apply_of_not_lt r z hj]
    unfold rad
    rw [if_neg hj]
    simp [edgeMidpoint, emb_apply_of_not_lt _ hj]

private theorem edgeMidpoint_planar (hd : 2 ≤ d) (r : ℕ) (w z : Site 2) (i : Fin 2) :
    edgeMidpoint d r w z (planarCoord hd i) = 10 * (r : ℤ) * (w i + z i) := by
  have hi :
      (⟨(planarCoord hd i).val, planarCoord_val_lt hd i⟩ : Fin 2) = i := Fin.ext rfl
  unfold edgeMidpoint
  rw [emb_apply_of_lt w (planarCoord_val_lt hd i),
    emb_apply_of_lt z (planarCoord_val_lt hd i), hi]

/-- For a genuine macro-edge, its midpoint is outside the central box at the first endpoint. -/
theorem edgeMidpoint_not_mem_Q_left (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z : Site 2} (hwz : (zdGraph 2).Adj w z) : edgeMidpoint d r w z ∉ Q d r t w := by
  intro hQ
  rw [Q, mem_abox] at hQ
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff w z).1 hwz
  · have h := hQ (planarCoord hd i)
    rw [ctr_planarCoord hd r w i, rad_planarCoord hd (5 * r) t i] at h
    have hm : edgeMidpoint d r w z (planarCoord hd i) =
        20 * (r : ℤ) * w i + 10 * r := by
      rw [edgeMidpoint_planar hd r w z i, hi]
      simp only [Pi.add_apply, Pi.single_apply]
      push_cast
      ring
    rw [hm] at h
    push_cast at h
    have hr' : (0 : ℤ) < r := by exact_mod_cast hr
    nlinarith
  · have h := hQ (planarCoord hd i)
    rw [ctr_planarCoord hd r w i, rad_planarCoord hd (5 * r) t i] at h
    have hm : edgeMidpoint d r w z (planarCoord hd i) =
        20 * (r : ℤ) * z i + 10 * r := by
      rw [edgeMidpoint_planar hd r w z i, hi]
      simp only [Pi.add_apply, Pi.single_apply]
      push_cast
      ring
    rw [hm, hi] at h
    simp only [Pi.add_apply, Pi.single_apply] at h
    push_cast at h
    have hr' : (0 : ℤ) < r := by exact_mod_cast hr
    nlinarith

/-- The same midpoint is outside the central box at the second endpoint. -/
theorem edgeMidpoint_not_mem_Q_right (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z : Site 2} (hwz : (zdGraph 2).Adj w z) : edgeMidpoint d r w z ∉ Q d r t z := by
  rw [edgeMidpoint_comm]
  exact edgeMidpoint_not_mem_Q_left hd r t hr hwz.symm

/-- Hence opposite orientations of a macro-edge share the midpoint of the bridge. -/
theorem edgeMidpoint_mem_E_and_reverse (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z : Site 2} (hwz : (zdGraph 2).Adj w z) :
    edgeMidpoint d r w z ∈ E d r t w z ∧ edgeMidpoint d r w z ∈ E d r t z w := by
  constructor
  · rw [E, Finset.mem_sdiff]
    exact ⟨edgeMidpoint_mem_hbox r t w z, edgeMidpoint_not_mem_Q_left hd r t hr hwz⟩
  · rw [E, Finset.mem_sdiff]
    constructor
    · have hH := edgeMidpoint_mem_hbox (d := d) r t z w
      rw [edgeMidpoint_comm d r z w] at hH
      exact hH
    · exact edgeMidpoint_not_mem_Q_right hd r t hr hwz

/-- Two adjacent corridors with a common head genuinely overlap: they both contain that head's
central box. -/
theorem not_disjoint_E_E_of_same_head (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w w' z : Site 2} (hwz : (zdGraph 2).Adj w z) (hwz' : (zdGraph 2).Adj w' z) :
    ¬ Disjoint (E d r t w z) (E d r t w' z) := by
  intro hdis
  have hcQ : ctr d r z ∈ Q d r t z := M_subset_Q r t z (ctr_mem_M r t z)
  have hcE : ctr d r z ∈ E d r t w z := Q_subset_E hd r t hr hwz.ne hcQ
  have hcE' : ctr d r z ∈ E d r t w' z := Q_subset_E hd r t hr hwz'.ne hcQ
  exact Finset.disjoint_left.1 hdis hcE hcE'

/-- Opposite orientations genuinely overlap in the bridge. -/
theorem not_disjoint_E_E_reverse (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z : Site 2} (hwz : (zdGraph 2).Adj w z) :
    ¬ Disjoint (E d r t w z) (E d r t z w) := by
  intro hdis
  obtain ⟨h1, h2⟩ := edgeMidpoint_mem_E_and_reverse hd r t hr hwz
  exact Finset.disjoint_left.1 hdis h1 h2

/-- **Exact edge-intersection classification.**  For oriented nearest-neighbour edges at positive
scale, disjointness is equivalent to having different heads and not being reversals. -/
theorem E_disjoint_E_iff (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z w' z' : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hwz' : (zdGraph 2).Adj w' z') :
    Disjoint (E d r t w z) (E d r t w' z') ↔
      z ≠ z' ∧ ¬ (w = z' ∧ z = w') := by
  constructor
  · intro hdis
    constructor
    · intro hheads
      subst z'
      exact not_disjoint_E_E_of_same_head hd r t hr hwz hwz' hdis
    · rintro ⟨hwz', hzw'⟩
      subst w'
      subst z'
      exact not_disjoint_E_E_reverse hd r t hr hwz hdis
  · rintro ⟨hheads, hrev⟩
    exact E_disjoint_E_of_heads_ne_of_not_reverse hd r t hr hwz hwz' hheads hrev

/-- Equivalently, the complete list of overlapping ordered edge pairs is: equal heads, or opposite
orientations of one unoriented edge. -/
theorem E_overlap_iff (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {w z w' z' : Site 2} (hwz : (zdGraph 2).Adj w z)
    (hwz' : (zdGraph 2).Adj w' z') :
    ¬ Disjoint (E d r t w z) (E d r t w' z') ↔
      z = z' ∨ (w = z' ∧ z = w') := by
  rw [E_disjoint_E_iff hd r t hr hwz hwz']
  tauto

/-! ## A finite cover and the `Good.cover` field -/

/-- If `S` is covered by the initial box and finitely many examined edge regions, a new edge whose
head is neither the origin nor an endpoint of any covering edge is disjoint from `S`.  The explicit
"new edge is not in `edges`" premise is unnecessary: it follows from endpoint freshness. -/
theorem disjoint_of_subset_Q_union_edges (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {S : Finset (Site d)} {edges : Finset (Site 2 × Site 2)} {w₀ z₀ : Site 2}
    (hcover : (S : Set (Site d)) ⊆ (Q d r t 0 : Set (Site d)) ∪
      ⋃ e ∈ edges, (E d r t e.1 e.2 : Set (Site d)))
    (hedges : ∀ e ∈ edges, (zdGraph 2).Adj e.1 e.2)
    (hnew : (zdGraph 2).Adj w₀ z₀) (hz₀ : z₀ ≠ 0)
    (hfresh : ∀ e ∈ edges, z₀ ≠ e.1 ∧ z₀ ≠ e.2) :
    Disjoint S (E d r t w₀ z₀) := by
  rw [Finset.disjoint_left]
  intro x hxS hxE
  rcases hcover (Finset.mem_coe.2 hxS) with hxQ | hxEdges
  · exact Finset.disjoint_left.1 (E_disjoint_Q_of_ne_head hd r t hr hnew hz₀.symm)
      hxE (Finset.mem_coe.1 hxQ)
  · obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.1 hxEdges
    have he' : e ∈ edges := Finset.mem_coe.1 he
    have hdis := E_disjoint_E_of_head_ne_endpoints hd r t hr hnew (hedges e he')
      (hfresh e he').1 (hfresh e he').2
    exact Finset.disjoint_left.1 hdis hxE (Finset.mem_coe.1 hxe)

/-- Endpoint freshness already implies that the pending ordered edge has not been examined. -/
theorem edge_not_mem_of_head_fresh {edges : Finset (Site 2 × Site 2)} {w₀ z₀ : Site 2}
    (hfresh : ∀ e ∈ edges, z₀ ≠ e.1 ∧ z₀ ≠ e.2) : (w₀, z₀) ∉ edges := by
  intro he
  exact (hfresh (w₀, z₀) he).2 rfl

/-- Direct application of `Good.cover`: an edge directed into an undetermined macro-vertex is
disjoint from every already inspected site. -/
theorem inspected_disjoint_E_of_good_of_undetermined (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r)
    {h : Tr d} (hg : Good d r t h) {w₀ z₀ : Site 2}
    (hnew : (zdGraph 2).Adj w₀ z₀) (hz₀ : z₀ ∉ h.openV ∪ h.closedV) :
    Disjoint h.inspected (E d r t w₀ z₀) := by
  obtain ⟨edges, hedges, hcover⟩ := hg.cover
  have hz₀zero : z₀ ≠ 0 := by
    intro hz
    subst z₀
    exact hz₀ (Finset.mem_union_left _ hg.zero_mem)
  refine disjoint_of_subset_Q_union_edges hd r t hr hcover
    (fun e he => (hedges e he).2.2) hnew hz₀zero ?_
  intro e he
  obtain ⟨he1, he2, -⟩ := hedges e he
  constructor
  · intro hz
    rw [hz] at hz₀
    exact hz₀ (Finset.mem_union_left _ he1)
  · intro hz
    rw [hz] at hz₀
    exact hz₀ he2

/-- For a good nonterminal exploration transcript, the entire corridor about to be examined is
fresh.  This is stronger than the definitional fact that `region = E \ inspected` is fresh. -/
theorem inspected_disjoint_pending_E (hd : 2 ≤ d) (r t n : ℕ) (hr : 0 < r)
    {h : Tr d} (hg : Good d r t h)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    Disjoint h.inspected (E d r t (pendW d n h) (pendZ d n h)) := by
  obtain ⟨-, hzo, hzc, -⟩ :=
    pendZ_mem d n (boundary_nonempty_of_not_terminal d n hT)
  have hzund : pendZ d n h ∉ h.openV ∪ h.closedV := by
    intro hz
    rcases Finset.mem_union.1 hz with hz | hz
    · exact hzo hz
    · exact hzc hz
  exact inspected_disjoint_E_of_good_of_undetermined hd r t hr hg
    (pendW_spec d r t n hg hT).2 hzund

/-- Consequently the set-difference used by the exploration does not remove anything: at a good
nonterminal transcript, `region` is the whole pending edge region. -/
theorem region_eq_pending_E (hd : 2 ≤ d) (r t n : ℕ) (hr : 0 < r)
    {h : Tr d} (hg : Good d r t h)
    (hT : ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (tgt n)) :
    region d r t n h = E d r t (pendW d n h) (pendZ d n h) := by
  exact Finset.sdiff_eq_self_of_disjoint (inspected_disjoint_pending_E hd r t n hr hg hT).symm

/-! ## Concrete non-vacuity at `d = 3`, `r = t = 1` -/

private def e₀ : Site 2 := Pi.single 0 1
private def e₁ : Site 2 := Pi.single 1 1

private theorem adj_zero_e₀ : (zdGraph 2).Adj (0 : Site 2) e₀ := by
  rw [zdGraph_adj_iff]
  exact ⟨0, Or.inl (by simp [e₀])⟩

private theorem adj_zero_e₁ : (zdGraph 2).Adj (0 : Site 2) e₁ := by
  rw [zdGraph_adj_iff]
  exact ⟨1, Or.inl (by simp [e₁])⟩

/-- Two explicit distinct edges leaving the origin in perpendicular directions have disjoint edge
regions. -/
example : Disjoint (E 3 1 1 0 e₀) (E 3 1 1 0 e₁) := by
  apply E_disjoint_E_of_heads_ne_of_not_reverse (d := 3) (by norm_num) 1 1 (by norm_num)
    adj_zero_e₀ adj_zero_e₁
  · intro h
    have := congrFun h 0
    simp [e₀, e₁] at this
  · rintro ⟨h, -⟩
    have := congrFun h 1
    simp [e₁] at this

/-- The reverse of the first explicit edge is distinct but genuinely overlaps it. -/
example : ¬ Disjoint (E 3 1 1 0 e₀) (E 3 1 1 e₀ 0) :=
  not_disjoint_E_E_reverse (d := 3) (by norm_num) 1 1 (by norm_num) adj_zero_e₀

#print axioms KNAll.Site.Corridor.E_disjoint_Q_iff
#print axioms KNAll.Site.Corridor.E_disjoint_E_iff
#print axioms KNAll.Site.Corridor.E_overlap_iff
#print axioms KNAll.Site.Corridor.disjoint_of_subset_Q_union_edges
#print axioms KNAll.Site.Corridor.inspected_disjoint_pending_E
#print axioms KNAll.Site.Corridor.region_eq_pending_E

end KNAll.Site.Corridor

end
