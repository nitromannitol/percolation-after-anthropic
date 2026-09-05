import Hypergraph.MacroExploration
import Hypergraph.TargetExtension
import Hypergraph.Certificate2

/-!
# The deterministic corridor geometry

The shell-window data of `KNAll.Site.TargetExt.LevelGeometry`, built explicitly inside the corridor
`E d r t w z` of `KN/MacroExploration.lean`.  Nothing probabilistic appears: every object is a
finite set of sites of `ℤ^d`, and every property is an inclusion, a disjointness, or the existence
of a nearest-neighbour path.

* `rbox c ρ`: the box of centre `c` and per-coordinate radius `ρ`.
* `connWithin_rbox_of_allOpen`: an all-open box is connected.
* `Level`: the three boxes `D ⊇ O ⊇ I` of a level, with the seed layer `D \ O` of depth `ℓ` and the
  shell `O \ I` of thickness `s`.
* For a contact `x` of the outer boundary of `D`: its outward direction, the clamped cube centre
  `cubeCentre`, the cube `cube x`, its quarter-face `face x` and its seed `seed x`.
* `sel`: a greedy selection of contacts pairwise far apart, whose seeds are pairwise disjoint.
* `toLevelGeometry`: the data fields of `LevelGeometry` instantiated at a level, with the
  reliability events and their two properties left as parameters, since they are the probabilistic
  input of the next module.
-/

noncomputable section

namespace KNAll.Site.Corridor

set_option linter.unusedSectionVars false

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.MacroExp

/-! ## Boxes -/

section Boxes

variable {d : ℕ}

/-- The box of centre `c` and per-coordinate radius `ρ`. -/
def rbox (c : Site d) (ρ : Fin d → ℤ) : Finset (Site d) :=
  Fintype.piFinset fun j => Finset.Icc (c j - ρ j) (c j + ρ j)

theorem mem_rbox {c x : Site d} {ρ : Fin d → ℤ} :
    x ∈ rbox c ρ ↔ ∀ j, c j - ρ j ≤ x j ∧ x j ≤ c j + ρ j := by
  simp [rbox, Fintype.mem_piFinset]

theorem rbox_mono {c : Site d} {ρ ρ' : Fin d → ℤ} (h : ∀ j, ρ j ≤ ρ' j) : rbox c ρ ⊆ rbox c ρ' := by
  intro x hx
  rw [mem_rbox] at hx ⊢
  intro j
  have := hx j
  have := h j
  omega

/-- The anisotropic boxes of `KN/MacroExploration.lean` are boxes. -/
theorem abox_eq_rbox (c : Site d) (R t : ℕ) : abox c R t = rbox c (rad R t) := rfl

/-- **The gate lemma.**  A site of a box adjacent to a site outside it lies on the boundary layer
of the box, so it is outside the box shrunk by one in every coordinate. -/
theorem notMem_rbox_sub_one_of_adj {c x y : Site d} {ρ : Fin d → ℤ} (hx : x ∉ rbox c ρ)
    (hy : y ∈ rbox c ρ) (hadj : (zdGraph d).Adj x y) : y ∉ rbox c (fun j => ρ j - 1) := by
  intro hy'
  rw [mem_rbox] at hy hy'
  refine hx (mem_rbox.2 fun j => ?_)
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff x y).1 hadj
  · have hrel : y j = x j + if j = i then 1 else 0 := by rw [hi]; simp [Pi.single_apply]
    have := hy j; have := hy' j
    split_ifs at hrel <;> omega
  · have hrel : x j = y j + if j = i then 1 else 0 := by rw [hi]; simp [Pi.single_apply]
    have := hy j; have := hy' j
    split_ifs at hrel <;> omega

/-- The sup-distance from a site to a box's centre is bounded by the radius. -/
theorem abs_sub_le_of_mem_rbox {c x : Site d} {ρ : Fin d → ℤ} (hx : x ∈ rbox c ρ) (j : Fin d) :
    |x j - c j| ≤ ρ j := by
  have := mem_rbox.1 hx j
  rw [abs_le]; omega

end Boxes

/-! ## An all-open box is connected -/

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

/-- Moving one coordinate one step towards `y` lowers the `ℓ¹` distance by one. -/
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

/-- The step stays in a box containing both endpoints. -/
theorem stepTo_mem_rbox {c x y : Site d} {ρ : Fin d → ℤ} (hx : x ∈ rbox c ρ) (hy : y ∈ rbox c ρ)
    {i : Fin d} (hne : x i ≠ y i) : stepTo x y i ∈ rbox c ρ := by
  rw [mem_rbox] at hx hy ⊢
  intro j
  by_cases hj : j = i
  · rw [hj, stepTo_apply_self]
    have h1 := hx i; have h2 := hy i
    split_ifs <;> omega
  · rw [stepTo_apply_of_ne x y hj]
    exact hx j

/-- **An all-open box is connected.**  Any two sites of a box all of whose sites are open are
joined by an open path inside the box. -/
theorem connWithin_rbox_of_allOpen {c : Site d} {ρ : Fin d → ℤ} {ω : SiteConfig (Site d)}
    (hopen : (↑(rbox c ρ) : Set (Site d)) ⊆ ω) :
    ∀ (n : ℕ) (x y : Site d), x ∈ rbox c ρ → y ∈ rbox c ρ → dist1 x y ≤ n →
      ω ∈ connWithin (zdGraph d) (↑(rbox c ρ) : Set (Site d)) x y := by
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
      have hmem := stepTo_mem_rbox hx hy hi
      have hrec := ih (stepTo x y i) y hmem hy (by omega)
      refine ⟨⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩, ?_⟩
      refine (SimpleGraph.Adj.reachable ?_).trans hrec.2
      exact (openSiteGraph_adj_iff' (zdGraph d) _ x _).2
        ⟨adj_stepTo x y i, ⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩,
          ⟨hopen (Finset.mem_coe.2 hmem), Finset.mem_coe.2 hmem⟩⟩


/-- The box with lower corner `lo` and upper corner `hi`. -/
def ibox (lo hi : Fin d → ℤ) : Finset (Site d) := Fintype.piFinset fun j => Finset.Icc (lo j) (hi j)

theorem mem_ibox {lo hi : Fin d → ℤ} {x : Site d} : x ∈ ibox lo hi ↔ ∀ j, lo j ≤ x j ∧ x j ≤ hi j := by
  simp [ibox, Fintype.mem_piFinset]

theorem stepTo_mem_ibox {lo hi : Fin d → ℤ} {x y : Site d} (hx : x ∈ ibox lo hi) (hy : y ∈ ibox lo hi)
    {i : Fin d} (hne : x i ≠ y i) : stepTo x y i ∈ ibox lo hi := by
  rw [mem_ibox] at hx hy ⊢
  intro j
  by_cases hj : j = i
  · rw [hj, stepTo_apply_self]
    have h1 := hx i; have h2 := hy i
    split_ifs <;> omega
  · rw [stepTo_apply_of_ne x y hj]
    exact hx j

/-- **An all-open interval box is connected.** -/
theorem connWithin_ibox_of_allOpen {lo hi : Fin d → ℤ} {ω : SiteConfig (Site d)}
    (hopen : (↑(ibox lo hi) : Set (Site d)) ⊆ ω) :
    ∀ (n : ℕ) (x y : Site d), x ∈ ibox lo hi → y ∈ ibox lo hi → dist1 x y ≤ n →
      ω ∈ connWithin (zdGraph d) (↑(ibox lo hi) : Set (Site d)) x y := by
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
      have hmem := stepTo_mem_ibox hx hy hi
      have hrec := ih (stepTo x y i) y hmem hy (by omega)
      refine ⟨⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩, ?_⟩
      refine (SimpleGraph.Adj.reachable ?_).trans hrec.2
      exact (openSiteGraph_adj_iff' (zdGraph d) _ x _).2
        ⟨adj_stepTo x y i, ⟨hopen (Finset.mem_coe.2 hx), Finset.mem_coe.2 hx⟩,
          ⟨hopen (Finset.mem_coe.2 hmem), Finset.mem_coe.2 hmem⟩⟩

end BoxConnected

/-! ## Levels -/

section Levels

variable {d : ℕ}

/-- The scales of the level structure: the radius of the outermost box at level `0`, the depth
`ℓ` of the seed layer, the thickness `s` of the shell, and the radius `M` of the local cubes. -/
structure Scales (d : ℕ) where
  /-- The per-coordinate radius of the box `D` at level `0`. -/
  ρ₀ : Fin d → ℤ
  /-- The depth of the seed layer `D \ O`. -/
  ℓ : ℕ
  /-- The thickness of the shell `O \ I`. -/
  s : ℕ
  /-- The radius of the local cubes. -/
  M : ℕ

variable (Sc : Scales d)

/-- The radius of `D` at level `j`: one less per level, so that consecutive levels are gated. -/
def ρD (j : ℕ) : Fin d → ℤ := fun q => Sc.ρ₀ q - j

/-- The radius of `O` at level `j`. -/
def ρO (j : ℕ) : Fin d → ℤ := fun q => ρD Sc j q - Sc.ℓ

/-- The radius of `I` at level `j`. -/
def ρI (j : ℕ) : Fin d → ℤ := fun q => ρO Sc j q - Sc.s

variable (c : Site d)

/-- The outer box of level `j`. -/
def Dbox (j : ℕ) : Finset (Site d) := rbox c (ρD Sc j)

/-- The middle box of level `j`. -/
def Obox (j : ℕ) : Finset (Site d) := rbox c (ρO Sc j)

/-- The inner box of level `j`. -/
def Ibox (j : ℕ) : Finset (Site d) := rbox c (ρI Sc j)

theorem Ibox_subset_Obox (j : ℕ) : Ibox Sc c j ⊆ Obox Sc c j :=
  rbox_mono fun q => by simp [ρI]

theorem Obox_subset_Dbox (j : ℕ) : Obox Sc c j ⊆ Dbox Sc c j :=
  rbox_mono fun q => by simp [ρO]

theorem Dbox_succ_subset (j : ℕ) : Dbox Sc c (j + 1) ⊆ Dbox Sc c j :=
  rbox_mono fun q => by simp only [ρD]; push_cast; omega

/-- **Consecutive levels are gated**: a site of `D j` adjacent to a site outside `D j` is not in
`D (j+1)`. -/
theorem gate (j : ℕ) {x y : Site d} (hx : x ∉ Dbox Sc c j) (hy : y ∈ Dbox Sc c j)
    (hadj : (zdGraph d).Adj x y) : y ∉ Dbox Sc c (j + 1) := by
  have h := notMem_rbox_sub_one_of_adj hx hy hadj
  have heq : Dbox Sc c (j + 1) = rbox c (fun q => ρD Sc j q - 1) := by
    unfold Dbox
    congr 1
    funext q
    simp [ρD]; ring
  rw [heq]
  exact h

end Levels

/-! ## Contacts, cubes, faces and seeds -/

section Contacts

variable {d : ℕ} [NeZero d]

/-- A contact of the box `rbox c ρ`: a site outside it adjacent to a site inside it. -/
def IsContact (c : Site d) (ρ : Fin d → ℤ) (x : Site d) : Prop :=
  x ∉ rbox c ρ ∧ ∃ y ∈ rbox c ρ, (zdGraph d).Adj x y

/-- A contact has an outward coordinate `i` and sign `σ`: it sits one step beyond the face of the
box in coordinate `i`, and within the box's range in every other coordinate. -/
theorem exists_dir {c : Site d} {ρ : Fin d → ℤ} {x : Site d} (h : IsContact c ρ x) :
    ∃ (i : Fin d) (σ : ℤ), (σ = 1 ∨ σ = -1) ∧ x i = c i + σ * (ρ i + 1) ∧
      ∀ q, q ≠ i → c q - ρ q ≤ x q ∧ x q ≤ c q + ρ q := by
  obtain ⟨hx, y, hy, hadj⟩ := h
  rw [mem_rbox] at hy
  obtain ⟨i, hi | hi⟩ := (zdGraph_adj_iff x y).1 hadj
  · -- `y = x + eᵢ`, so `x` is below the box in coordinate `i`
    have hrel : ∀ q, y q = x q + if q = i then 1 else 0 := fun q => by
      rw [hi]; simp [Pi.single_apply]
    refine ⟨i, -1, Or.inr rfl, ?_, fun q hq => ?_⟩
    · have hxi : x i ∉ Set.Icc (c i - ρ i) (c i + ρ i) := by
        intro hcon
        refine hx (mem_rbox.2 fun q => ?_)
        by_cases hq : q = i
        · subst hq; exact hcon
        · have := hy q; have := hrel q; simp [hq] at *; omega
      have := hy i; have := hrel i
      simp only [Set.mem_Icc, not_and, not_le] at hxi
      simp at *
      omega
    · have := hy q; have := hrel q; simp [hq] at *; omega
  · have hrel : ∀ q, x q = y q + if q = i then 1 else 0 := fun q => by
      rw [hi]; simp [Pi.single_apply]
    refine ⟨i, 1, Or.inl rfl, ?_, fun q hq => ?_⟩
    · have hxi : x i ∉ Set.Icc (c i - ρ i) (c i + ρ i) := by
        intro hcon
        refine hx (mem_rbox.2 fun q => ?_)
        by_cases hq : q = i
        · subst hq; exact hcon
        · have := hy q; have := hrel q; simp [hq] at *; omega
      have := hy i; have := hrel i
      simp only [Set.mem_Icc, not_and, not_le] at hxi
      simp at *
      omega
    · have := hy q; have := hrel q; simp [hq] at *; omega

open Classical in
/-- The outward coordinate of a contact (an arbitrary coordinate for a non-contact). -/
def dirI (c : Site d) (ρ : Fin d → ℤ) (x : Site d) : Fin d :=
  if h : IsContact c ρ x then (exists_dir h).choose else ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩

open Classical in
/-- The outward sign of a contact. -/
def dirσ (c : Site d) (ρ : Fin d → ℤ) (x : Site d) : ℤ :=
  if h : IsContact c ρ x then (exists_dir h).choose_spec.choose else 1

theorem dir_spec {c : Site d} {ρ : Fin d → ℤ} {x : Site d} (h : IsContact c ρ x) :
    (dirσ c ρ x = 1 ∨ dirσ c ρ x = -1) ∧
      x (dirI c ρ x) = c (dirI c ρ x) + dirσ c ρ x * (ρ (dirI c ρ x) + 1) ∧
      ∀ q, q ≠ dirI c ρ x → c q - ρ q ≤ x q ∧ x q ≤ c q + ρ q := by
  unfold dirI dirσ
  rw [dif_pos h, dif_pos h]
  exact (exists_dir h).choose_spec.choose_spec

variable (Sc : Scales d) (c : Site d) (j : ℕ)

/-- The outward coordinate of a contact of `D j`. -/
def cI (x : Site d) : Fin d := dirI c (ρD Sc j) x

/-- The outward sign of a contact of `D j`. -/
def cσ (x : Site d) : ℤ := dirσ c (ρD Sc j) x

/-- **The clamped cube centre.**  In the outward coordinate the cube touches the face of `O`; in
every other coordinate its centre is the contact's coordinate clamped so that the cube stays in
`O`. -/
def cubeCentre (x : Site d) : Site d := fun q =>
  if q = cI Sc c j x then c q + cσ Sc c j x * (ρO Sc j q - Sc.M)
  else max (c q - ρO Sc j q + Sc.M) (min (c q + ρO Sc j q - Sc.M) (x q))

/-- The local cube of a contact. -/
def cube (x : Site d) : Finset (Site d) := rbox (cubeCentre Sc c j x) (fun _ => Sc.M)

/-- The face of the local cube on the side of the contact: the sites of the cube lying on the
face of `O`. -/
def face (x : Site d) : Finset (Site d) :=
  (cube Sc c j x).filter fun u => u (cI Sc c j x) = c (cI Sc c j x) + cσ Sc c j x * ρO Sc j (cI Sc c j x)

/-- The lower corner of the seed of a contact. -/
def seedLo (x : Site d) : Fin d → ℤ := fun q =>
  if q = cI Sc c j x then min (c q + cσ Sc c j x * (ρO Sc j q + 1)) (c q + cσ Sc c j x * ρD Sc j q)
  else min (x q) (cubeCentre Sc c j x q - Sc.M)

/-- The upper corner of the seed of a contact. -/
def seedHi (x : Site d) : Fin d → ℤ := fun q =>
  if q = cI Sc c j x then max (c q + cσ Sc c j x * (ρO Sc j q + 1)) (c q + cσ Sc c j x * ρD Sc j q)
  else max (x q) (cubeCentre Sc c j x q + Sc.M)

/-- **The seed** of a contact: in the outward coordinate it spans the seed layer `D \ O`, and in
every other coordinate it spans from the contact's coordinate to the range of the cube. -/
def seed (x : Site d) : Finset (Site d) := ibox (seedLo Sc c j x) (seedHi Sc c j x)

theorem mem_seed {x y : Site d} :
    y ∈ seed Sc c j x ↔ ∀ q,
      (q = cI Sc c j x →
        min (c q + cσ Sc c j x * (ρO Sc j q + 1)) (c q + cσ Sc c j x * ρD Sc j q) ≤ y q ∧
        y q ≤ max (c q + cσ Sc c j x * (ρO Sc j q + 1)) (c q + cσ Sc c j x * ρD Sc j q)) ∧
      (q ≠ cI Sc c j x →
        min (x q) (cubeCentre Sc c j x q - Sc.M) ≤ y q ∧
        y q ≤ max (x q) (cubeCentre Sc c j x q + Sc.M)) := by
  simp only [seed, mem_ibox, seedLo, seedHi]
  refine forall_congr' fun q => ?_
  by_cases hq : q = cI Sc c j x
  · simp [hq]
  · simp [hq]

/-- **The well-formedness of the scales at a level**: the cubes fit in `O`, the shell holds a
cube, and the seed layer is not empty. -/
structure Fits (j : ℕ) : Prop where
  cube_le : ∀ q, (Sc.M : ℤ) ≤ ρO Sc j q
  shell : 2 * Sc.M + 1 ≤ Sc.s
  layer : 1 ≤ Sc.ℓ

variable {Sc c j}

/-- The cube centre lies in `O`, with room `M` on every side, in every coordinate. -/
theorem cubeCentre_range (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) (q : Fin d) :
    c q - ρO Sc j q + Sc.M ≤ cubeCentre Sc c j x q ∧
      cubeCentre Sc c j x q ≤ c q + ρO Sc j q - Sc.M := by
  have hM := hf.cube_le q
  obtain ⟨hσ, -, -⟩ := dir_spec hx
  unfold cubeCentre
  by_cases hq : q = cI Sc c j x
  · rw [if_pos hq]
    rcases hσ with h | h <;> rw [show cσ Sc c j x = dirσ c (ρD Sc j) x from rfl, h] <;> omega
  · rw [if_neg hq]
    omega

/-- **The cube lies in the shell `O \ I`.** -/
theorem cube_subset_shell (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    cube Sc c j x ⊆ Obox Sc c j \ Ibox Sc c j := by
  intro u hu
  rw [cube, mem_rbox] at hu
  rw [Finset.mem_sdiff, Obox, Ibox, mem_rbox, mem_rbox]
  constructor
  · intro q
    have := hu q
    have := cubeCentre_range hf hx q
    omega
  · intro hI
    obtain ⟨hσ, -, -⟩ := dir_spec hx
    have hi := hu (cI Sc c j x)
    have hI' := hI (cI Sc c j x)
    have hs := hf.shell
    have hcen : cubeCentre Sc c j x (cI Sc c j x)
        = c (cI Sc c j x) + cσ Sc c j x * (ρO Sc j (cI Sc c j x) - Sc.M) := by
      unfold cubeCentre; rw [if_pos rfl]
    rw [hcen] at hi
    simp only [ρI] at hI'
    rcases hσ with h | h <;> rw [show cσ Sc c j x = dirσ c (ρD Sc j) x from rfl, h] at hi <;> omega

theorem face_subset_cube (x : Site d) : face Sc c j x ⊆ cube Sc c j x := Finset.filter_subset _ _

/-- **The face lies in the shell.** -/
theorem face_subset_shell (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    face Sc c j x ⊆ Obox Sc c j \ Ibox Sc c j :=
  (face_subset_cube x).trans (cube_subset_shell hf hx)

/-- **The seed lies in `D`.** -/
theorem seed_subset_Dbox (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    seed Sc c j x ⊆ Dbox Sc c j := by
  intro y hy
  rw [mem_seed] at hy
  rw [Dbox, mem_rbox]
  intro q
  obtain ⟨hσ, hxi, hxq⟩ := dir_spec hx
  have hcr := cubeCentre_range hf hx q
  have hM := hf.cube_le q
  by_cases hq : q = cI Sc c j x
  · have h := (hy q).1 hq
    have hℓ : ρO Sc j q = ρD Sc j q - Sc.ℓ := rfl
    have hcσ : cσ Sc c j x = dirσ c (ρD Sc j) x := rfl
    have hl : (1 : ℤ) ≤ Sc.ℓ := by exact_mod_cast hf.layer
    rw [hcσ] at h
    rcases hσ with hs | hs <;> rw [hs] at h <;>
      simp only [one_mul, neg_one_mul, min_def, max_def] at h <;> split_ifs at h <;>
      constructor <;> linarith [h.1, h.2, hcr.1, hcr.2, hM, hl]
  · have h := (hy q).2 hq
    have hxr := hxq q hq
    have hℓ : ρO Sc j q = ρD Sc j q - Sc.ℓ := rfl
    have hℓ0 : (0 : ℤ) ≤ Sc.ℓ := Nat.cast_nonneg _
    simp only [min_def, max_def] at h
    split_ifs at h <;> constructor <;> linarith [h.1, h.2, hcr.1, hcr.2, hM, hxr.1, hxr.2]

/-- **The seed avoids `O`.** -/
theorem seed_disjoint_Obox (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    ∀ y ∈ seed Sc c j x, y ∉ Obox Sc c j := by
  intro y hy hO
  rw [mem_seed] at hy
  rw [Obox, mem_rbox] at hO
  obtain ⟨hσ, -, -⟩ := dir_spec hx
  have h := (hy (cI Sc c j x)).1 rfl
  have hO' := hO (cI Sc c j x)
  have hℓ : ρO Sc j (cI Sc c j x) = ρD Sc j (cI Sc c j x) - Sc.ℓ := rfl
  have hl := hf.layer
  rcases hσ with hs | hs <;> rw [show cσ Sc c j x = dirσ c (ρD Sc j) x from rfl, hs] at h <;>
    simp only [min_def, max_def] at h <;> split_ifs at h <;> omega


/-- **The seed lies in the ball of radius `ℓ + 2M` around its contact.** -/
theorem seed_subset_ball (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    ∀ y ∈ seed Sc c j x, ∀ q, |y q - x q| ≤ (Sc.ℓ : ℤ) + 2 * Sc.M := by
  intro y hy q
  rw [mem_seed] at hy
  obtain ⟨hσ, hxi, hxq⟩ := dir_spec hx
  have hcr := cubeCentre_range hf hx q
  have hM := hf.cube_le q
  have hℓ : ρO Sc j q = ρD Sc j q - Sc.ℓ := rfl
  have hM0 : (0 : ℤ) ≤ Sc.M := Nat.cast_nonneg _
  have hl : (1 : ℤ) ≤ Sc.ℓ := by exact_mod_cast hf.layer
  rw [abs_le]
  by_cases hq : q = cI Sc c j x
  · have h := (hy q).1 hq
    have hcσ : cσ Sc c j x = dirσ c (ρD Sc j) x := rfl
    have hxi' : x q = c q + dirσ c (ρD Sc j) x * (ρD Sc j q + 1) := by rw [hq]; exact hxi
    clear hxi hxq
    rw [hcσ] at h
    rcases hσ with hs | hs <;> rw [hs] at h hxi' <;>
      simp only [one_mul, neg_one_mul, min_def, max_def] at h hxi' <;> split_ifs at h <;>
      omega
  · have h := (hy q).2 hq
    have hxr := hxq q hq
    -- the clamp moves the coordinate by at most `ℓ + M`
    have hclamp : |cubeCentre Sc c j x q - x q| ≤ (Sc.ℓ : ℤ) + Sc.M := by
      unfold cubeCentre
      rw [if_neg hq, abs_le]
      simp only [min_def, max_def]
      split_ifs <;> constructor <;> linarith [hxr.1, hxr.2, hM]
    rw [abs_le] at hclamp
    simp only [min_def, max_def] at h
    split_ifs at h <;> constructor <;> linarith [h.1, h.2, hclamp.1, hclamp.2]

variable (Sc c j)

/-- The site of the seed layer adjacent to the contact. -/
def contactStep (x : Site d) : Site d :=
  Function.update x (cI Sc c j x) (x (cI Sc c j x) - cσ Sc c j x)

/-- The site of the seed layer adjacent to a face site. -/
def faceStep (x u : Site d) : Site d :=
  Function.update u (cI Sc c j x) (u (cI Sc c j x) + cσ Sc c j x)

variable {Sc c j}

/-- Two sites differing by `±1` in one coordinate are adjacent. -/
theorem adj_of_update (z : Site d) (i : Fin d) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    (zdGraph d).Adj z (Function.update z i (z i + σ)) := by
  rw [zdGraph_adj_iff]
  refine ⟨i, ?_⟩
  rcases hσ with rfl | rfl
  · left; funext q; by_cases hq : q = i
    · subst hq; simp
    · simp [hq]
  · right; funext q; by_cases hq : q = i
    · subst hq; simp
    · simp [hq]

theorem contactStep_mem_seed (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    contactStep Sc c j x ∈ seed Sc c j x := by
  rw [mem_seed]
  obtain ⟨hσ, hxi, -⟩ := dir_spec hx
  intro q
  constructor
  · intro hq
    subst hq
    simp only [contactStep, Function.update_self]
    have hcσ : cσ Sc c j x = dirσ c (ρD Sc j) x := rfl
    have hℓ : ρO Sc j (cI Sc c j x) = ρD Sc j (cI Sc c j x) - Sc.ℓ := rfl
    have hl : (1 : ℤ) ≤ Sc.ℓ := by exact_mod_cast hf.layer
    have hxi' : x (cI Sc c j x) = c (cI Sc c j x) + dirσ c (ρD Sc j) x * (ρD Sc j (cI Sc c j x) + 1) :=
      hxi
    clear hxi
    rw [hcσ]
    rcases hσ with hs | hs <;> rw [hs] at hxi' ⊢ <;>
      simp only [one_mul, neg_one_mul, min_def, max_def] at hxi' ⊢ <;>
      split_ifs <;> constructor <;> omega
  · intro hq
    simp only [contactStep, Function.update_of_ne hq]
    constructor
    · exact min_le_left _ _
    · exact le_max_left _ _

theorem faceStep_mem_seed (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) {u : Site d}
    (hu : u ∈ face Sc c j x) : faceStep Sc c j x u ∈ seed Sc c j x := by
  rw [face, Finset.mem_filter, cube, mem_rbox] at hu
  obtain ⟨hcube, hui⟩ := hu
  rw [mem_seed]
  obtain ⟨hσ, -, -⟩ := dir_spec hx
  intro q
  constructor
  · intro hq
    subst hq
    simp only [faceStep, Function.update_self]
    rw [hui]
    have hcσ : cσ Sc c j x = dirσ c (ρD Sc j) x := rfl
    have hℓ : ρO Sc j (cI Sc c j x) = ρD Sc j (cI Sc c j x) - Sc.ℓ := rfl
    have hl : (1 : ℤ) ≤ Sc.ℓ := by exact_mod_cast hf.layer
    rw [hcσ]
    rcases hσ with hs | hs <;> rw [hs] <;> simp only [one_mul, neg_one_mul, min_def, max_def] <;>
      split_ifs <;> constructor <;> linarith
  · intro hq
    simp only [faceStep, Function.update_of_ne hq]
    have := hcube q
    constructor
    · exact le_trans (min_le_right _ _) this.1
    · exact le_trans this.2 (le_max_right _ _)

theorem adj_contactStep {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    (zdGraph d).Adj x (contactStep Sc c j x) := by
  obtain ⟨hσ, -, -⟩ := dir_spec hx
  unfold contactStep
  have : x (cI Sc c j x) - cσ Sc c j x = x (cI Sc c j x) + (-cσ Sc c j x) := by ring
  rw [this]
  refine adj_of_update x _ ?_
  rcases hσ with h | h <;> rw [show cσ Sc c j x = dirσ c (ρD Sc j) x from rfl, h] <;> simp

theorem adj_faceStep {x : Site d} (hx : IsContact c (ρD Sc j) x) (u : Site d) :
    (zdGraph d).Adj u (faceStep Sc c j x u) := by
  obtain ⟨hσ, -, -⟩ := dir_spec hx
  unfold faceStep
  exact adj_of_update u _ hσ

/-- A confined connection extended by one open edge at its end. -/
theorem connWithin_of_connWithin_of_adj {S : Set (Site d)} {ω : SiteConfig (Site d)} {a b c' : Site d}
    (h : ω ∈ connWithin (zdGraph d) S a b) (hbc : (zdGraph d).Adj b c') (hc : c' ∈ ω ∩ S) :
    ω ∈ connWithin (zdGraph d) S a c' :=
  ⟨h.1, h.2.trans (SimpleGraph.Adj.reachable
    ((openSiteGraph_adj_iff' (zdGraph d) (ω ∩ S) b c').2
      ⟨hbc, mem_of_mem_siteCluster (zdGraph d) (ω ∩ S) ⟨h.1, h.2⟩, hc⟩))⟩

/-- **The seed connects the contact to every site of the face.**  With the contact, the face site
and every site of the seed open, the contact is joined to the face site inside the seed together
with those two sites: one step from the contact into the seed layer, a path inside the seed to the
site of the layer beneath the face site, and one step onto it. -/
theorem connWithin_seed (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) {u : Site d}
    (hu : u ∈ face Sc c j x) :
    (insert x (insert u (↑(seed Sc c j x) : Set (Site d))) : SiteConfig (Site d)) ∈
      connWithin (zdGraph d) (insert x (insert u (↑(seed Sc c j x) : Set (Site d)))) x u := by
  set S : Set (Site d) := insert x (insert u (↑(seed Sc c j x) : Set (Site d))) with hS
  have hseedS : (↑(seed Sc c j x) : Set (Site d)) ⊆ S := fun y hy => Or.inr (Or.inr hy)
  have hy := contactStep_mem_seed hf hx
  have hu' := faceStep_mem_seed hf hx hu
  -- inside the seed
  have hmid : (S : SiteConfig (Site d)) ∈ connWithin (zdGraph d) (↑(seed Sc c j x) : Set (Site d))
      (contactStep Sc c j x) (faceStep Sc c j x u) :=
    connWithin_ibox_of_allOpen hseedS _ _ _ hy hu' le_rfl
  have hmid' := connWithin_mono_set (zdGraph d) hseedS _ _ hmid
  -- the first step
  have hxS : x ∈ (S : SiteConfig (Site d)) ∩ S := ⟨Or.inl rfl, Or.inl rfl⟩
  have hyS : contactStep Sc c j x ∈ (S : SiteConfig (Site d)) ∩ S :=
    ⟨hseedS (Finset.mem_coe.2 hy), hseedS (Finset.mem_coe.2 hy)⟩
  have hfirst : (S : SiteConfig (Site d)) ∈ connWithin (zdGraph d) S x (faceStep Sc c j x u) :=
    TargetExt.connWithin_of_adj_of_connWithin (zdGraph d) (adj_contactStep hx) hxS hyS hmid'
  -- the last step
  have huS : u ∈ (S : SiteConfig (Site d)) ∩ S := ⟨Or.inr (Or.inl rfl), Or.inr (Or.inl rfl)⟩
  refine connWithin_of_connWithin_of_adj hfirst ?_ huS
  exact (adj_faceStep hx u).symm

end Contacts

/-! ## The selection of well-separated contacts -/

section Selection

variable {d : ℕ}

/-- Two sites are far apart at scale `b` when some coordinate separates them by more than `2 b`. -/
def Far (b : ℤ) (s x : Site d) : Prop := ∃ q, 2 * b + 1 ≤ |s q - x q|

theorem Far.symm {b : ℤ} {s x : Site d} (h : Far b s x) : Far b x s := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [abs_sub_comm]; exact hq⟩

/-- Balls of radius `b` around far-apart sites are disjoint. -/
theorem disjoint_of_far {b : ℤ} {s x : Site d} (h : Far b s x) :
    Disjoint (rbox s fun _ => b) (rbox x fun _ => b) := by
  rw [Finset.disjoint_left]
  intro y hys hyx
  obtain ⟨q, hq⟩ := h
  have h1 := abs_sub_le_of_mem_rbox hys q
  have h2 := abs_sub_le_of_mem_rbox hyx q
  rw [abs_le] at h1 h2
  rw [le_abs] at hq
  omega

open Classical in
/-- The greedy selection: run through the contacts and keep each one that is far from every one
already kept. -/
def sel (b : ℤ) (K : Finset (Site d)) : Finset (Site d) :=
  K.toList.foldl (fun acc x => if ∀ s ∈ acc, Far b s x then insert x acc else acc) ∅

open Classical in
theorem sel_aux (b : ℤ) :
    ∀ (l : List (Site d)) (acc : Finset (Site d)),
      (∀ s ∈ acc, ∀ s' ∈ acc, s ≠ s' → Far b s s') →
      (∀ s ∈ l.foldl (fun acc x => if ∀ s ∈ acc, Far b s x then insert x acc else acc) acc,
          s ∈ acc ∨ s ∈ l) ∧
      (∀ s ∈ l.foldl (fun acc x => if ∀ s ∈ acc, Far b s x then insert x acc else acc) acc,
        ∀ s' ∈ l.foldl (fun acc x => if ∀ s ∈ acc, Far b s x then insert x acc else acc) acc,
          s ≠ s' → Far b s s') := by
  intro l
  induction l with
  | nil =>
    intro acc hacc
    exact ⟨fun s hs => Or.inl hs, hacc⟩
  | cons x l ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    by_cases hfar : ∀ s ∈ acc, Far b s x
    · rw [if_pos hfar]
      have hacc' : ∀ s ∈ insert x acc, ∀ s' ∈ insert x acc, s ≠ s' → Far b s s' := by
        intro s hs s' hs' hne
        rw [Finset.mem_insert] at hs hs'
        rcases hs with rfl | hs <;> rcases hs' with rfl | hs'
        · exact absurd rfl hne
        · exact (hfar s' hs').symm
        · exact hfar s hs
        · exact hacc s hs s' hs' hne
      obtain ⟨h1, h2⟩ := ih (insert x acc) hacc'
      refine ⟨fun s hs => ?_, h2⟩
      rcases h1 s hs with hs | hs
      · rw [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · exact Or.inr (List.mem_cons_self)
        · exact Or.inl hs
      · exact Or.inr (List.mem_cons_of_mem _ hs)
    · rw [if_neg hfar]
      obtain ⟨h1, h2⟩ := ih acc hacc
      exact ⟨fun s hs => (h1 s hs).imp_right (List.mem_cons_of_mem _), h2⟩

theorem sel_subset (b : ℤ) (K : Finset (Site d)) : sel b K ⊆ K := by
  classical
  intro s hs
  have h := (sel_aux b K.toList ∅ (fun s hs => absurd hs (Finset.notMem_empty s))).1 s hs
  rcases h with h | h
  · exact absurd h (Finset.notMem_empty s)
  · exact Finset.mem_toList.1 h

theorem sel_far (b : ℤ) (K : Finset (Site d)) :
    ∀ s ∈ sel b K, ∀ s' ∈ sel b K, s ≠ s' → Far b s s' := by
  classical
  exact (sel_aux b K.toList ∅ (fun s hs => absurd hs (Finset.notMem_empty s))).2

end Selection

/-! ## Packaging: the data of a level -/

section Packaging

variable {d : ℕ} [NeZero d] (Sc : Scales d) (c : Site d) (j : ℕ)

/-- The radius of the ball around a contact containing its seed. -/
def ballRad : ℤ := (Sc.ℓ : ℤ) + 2 * Sc.M

theorem seed_subset_rbox (hf : Fits Sc j) {x : Site d} (hx : IsContact c (ρD Sc j) x) :
    seed Sc c j x ⊆ rbox x fun _ => ballRad Sc := by
  intro y hy
  rw [mem_rbox]
  intro q
  have := seed_subset_ball hf hx y hy q
  rw [abs_le] at this
  unfold ballRad
  omega

open Classical in
/-- **The selection of a level**: the greedy selection among the contacts of the given set. -/
def selC (K : Finset (Site d)) : Finset (Site d) :=
  sel (ballRad Sc) (K.filter (IsContact c (ρD Sc j)))

theorem selC_subset (K : Finset (Site d)) : selC Sc c j K ⊆ K := by
  classical
  exact (sel_subset _ _).trans (Finset.filter_subset _ _)

theorem isContact_of_mem_selC {K : Finset (Site d)} {x : Site d} (hx : x ∈ selC Sc c j K) :
    IsContact c (ρD Sc j) x := by
  classical
  exact (Finset.mem_filter.1 (sel_subset _ _ hx)).2

/-- On a set of contacts the selection is the plain greedy selection. -/
theorem selC_eq_of_contacts {K : Finset (Site d)} (hK : ∀ x ∈ K, IsContact c (ρD Sc j) x) :
    selC Sc c j K = sel (ballRad Sc) K := by
  classical
  unfold selC
  rw [Finset.filter_true_of_mem hK]

/-- **Selected contacts have pairwise disjoint seeds.** -/
theorem selC_pairwiseDisjoint_seed (hf : Fits Sc j) (K : Finset (Site d)) :
    (↑(selC Sc c j K) : Set (Site d)).PairwiseDisjoint (seed Sc c j) := by
  classical
  intro s hs s' hs' hne
  have hs1 := Finset.mem_coe.1 hs
  have hs2 := Finset.mem_coe.1 hs'
  have hfar := sel_far (ballRad Sc) _ s hs1 s' hs2 hne
  exact (disjoint_of_far hfar).mono
    (seed_subset_rbox Sc c j hf (isContact_of_mem_selC Sc c j hs1))
    (seed_subset_rbox Sc c j hf (isContact_of_mem_selC Sc c j hs2))

/-- A contact in the sense of `TargetExt.outerBoundary` is a contact of the box. -/
theorem isContact_of_mem_outerBoundary (Dom : Finset (Site d)) {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox Sc c j)) : IsContact c (ρD Sc j) x := by
  classical
  simp only [TargetExt.outerBoundary, Finset.mem_filter, Finset.mem_sdiff] at hx
  exact ⟨hx.1.2, hx.2⟩

/-- **The data of a level of `TargetExt.LevelGeometry`**, from the corridor geometry.  The
reliability events, their determination by `O` and the relay property are parameters: they are
the probabilistic input of the next module. -/
def toLevelGeometry (hf : Fits Sc j) (Dom : Finset (Site d)) (hDDom : Dbox Sc c j ⊆ Dom)
    (o : Site d) (ho : o ∉ Dbox Sc c j) (T : Set (Site d))
    (Gx : Site d → Set (SiteConfig (Site d)))
    (hGdet : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox Sc c j),
      DeterminedBy (Gx x) (↑(Obox Sc c j) : Set (Site d)))
    (hrelay : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox Sc c j), ∀ ω ∈ Gx x,
      ∃ u ∈ face Sc c j x, u ∈ ω ∧ ∀ ω' ∈ Gx x,
        ω' ∩ (↑(Obox Sc c j \ Ibox Sc c j) : Set (Site d)) = ω ∩ ↑(Obox Sc c j \ Ibox Sc c j) →
          ω' ∈ TargetExt.toTarget (zdGraph d) (Obox Sc c j) T u) :
    TargetExt.LevelGeometry (zdGraph d) Dom o T where
  D := Dbox Sc c j
  O := Obox Sc c j
  Int := Ibox Sc c j
  U := face Sc c j
  J := seed Sc c j
  sel := selC Sc c j
  Gx := Gx
  hIntO := Ibox_subset_Obox Sc c j
  hOD := Obox_subset_Dbox Sc c j
  hDDom := hDDom
  ho := ho
  hU x hx := face_subset_shell hf (isContact_of_mem_outerBoundary Sc c j Dom hx)
  hJD x hx := seed_subset_Dbox hf (isContact_of_mem_outerBoundary Sc c j Dom hx)
  hJO x hx := seed_disjoint_Obox hf (isContact_of_mem_outerBoundary Sc c j Dom hx)
  hW3 x hx u hu := connWithin_seed hf (isContact_of_mem_outerBoundary Sc c j Dom hx) hu
  hsel_sub K := selC_subset Sc c j K
  hsel_disj K := selC_pairwiseDisjoint_seed Sc c j hf K
  hGdet := hGdet
  hrelay := hrelay

end Packaging


/-! ## Placement in the corridor and in the slab -/

section Placement

variable {d : ℕ} [NeZero d]

/-- A box centred at the centre of the macro-vertex `z`, of planar radius at most `5 r` and
transverse radius at most `t`, lies in the central box `Q z`. -/
theorem rbox_subset_Q (r t : ℕ) (z : Site 2) {ρ : Fin d → ℤ}
    (hρ : ∀ q, ρ q ≤ rad (5 * r) t q) : rbox (ctr d r z) ρ ⊆ Q d r t z :=
  rbox_mono hρ

/-- The central box of `z` lies in the edge region leading to `z` from any other macro-vertex. -/
theorem Q_subset_E (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r) {w z : Site 2} (hwz : w ≠ z) :
    Q d r t z ⊆ E d r t w z := by
  intro x hx
  rw [Q, mem_abox] at hx
  rw [E, Finset.mem_sdiff, mem_hbox, Q, mem_abox]
  constructor
  · intro q
    have := hx q
    constructor
    · have := min_le_right (ctr d r w q) (ctr d r z q); omega
    · have := le_max_right (ctr d r w q) (ctr d r z q); omega
  · intro hQ
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
    have hr' : (0 : ℤ) ≤ 20 * (r : ℤ) := by positivity
    have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast hr
    rcases lt_or_gt_of_ne hi with hlt | hlt
    · have hle : w i + 1 ≤ z i := hlt
      have := mul_le_mul_of_nonneg_left hle hr'
      push_cast at h1 h2
      nlinarith
    · have hle : z i + 1 ≤ w i := hlt
      have := mul_le_mul_of_nonneg_left hle hr'
      push_cast at h1 h2
      nlinarith

/-- **Every level of the corridor lies in the edge region**, hence in the slab. -/
theorem Dbox_subset_E (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r) {w z : Site 2} (hwz : w ≠ z)
    (Sc : Scales d) (hρ : ∀ q, Sc.ρ₀ q ≤ rad (5 * r) t q) (j : ℕ) :
    Dbox Sc (ctr d r z) j ⊆ E d r t w z :=
  (Dbox_succ_subset Sc _ j |>.trans (by
    -- `D j ⊆ D 0`
    exact fun x hx => hx) : Dbox Sc (ctr d r z) (j + 1) ⊆ Dbox Sc (ctr d r z) j) |> fun _ =>
  (rbox_mono (fun q => by
    have := hρ q
    simp only [ρD]
    have : (0 : ℤ) ≤ j := Nat.cast_nonneg j
    omega) : Dbox Sc (ctr d r z) j ⊆ rbox (ctr d r z) (rad (5 * r) t)).trans
    (Q_subset_E hd r t hr hwz)

theorem Dbox_subset_thin (hd : 2 ≤ d) (r t : ℕ) (hr : 0 < r) {w z : Site 2} (hwz : w ≠ z)
    (Sc : Scales d) (hρ : ∀ q, Sc.ρ₀ q ≤ rad (5 * r) t q) (j : ℕ) :
    (↑(Dbox Sc (ctr d r z) j) : Set (Site d)) ⊆ thin d t :=
  (Finset.coe_subset.2 (Dbox_subset_E hd r t hr hwz Sc hρ j)).trans (E_subset_thin hd r t w z)

/-- **Freshness.**  Whatever lies in the region read at an examination avoids everything inspected
before it; in particular so does every level placed inside it. -/
theorem disjoint_inspected_of_subset_region (r t n : ℕ) (h : Tr d) {A : Finset (Site d)}
    (hA : A ⊆ region d r t n h) : Disjoint A h.inspected :=
  Finset.disjoint_of_subset_left hA Finset.sdiff_disjoint

end Placement

/-! ## The scales recorded by a certificate

`KN/Certificate2.lean` records the level count `levels`, the corridor radius `corridor`, the
transverse half-width `halfWidth`, the cube radius `faceTarget`, and the seed data `seedSize`,
`seedCount`, `contacts`.  The scales of the level structure are read off them: the seed layer has
depth `1`, the shell has thickness `2 faceTarget + 1`, and the cubes have radius `faceTarget`. -/

section FromCertificate

variable {d : ℕ} [NeZero d]

/-- The level scales of a certificate. -/
def scalesOf (C : LeftImp2.Certificate2 d) : Scales d where
  ρ₀ := rad C.corridor C.halfWidth
  ℓ := 1
  s := 2 * C.faceTarget + 1
  M := C.faceTarget

/-- **The planar coordinates fit at every level** of a well-formed certificate: the corridor radius
`corridor ≥ levels (2 faceTarget + 2)` leaves room for `faceTarget` after `levels` levels and the
seed layer. -/
theorem scalesOf_cube_le_planar (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed) {j : ℕ}
    (hj : j < C.levels) {q : Fin d} (hq : q.val < 2) :
    ((scalesOf C).M : ℤ) ≤ ρO (scalesOf C) j q := by
  have h := hwf.corridor_ge
  simp only [ρO, ρD, scalesOf, rad, if_pos hq]
  have h1 : C.levels * (2 * C.faceTarget + 2) ≤ C.corridor := h
  have h2 : (j + 1) * (2 * C.faceTarget + 2) ≤ C.levels * (2 * C.faceTarget + 2) :=
    Nat.mul_le_mul_right _ hj
  have h3 : (j + 1) * (2 * C.faceTarget + 2) = j * (2 * C.faceTarget + 2) + 2 * C.faceTarget + 2 := by
    ring
  have h4 : j ≤ j * (2 * C.faceTarget + 2) := Nat.le_mul_of_pos_right _ (by omega)
  push_cast
  omega

/-- **The fit at a level, given transverse room.**  The transverse half-width has to leave room for
`levels` levels, the seed layer and a cube: `halfWidth ≥ levels + faceTarget + 1`.  The certificate's
well-formedness does not record this (its extraction takes `halfWidth = faceTarget`), so it is a
hypothesis here. -/
theorem fits_scalesOf (C : LeftImp2.Certificate2 d) (hwf : C.WellFormed)
    (ht : C.levels + C.faceTarget + 1 ≤ C.halfWidth) {j : ℕ} (hj : j < C.levels) :
    Fits (scalesOf C) j where
  cube_le q := by
    by_cases hq : q.val < 2
    · exact scalesOf_cube_le_planar C hwf hj hq
    · simp only [ρO, ρD, scalesOf, rad, if_neg hq]
      push_cast
      omega
  shell := le_rfl
  layer := le_rfl

end FromCertificate

/-! ## Non-vacuity at `d = 3` -/

section NonVacuity

/-- Scales at `d = 3`: base radius `7` in every coordinate, seed depth `1`, shell `3`, cubes of
radius `1`; they fit at levels `0`, `1` and `2`. -/
def sc3 : Scales 3 := ⟨fun _ => 7, 1, 3, 1⟩

example : Fits sc3 2 where
  cube_le q := by simp [ρO, ρD, sc3]
  shell := by simp [sc3]
  layer := by simp [sc3]

/-- The contact `(8, 0, 0)` of the box of radius `7` at the origin. -/
example : IsContact (0 : Site 3) (ρD sc3 0) (Pi.single 0 8) := by
  refine ⟨?_, Pi.single 0 7, ?_, ?_⟩
  · rw [mem_rbox]
    intro h
    have := h 0
    simp [ρD, sc3] at this
  · rw [mem_rbox]
    intro j
    fin_cases j <;> simp [ρD, sc3]
  · rw [zdGraph_adj_iff]
    refine ⟨0, Or.inr ?_⟩
    funext j
    fin_cases j <;> simp

/-- The cube of a contact of the box of radius `7` lies in the shell `O \ I` at level `0`. -/
example : cube sc3 (0 : Site 3) 0 (Pi.single 0 8) ⊆ Obox sc3 0 0 \ Ibox sc3 0 0 :=
  cube_subset_shell ⟨fun q => by simp [ρO, ρD, sc3], by simp [sc3], by simp [sc3]⟩ (by
    refine ⟨?_, Pi.single 0 7, ?_, ?_⟩
    · rw [mem_rbox]
      intro h
      have := h 0
      simp [ρD, sc3] at this
    · rw [mem_rbox]
      intro j
      fin_cases j <;> simp [ρD, sc3]
    · rw [zdGraph_adj_iff]
      refine ⟨0, Or.inr ?_⟩
      funext j
      fin_cases j <;> simp)

/-- The corridor at `r = 1`, `t = 7`: the box of radius `5` at the centre of `e₀` fits in the edge
region from `0` to `e₀`, so scales with `ρ₀ = 5` place every level inside the corridor. -/
example : Dbox ⟨fun _ => 5, 1, 3, 1⟩ (ctr 3 1 (Pi.single 0 1)) 2 ⊆ E 3 1 7 0 (Pi.single 0 1) :=
  Dbox_subset_E (by norm_num) 1 7 Nat.one_pos (by
    intro h
    have := congrFun h 0
    simp at this) _ (fun q => by
    simp only [rad]
    split_ifs <;> norm_num) 2

end NonVacuity

end KNAll.Site.Corridor

end

/-! ## Co-import check -/

noncomputable section CoImportCheck

open KNAll.Site KNAll.Site.MacroExp KNAll.Site.Corridor KNAll.Site.TargetExt KNAll.Site.LeftImp
  KNAll.Site.LeftImp2 KNAll.Site.FRDom
open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

-- the level data instantiate the structure of `KN.TargetExtension`
example (d : ℕ) [NeZero d] (Sc : Scales d) (c : Site d) (j : ℕ) (hf : Fits Sc j)
    (Dom : Finset (Site d)) (hDDom : Dbox Sc c j ⊆ Dom) (o : Site d) (ho : o ∉ Dbox Sc c j)
    (T : Set (Site d)) (Gx : Site d → Set (KNAll.Site.SiteConfig (Site d)))
    (hGdet : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox Sc c j),
      DeterminedBy (Gx x) (↑(Obox Sc c j) : Set (Site d)))
    (hrelay : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Dbox Sc c j), ∀ ω ∈ Gx x,
      ∃ u ∈ face Sc c j x, u ∈ ω ∧ ∀ ω' ∈ Gx x,
        ω' ∩ (↑(Obox Sc c j \ Ibox Sc c j) : Set (Site d)) = ω ∩ ↑(Obox Sc c j \ Ibox Sc c j) →
          ω' ∈ TargetExt.toTarget (zdGraph d) (Obox Sc c j) T u) :
    LevelGeometry (zdGraph d) Dom o T :=
  toLevelGeometry Sc c j hf Dom hDDom o ho T Gx hGdet hrelay

-- the scales of a certificate, and the corridor of the exploration
example (d : ℕ) [NeZero d] (C : Certificate2 d) : Scales d := scalesOf C
example (d : ℕ) [NeZero d] (r t n : ℕ) (h : Tr d) : Finset (Site d) := region d r t n h

#print axioms KNAll.Site.Corridor.connWithin_ibox_of_allOpen
#print axioms KNAll.Site.Corridor.gate
#print axioms KNAll.Site.Corridor.cube_subset_shell
#print axioms KNAll.Site.Corridor.seed_subset_Dbox
#print axioms KNAll.Site.Corridor.seed_disjoint_Obox
#print axioms KNAll.Site.Corridor.connWithin_seed
#print axioms KNAll.Site.Corridor.selC_pairwiseDisjoint_seed
#print axioms KNAll.Site.Corridor.toLevelGeometry
#print axioms KNAll.Site.Corridor.Dbox_subset_E
#print axioms KNAll.Site.Corridor.fits_scalesOf

end CoImportCheck
