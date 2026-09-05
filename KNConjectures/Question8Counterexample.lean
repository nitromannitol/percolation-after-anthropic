import KNConjectures.Question8Cases

/-!
# Kozma--Nitzan Question 8: the exact four-vertex counterexample

Vertices are `0 = o`, `1 = a₁`, `2 = a₂`, and `3 = b`.  The only positive-weight
pairs form the path `0--1--2--3`, with respective weights `s,q,t`.  We first prove all six
identities from equations (path1)--(path3), and then specialise to `(s,q,t) = (1,1/2,1)`.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

/-! ### The weighted path -/

abbrev q8e01 : Sym2 (Fin 4) := s(0, 1)
abbrev q8e12 : Sym2 (Fin 4) := s(1, 2)
abbrev q8e23 : Sym2 (Fin 4) := s(2, 3)

/-- The relay set `{a₁,a₂}`. -/
def q8PathA : Finset (Fin 4) := {1, 2}

/-- The three-edge path weighting, with every other pair assigned weight zero. -/
def q8PathWeight (s q t : unitInterval) : Sym2 (Fin 4) → unitInterval := fun e ↦
  if e = q8e01 then s else if e = q8e12 then q else if e = q8e23 then t else 0

private def q8PathEdges : Finset (Sym2 (Fin 4)) := {q8e01, q8e12, q8e23}

private theorem q8Path_support_subset (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) : ω ⊆ (↑q8PathEdges : Set (Sym2 (Fin 4))) := by
  intro e he
  by_contra hn
  change e ∉ q8PathEdges at hn
  have hn' : e ≠ q8e01 ∧ e ≠ q8e12 ∧ e ≠ q8e23 := by
    simpa [q8PathEdges] using hn
  have hw0 : q8PathWeight s q t e = 0 := by
    simp [q8PathWeight, hn'.1, hn'.2.1, hn'.2.2]
  exact hω.2 e hw0 he

/-- A colouring constant on edges is constant on every reachable component. -/
private theorem q8_color_invariant {V : Type*} (G : SimpleGraph V) (c : V → Bool)
    (hc : ∀ x y, G.Adj x y → c x = c y) {x y : V} (h : G.Reachable x y) : c x = c y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (hc _ _ hadj).trans ih

private theorem q8Path_color_adj (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) (c : Fin 4 → Bool)
    (h01 : q8e01 ∈ ω → c 0 = c 1) (h12 : q8e12 ∈ ω → c 1 = c 2)
    (h23 : q8e23 ∈ ω → c 2 = c 3) :
    ∀ x y, (openGraph ω).Adj x y → c x = c y := by
  intro x y hadj
  have hopen : s(x, y) ∈ ω := ((openGraph_adj ω x y).1 hadj).1
  have hp := q8Path_support_subset s q t ω hω hopen
  simp only [q8PathEdges, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
    mem_singleton_iff] at hp
  rcases hp with hp | hp | hp
  · rw [Sym2.eq_iff] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h01 hopen
    · have hopen' : q8e01 ∈ ω := by
        change s(0, 1) ∈ ω
        rw [Sym2.eq_swap]
        exact hopen
      exact (h01 hopen').symm
  · rw [Sym2.eq_iff] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h12 hopen
    · have hopen' : q8e12 ∈ ω := by
        change s(1, 2) ∈ ω
        rw [Sym2.eq_swap]
        exact hopen
      exact (h12 hopen').symm
  · rw [Sym2.eq_iff] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h23 hopen
    · have hopen' : q8e23 ∈ ω := by
        change s(2, 3) ∈ ω
        rw [Sym2.eq_swap]
        exact hopen
      exact (h23 hopen').symm

private def q8C0 : Fin 4 → Bool := fun v ↦ decide (v = 0)
private def q8C01 : Fin 4 → Bool := fun v ↦ decide (v = 0 ∨ v = 1)
private def q8C012 : Fin 4 → Bool := fun v ↦ decide (v ≠ 3)

private theorem q8Path_e01_of_reach (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) {x y : Fin 4}
    (hc : q8C0 x ≠ q8C0 y) (hxy : (openGraph ω).Reachable x y) : q8e01 ∈ ω := by
  by_contra h01
  exact hc (q8_color_invariant (openGraph ω) q8C0
    (q8Path_color_adj s q t ω hω q8C0 (fun h ↦ (h01 h).elim)
      (fun _ ↦ rfl) (fun _ ↦ rfl)) hxy)

private theorem q8Path_e12_of_reach (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) {x y : Fin 4}
    (hc : q8C01 x ≠ q8C01 y) (hxy : (openGraph ω).Reachable x y) : q8e12 ∈ ω := by
  by_contra h12
  exact hc (q8_color_invariant (openGraph ω) q8C01
    (q8Path_color_adj s q t ω hω q8C01 (fun _ ↦ rfl)
      (fun h ↦ (h12 h).elim) (fun _ ↦ rfl)) hxy)

private theorem q8Path_e23_of_reach (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) {x y : Fin 4}
    (hc : q8C012 x ≠ q8C012 y) (hxy : (openGraph ω).Reachable x y) : q8e23 ∈ ω := by
  by_contra h23
  exact hc (q8_color_invariant (openGraph ω) q8C012
    (q8Path_color_adj s q t ω hω q8C012 (fun _ ↦ rfl)
      (fun _ ↦ rfl) (fun h ↦ (h23 h).elim)) hxy)

private theorem q8Path_adj_reach (ω : BondConfig (Fin 4)) {x y : Fin 4}
    (h : s(x, y) ∈ ω) (hne : x ≠ y) : (openGraph ω).Reachable x y :=
  SimpleGraph.Adj.reachable ((openGraph_adj ω x y).2 ⟨h, hne⟩)

private theorem q8Path_U_iff (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) :
    ω ∈ U q8PathA 0 ↔ q8e01 ∈ ω := by
  constructor
  · intro hU
    obtain ⟨x, hx, hox⟩ := mem_iUnion₂.1 hU
    have hx' : x = 1 ∨ x = 2 := by simpa [q8PathA] using hx
    rcases hx' with rfl | rfl
    · exact q8Path_e01_of_reach s q t ω hω (by decide) hox
    · exact q8Path_e01_of_reach s q t ω hω (by decide) hox
  · intro h01
    exact mem_iUnion₂.2 ⟨1, by simp [q8PathA], q8Path_adj_reach ω h01 (by decide)⟩

private theorem q8Path_conn03_iff (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) :
    ω ∈ (openConn (0 : Fin 4) 3 : Set (BondConfig (Fin 4))) ↔
      q8e01 ∈ ω ∧ q8e12 ∈ ω ∧ q8e23 ∈ ω := by
  constructor
  · intro h
    exact ⟨q8Path_e01_of_reach s q t ω hω (by decide) h,
      q8Path_e12_of_reach s q t ω hω (by decide) h,
      q8Path_e23_of_reach s q t ω hω (by decide) h⟩
  · rintro ⟨h01, h12, h23⟩
    exact (q8Path_adj_reach ω h01 (by decide)).trans
      ((q8Path_adj_reach ω h12 (by decide)).trans
        (q8Path_adj_reach ω h23 (by decide)))

private theorem q8Path_conn13_iff (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) :
    ω ∈ (openConn (1 : Fin 4) 3 : Set (BondConfig (Fin 4))) ↔
      q8e12 ∈ ω ∧ q8e23 ∈ ω := by
  constructor
  · intro h
    exact ⟨q8Path_e12_of_reach s q t ω hω (by decide) h,
      q8Path_e23_of_reach s q t ω hω (by decide) h⟩
  · rintro ⟨h12, h23⟩
    exact (q8Path_adj_reach ω h12 (by decide)).trans
      (q8Path_adj_reach ω h23 (by decide))

private theorem q8Path_conn23_iff (s q t : unitInterval) (ω : BondConfig (Fin 4))
    (hω : ω ∈ q8Support (q8PathWeight s q t)) :
    ω ∈ (openConn (2 : Fin 4) 3 : Set (BondConfig (Fin 4))) ↔ q8e23 ∈ ω := by
  constructor
  · intro h
    exact q8Path_e23_of_reach s q t ω hω (by decide) h
  · intro h23
    exact q8Path_adj_reach ω h23 (by decide)

/-! ### Replacing connectivity events by their path cylinders -/

private theorem q8Path_real_eq_of_support (s q t : unitInterval)
    {E C : Set (BondConfig (Fin 4))}
    (h : ∀ ω, ω ∈ q8Support (q8PathWeight s q t) → (ω ∈ E ↔ ω ∈ C)) :
    (prodBernoulli (q8PathWeight s q t)).real E =
      (prodBernoulli (q8PathWeight s q t)).real C := by
  have hEC : E ∩ q8Support (q8PathWeight s q t) =
      C ∩ q8Support (q8PathWeight s q t) := by
    ext ω
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hE, hω⟩
      exact ⟨(h ω hω).1 hE, hω⟩
    · rintro ⟨hC, hω⟩
      exact ⟨(h ω hω).2 hC, hω⟩
  have hnull := q8Support_compl_null (q8PathWeight s q t)
  have hE := measure_inter_conull (μ := prodBernoulli (q8PathWeight s q t)) (s := E) hnull
  have hC := measure_inter_conull (μ := prodBernoulli (q8PathWeight s q t)) (s := C) hnull
  calc
    (prodBernoulli (q8PathWeight s q t)).real E =
        (prodBernoulli (q8PathWeight s q t)).real
          (E ∩ q8Support (q8PathWeight s q t)) := by
      simpa only [measureReal_def] using congrArg ENNReal.toReal hE |>.symm
    _ = (prodBernoulli (q8PathWeight s q t)).real
          (C ∩ q8Support (q8PathWeight s q t)) := by rw [hEC]
    _ = (prodBernoulli (q8PathWeight s q t)).real C := by
      simpa only [measureReal_def] using congrArg ENNReal.toReal hC

private theorem q8Path_prob_X (s q t : unitInterval) :
    (prodBernoulli (q8PathWeight s q t)).real
      {ω : BondConfig (Fin 4) | q8e01 ∈ ω} = (s : ℝ) := by
  rw [prodBernoulli_real_setOf_mem]
  simp [q8PathWeight]

private theorem q8Path_prob_XYZ (s q t : unitInterval) :
    (prodBernoulli (q8PathWeight s q t)).real
      {ω : BondConfig (Fin 4) | q8e01 ∈ ω ∧ q8e12 ∈ ω ∧ q8e23 ∈ ω} =
        (s : ℝ) * q * t := by
  have h := prodBernoulli_real_setOf_forall_iff (q8PathWeight s q t)
    ({q8e01, q8e12, q8e23} : Finset (Sym2 (Fin 4))) (fun _ ↦ True)
  have hset :
      {ω : BondConfig (Fin 4) | ∀ e ∈ ({q8e01, q8e12, q8e23} : Finset (Sym2 (Fin 4))),
        (e ∈ ω ↔ True)} =
      {ω : BondConfig (Fin 4) | q8e01 ∈ ω ∧ q8e12 ∈ ω ∧ q8e23 ∈ ω} := by
    ext ω
    simp
  rw [hset] at h
  simpa [q8PathWeight, mul_assoc] using h

private theorem q8Path_prob_XZ (s q t : unitInterval) :
    (prodBernoulli (q8PathWeight s q t)).real
      {ω : BondConfig (Fin 4) | q8e01 ∈ ω ∧ q8e23 ∈ ω} = (s : ℝ) * t := by
  have h := prodBernoulli_real_setOf_forall_iff (q8PathWeight s q t)
    ({q8e01, q8e23} : Finset (Sym2 (Fin 4))) (fun _ ↦ True)
  have hset :
      {ω : BondConfig (Fin 4) | ∀ e ∈ ({q8e01, q8e23} : Finset (Sym2 (Fin 4))),
        (e ∈ ω ↔ True)} =
      {ω : BondConfig (Fin 4) | q8e01 ∈ ω ∧ q8e23 ∈ ω} := by
    ext ω
    simp
  rw [hset] at h
  simpa [q8PathWeight, mul_assoc] using h

private theorem q8Path_prob_notXYZ (s q t : unitInterval) :
    (prodBernoulli (q8PathWeight s q t)).real
      {ω : BondConfig (Fin 4) | q8e01 ∉ ω ∧ q8e12 ∈ ω ∧ q8e23 ∈ ω} =
        (1 - (s : ℝ)) * q * t := by
  have h := prodBernoulli_real_setOf_forall_iff (q8PathWeight s q t)
    ({q8e01, q8e12, q8e23} : Finset (Sym2 (Fin 4))) (fun e ↦ e ≠ q8e01)
  have hset :
      {ω : BondConfig (Fin 4) | ∀ e ∈ ({q8e01, q8e12, q8e23} : Finset (Sym2 (Fin 4))),
        (e ∈ ω ↔ e ≠ q8e01)} =
      {ω : BondConfig (Fin 4) | q8e01 ∉ ω ∧ q8e12 ∈ ω ∧ q8e23 ∈ ω} := by
    ext ω
    simp
  rw [hset] at h
  simpa [q8PathWeight, mul_assoc] using h

private theorem q8Path_prob_notXZ (s q t : unitInterval) :
    (prodBernoulli (q8PathWeight s q t)).real
      {ω : BondConfig (Fin 4) | q8e01 ∉ ω ∧ q8e23 ∈ ω} =
        (1 - (s : ℝ)) * t := by
  have h := prodBernoulli_real_setOf_forall_iff (q8PathWeight s q t)
    ({q8e01, q8e23} : Finset (Sym2 (Fin 4))) (fun e ↦ e ≠ q8e01)
  have hset :
      {ω : BondConfig (Fin 4) | ∀ e ∈ ({q8e01, q8e23} : Finset (Sym2 (Fin 4))),
        (e ∈ ω ↔ e ≠ q8e01)} =
      {ω : BondConfig (Fin 4) | q8e01 ∉ ω ∧ q8e23 ∈ ω} := by
    ext ω
    simp
  rw [hset] at h
  simpa [q8PathWeight] using h

/-! ### The six identities (path1)--(path3) -/

/-- Equation (path1), first identity: `P(U) = s`. -/
theorem q8_path_U (s q t : unitInterval) :
    (prodBernoulli (q8PathWeight s q t)).real (U q8PathA 0) = (s : ℝ) := by
  calc
    _ = (prodBernoulli (q8PathWeight s q t)).real
        {ω : BondConfig (Fin 4) | q8e01 ∈ ω} :=
      q8Path_real_eq_of_support s q t (fun ω hω ↦ q8Path_U_iff s q t ω hω)
    _ = (s : ℝ) := q8Path_prob_X s q t

/-- Equation (path1), second identity: `R = sqt`. -/
theorem q8_path_R (s q t : unitInterval) :
    q8R (q8PathWeight s q t) q8PathA 0 3 = (s : ℝ) * q * t := by
  unfold q8R
  calc
    _ = (prodBernoulli (q8PathWeight s q t)).real
        {ω : BondConfig (Fin 4) | q8e01 ∈ ω ∧ q8e12 ∈ ω ∧ q8e23 ∈ ω} := by
      apply q8Path_real_eq_of_support s q t
      intro ω hω
      simp only [mem_inter_iff, mem_setOf_eq]
      rw [q8Path_conn03_iff s q t ω hω, q8Path_U_iff s q t ω hω]
      tauto
    _ = _ := q8Path_prob_XYZ s q t

/-- Equation (path2), first identity: `L_a₁ = sqt`. -/
theorem q8_path_L_a1 (s q t : unitInterval) :
    q8L (q8PathWeight s q t) q8PathA 0 3 1 = (s : ℝ) * q * t := by
  unfold q8L
  calc
    _ = (prodBernoulli (q8PathWeight s q t)).real
        {ω : BondConfig (Fin 4) | q8e01 ∈ ω ∧ q8e12 ∈ ω ∧ q8e23 ∈ ω} := by
      apply q8Path_real_eq_of_support s q t
      intro ω hω
      simp only [mem_inter_iff, mem_setOf_eq]
      rw [q8Path_conn13_iff s q t ω hω, q8Path_U_iff s q t ω hω]
      tauto
    _ = _ := q8Path_prob_XYZ s q t

/-- Equation (path2), second identity: `L_a₂ = st`. -/
theorem q8_path_L_a2 (s q t : unitInterval) :
    q8L (q8PathWeight s q t) q8PathA 0 3 2 = (s : ℝ) * t := by
  unfold q8L
  calc
    _ = (prodBernoulli (q8PathWeight s q t)).real
        {ω : BondConfig (Fin 4) | q8e01 ∈ ω ∧ q8e23 ∈ ω} := by
      apply q8Path_real_eq_of_support s q t
      intro ω hω
      simp only [mem_inter_iff, mem_setOf_eq]
      rw [q8Path_conn23_iff s q t ω hω, q8Path_U_iff s q t ω hω]
      tauto
    _ = _ := q8Path_prob_XZ s q t

/-- Equation (path3), first identity: `ρ_a₁ = (1-s)qt`. -/
theorem q8_path_score_a1 (s q t : unitInterval) :
    q8Score (q8PathWeight s q t) q8PathA 0 3 1 = (1 - (s : ℝ)) * q * t := by
  unfold q8Score
  calc
    _ = (prodBernoulli (q8PathWeight s q t)).real
        {ω : BondConfig (Fin 4) | q8e01 ∉ ω ∧ q8e12 ∈ ω ∧ q8e23 ∈ ω} := by
      apply q8Path_real_eq_of_support s q t
      intro ω hω
      simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq]
      rw [q8Path_conn13_iff s q t ω hω, q8Path_U_iff s q t ω hω]
      tauto
    _ = _ := q8Path_prob_notXYZ s q t

/-- Equation (path3), second identity: `ρ_a₂ = (1-s)t`. -/
theorem q8_path_score_a2 (s q t : unitInterval) :
    q8Score (q8PathWeight s q t) q8PathA 0 3 2 = (1 - (s : ℝ)) * t := by
  unfold q8Score
  calc
    _ = (prodBernoulli (q8PathWeight s q t)).real
        {ω : BondConfig (Fin 4) | q8e01 ∉ ω ∧ q8e23 ∈ ω} := by
      apply q8Path_real_eq_of_support s q t
      intro ω hω
      simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq]
      rw [q8Path_conn23_iff s q t ω hω, q8Path_U_iff s q t ω hω]
      tauto
    _ = _ := q8Path_prob_notXZ s q t

/-! ### The boundary counterexample -/

def q8Half : unitInterval := ⟨1 / 2, by norm_num⟩

/-- The every-minimiser reading of Question 8 is false. -/
theorem not_question8EveryMin : ¬ Question8EveryMin := by
  intro hQ8
  let w := q8PathWeight (1 : unitInterval) q8Half (1 : unitInterval)
  have hU : (prodBernoulli w).real (U q8PathA 0) = 1 := by
    simpa [w] using q8_path_U (1 : unitInterval) q8Half (1 : unitInterval)
  have hD : (prodBernoulli w).real (U q8PathA 0)ᶜ = 0 := by
    rw [measureReal_compl MeasurableSet.of_discrete, probReal_univ, hU]
    norm_num
  have hmin2 : IsQ8Min w q8PathA 0 3 2 :=
    q8_degenerate_allMin w q8PathA 0 3 hD 2 (by simp [q8PathA])
  have hbad := hQ8 4 w q8PathA 0 3 2 hmin2
  have hL : q8L w q8PathA 0 3 2 = 1 := by
    simpa [w, q8Half] using q8_path_L_a2 (1 : unitInterval) q8Half (1 : unitInterval)
  have hR : q8R w q8PathA 0 3 = (1 / 2 : ℝ) := by
    simpa [w, q8Half] using q8_path_R (1 : unitInterval) q8Half (1 : unitInterval)
  rw [hL, hR] at hbad
  norm_num at hbad

#print axioms q8Path_support_subset
#print axioms q8_color_invariant
#print axioms q8Path_color_adj
#print axioms q8Path_e01_of_reach
#print axioms q8Path_e12_of_reach
#print axioms q8Path_e23_of_reach
#print axioms q8Path_adj_reach
#print axioms q8Path_U_iff
#print axioms q8Path_conn03_iff
#print axioms q8Path_conn13_iff
#print axioms q8Path_conn23_iff
#print axioms q8Path_real_eq_of_support
#print axioms q8Path_prob_X
#print axioms q8Path_prob_XYZ
#print axioms q8Path_prob_XZ
#print axioms q8Path_prob_notXYZ
#print axioms q8Path_prob_notXZ

end KNAll

end

#print axioms KNAll.q8_path_U
#print axioms KNAll.q8_path_R
#print axioms KNAll.q8_path_L_a1
#print axioms KNAll.q8_path_L_a2
#print axioms KNAll.q8_path_score_a1
#print axioms KNAll.q8_path_score_a2
#print axioms KNAll.not_question8EveryMin
