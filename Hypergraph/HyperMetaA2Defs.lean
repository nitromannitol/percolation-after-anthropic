import Hypergraph.HyperStarBridgeS

/-!
# Functionals for the hyperedge META-A2 induction

This is the labelled-hyperedge analogue of `CovTau/MetaA2Defs.lean`.  It only
defines the four finite functionals and proves their elementary order,
vanishing, and empty-source facts.  The Ahlswede--Daykin induction is deliberately
left to a later module.
-/

noncomputable section

namespace KNAll.Site.HyperMetaA2

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.AGBase KNAll.Site.CTOne KNAll.Site.CSHTwoA
open KNAll.Site.CSHTwoB KNAll.Site.CSHThree
open Percolation.Literature.BHK2006 (weight weight_nonneg sum_ind_nonneg sum_ind_mono)
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V E : Type*}

/-! ## Avoidance only sees the current world -/

/-- A singleton cluster in the induced model, when rooted in `U`, is contained
in `U`. -/
theorem rCluster_singleton_subset_world (H : Hypergraph V E) (U : Finset V)
    {v : V} (hv : v ∈ U) (omega : Set E) :
    rCluster H U ({v} : Set V) omega ⊆ (U : Set V) := by
  intro a ha
  have hva : (openHyperGraph H (omega ∩ labelsIn H U)).Reachable v a :=
    mem_rCluster_singleton.1 ha
  refine CSHThree.reach_stays (W := (U : Set V)) ?_ hva hv
  intro p q hp hpq
  obtain ⟨_, e, he, _, hqe⟩ := (openHyperGraph_adj_iff H _ p q).1 hpq
  exact he.2 q hqe

/-- Avoided sets agreeing inside `U` define the same singleton avoidance
event in the model induced on `U`. -/
theorem rAvoid_eq_of_agree (H : Hypergraph V E) (U : Finset V) {v : V}
    (hv : v ∈ U) {X Y : Set V}
    (hXY : ∀ a ∈ U, a ∈ X ↔ a ∈ Y) :
    rAvoid H U ({v} : Set V) X = rAvoid H U ({v} : Set V) Y := by
  ext omega
  simp only [mem_rAvoid]
  constructor
  · intro hX a haY haC
    exact hX a ((hXY a (rCluster_singleton_subset_world H U hv omega haC)).2 haY) haC
  · intro hY a haX haC
    exact hY a ((hXY a (rCluster_singleton_subset_world H U hv omega haC)).1 haX) haC

/-- In particular, an avoided set may be intersected with the current world. -/
theorem rAvoid_inter_world (H : Hypergraph V E) (U : Finset V) {v : V}
    (hv : v ∈ U) (X : Set V) :
    rAvoid H U ({v} : Set V) (X ∩ (U : Set V)) =
      rAvoid H U ({v} : Set V) X :=
  rAvoid_eq_of_agree H U hv fun _ haU =>
    ⟨fun h => h.1, fun h => ⟨h, haU⟩⟩

/-! ## The four functionals -/

variable [Fintype E]

/-- `E_A(N)`: the observer `o` reaches `v` while the cluster of `v` avoids
`A ∪ N`, in the world induced on `U`. -/
def Eav (H : Hypergraph V E) (w : E → ℝ) (U : Finset V) (A : Set V)
    (o v : V) (N : Set V) : ℝ :=
  ∑ omega : Set E, weight w omega *
    (AGBase.indMem o (rCluster H U ({v} : Set V) omega) *
      ind (rAvoid H U ({v} : Set V) (A ∪ N)) omega)

/-- `M_A(N)`: the cluster of `v` avoids `A ∪ N` in the world `U`. -/
def Mav (H : Hypergraph V E) (w : E → ℝ) (U : Finset V) (A : Set V)
    (v : V) (N : Set V) : ℝ :=
  ∑ omega : Set E, weight w omega *
    ind (rAvoid H U ({v} : Set V) (A ∪ N)) omega

/-- The avoided conditional observer probability in the world `U`. -/
def qav (H : Hypergraph V E) (w : E → ℝ) (U : Finset V) (A : Set V)
    (o v : V) : ℝ :=
  Eav H w U A o v ∅ / Mav H w U A v ∅

/-- `Y_F(N) = E[F(U \\ C_N); x ∉ C_N]`. -/
def Yw (H : Hypergraph V E) (w : E → ℝ) (U : Finset V) (x : V)
    (F : Finset V → ℝ) (N : Set V) : ℝ :=
  ∑ omega : Set E, weight w omega *
    (F (rest H U N omega) * ind (rAvoid H U ({x} : Set V) N) omega)

/-- `X_F(N) = E[q_A(U \\ C_N) F(U \\ C_N); x ∉ C_N]`. -/
def Xw (H : Hypergraph V E) (w : E → ℝ) (U : Finset V) (x : V)
    (A : Set V) (o v : V) (F : Finset V → ℝ) (N : Set V) : ℝ :=
  ∑ omega : Set E, weight w omega *
    (qav H w (rest H U N omega) A o v * F (rest H U N omega) *
      ind (rAvoid H U ({x} : Set V) N) omega)

/-! ## Elementary inequalities -/

section Props

variable {H : Hypergraph V E} {w : E → ℝ}
variable (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
include hw0 hw1

theorem Eav_nonneg (U : Finset V) (A : Set V) (o v : V) (N : Set V) :
    0 ≤ Eav H w U A o v N :=
  sum_ind_nonneg hw0 hw1 (fun _ => AGBase.indMem_nonneg _ _) _

theorem Mav_nonneg (U : Finset V) (A : Set V) (v : V) (N : Set V) :
    0 ≤ Mav H w U A v N :=
  Finset.sum_nonneg fun omega _ =>
    mul_nonneg (weight_nonneg hw0 hw1 omega) (ind_nonneg _ _)

theorem Eav_le_Mav (U : Finset V) (A : Set V) (o v : V) (N : Set V) :
    Eav H w U A o v N ≤ Mav H w U A v N := by
  apply Finset.sum_le_sum
  intro omega _
  refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg hw0 hw1 omega)
  have hi0 := ind_nonneg (rAvoid H U ({v} : Set V) (A ∪ N)) omega
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right
      (CTOne.indMem_le_one o (rCluster H U ({v} : Set V) omega)) hi0

theorem Eav_antitone (U : Finset V) (A : Set V) (o v : V)
    {N N' : Set V} (hNN' : N ⊆ N') :
    Eav H w U A o v N' ≤ Eav H w U A o v N := by
  unfold Eav
  exact sum_ind_mono hw0 hw1 (fun _ => AGBase.indMem_nonneg _ _)
    (rAvoid_antitone H U ({v} : Set V) (Set.union_subset_union_right A hNN'))

theorem Mav_antitone (U : Finset V) (A : Set V) (v : V)
    {N N' : Set V} (hNN' : N ⊆ N') :
    Mav H w U A v N' ≤ Mav H w U A v N := by
  have h := sum_ind_mono (w := w) hw0 hw1
    (h := fun _ : Set E => (1 : ℝ)) (fun _ => zero_le_one)
    (rAvoid_antitone H U ({v} : Set V)
      (Set.union_subset_union_right A hNN'))
  simpa only [Mav, one_mul] using h

theorem qav_nonneg (U : Finset V) (A : Set V) (o v : V) :
    0 ≤ qav H w U A o v :=
  div_nonneg (Eav_nonneg hw0 hw1 U A o v ∅)
    (Mav_nonneg hw0 hw1 U A v ∅)

theorem Yw_nonneg (U : Finset V) (x : V) {F : Finset V → ℝ}
    (hF0 : ∀ U', 0 ≤ F U') (N : Set V) :
    0 ≤ Yw H w U x F N :=
  sum_ind_nonneg hw0 hw1 (fun _ => hF0 _) _

theorem Xw_nonneg (U : Finset V) (x : V) (A : Set V) (o v : V)
    {F : Finset V → ℝ} (hF0 : ∀ U', 0 ≤ F U') (N : Set V) :
    0 ≤ Xw H w U x A o v F N :=
  sum_ind_nonneg hw0 hw1
    (fun omega => mul_nonneg (qav_nonneg hw0 hw1 _ A o v) (hF0 _)) _

end Props

/-! ## Vanishing and empty-source identities -/

section Basic

theorem Eav_eq_zero_of_mem (H : Hypergraph V E) (w : E → ℝ) (U : Finset V)
    (A : Set V) (o v : V) {N : Set V} (hv : v ∈ A ∪ N) :
    Eav H w U A o v N = 0 := by
  unfold Eav
  apply Finset.sum_eq_zero
  intro omega _
  have he : rAvoid H U ({v} : Set V) (A ∪ N) = ∅ :=
    rAvoid_eq_empty H U (Set.mem_singleton v) hv
  rw [he, ind_of_not_mem (Set.notMem_empty omega)]
  ring

theorem Yw_eq_zero_of_mem (H : Hypergraph V E) (w : E → ℝ) (U : Finset V)
    (x : V) (F : Finset V → ℝ) {N : Set V} (hx : x ∈ N) :
    Yw H w U x F N = 0 := by
  unfold Yw
  apply Finset.sum_eq_zero
  intro omega _
  have he : rAvoid H U ({x} : Set V) N = ∅ :=
    rAvoid_eq_empty H U (Set.mem_singleton x) hx
  rw [he, ind_of_not_mem (Set.notMem_empty omega)]
  ring

theorem Yw_eq_zero_of_not_mem (H : Hypergraph V E) (w : E → ℝ)
    {U : Finset V} (x : V) {v : V} {F : Finset V → ℝ}
    (hFv : ∀ U' : Finset V, v ∉ U' → F U' = 0) (hv : v ∉ U)
    (N : Set V) : Yw H w U x F N = 0 := by
  unfold Yw
  apply Finset.sum_eq_zero
  intro omega _
  rw [hFv _ (fun hv' => hv (rest_subset H U N omega hv'))]
  ring

theorem Xw_empty (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (U : Finset V) (x : V)
    (A : Set V) (o v : V) (F : Finset V → ℝ) :
    Xw H w U x A o v F ∅ = qav H w U A o v * F U := by
  unfold Xw
  have hind : ∀ omega : Set E,
      ind (rAvoid H U ({x} : Set V) (∅ : Set V)) omega = 1 := by
    intro omega
    rw [ind_of_mem]
    intro a ha
    exact ha.elim
  simp only [rest_empty, hind, mul_one]
  rw [← Finset.sum_mul, hm, one_mul]

end Basic

/-! ## Star decompositions -/

section Step

/-- Star decomposition of the pure world functional `Y_F`. -/
theorem Yw_step (H : Hypergraph V E) {U Z : Finset V} {x : V}
    (hx : x ∉ (Z : Set V)) {N : Set V} (hZN : (Z : Set V) ⊆ N)
    (w : E → ℝ) (hm : ∑ omega : Set E, weight w omega = 1)
    (F : Finset V → ℝ) :
    Yw H w U x F N =
      ∑ omega : Set E, weight w omega *
        Yw H w (U \ Z) x F ((N \ (Z : Set V)) ∪ rTrace H U Z omega) := by
  unfold Yw
  rw [CSHTwoB.setStep_sum H hx hZN w hm F]

/-- Star decomposition of the tilted world functional `X_F`. -/
theorem Xw_step (H : Hypergraph V E) {U Z : Finset V} {x : V}
    (hx : x ∉ (Z : Set V)) {N : Set V} (hZN : (Z : Set V) ⊆ N)
    (w : E → ℝ) (hm : ∑ omega : Set E, weight w omega = 1)
    (A : Set V) (o v : V) (F : Finset V → ℝ) :
    Xw H w U x A o v F N =
      ∑ omega : Set E, weight w omega *
        Xw H w (U \ Z) x A o v F
          ((N \ (Z : Set V)) ∪ rTrace H U Z omega) := by
  unfold Xw
  rw [CSHTwoB.setStep_sum H hx hZN w hm
    (fun U' => qav H w U' A o v * F U')]

/-- The two descriptions of the avoided set after deleting `Z` agree inside
the residual world. -/
theorem union_diff_agree (U Z : Finset V) (A N R : Set V) :
    ∀ a ∈ U \ Z,
      a ∈ ((A ∪ N) \ (Z : Set V)) ∪ R ↔
        a ∈ A ∪ ((N \ (Z : Set V)) ∪ R) := by
  intro a ha
  have haZ : a ∉ Z := (Finset.mem_sdiff.1 ha).2
  simp only [Set.mem_union, Set.mem_sdiff, Finset.mem_coe]
  tauto

/-- Star decomposition of the avoided observer mass `E_A`. -/
theorem Eav_step (H : Hypergraph V E) {U Z : Finset V} {v : V}
    (hvU : v ∈ U) (hvZ : v ∉ Z) {A N : Set V}
    (hZN : (Z : Set V) ⊆ N) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (o : V) :
    Eav H w U A o v N =
      ∑ omega : Set E, weight w omega *
        Eav H w (U \ Z) A o v
          ((N \ (Z : Set V)) ∪ rTrace H U Z omega) := by
  have hvUZ : v ∈ U \ Z := Finset.mem_sdiff.2 ⟨hvU, hvZ⟩
  have hSZ : ∀ y ∈ ({v} : Set V), y ∉ (Z : Set V) := by
    intro y hy
    simpa only [Set.mem_singleton_iff] using hy ▸ hvZ
  have hZW : (Z : Set V) ⊆ A ∪ N := hZN.trans Set.subset_union_right
  unfold Eav
  rw [avoid_step_sum hSZ hZW w hm
    (fun C => AGBase.indMem o C)]
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  unfold blockAvoidE
  apply Finset.sum_congr rfl
  intro eta _
  have hev := rAvoid_eq_of_agree H (U \ Z) hvUZ
    (union_diff_agree U Z A N (rTrace H U Z omega))
  rw [hev]

/-- Star decomposition of the avoided mass `M_A`. -/
theorem Mav_step (H : Hypergraph V E) {U Z : Finset V} {v : V}
    (hvU : v ∈ U) (hvZ : v ∉ Z) {A N : Set V}
    (hZN : (Z : Set V) ⊆ N) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) :
    Mav H w U A v N =
      ∑ omega : Set E, weight w omega *
        Mav H w (U \ Z) A v
          ((N \ (Z : Set V)) ∪ rTrace H U Z omega) := by
  have hvUZ : v ∈ U \ Z := Finset.mem_sdiff.2 ⟨hvU, hvZ⟩
  have hSZ : ∀ y ∈ ({v} : Set V), y ∉ (Z : Set V) := by
    intro y hy
    simpa only [Set.mem_singleton_iff] using hy ▸ hvZ
  have hZW : (Z : Set V) ⊆ A ∪ N := hZN.trans Set.subset_union_right
  unfold Mav
  have hstep := avoid_step_sum (H := H) (U := U) (Z := Z)
    (S := ({v} : Set V)) hSZ hZW w hm (fun _ => (1 : ℝ))
  simp only [one_mul] at hstep
  rw [hstep]
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  unfold blockAvoidE
  apply Finset.sum_congr rfl
  intro eta _
  have hev := rAvoid_eq_of_agree H (U \ Z) hvUZ
    (union_diff_agree U Z A N (rTrace H U Z omega))
  rw [hev]
  simp

/-- `E_A` only sees the part of its avoided set inside the current world. -/
theorem Eav_eq_inter (H : Hypergraph V E) (w : E → ℝ) (U : Finset V)
    (A : Set V) (o : V) {v : V} (hv : v ∈ U) (N : Set V) :
    Eav H w U A o v N =
      ∑ omega : Set E, weight w omega *
        (AGBase.indMem o (rCluster H U ({v} : Set V) omega) *
          ind (rAvoid H U ({v} : Set V) ((A ∪ N) ∩ (U : Set V))) omega) := by
  unfold Eav
  rw [rAvoid_inter_world H U hv (A ∪ N)]

/-- `M_A` only sees the part of its avoided set inside the current world. -/
theorem Mav_eq_inter (H : Hypergraph V E) (w : E → ℝ) (U : Finset V)
    (A : Set V) {v : V} (hv : v ∈ U) (N : Set V) :
    Mav H w U A v N =
      ∑ omega : Set E, weight w omega *
        ind (rAvoid H U ({v} : Set V) ((A ∪ N) ∩ (U : Set V))) omega := by
  unfold Mav
  rw [rAvoid_inter_world H U hv (A ∪ N)]

end Step

end KNAll.Site.HyperMetaA2

end

#print axioms KNAll.Site.HyperMetaA2.rAvoid_eq_of_agree
#print axioms KNAll.Site.HyperMetaA2.Eav_nonneg
#print axioms KNAll.Site.HyperMetaA2.Eav_le_Mav
#print axioms KNAll.Site.HyperMetaA2.Xw_empty
#print axioms KNAll.Site.HyperMetaA2.Eav_step
#print axioms KNAll.Site.HyperMetaA2.Mav_step
#print axioms KNAll.Site.HyperMetaA2.Eav_eq_inter
