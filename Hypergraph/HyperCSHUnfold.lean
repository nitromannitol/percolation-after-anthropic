import Hypergraph.HyperCSHHtwBridge

/-!
# The hyperedge CSH unfolding

This additive module ports the finite-sum part of the conditioned-slack
unfolding to independent labelled hyperedges.  The state exposed at a cluster
is always its set of vertices, while the fresh coordinates remain the original
labels.  In particular no identity between intersections of outside traces is
used here.
-/

noncomputable section

namespace KNAll.Site.HyperCSHUnfold

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open Percolation.Continuity
open KNAll.Site KNAll.Site.AGBase KNAll.Site.CTBase KNAll.Site.CTOne
open KNAll.Site.CSHDefs KNAll.Site.CSHTwoA KNAll.Site.CSHTwoB
open KNAll.Site.CSHThree KNAll.Site.HyperCSHHtw
open Percolation.Literature.BHK2006 (weight)
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem)
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ## Reachability after deleting an explored cluster -/

/-- If `s` avoids `X`, deleting every label meeting `C_X` preserves the
vertex cluster of `s`. -/
theorem hyperClusterSet_off_cut_of_avoid (H : Hypergraph V E)
    {omega : Set E} {X : Set V} {s : V}
    (h : omega ∈ avoidEvent H ({s} : Set V) X) :
    hyperClusterSet H (off H (hyperClusterSet H omega X) omega) ({s} : Set V) =
      hyperClusterSet H omega ({s} : Set V) := by
  apply Set.Subset.antisymm
  · exact hyperClusterSet_mono H _ (off_subset H _ _)
  · apply hyperClusterSet_off_subset H s X (Set.Subset.rfl)
    exact (mem_avoidEvent_singleton_iff H X s omega).1 h

/-- Reachability from a root avoiding `X` is unchanged in the world with
`C_X` deleted. -/
theorem reachable_off_cut_iff_of_avoid (H : Hypergraph V E)
    {omega : Set E} {X : Set V} {s : V}
    (h : omega ∈ avoidEvent H ({s} : Set V) X) (t : V) :
    (openHyperGraph H (off H (hyperClusterSet H omega X) omega)).Reachable s t ↔
      (openHyperGraph H omega).Reachable s t := by
  rw [← mem_hyperClusterSet_singleton, ← mem_hyperClusterSet_singleton,
    hyperClusterSet_off_cut_of_avoid H h]

/-- If `d` meets the cluster of `X`, it is isolated after deleting all labels
meeting that cluster. -/
theorem reachable_off_cut_iff_of_dead (H : Hypergraph V E)
    {omega eta : Set E} {X : Set V} {d : V}
    (h : omega ∉ avoidEvent H ({d} : Set V) X) (t : V) :
    (openHyperGraph H (off H (hyperClusterSet H omega X) eta)).Reachable t d ↔ t = d := by
  have hdC : d ∈ hyperClusterSet H omega X := by
    rw [mem_avoidEvent_singleton_iff] at h
    push Not at h
    obtain ⟨x, hx, hdx⟩ := h
    exact ⟨x, hx, hdx.symm⟩
  constructor
  · intro htd
    by_contra hne
    exact not_reachable_off_of_mem H hdC (fun hdt ↦ hne hdt.symm) htd.symm
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

/-- If `d` avoids `Y`, deleting the labels meeting `C_d` preserves the
cluster, and hence the cut, of `Y`. -/
theorem hyperClusterSet_off_singleton_of_avoid (H : Hypergraph V E)
    {zeta : Set E} {Y : Set V} {d : V}
    (h : zeta ∈ avoidEvent H ({d} : Set V) Y) :
    hyperClusterSet H (off H (hyperClusterSet H zeta ({d} : Set V)) zeta) Y =
      hyperClusterSet H zeta Y := by
  apply Set.Subset.antisymm
  · exact hyperClusterSet_mono H Y (off_subset H _ _)
  · rintro u ⟨y, hyY, hyu⟩
    have hyd : zeta ∈ avoidEvent H ({y} : Set V) ({d} : Set V) := by
      refine (mem_avoidEvent_singleton_iff H ({d} : Set V) y zeta).2 ?_
      intro d' hd' hyd'
      rw [Set.mem_singleton_iff] at hd'
      subst d'
      exact (mem_avoidEvent_singleton_iff H Y d zeta).1 h y hyY hyd'.symm
    have hcl := hyperClusterSet_off_cut_of_avoid H hyd
    exact ⟨y, hyY, by
      rw [← mem_hyperClusterSet_singleton, hcl]
      exact ⟨y, rfl, hyu⟩⟩

theorem cut_off_singleton_of_avoid (H : Hypergraph V E)
    {zeta : Set E} {Y : Set V} {d : V}
    (h : zeta ∈ avoidEvent H ({d} : Set V) Y) :
    cut H Y (off H (hyperClusterSet H zeta ({d} : Set V)) zeta) = cut H Y zeta := by
  unfold cut
  rw [hyperClusterSet_off_singleton_of_avoid H h]

/-! ## World covariance -/

def wcovOff (H : Hypergraph V E) (w : E → ℝ) (Y : Set V)
    (phi psi : Set E → ℝ) (omega : Set E) : ℝ :=
  wmeanOff H w Y (fun beta ↦ phi beta * psi beta) omega -
    wmeanOff H w Y phi omega * wmeanOff H w Y psi omega

theorem wcovOff_eq_sum (H : Hypergraph V E) (w : E → ℝ) (Y : Set V)
    (phi psi : Set E → ℝ) (omega : Set E) :
    wcovOff H w Y phi psi omega =
      ∑ eta, weight w eta *
        ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) *
          psi (eta \ cut H Y omega)) := by
  have he : ∀ eta, weight w eta *
      ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) *
        psi (eta \ cut H Y omega)) =
      weight w eta * (phi (eta \ cut H Y omega) * psi (eta \ cut H Y omega)) -
        wmeanOff H w Y phi omega *
          (weight w eta * psi (eta \ cut H Y omega)) := by
    intro eta
    ring
  rw [Finset.sum_congr rfl (fun eta _ ↦ he eta), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rfl

theorem wcovOff_zero_right (H : Hypergraph V E) (w : E → ℝ) (Y : Set V)
    (phi : Set E → ℝ) (omega : Set E) :
    wcovOff H w Y phi (fun _ ↦ 0) omega = 0 := by
  rw [wcovOff_eq_sum]
  simp

theorem wcovOff_add_right (H : Hypergraph V E) (w : E → ℝ) (Y : Set V)
    (phi psi₁ psi₂ : Set E → ℝ) (omega : Set E) :
    wcovOff H w Y phi (fun zeta ↦ psi₁ zeta + psi₂ zeta) omega =
      wcovOff H w Y phi psi₁ omega + wcovOff H w Y phi psi₂ omega := by
  simp only [wcovOff_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun eta _ ↦ by ring

theorem wcovOff_finset_sum (H : Hypergraph V E) (w : E → ℝ) (Y : Set V)
    (phi : Set E → ℝ) {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (psi : ι → Set E → ℝ) (omega : Set E) :
    ∑ i ∈ s, a i * wcovOff H w Y phi (psi i) omega =
      wcovOff H w Y phi (fun zeta ↦ ∑ i ∈ s, a i * psi i zeta) omega := by
  simp only [wcovOff_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun eta _ ↦ ?_
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem wcovOff_affine (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (Y : Set V)
    (phi psi₁ psi₂ chi₁ chi₂ : Set E → ℝ) (p K : ℝ) (omega : Set E) :
    wcovOff H w Y phi
        (fun zeta ↦ (psi₁ zeta - p * psi₂ zeta) -
          (chi₁ zeta - p * chi₂ zeta) + K) omega =
      wcovOff H w Y phi psi₁ omega - p * wcovOff H w Y phi psi₂ omega -
        wcovOff H w Y phi chi₁ omega + p * wcovOff H w Y phi chi₂ omega := by
  simp only [wcovOff_eq_sum]
  have hzero : ∑ eta, weight w eta *
      ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) * K) = 0 := by
    have he : ∀ eta, weight w eta *
        ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) * K) =
      K * (weight w eta * phi (eta \ cut H Y omega)) -
        K * wmeanOff H w Y phi omega * weight w eta := by
      intro eta
      ring
    rw [Finset.sum_congr rfl (fun eta _ ↦ he eta), Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hm]
    unfold wmeanOff
    ring
  have he : ∀ eta, weight w eta *
      ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) *
        ((psi₁ (eta \ cut H Y omega) - p * psi₂ (eta \ cut H Y omega)) -
          (chi₁ (eta \ cut H Y omega) - p * chi₂ (eta \ cut H Y omega)) + K)) =
      weight w eta * ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) *
        psi₁ (eta \ cut H Y omega)) -
      p * (weight w eta * ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) *
        psi₂ (eta \ cut H Y omega))) -
      weight w eta * ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) *
        chi₁ (eta \ cut H Y omega)) +
      p * (weight w eta * ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) *
        chi₂ (eta \ cut H Y omega))) +
      weight w eta * ((phi (eta \ cut H Y omega) - wmeanOff H w Y phi omega) * K) := by
    intro eta
    ring
  rw [Finset.sum_congr rfl (fun eta _ ↦ he eta), Finset.sum_add_distrib,
    hzero, add_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## Measure/finite-sum dictionary -/

theorem setIntegral_eq_sum_ind (H : Hypergraph V E) (A : Set (Set E))
    (f : Set E → ℝ) :
    ∫ omega in A, f omega ∂(prodBernoulli H.prob) =
      ∑ omega, weight (fun e ↦ (H.prob e : ℝ)) omega * (ind A omega * f omega) := by
  rw [← integral_indicator (measurableSet_of_fintype A),
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun omega _ ↦ ?_
  by_cases h : omega ∈ A
  · rw [Set.indicator_of_mem h, ind_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, ind_of_not_mem h, zero_mul, mul_zero]

theorem integral_world_eq_wmeanOff (H : Hypergraph V E) (Y : Set V)
    (omega : Set E) (F : Set E → ℝ) :
    ∫ eta, F eta ∂(prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob) =
      wmeanOff H (fun e ↦ (H.prob e : ℝ)) Y F omega := by
  rw [← delE_cut_eq_integral_deleteHyper H Y omega F]
  unfold delE wmeanOff
  rw [Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]

theorem world_cov_eq_wcovOff (H : Hypergraph V E) (Y : Set V)
    (omega : Set E) (G : Set E → ℝ) (A : Set (Set E)) :
    (∫ eta in A, G eta
        ∂(prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob)) -
      (∫ eta, G eta
        ∂(prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob)) *
        (prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob).real A =
      wcovOff H (fun e ↦ (H.prob e : ℝ)) Y G (ind A) omega := by
  rw [← integral_indicator (measurableSet_of_fintype A),
    ← integral_indicator_one (measurableSet_of_fintype A),
    integral_world_eq_wmeanOff, integral_world_eq_wmeanOff,
    integral_world_eq_wmeanOff]
  unfold wcovOff
  have h1 : A.indicator G = fun beta ↦ G beta * ind A beta := by
    funext beta
    by_cases hb : beta ∈ A
    · rw [Set.indicator_of_mem hb, ind_of_mem hb, mul_one]
    · rw [Set.indicator_of_notMem hb, ind_of_not_mem hb, mul_zero]
  have h2 : A.indicator (1 : Set E → ℝ) = ind A := by
    funext beta
    by_cases hb : beta ∈ A
    · rw [Set.indicator_of_mem hb, ind_of_mem hb, Pi.one_apply]
    · rw [Set.indicator_of_notMem hb, ind_of_not_mem hb]
  rw [h1, h2]

/-! ## Markov merge at the cluster of the avoided set -/

/-- Merge the outer configuration and the fresh world at `C_Y`.  This is the
label-coordinate version of the first finite Fubini step in Lemma U. -/
theorem markov_merge_Y (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (x : V) (Y : Set V)
    (g : Set V → ℝ) (psi : Set E → ℝ) :
    ∑ omega, weight w omega * (ind (avoidEvent H ({x} : Set V) Y) omega *
        ∑ eta, weight w eta *
          ((g (hyperClusterSet H (eta \ cut H Y omega) ({x} : Set V)) -
            wmeanOff H w Y
              (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) omega) *
            psi (eta \ cut H Y omega))) =
      ∑ zeta, weight w zeta * (ind (avoidEvent H ({x} : Set V) Y) zeta *
        ((g (hyperClusterSet H zeta ({x} : Set V)) -
          wmeanOff H w Y
            (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) zeta) *
          psi (zeta \ cut H Y zeta))) := by
  let K : Set V → Set E → ℝ := fun W beta ↦
    (if x ∈ W then 0 else 1) *
      ((g (hyperClusterSet H beta ({x} : Set V)) -
        ∑ eta', weight w eta' *
          g (hyperClusterSet H (eta' \ labelsMeeting H W) ({x} : Set V))) *
        psi beta)
  have hind : ∀ zeta : Set E,
      ind (avoidEvent H ({x} : Set V) Y) zeta =
        if x ∈ hyperClusterSet H zeta Y then 0 else 1 := by
    intro zeta
    exact ind_avoidEv_eq_ite H x Y zeta
  have hmean : ∀ zeta : Set E,
      wmeanOff H w Y
          (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) zeta =
        ∑ eta', weight w eta' *
          g (hyperClusterSet H
            (eta' \ labelsMeeting H (hyperClusterSet H zeta Y)) ({x} : Set V)) := by
    intro zeta
    rfl
  have key := set_sum_cond_sdiff_off_empty H w hm Y K
  have hR : ∀ omega, weight w omega *
      ∑ eta, weight w eta *
        K (hyperClusterSet H omega Y) (eta \ cut H Y omega) =
      weight w omega * (ind (avoidEvent H ({x} : Set V) Y) omega *
        ∑ eta, weight w eta *
          ((g (hyperClusterSet H (eta \ cut H Y omega) ({x} : Set V)) -
            wmeanOff H w Y
              (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) omega) *
            psi (eta \ cut H Y omega))) := by
    intro omega
    rw [hind, hmean]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun eta _ ↦ ?_
    change weight w eta *
      ((if x ∈ hyperClusterSet H omega Y then 0 else 1) *
        ((g (hyperClusterSet H (eta \ cut H Y omega) ({x} : Set V)) -
          ∑ eta', weight w eta' *
            g (hyperClusterSet H
              (eta' \ labelsMeeting H (hyperClusterSet H omega Y)) ({x} : Set V))) *
          psi (eta \ cut H Y omega))) = _
    ring
  have hL : ∀ zeta, weight w zeta *
      K (hyperClusterSet H zeta Y) (zeta \ cut H Y zeta) =
      weight w zeta * (ind (avoidEvent H ({x} : Set V) Y) zeta *
        ((g (hyperClusterSet H zeta ({x} : Set V)) -
          wmeanOff H w Y
            (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) zeta) *
          psi (zeta \ cut H Y zeta))) := by
    intro zeta
    rw [hind, hmean]
    by_cases hx : x ∈ hyperClusterSet H zeta Y
    · simp [K, hx]
    · have hav : zeta ∈ avoidEvent H ({x} : Set V) Y := by
        exact (mem_avoidEvent_singleton_iff H Y x zeta).2
          (fun y hy hxy ↦ hx ⟨y, hy, hxy.symm⟩)
      have hcluster := hyperClusterSet_off_cut_of_avoid H hav
      change weight w zeta *
        ((if x ∈ hyperClusterSet H zeta Y then 0 else 1) *
          ((g (hyperClusterSet H (zeta \ cut H Y zeta) ({x} : Set V)) -
            ∑ eta', weight w eta' *
              g (hyperClusterSet H
                (eta' \ labelsMeeting H (hyperClusterSet H zeta Y)) ({x} : Set V))) *
            psi (zeta \ cut H Y zeta))) = _
      rw [if_neg hx]
      rw [show zeta \ cut H Y zeta =
        off H (hyperClusterSet H zeta Y) zeta from rfl, hcluster]
  calc
    _ = ∑ omega, weight w omega *
        ∑ eta, weight w eta *
          K (hyperClusterSet H omega Y) (eta \ cut H Y omega) :=
      Finset.sum_congr rfl fun omega _ ↦ (hR omega).symm
    _ = ∑ zeta, weight w zeta *
        K (hyperClusterSet H zeta Y) (zeta \ cut H Y zeta) := key.symm
    _ = _ := Finset.sum_congr rfl fun zeta _ ↦ hL zeta

/-- A function of `C_Y` is orthogonal to the centered fresh-world residual. -/
theorem residual_orthogonal (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (x : V) (Y : Set V)
    (g : Set V → ℝ) (kappa : Set V → ℝ) :
    ∑ zeta, weight w zeta *
      (ind (avoidEvent H ({x} : Set V) Y) zeta *
        (kappa (hyperClusterSet H zeta Y) *
          (g (hyperClusterSet H zeta ({x} : Set V)) -
            wmeanOff H w Y
              (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) zeta))) = 0 := by
  let K : Set V → Set E → ℝ := fun W beta ↦
    (if x ∈ W then 0 else 1) *
      (kappa W *
        (g (hyperClusterSet H beta ({x} : Set V)) -
          ∑ eta', weight w eta' *
            g (hyperClusterSet H (eta' \ labelsMeeting H W) ({x} : Set V))))
  have hind : ∀ zeta : Set E,
      ind (avoidEvent H ({x} : Set V) Y) zeta =
        if x ∈ hyperClusterSet H zeta Y then 0 else 1 :=
    fun zeta ↦ ind_avoidEv_eq_ite H x Y zeta
  have hmean : ∀ zeta : Set E,
      wmeanOff H w Y
          (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) zeta =
        ∑ eta', weight w eta' *
          g (hyperClusterSet H
            (eta' \ labelsMeeting H (hyperClusterSet H zeta Y)) ({x} : Set V)) :=
    fun _ ↦ rfl
  have key := set_sum_cond_sdiff_off_empty H w hm Y K
  have hL : ∀ zeta, weight w zeta *
      K (hyperClusterSet H zeta Y) (zeta \ cut H Y zeta) =
      weight w zeta *
        (ind (avoidEvent H ({x} : Set V) Y) zeta *
          (kappa (hyperClusterSet H zeta Y) *
            (g (hyperClusterSet H zeta ({x} : Set V)) -
              wmeanOff H w Y
                (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) zeta))) := by
    intro zeta
    rw [hind, hmean]
    by_cases hx : x ∈ hyperClusterSet H zeta Y
    · simp [K, hx]
    · have hav : zeta ∈ avoidEvent H ({x} : Set V) Y :=
        (mem_avoidEvent_singleton_iff H Y x zeta).2
          (fun y hy hxy ↦ hx ⟨y, hy, hxy.symm⟩)
      have hc := hyperClusterSet_off_cut_of_avoid H hav
      change weight w zeta *
        ((if x ∈ hyperClusterSet H zeta Y then 0 else 1) *
          (kappa (hyperClusterSet H zeta Y) *
            (g (hyperClusterSet H (off H (hyperClusterSet H zeta Y) zeta)
                ({x} : Set V)) -
              ∑ eta', weight w eta' *
                g (hyperClusterSet H
                  (eta' \ labelsMeeting H (hyperClusterSet H zeta Y))
                  ({x} : Set V))))) = _
      rw [if_neg hx, hc]
  have hR : ∀ omega, weight w omega *
      ∑ eta, weight w eta *
        K (hyperClusterSet H omega Y) (eta \ cut H Y omega) = 0 := by
    intro omega
    have he : ∀ eta, weight w eta *
        K (hyperClusterSet H omega Y) (eta \ cut H Y omega) =
      ((if x ∈ hyperClusterSet H omega Y then 0 else 1) *
        kappa (hyperClusterSet H omega Y)) *
          (weight w eta *
            g (hyperClusterSet H (eta \ cut H Y omega) ({x} : Set V))) -
      ((if x ∈ hyperClusterSet H omega Y then 0 else 1) *
        kappa (hyperClusterSet H omega Y) *
          ∑ eta', weight w eta' *
            g (hyperClusterSet H
              (eta' \ labelsMeeting H (hyperClusterSet H omega Y))
              ({x} : Set V))) * weight w eta := by
      intro eta
      change _
      ring
    rw [Finset.sum_congr rfl (fun eta _ ↦ he eta),
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
    rw [show cut H Y omega = labelsMeeting H (hyperClusterSet H omega Y) from rfl]
    ring
  calc
    _ = ∑ zeta, weight w zeta *
        K (hyperClusterSet H zeta Y) (zeta \ cut H Y zeta) :=
      Finset.sum_congr rfl fun zeta _ ↦ (hL zeta).symm
    _ = ∑ omega, weight w omega *
        ∑ eta, weight w eta *
          K (hyperClusterSet H omega Y) (eta \ cut H Y omega) := key
    _ = 0 := Finset.sum_eq_zero fun omega _ ↦ hR omega

/-! ## One decoy -/

theorem chi_reachable_eq_ind (H : Hypergraph V E) (zeta : Set E)
    (w' d : V) :
    CSH.chi (openHyperGraph H zeta).Reachable w' d =
      ind (hyperConn H d w') zeta := by
  unfold CSH.chi
  by_cases h : (openHyperGraph H zeta).Reachable w' d
  · rw [if_pos h, ind_of_mem]
    exact h.symm
  · rw [if_neg h, ind_of_not_mem]
    exact fun h' ↦ h h'.symm

theorem av_reachable_eq_ind (H : Hypergraph V E) (zeta : Set E)
    (S : Set V) (d : V) :
    CSH.av (openHyperGraph H zeta).Reachable S d =
      ind (avoidEvent H ({d} : Set V) S) zeta := by
  unfold CSH.av
  by_cases h : ∀ s ∈ S, ¬ (openHyperGraph H zeta).Reachable d s
  · rw [if_pos h, ind_of_mem]
    exact (mem_avoidEvent_singleton_iff H S d zeta).2 h
  · rw [if_neg h, ind_of_not_mem]
    exact fun hz ↦ h ((mem_avoidEvent_singleton_iff H S d zeta).1 hz)

theorem jn_reachable_eq_ind (H : Hypergraph V E) (zeta : Set E)
    (S : Set V) (u : V) :
    CSH.jn (openHyperGraph H zeta).Reachable S u = ind (connTo H u S) zeta := by
  unfold CSH.jn
  by_cases h : ∃ s ∈ S, (openHyperGraph H zeta).Reachable u s
  · rw [if_pos h, ind_of_mem (show zeta ∈ connTo H u S from h)]
  · rw [if_neg h, ind_of_not_mem (show zeta ∉ connTo H u S from h)]

theorem world_term_alive (H : Hypergraph V E) {zeta : Set E}
    {Y : Set V} {d : V} (h : zeta ∈ avoidEvent H ({d} : Set V) Y)
    (S : Set V) (L' : List (V × (V → ℝ))) (c : V → ℝ) (u : V) :
    CSH.av (openHyperGraph H (zeta \ cut H Y zeta)).Reachable S d *
        CSH.slForm L'
          (fun w' ↦ CSH.chi
            (openHyperGraph H (zeta \ cut H Y zeta)).Reachable w' d - c w') u =
      ind (avoidEvent H ({d} : Set V) S) zeta *
        CSH.slForm L' (fun w' ↦ ind (hyperConn H d w') zeta - c w') u := by
  have hreach : ∀ a,
      (openHyperGraph H (zeta \ cut H Y zeta)).Reachable a d ↔
        (openHyperGraph H zeta).Reachable a d := by
    intro a
    have hh := reachable_off_cut_iff_of_avoid H h a
    change (openHyperGraph H
      (off H (hyperClusterSet H zeta Y) zeta)).Reachable a d ↔ _
    simpa only [SimpleGraph.reachable_comm] using hh
  have hfun :
      (fun w' ↦ CSH.chi
        (openHyperGraph H (zeta \ cut H Y zeta)).Reachable w' d - c w') =
      fun w' ↦ ind (hyperConn H d w') zeta - c w' := by
    funext w'
    rw [← chi_reachable_eq_ind H zeta w' d]
    unfold CSH.chi
    rw [show (openHyperGraph H (zeta \ cut H Y zeta)).Reachable w' d =
      (openHyperGraph H zeta).Reachable w' d from propext (hreach w')]
  have hav : CSH.av
      (openHyperGraph H (zeta \ cut H Y zeta)).Reachable S d =
      ind (avoidEvent H ({d} : Set V) S) zeta := by
    rw [← av_reachable_eq_ind H zeta S d]
    unfold CSH.av
    have heq : (∀ s ∈ S,
        ¬ (openHyperGraph H (zeta \ cut H Y zeta)).Reachable d s) ↔
      ∀ s ∈ S, ¬ (openHyperGraph H zeta).Reachable d s :=
      forall₂_congr fun s _ ↦ not_congr (reachable_off_cut_iff_of_avoid H h s)
    rw [show (∀ s ∈ S,
      ¬ (openHyperGraph H (zeta \ cut H Y zeta)).Reachable d s) =
        (∀ s ∈ S, ¬ (openHyperGraph H zeta).Reachable d s) from propext heq]
  rw [hfun, hav]

theorem world_term_dead (H : Hypergraph V E) {zeta : Set E}
    {Y : Set V} {d : V} (h : zeta ∉ avoidEvent H ({d} : Set V) Y)
    {S : Set V} (hdS : d ∉ S) (L' : List (V × (V → ℝ)))
    (hL' : ∀ dc ∈ L', dc.1 ≠ d) (c : V → ℝ) {u : V} (hu : u ≠ d) :
    CSH.av (openHyperGraph H (zeta \ cut H Y zeta)).Reachable S d *
        CSH.slForm L'
          (fun w' ↦ CSH.chi
            (openHyperGraph H (zeta \ cut H Y zeta)).Reachable w' d - c w') u =
      - CSH.slForm L' c u := by
  have hreach : ∀ a,
      (openHyperGraph H (zeta \ cut H Y zeta)).Reachable a d ↔ a = d :=
    fun a ↦ reachable_off_cut_iff_of_dead H h a
  have hav : CSH.av
      (openHyperGraph H (zeta \ cut H Y zeta)).Reachable S d = 1 := by
    unfold CSH.av
    rw [if_pos]
    intro s hs hr
    rw [SimpleGraph.reachable_comm, hreach s] at hr
    exact hdS (hr ▸ hs)
  have hchi : ∀ w', w' ≠ d →
      CSH.chi (openHyperGraph H (zeta \ cut H Y zeta)).Reachable w' d = 0 := by
    intro w' hw'
    unfold CSH.chi
    rw [if_neg (fun hr ↦ hw' ((hreach w').1 hr))]
  have hsl : CSH.slForm L'
      (fun w' ↦ CSH.chi
        (openHyperGraph H (zeta \ cut H Y zeta)).Reachable w' d - c w') u =
      CSH.slForm L' (fun w' ↦ (-1 : ℝ) • c w') u := by
    refine CSH.slForm_congr L' ?_ fun dc hdc ↦ ?_
    · rw [hchi u hu]
      simp
    · rw [hchi dc.1 (hL' dc hdc)]
      simp
  rw [hav, one_mul, hsl,
    show (fun w' ↦ (-1 : ℝ) • c w') = (-1 : ℝ) • c from rfl,
    CSH.slForm_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The centered residual appearing after the first Markov merge. -/
def resid (H : Hypergraph V E) (w : E → ℝ) (x : V) (Y : Set V)
    (g : Set V → ℝ) (zeta : Set E) : ℝ :=
  ind (avoidEvent H ({x} : Set V) Y) zeta *
    (g (hyperClusterSet H zeta ({x} : Set V)) -
      wmeanOff H w Y
        (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) zeta)

/-- The Lemma-Phi functional evaluated at the cluster of a decoy. -/
def phiS (H : Hypergraph V E) (w : E → ℝ) (x : V) (Y : Set V)
    (g : Set V → ℝ) (d : V) (zeta : Set E) : ℝ :=
  ∑ eta, weight w eta *
    phiIntegrand H x Y (hyperClusterSet H zeta ({d} : Set V)) g eta

theorem resid_off_singleton (H : Hypergraph V E) (w : E → ℝ)
    {x : V} {Y : Set V} (g : Set V → ℝ) {d : V} {zeta : Set E}
    (h : zeta ∈ avoidEvent H ({d} : Set V) (insert x Y)) :
    resid H w x Y g
        (off H (hyperClusterSet H zeta ({d} : Set V)) zeta) =
      resid H w x Y g zeta := by
  have hdY : zeta ∈ avoidEvent H ({d} : Set V) Y :=
    (mem_avoidEvent_singleton_iff H Y d zeta).2 fun y hy ↦
      (mem_avoidEvent_singleton_iff H (insert x Y) d zeta).1 h y
        (Set.mem_insert_of_mem x hy)
  have hxd : zeta ∈ avoidEvent H ({x} : Set V) ({d} : Set V) :=
    (mem_avoidEvent_singleton_iff H ({d} : Set V) x zeta).2 fun d' hd' hxd' ↦ by
      rw [Set.mem_singleton_iff] at hd'
      subst d'
      exact (mem_avoidEvent_singleton_iff H (insert x Y) d zeta).1 h x
        (Set.mem_insert x Y) hxd'.symm
  unfold resid
  have hcX := hyperClusterSet_off_cut_of_avoid H hxd
  have hcY := cut_off_singleton_of_avoid H hdY
  have hi : ind (avoidEvent H ({x} : Set V) Y)
      (off H (hyperClusterSet H zeta ({d} : Set V)) zeta) =
      ind (avoidEvent H ({x} : Set V) Y) zeta := by
    by_cases hx : zeta ∈ avoidEvent H ({x} : Set V) Y
    · rw [ind_of_mem hx, ind_of_mem]
      exact (mem_avoidEvent_singleton_iff H Y x _).2 fun y hy hxy ↦
        (mem_avoidEvent_singleton_iff H Y x zeta).1 hx y hy
          ((reachable_off_cut_iff_of_avoid H hxd y).1 hxy)
    · rw [ind_of_not_mem hx, ind_of_not_mem]
      intro hx'
      apply hx
      exact (mem_avoidEvent_singleton_iff H Y x zeta).2 fun y hy hxy ↦
        (mem_avoidEvent_singleton_iff H Y x _).1 hx' y hy
          ((reachable_off_cut_iff_of_avoid H hxd y).2 hxy)
  rw [hi, hcX]
  congr 2
  unfold wmeanOff
  rw [hcY]

theorem sum_resid_world_singleton (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (x : V) (Y : Set V)
    (g : Set V → ℝ) (d : V) (zeta : Set E) :
    ∑ eta, weight w eta *
        resid H w x Y g
          (off H (hyperClusterSet H zeta ({d} : Set V)) eta) =
      - phiS H w x Y g d zeta := by
  unfold phiS
  rw [sum_phiIntegrand_eq H w hm x Y
    (hyperClusterSet H zeta ({d} : Set V)) g, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun eta _ ↦ ?_
  unfold resid
  rw [avoidEv_eq]
  simp only [off]
  ring

theorem ind_avoid_eq_ite_cluster (H : Hypergraph V E) (d : V)
    (A : Set V) (zeta : Set E) :
    ind (avoidEvent H ({d} : Set V) A) zeta =
      if Disjoint (hyperClusterSet H zeta ({d} : Set V)) A then 1 else 0 := by
  by_cases h : Disjoint (hyperClusterSet H zeta ({d} : Set V)) A
  · rw [if_pos h, ind_of_mem]
    exact h
  · rw [if_neg h, ind_of_not_mem]
    exact h

theorem ind_hyperConn_eq_ite_cluster (H : Hypergraph V E) (d w' : V)
    (zeta : Set E) :
    ind (hyperConn H d w') zeta =
      if w' ∈ hyperClusterSet H zeta ({d} : Set V) then 1 else 0 := by
  by_cases h : w' ∈ hyperClusterSet H zeta ({d} : Set V)
  · rw [if_pos h, ind_of_mem]
    rwa [mem_hyperConn, ← mem_hyperClusterSet_singleton]
  · rw [if_neg h, ind_of_not_mem]
    intro hc
    exact h ((mem_hyperClusterSet_singleton H zeta d w').2 hc)

/-- Markov at the decoy cluster followed by Lemma Phi. -/
theorem sum_resid_mul_clusterFn (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (x : V) (Y : Set V)
    (g : Set V → ℝ) (d : V) {A : Set V} (hA : insert x Y ⊆ A)
    (f : Set V → ℝ) :
    ∑ zeta, weight w zeta *
      (resid H w x Y g zeta *
        (ind (avoidEvent H ({d} : Set V) A) zeta *
          f (hyperClusterSet H zeta ({d} : Set V)))) =
      - ∑ zeta, weight w zeta *
        (ind (avoidEvent H ({d} : Set V) A) zeta *
          f (hyperClusterSet H zeta ({d} : Set V)) *
          phiS H w x Y g d zeta) := by
  let K : Set V → Set E → ℝ := fun W beta ↦
    (if Disjoint W A then 1 else 0) * f W * resid H w x Y g beta
  have key := set_sum_cond_sdiff_off_empty H w hm ({d} : Set V) K
  have hL : ∀ zeta, weight w zeta *
      K (hyperClusterSet H zeta ({d} : Set V))
        (zeta \ cut H ({d} : Set V) zeta) =
      weight w zeta *
        (resid H w x Y g zeta *
          (ind (avoidEvent H ({d} : Set V) A) zeta *
            f (hyperClusterSet H zeta ({d} : Set V)))) := by
    intro zeta
    rw [ind_avoid_eq_ite_cluster]
    by_cases hav : Disjoint (hyperClusterSet H zeta ({d} : Set V)) A
    · have hz : zeta ∈ avoidEvent H ({d} : Set V) A := hav
      have hz' : zeta ∈ avoidEvent H ({d} : Set V) (insert x Y) :=
        avoidEvent_antitone H ({d} : Set V) hA hz
      have hr := resid_off_singleton H w g hz'
      change weight w zeta *
        ((if Disjoint (hyperClusterSet H zeta ({d} : Set V)) A then 1 else 0) *
          f (hyperClusterSet H zeta ({d} : Set V)) *
          resid H w x Y g
            (off H (hyperClusterSet H zeta ({d} : Set V)) zeta)) = _
      rw [if_pos hav, hr]
      ring
    · change weight w zeta *
        ((if Disjoint (hyperClusterSet H zeta ({d} : Set V)) A then 1 else 0) *
          f (hyperClusterSet H zeta ({d} : Set V)) * _) =
        weight w zeta *
          (resid H w x Y g zeta *
            ((if Disjoint (hyperClusterSet H zeta ({d} : Set V)) A then 1 else 0) * _))
      rw [if_neg hav]
      ring
  have hR : ∀ zeta, weight w zeta *
      ∑ eta, weight w eta *
        K (hyperClusterSet H zeta ({d} : Set V))
          (eta \ cut H ({d} : Set V) zeta) =
      - (weight w zeta *
        (ind (avoidEvent H ({d} : Set V) A) zeta *
          f (hyperClusterSet H zeta ({d} : Set V)) *
          phiS H w x Y g d zeta)) := by
    intro zeta
    rw [ind_avoid_eq_ite_cluster]
    change weight w zeta *
      ∑ eta, weight w eta *
        ((if Disjoint (hyperClusterSet H zeta ({d} : Set V)) A then 1 else 0) *
          f (hyperClusterSet H zeta ({d} : Set V)) *
          resid H w x Y g
            (off H (hyperClusterSet H zeta ({d} : Set V)) eta)) = _
    have hfac :
        (∑ eta, weight w eta *
          ((if Disjoint (hyperClusterSet H zeta ({d} : Set V)) A then 1 else 0) *
            f (hyperClusterSet H zeta ({d} : Set V)) *
            resid H w x Y g
              (off H (hyperClusterSet H zeta ({d} : Set V)) eta))) =
        (if Disjoint (hyperClusterSet H zeta ({d} : Set V)) A then 1 else 0) *
          f (hyperClusterSet H zeta ({d} : Set V)) *
          ∑ eta, weight w eta *
            resid H w x Y g
              (off H (hyperClusterSet H zeta ({d} : Set V)) eta) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun eta _ ↦ by ring
    rw [hfac, sum_resid_world_singleton H w hm x Y g d zeta]
    ring
  calc
    _ = ∑ zeta, weight w zeta *
        K (hyperClusterSet H zeta ({d} : Set V))
          (zeta \ cut H ({d} : Set V) zeta) :=
      Finset.sum_congr rfl fun zeta _ ↦ (hL zeta).symm
    _ = ∑ zeta, weight w zeta *
        ∑ eta, weight w eta *
          K (hyperClusterSet H zeta ({d} : Set V))
            (eta \ cut H ({d} : Set V) zeta) := key
    _ = ∑ zeta, - (weight w zeta *
        (ind (avoidEvent H ({d} : Set V) A) zeta *
          f (hyperClusterSet H zeta ({d} : Set V)) *
          phiS H w x Y g d zeta)) :=
      Finset.sum_congr rfl fun zeta _ ↦ hR zeta
    _ = _ := by rw [Finset.sum_neg_distrib]

/-- Centering at the conditional connection constant turns the one-decoy
moment into a denominator-free covariance. -/
theorem sum_resid_decoy_moment (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (x : V) (Y : Set V)
    (g : Set V → ℝ) (d : V) {A : Set V} (hA : insert x Y ⊆ A)
    (w' : V) {c : ℝ}
    (hm₀ : ∑ zeta, weight w zeta *
      ind (avoidEvent H ({d} : Set V) A) zeta ≠ 0)
    (hc : c =
      (∑ zeta, weight w zeta *
        ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta) /
      ∑ zeta, weight w zeta *
        ind (avoidEvent H ({d} : Set V) A) zeta) :
    ∑ zeta, weight w zeta *
      (resid H w x Y g zeta *
        (ind (avoidEvent H ({d} : Set V) A) zeta *
          (ind (hyperConn H d w') zeta - c))) =
      - ((∑ zeta, weight w zeta *
          ind (avoidEvent H ({d} : Set V) A) zeta)⁻¹ *
        ((∑ zeta, weight w zeta *
            ind (avoidEvent H ({d} : Set V) A) zeta) *
          (∑ zeta, weight w zeta *
            (ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta *
              phiS H w x Y g d zeta)) -
        (∑ zeta, weight w zeta *
            ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta) *
          (∑ zeta, weight w zeta *
            (ind (avoidEvent H ({d} : Set V) A) zeta *
              phiS H w x Y g d zeta)))) := by
  let f : Set V → ℝ := fun K ↦ (if w' ∈ K then (1 : ℝ) else 0) - c
  have hf : ∀ zeta,
      f (hyperClusterSet H zeta ({d} : Set V)) =
        ind (hyperConn H d w') zeta - c := by
    intro zeta
    simp only [f, ind_hyperConn_eq_ite_cluster]
  have h1 := sum_resid_mul_clusterFn H w hm x Y g d hA f
  simp only [hf] at h1
  rw [h1]
  let m₀ := ∑ zeta, weight w zeta *
    ind (avoidEvent H ({d} : Set V) A) zeta
  let m₁ := ∑ zeta, weight w zeta *
    ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta
  let P₁ := ∑ zeta, weight w zeta *
    (ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta *
      phiS H w x Y g d zeta)
  let P₀ := ∑ zeta, weight w zeta *
    (ind (avoidEvent H ({d} : Set V) A) zeta * phiS H w x Y g d zeta)
  have he : ∑ zeta, weight w zeta *
      (ind (avoidEvent H ({d} : Set V) A) zeta *
        (ind (hyperConn H d w') zeta - c) * phiS H w x Y g d zeta) =
      P₁ - c * P₀ := by
    rw [show P₁ = ∑ zeta, weight w zeta *
      (ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta *
        phiS H w x Y g d zeta) from rfl,
      show P₀ = ∑ zeta, weight w zeta *
        (ind (avoidEvent H ({d} : Set V) A) zeta *
          phiS H w x Y g d zeta) from rfl,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun zeta _ ↦ ?_
    rw [Percolation.Literature.BHK2006.ind_inter]
    ring
  rw [he, hc]
  have hm₀' : m₀ ≠ 0 := hm₀
  change -(P₁ - m₁ / m₀ * P₀) =
    -(m₀⁻¹ * (m₀ * P₁ - m₁ * P₀))
  field_simp [hm₀']

theorem ind_avoid_mul_union (H : Hypergraph V E) (d : V)
    (S Y : Set V) (zeta : Set E) :
    ind (avoidEvent H ({d} : Set V) Y) zeta *
      ind (avoidEvent H ({d} : Set V) S) zeta =
    ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta := by
  by_cases hY : zeta ∈ avoidEvent H ({d} : Set V) Y
  · by_cases hS : zeta ∈ avoidEvent H ({d} : Set V) S
    · rw [ind_of_mem hY, ind_of_mem hS, one_mul, ind_of_mem]
      exact Set.disjoint_union_right.2 ⟨hS, hY⟩
    · rw [ind_of_mem hY, ind_of_not_mem hS, mul_zero, ind_of_not_mem]
      exact fun h ↦ hS (Set.disjoint_union_right.1 h).1
  · rw [ind_of_not_mem hY, zero_mul, ind_of_not_mem]
    exact fun h ↦ hY (Set.disjoint_union_right.1 h).2

theorem one_sub_ind_avoid_eq_cluster (H : Hypergraph V E) (d : V)
    (Y : Set V) (zeta : Set E) :
    1 - ind (avoidEvent H ({d} : Set V) Y) zeta =
      1 - (if d ∈ hyperClusterSet H zeta Y then 0 else 1) := by
  rw [← avoidEv_eq, ind_avoidEv_eq_ite]

/-- The complete contribution of one decoy. -/
theorem decoy_world_term (H : Hypergraph V E) (w : E → ℝ)
    (hm : ∑ omega : Set E, weight w omega = 1) (x : V) (Y : Set V)
    (g : Set V → ℝ) {S : Set V} (hxS : x ∈ S) {d : V} (hdS : d ∉ S)
    (L' : List (V × (V → ℝ))) (hL' : ∀ dc ∈ L', dc.1 ≠ d)
    {u : V} (hu : u ≠ d) (c : V → ℝ)
    (hm₀ : ∑ zeta, weight w zeta *
      ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta ≠ 0)
    (hc : ∀ w', c w' =
      (∑ zeta, weight w zeta *
        ind (avoidEvent H ({d} : Set V) (S ∪ Y) ∩ hyperConn H d w') zeta) /
      ∑ zeta, weight w zeta *
        ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta) :
    ∑ omega, weight w omega *
      (ind (avoidEvent H ({x} : Set V) Y) omega *
        wcovOff H w Y
          (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)))
          (fun zeta ↦
            CSH.av (openHyperGraph H zeta).Reachable S d *
              CSH.slForm L'
                (fun w' ↦ CSH.chi (openHyperGraph H zeta).Reachable w' d - c w') u)
          omega) =
      - ((∑ zeta, weight w zeta *
          ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta)⁻¹ *
        CSH.slForm L' (fun w' ↦
          (∑ zeta, weight w zeta *
            ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta) *
              (∑ zeta, weight w zeta *
                (ind (avoidEvent H ({d} : Set V) (S ∪ Y) ∩ hyperConn H d w') zeta *
                  phiS H w x Y g d zeta)) -
          (∑ zeta, weight w zeta *
            ind (avoidEvent H ({d} : Set V) (S ∪ Y) ∩ hyperConn H d w') zeta) *
              (∑ zeta, weight w zeta *
                (ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta *
                  phiS H w x Y g d zeta))) u) := by
  have hA : insert x Y ⊆ S ∪ Y := by
    intro a ha
    rcases Set.mem_insert_iff.1 ha with rfl | ha
    · exact Or.inl hxS
    · exact Or.inr ha
  let G : Set E → ℝ := fun beta ↦
    g (hyperClusterSet H beta ({x} : Set V))
  let psi : Set E → ℝ := fun zeta ↦
    CSH.av (openHyperGraph H zeta).Reachable S d *
      CSH.slForm L'
        (fun w' ↦ CSH.chi (openHyperGraph H zeta).Reachable w' d - c w') u
  let m₀ := ∑ zeta, weight w zeta *
    ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta
  let Q : V → ℝ := fun w' ↦
    m₀ * (∑ zeta, weight w zeta *
      (ind (avoidEvent H ({d} : Set V) (S ∪ Y) ∩ hyperConn H d w') zeta *
        phiS H w x Y g d zeta)) -
    (∑ zeta, weight w zeta *
      ind (avoidEvent H ({d} : Set V) (S ∪ Y) ∩ hyperConn H d w') zeta) *
      (∑ zeta, weight w zeta *
        (ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta *
          phiS H w x Y g d zeta))
  have step1 : ∑ omega, weight w omega *
      (ind (avoidEvent H ({x} : Set V) Y) omega * wcovOff H w Y G psi omega) =
      ∑ zeta, weight w zeta * (resid H w x Y g zeta * psi (zeta \ cut H Y zeta)) := by
    have hmerge := markov_merge_Y H w hm x Y g psi
    have hlhs : ∀ omega, weight w omega *
        (ind (avoidEvent H ({x} : Set V) Y) omega * wcovOff H w Y G psi omega) =
      weight w omega * (ind (avoidEvent H ({x} : Set V) Y) omega *
        ∑ eta, weight w eta *
          ((g (hyperClusterSet H (eta \ cut H Y omega) ({x} : Set V)) -
            wmeanOff H w Y
              (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V))) omega) *
            psi (eta \ cut H Y omega))) := by
      intro omega
      rw [wcovOff_eq_sum]
    rw [Finset.sum_congr rfl (fun omega _ ↦ hlhs omega), hmerge]
    refine Finset.sum_congr rfl fun zeta _ ↦ ?_
    unfold resid
    ring
  have step2 : ∀ zeta, psi (zeta \ cut H Y zeta) =
      ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta *
        CSH.slForm L' (fun w' ↦ ind (hyperConn H d w') zeta - c w') u +
      (1 - ind (avoidEvent H ({d} : Set V) Y) zeta) *
        (- CSH.slForm L' c u) := by
    intro zeta
    by_cases hdy : zeta ∈ avoidEvent H ({d} : Set V) Y
    · change CSH.av (openHyperGraph H (zeta \ cut H Y zeta)).Reachable S d *
        CSH.slForm L'
          (fun w' ↦ CSH.chi
            (openHyperGraph H (zeta \ cut H Y zeta)).Reachable w' d - c w') u = _
      rw [world_term_alive H hdy S L' c u, ← ind_avoid_mul_union H d S Y zeta,
        ind_of_mem hdy]
      ring
    · change CSH.av (openHyperGraph H (zeta \ cut H Y zeta)).Reachable S d *
        CSH.slForm L'
          (fun w' ↦ CSH.chi
            (openHyperGraph H (zeta \ cut H Y zeta)).Reachable w' d - c w') u = _
      rw [world_term_dead H hdy hdS L' hL' c hu, ind_of_not_mem hdy]
      have hzero : ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta = 0 :=
        ind_of_not_mem fun h' ↦ hdy (Set.disjoint_union_right.1 h').2
      rw [hzero]
      ring
  have step3 : ∑ zeta, weight w zeta *
      (resid H w x Y g zeta *
        ((1 - ind (avoidEvent H ({d} : Set V) Y) zeta) *
          (- CSH.slForm L' c u))) = 0 := by
    have horth := residual_orthogonal H w hm x Y g
      (fun W ↦ (1 - (if d ∈ W then (0 : ℝ) else 1)) *
        (- CSH.slForm L' c u))
    rw [← horth]
    refine Finset.sum_congr rfl fun zeta _ ↦ ?_
    unfold resid
    rw [one_sub_ind_avoid_eq_cluster H d Y zeta]
    ring
  have step4 : ∑ zeta, weight w zeta *
      (resid H w x Y g zeta *
        (ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta *
          CSH.slForm L' (fun w' ↦ ind (hyperConn H d w') zeta - c w') u)) =
      - (m₀⁻¹ * CSH.slForm L' Q u) := by
    have hlin : ∀ zeta,
        CSH.slForm L' (fun w' ↦ ind (hyperConn H d w') zeta - c w') u =
          ∑ w', CSH.slForm L' (Pi.single w' (1 : ℝ)) u *
            (ind (hyperConn H d w') zeta - c w') :=
      fun zeta ↦ CSH.slForm_eq_sum_single L' _ u
    simp only [hlin, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ w', ∑ zeta, weight w zeta *
        (resid H w x Y g zeta *
          (ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta *
            (CSH.slForm L' (Pi.single w' (1 : ℝ)) u *
              (ind (hyperConn H d w') zeta - c w')))) =
        CSH.slForm L' (Pi.single w' (1 : ℝ)) u * (-(m₀⁻¹ * Q w')) := by
      intro w'
      rw [← sum_resid_decoy_moment H w hm x Y g d hA w' hm₀ (hc w'),
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun zeta _ ↦ by ring
    rw [Finset.sum_congr rfl (fun w' _ ↦ hinner w'),
      CSH.slForm_eq_sum_single L' Q u, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w' _ ↦ by ring
  rw [step1]
  have hsplit : ∀ zeta, weight w zeta *
      (resid H w x Y g zeta * psi (zeta \ cut H Y zeta)) =
      weight w zeta *
        (resid H w x Y g zeta *
          (ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta *
            CSH.slForm L' (fun w' ↦ ind (hyperConn H d w') zeta - c w') u)) +
      weight w zeta *
        (resid H w x Y g zeta *
          ((1 - ind (avoidEvent H ({d} : Set V) Y) zeta) *
            (- CSH.slForm L' c u))) := by
    intro zeta
    rw [step2 zeta]
    ring
  rw [Finset.sum_congr rfl (fun zeta _ ↦ hsplit zeta),
    Finset.sum_add_distrib, step3, step4, add_zero]

/-- The finite-sum definition of `phiS` agrees with the existing `phiFun`. -/
theorem phiS_prob_eq_phiFun (H : Hypergraph V E) (x : V) (Y : Set V)
    (g : Set V → ℝ) (d : V) (zeta : Set E) :
    phiS H (fun e ↦ (H.prob e : ℝ)) x Y g d zeta =
      phiFun H x Y g (hyperClusterSet H zeta ({d} : Set V)) := by
  unfold phiS phiFun
  rw [Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]

theorem real_eq_sum_ind (H : Hypergraph V E) (A : Set (Set E)) :
    (prodBernoulli H.prob).real A =
      ∑ zeta, weight (fun e ↦ (H.prob e : ℝ)) zeta * ind A zeta := by
  rw [← AGBase.integral_ind A,
    Percolation.Literature.BHK2006.integral_prodBernoulli_eq_sum]

theorem avoidConst_eq_div (H : Hypergraph V E) (d : V) (A : Set V)
    (w' : V) :
    avoidConst H d A w' =
      (∑ zeta, weight (fun e ↦ (H.prob e : ℝ)) zeta *
        ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta) /
      ∑ zeta, weight (fun e ↦ (H.prob e : ℝ)) zeta *
        ind (avoidEvent H ({d} : Set V) A) zeta := by
  unfold avoidConst
  rw [real_eq_sum_ind, real_eq_sum_ind]

theorem covD_phiFun_eq (H : Hypergraph V E) (x : V) (Y A : Set V)
    (g : Set V → ℝ) (d w' : V) :
    covD H d A (phiFun H x Y g) w' =
      (∑ zeta, weight (fun e ↦ (H.prob e : ℝ)) zeta *
        ind (avoidEvent H ({d} : Set V) A) zeta) *
        (∑ zeta, weight (fun e ↦ (H.prob e : ℝ)) zeta *
          (ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta *
            phiS H (fun e ↦ (H.prob e : ℝ)) x Y g d zeta)) -
      (∑ zeta, weight (fun e ↦ (H.prob e : ℝ)) zeta *
        ind (avoidEvent H ({d} : Set V) A ∩ hyperConn H d w') zeta) *
        (∑ zeta, weight (fun e ↦ (H.prob e : ℝ)) zeta *
          (ind (avoidEvent H ({d} : Set V) A) zeta *
            phiS H (fun e ↦ (H.prob e : ℝ)) x Y g d zeta)) := by
  unfold covD avoidIntegral
  rw [real_eq_sum_ind, real_eq_sum_ind, setIntegral_eq_sum_ind,
    setIntegral_eq_sum_ind]
  simp only [phiS_prob_eq_phiFun]
  ring

/-! ## Summing the decoy contributions -/

def subT (H : Hypergraph V E) (x : V) (Y : Set V) (g : Set V → ℝ)
    (u : V) : Set V → List V → ℝ
  | _, [] => 0
  | S, d :: ds =>
      ((prodBernoulli H.prob).real
        (avoidEvent H ({d} : Set V) (S ∪ Y)))⁻¹ *
        CSH.slForm (decoyList H (insert d (S ∪ Y)) ds)
          (covD H d (S ∪ Y) (phiFun H x Y g)) u +
      subT H x Y g u (insert d S) ds

theorem sum_ind_avoid_ne_zero (H : Hypergraph V E)
    (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1) {d : V} {A : Set V}
    (hdA : d ∉ A) :
    ∑ zeta, weight (fun e ↦ (H.prob e : ℝ)) zeta *
      ind (avoidEvent H ({d} : Set V) A) zeta ≠ 0 := by
  rw [← real_eq_sum_ind]
  exact (prodBernoulli_real_pos_of_nonempty hp
    ⟨∅, empty_mem_avoidEvent_singleton H hdA⟩).ne'

theorem sum_wcov_unfoldT (H : Hypergraph V E)
    (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1)
    (x : V) (Y : Set V) (g : Set V → ℝ) (u : V) :
    ∀ (D : List V) (S : Set V), x ∈ S → D.Nodup →
      (∀ d ∈ D, d ∉ S ∧ d ∉ Y ∧ d ≠ u) →
      ∑ omega, weight (fun e ↦ (H.prob e : ℝ)) omega *
        (ind (avoidEvent H ({x} : Set V) Y) omega *
          wcovOff H (fun e ↦ (H.prob e : ℝ)) Y
            (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)))
            (fun zeta ↦ CSH.unfoldT (openHyperGraph H zeta).Reachable S
              (decoyList H (S ∪ Y) D) u) omega) =
        - subT H x Y g u S D := by
  intro D
  induction D with
  | nil =>
      intro S _ _ _
      simp only [decoyList, CSH.unfoldT, subT, neg_zero]
      exact Finset.sum_eq_zero fun omega _ ↦ by
        rw [wcovOff_zero_right]
        ring
  | cons d ds ih =>
      intro S hxS hnd hdis
      let w : E → ℝ := fun e ↦ (H.prob e : ℝ)
      have hm : ∑ omega : Set E, weight w omega = 1 := sum_weight_prob H
      have hdS : d ∉ S := (hdis d List.mem_cons_self).1
      have hdY : d ∉ Y := (hdis d List.mem_cons_self).2.1
      have hud : u ≠ d := fun h ↦ (hdis d List.mem_cons_self).2.2 h.symm
      have hnd' : ds.Nodup := (List.nodup_cons.1 hnd).2
      have hd_notin : d ∉ ds := (List.nodup_cons.1 hnd).1
      have hL : decoyList H (S ∪ Y) (d :: ds) =
          (d, avoidConst H d (S ∪ Y)) ::
            decoyList H (insert d (S ∪ Y)) ds := rfl
      have hset : insert d (S ∪ Y) = insert d S ∪ Y := by
        rw [Set.insert_union]
      have hL' : ∀ dc ∈ decoyList H (insert d (S ∪ Y)) ds,
          dc.1 ≠ d := by
        intro dc hdc heq
        have hdmem : dc.1 ∈
            (decoyList H (insert d (S ∪ Y)) ds).map Prod.fst :=
          List.mem_map.2 ⟨dc, hdc, rfl⟩
        rw [map_fst_decoyList, heq] at hdmem
        exact hd_notin hdmem
      have hm₀ : ∑ zeta, weight w zeta *
          ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta ≠ 0 :=
        sum_ind_avoid_ne_zero H hp (fun h ↦ h.elim hdS hdY)
      have hsplit : ∀ omega,
          wcovOff H w Y
            (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)))
            (fun zeta ↦ CSH.unfoldT (openHyperGraph H zeta).Reachable S
              (decoyList H (S ∪ Y) (d :: ds)) u) omega =
          wcovOff H w Y
            (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)))
            (fun zeta ↦ CSH.av (openHyperGraph H zeta).Reachable S d *
              CSH.slForm (decoyList H (insert d (S ∪ Y)) ds)
                (fun w' ↦ CSH.chi (openHyperGraph H zeta).Reachable w' d -
                  avoidConst H d (S ∪ Y) w') u) omega +
          wcovOff H w Y
            (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)))
            (fun zeta ↦ CSH.unfoldT (openHyperGraph H zeta).Reachable
              (insert d S) (decoyList H (insert d S ∪ Y) ds) u) omega := by
        intro omega
        rw [← wcovOff_add_right, hL]
        simp only [CSH.unfoldT, hset]
      have hhead := decoy_world_term H w hm x Y g hxS hdS
        (decoyList H (insert d (S ∪ Y)) ds) hL' hud
        (avoidConst H d (S ∪ Y)) hm₀
        (fun w' ↦ avoidConst_eq_div H d (S ∪ Y) w')
      have hQ : (fun w' ↦
          (∑ zeta, weight w zeta *
            ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta) *
              (∑ zeta, weight w zeta *
                (ind (avoidEvent H ({d} : Set V) (S ∪ Y) ∩ hyperConn H d w') zeta *
                  phiS H w x Y g d zeta)) -
          (∑ zeta, weight w zeta *
            ind (avoidEvent H ({d} : Set V) (S ∪ Y) ∩ hyperConn H d w') zeta) *
              (∑ zeta, weight w zeta *
                (ind (avoidEvent H ({d} : Set V) (S ∪ Y)) zeta *
                  phiS H w x Y g d zeta))) =
          covD H d (S ∪ Y) (phiFun H x Y g) := by
        funext w'
        rw [covD_phiFun_eq]
      rw [hQ, ← real_eq_sum_ind] at hhead
      have htail := ih (insert d S) (Set.mem_insert_of_mem d hxS) hnd'
        (fun e he ↦ ⟨
          fun heS ↦ (Set.mem_insert_iff.1 heS).elim
            (fun hed ↦ hd_notin (hed ▸ he))
            (hdis e (List.mem_cons_of_mem d he)).1,
          (hdis e (List.mem_cons_of_mem d he)).2.1,
          (hdis e (List.mem_cons_of_mem d he)).2.2⟩)
      have heq : ∀ omega, weight w omega *
          (ind (avoidEvent H ({x} : Set V) Y) omega *
            wcovOff H w Y
              (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)))
              (fun zeta ↦ CSH.unfoldT (openHyperGraph H zeta).Reachable S
                (decoyList H (S ∪ Y) (d :: ds)) u) omega) =
        weight w omega *
          (ind (avoidEvent H ({x} : Set V) Y) omega *
            wcovOff H w Y
              (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)))
              (fun zeta ↦ CSH.av (openHyperGraph H zeta).Reachable S d *
                CSH.slForm (decoyList H (insert d (S ∪ Y)) ds)
                  (fun w' ↦ CSH.chi (openHyperGraph H zeta).Reachable w' d -
                    avoidConst H d (S ∪ Y) w') u) omega) +
        weight w omega *
          (ind (avoidEvent H ({x} : Set V) Y) omega *
            wcovOff H w Y
              (fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)))
              (fun zeta ↦ CSH.unfoldT (openHyperGraph H zeta).Reachable
                (insert d S) (decoyList H (insert d S ∪ Y) ds) u) omega) := by
        intro omega
        rw [hsplit]
        ring
      rw [Finset.sum_congr rfl (fun omega _ ↦ heq omega),
        Finset.sum_add_distrib, hhead, htail]
      simp only [subT, hset]
      ring

end KNAll.Site.HyperCSHUnfold

end

#print axioms KNAll.Site.HyperCSHUnfold.hyperClusterSet_off_cut_of_avoid
#print axioms KNAll.Site.HyperCSHUnfold.wcovOff_affine
#print axioms KNAll.Site.HyperCSHUnfold.world_cov_eq_wcovOff
#print axioms KNAll.Site.HyperCSHUnfold.markov_merge_Y
#print axioms KNAll.Site.HyperCSHUnfold.residual_orthogonal
