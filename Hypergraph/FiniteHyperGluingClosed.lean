import Hypergraph.HyperCSHUnfold
import Hypergraph.HyperFixedFromCSH

/-!
# Unconditional finite hyperedge gluing

This file is the final composition layer for the labelled-hyperedge proof.  The
two-block Gibbs reduction (including its quantitative terminal bound) is in
`KN.HyperCSHTwoA`; the labelled one-decoy unfolding is in
`KN.HyperCSHUnfold`; and the horizontal term is discharged in
`KN.HyperCSHHtwBridge`.  Here they are put together without an additional
correlation hypothesis.
-/

noncomputable section

namespace KNAll.Site.FiniteHyperGluingClosed

open MeasureTheory Set Percolation.Literature
  Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.AGBase KNAll.Site.CTOne
open KNAll.Site.CSHDefs KNAll.Site.CSHTwoA KNAll.Site.CSHTwoB KNAll.Site.CSHThree
open KNAll.Site.HyperCSHHtw KNAll.Site.HyperCSHUnfold
open Percolation.Literature.BHK2006 (weight)
open Percolation.Literature.DecisionTree (ind)
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The existing `psiIso` is literally the repaired globally defined
observable `1[(K \ {k}).Nonempty]`, not an observable defined only on
realizable clusters. -/
theorem psiIso_eq_sdiff_nonempty (k : V) (K : Set V) :
    psiIso k K = if (K \ ({k} : Set V)).Nonempty then 1 else 0 := by
  unfold psiIso
  by_cases hK : K ⊆ ({k} : Set V)
  · rw [if_pos hK, if_neg]
    rintro ⟨u, huK, hu⟩
    exact hu (hK huK)
  · rw [if_neg hK, if_pos]
    obtain ⟨u, huK, hu⟩ := Set.not_subset.1 hK
    exact ⟨u, huK, hu⟩

/-- Global isotonicity of the repaired singleton-complement observable. -/
theorem corrected_fk_monotone (k : V) :
    Monotone (fun K : Set V ↦
      if (K \ ({k} : Set V)).Nonempty then (1 : ℝ) else 0) := by
  simpa only [← psiIso_eq_sdiff_nonempty] using psiIso_mono (V := V) k

/-- The deleted-world covariance used in the unfolding is exactly `covH`. -/
theorem world_cov_eq_covH (H : Hypergraph V E) (x u : V) (S Y : Set V)
    (g : Set V → ℝ) (omega : Set E) :
    (∫ eta in HyperCSHHtw.connTo H u S,
          g (hyperClusterSet H eta ({x} : Set V))
          ∂(prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob)) -
        (∫ eta, g (hyperClusterSet H eta ({x} : Set V))
          ∂(prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob)) *
          (prodBernoulli (deleteHyper H (hyperClusterSet H omega Y)).prob).real
            (HyperCSHHtw.connTo H u S) =
      CSHThree.covH H g x S u (hyperClusterSet H omega Y) := by
  let C := hyperClusterSet H omega Y
  let Hd := deleteHyper H C
  have hcl : hyperClusterSet Hd = hyperClusterSet H := rfl
  have hconn : HyperCSHHtw.connTo Hd u S = HyperCSHHtw.connTo H u S := rfl
  have hb := HyperCSHHtw.BfS_univ_eq Hd x u S g
  have hc := HyperCSHHtw.BfS_univ_eq_covH Hd x u S g
  rw [hcl, hconn] at hb
  calc
    _ = KNAll.Site.HyperA2H.BfS Hd (fun e ↦ (Hd.prob e : ℝ))
          Finset.univ x S u g := hb.symm
    _ = CSHThree.covH Hd g x S u ∅ := hc
    _ = CSHThree.covH H g x S u C :=
      HyperCSHHtw.covH_deleteHyper_empty_eq H C g x S u
    _ = _ := rfl

/-- Indicator form of the singleton source marker. -/
theorem ind_hyperConn_eq_jn_singleton (H : Hypergraph V E) (x : V)
    (zeta : Set E) :
    (fun u ↦ ind (hyperConn H x u) zeta) =
      Percolation.Continuity.CSH.jn
        (openHyperGraph H zeta).Reachable ({x} : Set V) := by
  funext u
  rw [HyperCSHUnfold.jn_reachable_eq_ind, HyperCSHHtw.connTo_singleton,
    hyperConn_comm H u x]

/-- Lemma U: the level margin splits into the horizontal set-marker term and
the accumulated lower-level decoy terms. -/
theorem within_unfold (H : Hypergraph V E)
    (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1)
    (x : V) (Y : Set V) (D : List V) (o v : V)
    (hnd : D.Nodup)
    (hD : ∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v)
    (g : Set V → ℝ) (p : ℝ) :
    (∫ omega in avoidEvent H ({x} : Set V) Y,
        Percolation.Continuity.CSH.cshMarg
          (decoyList H (insert x Y) D) p o v
          (fun u ↦
            (∫ eta in hyperConn H x u,
                g (hyperClusterSet H eta ({x} : Set V))
                ∂(prodBernoulli
                  (deleteHyper H (hyperClusterSet H omega Y)).prob)) -
              (∫ eta, g (hyperClusterSet H eta ({x} : Set V))
                ∂(prodBernoulli
                  (deleteHyper H (hyperClusterSet H omega Y)).prob)) *
                (prodBernoulli
                  (deleteHyper H (hyperClusterSet H omega Y)).prob).real
                    (hyperConn H x u)) ∂(prodBernoulli H.prob)) =
      (∫ omega in avoidEvent H ({x} : Set V) Y,
        (CSHThree.covH H g x
              (({x} : Set V) ∪ {d | d ∈ D}) o
              (hyperClusterSet H omega Y) -
          p * CSHThree.covH H g x
              (({x} : Set V) ∪ {d | d ∈ D}) v
              (hyperClusterSet H omega Y)) ∂(prodBernoulli H.prob)) +
        (HyperCSHUnfold.subT H x Y g o ({x} : Set V) D -
          p * HyperCSHUnfold.subT H x Y g v ({x} : Set V) D) := by
  let w : E → ℝ := fun e ↦ (H.prob e : ℝ)
  have hm : ∑ omega : Set E, weight w omega = 1 := sum_weight_prob H
  set L := decoyList H (insert x Y) D with hLdef
  set G : Set E → ℝ :=
    fun beta ↦ g (hyperClusterSet H beta ({x} : Set V)) with hG
  have hL' : L = decoyList H (({x} : Set V) ∪ Y) D := by
    rw [hLdef, Set.singleton_union]
  have hdecs : {d : V | d ∈ L.map Prod.fst} = {d | d ∈ D} := by
    rw [hLdef, CSHTwoA.map_fst_decoyList]
  set Sset : Set V := ({x} : Set V) ∪ {d | d ∈ D} with hSset
  set Jf : V → Set E → ℝ := fun u zeta ↦
    Percolation.Continuity.CSH.jn
      (openHyperGraph H zeta).Reachable Sset u with hJf
  set Tf : V → Set E → ℝ := fun u zeta ↦
    Percolation.Continuity.CSH.unfoldT
      (openHyperGraph H zeta).Reachable ({x} : Set V) L u with hTf
  rw [HyperCSHUnfold.setIntegral_eq_sum_ind,
    HyperCSHUnfold.setIntegral_eq_sum_ind]
  simp only [HyperCSHUnfold.world_cov_eq_wcovOff]
  have stepB : ∀ omega,
      Percolation.Continuity.CSH.cshMarg L p o v
          (fun u ↦ HyperCSHUnfold.wcovOff H w Y G
            (ind (hyperConn H x u)) omega) =
        HyperCSHUnfold.wcovOff H w Y G (Jf o) omega -
          p * HyperCSHUnfold.wcovOff H w Y G (Jf v) omega -
          HyperCSHUnfold.wcovOff H w Y G (Tf o) omega +
          p * HyperCSHUnfold.wcovOff H w Y G (Tf v) omega := by
    intro omega
    rw [Percolation.Continuity.CSH.cshMarg_eq_sum_single,
      HyperCSHUnfold.wcovOff_finset_sum]
    have inner :
        (fun zeta ↦ ∑ u,
          Percolation.Continuity.CSH.cshMarg L p o v (Pi.single u (1 : ℝ)) *
            ind (hyperConn H x u) zeta) =
          fun zeta ↦ (Jf o zeta - p * Jf v zeta) -
            (Tf o zeta - p * Tf v zeta) +
              (Percolation.Continuity.CSH.unfoldK L o -
                p * Percolation.Continuity.CSH.unfoldK L v) := by
      funext zeta
      rw [← Percolation.Continuity.CSH.cshMarg_eq_sum_single L p o v
        (fun u ↦ ind (hyperConn H x u) zeta),
        ind_hyperConn_eq_jn_singleton]
      simp only [Percolation.Continuity.CSH.cshMarg,
        CSHTwoA.slForm_jn_reachable H zeta L ({x} : Set V), hdecs,
        hJf, hTf, hSset]
      ring
    rw [inner, HyperCSHUnfold.wcovOff_affine H w hm]
  have hDo : ∀ d ∈ D,
      d ∉ ({x} : Set V) ∧ d ∉ Y ∧ d ≠ o := by
    intro d hd
    exact ⟨fun h ↦ (hD d hd).1 (Set.mem_singleton_iff.1 h),
      (hD d hd).2.1, (hD d hd).2.2.1⟩
  have hDv : ∀ d ∈ D,
      d ∉ ({x} : Set V) ∧ d ∉ Y ∧ d ≠ v := by
    intro d hd
    exact ⟨fun h ↦ (hD d hd).1 (Set.mem_singleton_iff.1 h),
      (hD d hd).2.1, (hD d hd).2.2.2⟩
  have stepCo := HyperCSHUnfold.sum_wcov_unfoldT
    H hp x Y g o D ({x} : Set V) (Set.mem_singleton x) hnd hDo
  have stepCv := HyperCSHUnfold.sum_wcov_unfoldT
    H hp x Y g v D ({x} : Set V) (Set.mem_singleton x) hnd hDv
  rw [← hL'] at stepCo stepCv
  have e : ∀ omega,
      weight w omega *
          (ind (avoidEvent H ({x} : Set V) Y) omega *
            Percolation.Continuity.CSH.cshMarg L p o v
              (fun u ↦ HyperCSHUnfold.wcovOff H w Y G
                (ind (hyperConn H x u)) omega)) =
        weight w omega *
          (ind (avoidEvent H ({x} : Set V) Y) omega *
            (HyperCSHUnfold.wcovOff H w Y G (Jf o) omega -
              p * HyperCSHUnfold.wcovOff H w Y G (Jf v) omega)) -
        weight w omega *
          (ind (avoidEvent H ({x} : Set V) Y) omega *
            HyperCSHUnfold.wcovOff H w Y G (Tf o) omega) +
        p * (weight w omega *
          (ind (avoidEvent H ({x} : Set V) Y) omega *
            HyperCSHUnfold.wcovOff H w Y G (Tf v) omega)) := by
    intro omega
    rw [stepB omega]
    ring
  rw [Finset.sum_congr rfl (fun omega _ ↦ e omega),
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change
    (∑ omega, weight w omega *
      (ind (avoidEvent H ({x} : Set V) Y) omega *
        (HyperCSHUnfold.wcovOff H w Y G (Jf o) omega -
          p * HyperCSHUnfold.wcovOff H w Y G (Jf v) omega))) -
      (∑ omega, weight w omega *
        (ind (avoidEvent H ({x} : Set V) Y) omega *
          HyperCSHUnfold.wcovOff H w Y G
            (fun zeta ↦ Percolation.Continuity.CSH.unfoldT
              (openHyperGraph H zeta).Reachable ({x} : Set V) L o) omega)) +
      p * (∑ omega, weight w omega *
        (ind (avoidEvent H ({x} : Set V) Y) omega *
          HyperCSHUnfold.wcovOff H w Y G
            (fun zeta ↦ Percolation.Continuity.CSH.unfoldT
              (openHyperGraph H zeta).Reachable ({x} : Set V) L v) omega)) = _
  rw [stepCo, stepCv]
  have hJ : ∀ u, Jf u = ind (HyperCSHHtw.connTo H u Sset) := by
    intro u
    funext zeta
    rw [hJf]
    exact HyperCSHUnfold.jn_reachable_eq_ind H zeta Sset u
  rw [hJ o, hJ v]
  have eM : ∀ omega,
      HyperCSHUnfold.wcovOff H w Y G
          (ind (HyperCSHHtw.connTo H o Sset)) omega =
        CSHThree.covH H g x Sset o (hyperClusterSet H omega Y) := by
    intro omega
    rw [← HyperCSHUnfold.world_cov_eq_wcovOff]
    exact world_cov_eq_covH H x o Sset Y g omega
  have eV : ∀ omega,
      HyperCSHUnfold.wcovOff H w Y G
          (ind (HyperCSHHtw.connTo H v Sset)) omega =
        CSHThree.covH H g x Sset v (hyperClusterSet H omega Y) := by
    intro omega
    rw [← HyperCSHUnfold.world_cov_eq_wcovOff]
    exact world_cov_eq_covH H x v Sset Y g omega
  simp_rw [eM, eV]
  rw [hSset]
  ring

/-- The accumulated decoy correction is a nonnegative combination of lower
levels of the same hierarchy. -/
theorem subT_comb_nonneg (H : Hypergraph V E)
    (x : V) (Y : Set V) (D₀ : List V) (o v : V)
    {g : Set V → ℝ} (hg : Monotone g)
    (hIH : ∀ (pre : List V) (d : V) (ds' : List V),
      D₀ = pre ++ d :: ds' →
      ∀ h : Set V → ℝ, Monotone h → (∀ C, 0 ≤ h C) →
        0 ≤ cshMargin H d (insert x Y ∪ {e | e ∈ pre}) ds' o v h) :
    ∀ (rest pre : List V), D₀ = pre ++ rest →
      0 ≤ HyperCSHUnfold.subT H x Y g o
            (({x} : Set V) ∪ {e | e ∈ pre}) rest -
        obsConst H o v (insert x Y ∪ {d | d ∈ D₀}) *
          HyperCSHUnfold.subT H x Y g v
            (({x} : Set V) ∪ {e | e ∈ pre}) rest := by
  intro rest
  induction rest with
  | nil =>
      intro pre _
      simp [HyperCSHUnfold.subT]
  | cons d ds ih =>
      intro pre hsplit
      set A : Set V := ({x} : Set V) ∪ {e | e ∈ pre} ∪ Y with hA
      have hA' : A = insert x Y ∪ {e | e ∈ pre} := by
        ext u
        simp only [hA, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_setOf_eq, Set.mem_insert_iff]
        tauto
      have hset : insert d A ∪ {e | e ∈ ds} =
          insert x Y ∪ {e | e ∈ D₀} := by
        ext u
        simp only [hA, hsplit, Set.mem_union, Set.mem_insert_iff,
          Set.mem_singleton_iff, Set.mem_setOf_eq, List.mem_append,
          List.mem_cons]
        tauto
      have hmargin :
          Percolation.Continuity.CSH.slForm
              (decoyList H (insert d A) ds)
              (covD H d A (phiFun H x Y g)) o -
            obsConst H o v (insert x Y ∪ {e | e ∈ D₀}) *
              Percolation.Continuity.CSH.slForm
                (decoyList H (insert d A) ds)
                (covD H d A (phiFun H x Y g)) v =
          cshMargin H d (insert x Y ∪ {e | e ∈ pre}) ds o v
            (phiFun H x Y g) := by
        rw [← hset, ← hA']
        rfl
      have hhead : 0 ≤
          cshMargin H d (insert x Y ∪ {e | e ∈ pre}) ds o v
            (phiFun H x Y g) :=
        hIH pre d ds hsplit (phiFun H x Y g)
          (phiFun_mono H x Y hg) (fun K ↦ phiFun_nonneg H x Y hg K)
      have hinv : 0 ≤
          ((prodBernoulli H.prob).real
            (avoidEvent H ({d} : Set V) A))⁻¹ :=
        inv_nonneg.2 measureReal_nonneg
      have htail := ih (pre ++ [d]) (by rw [hsplit]; simp)
      have hS' : (({x} : Set V) ∪ {e | e ∈ pre ++ [d]}) =
          insert d (({x} : Set V) ∪ {e | e ∈ pre}) := by
        ext u
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
          List.mem_append, List.mem_singleton, Set.mem_insert_iff]
        tauto
      rw [hS'] at htail
      have hSY : (({x} : Set V) ∪ {e | e ∈ pre}) ∪ Y = A := rfl
      simp only [HyperCSHUnfold.subT, hSY]
      have key :
          ((prodBernoulli H.prob).real
              (avoidEvent H ({d} : Set V) A))⁻¹ *
                Percolation.Continuity.CSH.slForm
                  (decoyList H (insert d A) ds)
                  (covD H d A (phiFun H x Y g)) o +
              HyperCSHUnfold.subT H x Y g o
                (insert d (({x} : Set V) ∪ {e | e ∈ pre})) ds -
            obsConst H o v (insert x Y ∪ {d | d ∈ D₀}) *
              (((prodBernoulli H.prob).real
                  (avoidEvent H ({d} : Set V) A))⁻¹ *
                    Percolation.Continuity.CSH.slForm
                      (decoyList H (insert d A) ds)
                      (covD H d A (phiFun H x Y g)) v +
                HyperCSHUnfold.subT H x Y g v
                  (insert d (({x} : Set V) ∪ {e | e ∈ pre})) ds) =
          ((prodBernoulli H.prob).real
              (avoidEvent H ({d} : Set V) A))⁻¹ *
                cshMargin H d (insert x Y ∪ {e | e ∈ pre}) ds o v
                  (phiFun H x Y g) +
            (HyperCSHUnfold.subT H x Y g o
                (insert d (({x} : Set V) ∪ {e | e ∈ pre})) ds -
              obsConst H o v (insert x Y ∪ {d | d ∈ D₀}) *
                HyperCSHUnfold.subT H x Y g v
                  (insert d (({x} : Set V) ∪ {e | e ∈ pre})) ds) := by
        rw [← hmargin]
        ring
      rw [key]
      exact add_nonneg (mul_nonneg hinv hhead) htail

/-- Lemmas U and H together discharge the world-margin premise of the
record-based Gibbs reduction. -/
theorem within_nonneg (H : Hypergraph V E)
    (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1)
    (x : V) (Y : Set V) (D : List V) (o v : V)
    (hv : v ∉ insert x Y) (hnd : D.Nodup)
    (hD : ∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v)
    {g : Set V → ℝ} (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C)
    (hIH : ∀ (pre : List V) (d : V) (ds' : List V),
      D = pre ++ d :: ds' →
      ∀ h : Set V → ℝ, Monotone h → (∀ C, 0 ≤ h C) →
        0 ≤ cshMargin H d (insert x Y ∪ {e | e ∈ pre}) ds' o v h) :
    0 ≤ ∫ omega in avoidEvent H ({x} : Set V) Y,
      Percolation.Continuity.CSH.cshMarg
        (decoyList H (insert x Y) D)
        (obsConst H o v (insert x Y ∪ {d | d ∈ D})) o v
        (fun u ↦
          (∫ eta in hyperConn H x u,
              g (hyperClusterSet H eta ({x} : Set V))
              ∂(prodBernoulli
                (deleteHyper H (hyperClusterSet H omega Y)).prob)) -
            (∫ eta, g (hyperClusterSet H eta ({x} : Set V))
              ∂(prodBernoulli
                (deleteHyper H (hyperClusterSet H omega Y)).prob)) *
              (prodBernoulli
                (deleteHyper H (hyperClusterSet H omega Y)).prob).real
                  (hyperConn H x u)) ∂(prodBernoulli H.prob) := by
  let S : Set V := ({x} : Set V) ∪ {d | d ∈ D}
  have hxS : x ∈ S := by
    exact Or.inl (Set.mem_singleton x)
  have hvS : v ∉ S := by
    rintro (h | h)
    · exact hv (Set.mem_insert_iff.2 (Or.inl (Set.mem_singleton_iff.1 h)))
    · exact (hD v h).2.2.2 rfl
  have hvY : v ∉ Y := fun h ↦ hv (Set.mem_insert_iff.2 (Or.inr h))
  have hset : S ∪ Y = insert x Y ∪ {d | d ∈ D} := by
    ext u
    simp only [S, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Set.mem_insert_iff]
    tauto
  have hHP := HyperCSHHtw.hpart_nonneg H hp hxS hvS o hg hg0 Y hvY
  rw [hset] at hHP
  rw [within_unfold H hp x Y D o v hnd hD g]
  have hsub := subT_comb_nonneg H x Y D o v hg hIH D [] (by simp)
  have hS0 : (({x} : Set V) ∪ {e | e ∈ ([] : List V)}) = ({x} : Set V) := by
    ext u
    simp
  rw [hS0] at hsub
  exact add_nonneg hHP hsub

/-- The conditioned slack hierarchy for every strictly interior finite
labelled hypergraph. -/
theorem cshMargin_nonneg (H : Hypergraph V E)
    (hp : ∀ e, 0 < H.prob e ∧ H.prob e < 1) :
    ∀ (D : List V) (x : V) (Y : Set V) (o v : V),
      x ∉ Y → o ∉ insert x Y → v ∉ insert x Y → o ≠ v →
      D.Nodup →
      (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ o ∧ d ≠ v) →
      ∀ f : Set V → ℝ, Monotone f →
        0 ≤ cshMargin H x Y D o v f := by
  suffices hk : ∀ (k : ℕ) (D : List V), D.length ≤ k →
      ∀ (x : V) (Y : Set V) (o v : V),
        x ∉ Y → o ∉ insert x Y → v ∉ insert x Y → o ≠ v →
        D.Nodup →
        (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ o ∧ d ≠ v) →
        ∀ f : Set V → ℝ, Monotone f →
          0 ≤ cshMargin H x Y D o v f from
    fun D ↦ hk D.length D le_rfl
  intro k
  induction k with
  | zero =>
      intro D hlen x Y o v hxY ho hv hov hnd hdis f hf
      have hnil : D = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
      subst hnil
      have hY : ∀ e ∈ labelsMeeting H Y, (H.prob e : ℝ) < 1 :=
        fun e _ ↦ (hp e).2
      refine CSHTwoA.cshMargin_nonneg_of_within H x Y [] o v hY ?_ f hf
      intro g hg hg0
      exact within_nonneg H hp x Y [] o v hv List.nodup_nil
        (fun d hd ↦ absurd hd (List.not_mem_nil)) hg hg0
        (fun pre d ds' hs ↦ by simp at hs)
  | succ k ih =>
      intro D hlen x Y o v hxY ho hv hov hnd hdis f hf
      have hY : ∀ e ∈ labelsMeeting H Y, (H.prob e : ℝ) < 1 :=
        fun e _ ↦ (hp e).2
      refine CSHTwoA.cshMargin_nonneg_of_within H x Y D o v hY
        (fun g hg hg0 ↦ ?_) f hf
      refine within_nonneg H hp x Y D o v hv hnd ?_ hg hg0 ?_
      · intro d hd
        exact ⟨fun hdx ↦ (hdis d hd).1
            (Set.mem_insert_iff.2 (Or.inl hdx)),
          fun hdY ↦ (hdis d hd).1
            (Set.mem_insert_iff.2 (Or.inr hdY)),
          (hdis d hd).2.1, (hdis d hd).2.2⟩
      · intro pre d ds' hsplit h hh hh0
        have hlen' : ds'.length ≤ k := by
          have heq : D.length = pre.length + (ds'.length + 1) := by
            rw [hsplit, List.length_append, List.length_cons]
          omega
        have hdD : d ∈ D := by
          rw [hsplit]
          exact List.mem_append_right pre List.mem_cons_self
        have hpreD : ∀ e ∈ pre, e ∈ D := by
          intro e he
          rw [hsplit]
          exact List.mem_append_left _ he
        have hdsD : ∀ e ∈ ds', e ∈ D := by
          intro e he
          rw [hsplit]
          exact List.mem_append_right pre (List.mem_cons_of_mem d he)
        have hnd' : (pre ++ d :: ds').Nodup := hsplit ▸ hnd
        have hndds : ds'.Nodup :=
          (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).2
        have hd_notin_ds : d ∉ ds' :=
          (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).1
        have hd_notin_pre : d ∉ pre := fun hdp ↦
          (List.nodup_append.1 hnd').2.2 d hdp d List.mem_cons_self rfl
        have hds_notin_pre : ∀ e ∈ ds', e ∉ pre := by
          intro e he hep
          exact (List.nodup_append.1 hnd').2.2 e hep e
            (List.mem_cons_of_mem d he) rfl
        let Y' : Set V := insert x Y ∪ {e | e ∈ pre}
        have hdY' : d ∉ Y' := by
          rintro (h1 | h2)
          · exact (hdis d hdD).1 h1
          · exact hd_notin_pre h2
        have hoY' : o ∉ insert d Y' := by
          rintro (h0 | h1 | h2)
          · exact (hdis d hdD).2.1 h0.symm
          · exact ho h1
          · exact (hdis o (hpreD o h2)).2.1 rfl
        have hvY' : v ∉ insert d Y' := by
          rintro (h0 | h1 | h2)
          · exact (hdis d hdD).2.2 h0.symm
          · exact hv h1
          · exact (hdis v (hpreD v h2)).2.2 rfl
        have hdis' : ∀ e ∈ ds',
            e ∉ insert d Y' ∧ e ≠ o ∧ e ≠ v := by
          intro e he
          refine ⟨?_, (hdis e (hdsD e he)).2.1,
            (hdis e (hdsD e he)).2.2⟩
          rintro (h0 | h1 | h2)
          · exact hd_notin_ds (h0 ▸ he)
          · exact (hdis e (hdsD e he)).1 h1
          · exact hds_notin_pre e he h2
        exact ih ds' hlen' d Y' o v hdY' hoY' hvY' hov hndds hdis' h hh

/-- The formerly open interior hierarchy is inhabited for every finite
labelled hypergraph. -/
theorem hyperCSHInterior :
    KNAll.Site.HyperFixedFromCSH.HyperCSHInterior := by
  intro W L _ _ H hp x Y D o v hxY hox hvx hoY hvY hov hnd hdis
  have ho : o ∉ insert x Y := by
    rw [Set.mem_insert_iff, not_or]
    exact ⟨hox, hoY⟩
  have hv : v ∉ insert x Y := by
    rw [Set.mem_insert_iff, not_or]
    exact ⟨hvx, hvY⟩
  refine fun f hf ↦ cshMargin_nonneg H hp D x Y o v hxY ho hv hov hnd ?_ f hf
  intro d hd
  exact ⟨by
    rw [Set.mem_insert_iff, not_or]
    exact ⟨(hdis d hd).1, (hdis d hd).2.1⟩,
    (hdis d hd).2.2.1, (hdis d hd).2.2.2⟩

/-- Finite multiplicative gluing for independent labelled hyperedges. -/
theorem hyperedgeGluing : HyperedgeGluing :=
  KNAll.Site.HyperFixedFromCSH.hyperedgeGluing_of_cshInterior
    hyperCSHInterior

/-- The pinned site connector inequality consumed by the lattice layer. -/
theorem pinnedSiteGluing : PinnedSiteGluing :=
  pinnedSiteGluing_of_hyperedgeGluing hyperedgeGluing

end KNAll.Site.FiniteHyperGluingClosed

end

#print axioms KNAll.Site.FiniteHyperGluingClosed.world_cov_eq_covH
#print axioms KNAll.Site.FiniteHyperGluingClosed.corrected_fk_monotone
#print axioms KNAll.Site.FiniteHyperGluingClosed.within_unfold
#print axioms KNAll.Site.FiniteHyperGluingClosed.subT_comb_nonneg
#print axioms KNAll.Site.FiniteHyperGluingClosed.within_nonneg
#print axioms KNAll.Site.FiniteHyperGluingClosed.cshMargin_nonneg
#print axioms KNAll.Site.FiniteHyperGluingClosed.hyperCSHInterior
#print axioms KNAll.Site.FiniteHyperGluingClosed.hyperedgeGluing
#print axioms KNAll.Site.FiniteHyperGluingClosed.pinnedSiteGluing
