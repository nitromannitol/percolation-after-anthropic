import Hypergraph.SiteStatements

/-!
# The lower bound `p_c^site(ℤ^d) ≥ 1/(2d)`

This module proves, for site percolation on `ℤ^d`, the path-counting half of Grimmett 1999,
Theorem (1.10).  It is the site transcription of `Percolation.Literature.theta_zd_le_pow`,
`Percolation.Literature.theta_zd_eq_zero_of_lt` and `Percolation.Literature.criticalProb_zd_pos`,
with vertices in place of edges.

* `exists_openSiteWord_of_infinite`: if the open cluster of the origin is infinite then for every
  `n` there is a step word `w ∈ ({1,…,d} × {±})ⁿ` whose `n` positions `wordPos w k`, `k < n`, are
  distinct and open.  The word is read off a self-avoiding open path, which exists because the
  cluster leaves the finite set of endpoints of shorter words.
* `thetaSite_le_pow`: hence `θ(p) ≤ (2d)ⁿ pⁿ`, since there are at most `(2d)ⁿ` words and each
  contributes `pⁿ` (`siteBernoulli_real_subset`).
* `thetaSite_eq_zero_of_lt`: `θ(p) = 0` for `p < 1/(2d)`, because `(2dp)ⁿ → 0`.
* `criticalProbSite_ge`, `criticalProbSite_pos`: `p_c^site(ℤ^d) ≥ 1/(2d) > 0`.

`sInf_notMem_of_left_improvable` is the abstract endgame lemma: an infimum is not attained when
every member of the set is beaten by a smaller one.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §1.4 pp. 15–16, (1.13)–(1.16).
-/

noncomputable section

namespace KNAll.Site

open Filter MeasureTheory Set Topology
open Percolation.Literature Percolation.Literature.LatticeModels

/-! ## An infimum with no smallest member is not attained -/

/-- If every member of `S` is beaten by a smaller member, then `sInf S ∉ S`. -/
theorem sInf_notMem_of_left_improvable (S : Set ℝ) (hbdd : BddBelow S)
    (h : ∀ p ∈ S, ∃ q ∈ S, q < p) : sInf S ∉ S := by
  intro hmem
  obtain ⟨q, hq, hlt⟩ := h _ hmem
  exact absurd (csInf_le hbdd hq) (not_le.2 hlt)

/-! ## Cylinders of open vertices -/

/-- All vertices of a finite set are open with probability `p ^ |F|`. -/
theorem siteBernoulli_real_subset {V : Type*} (p : unitInterval) (F : Finset V) :
    (siteBernoulli (fun _ : V => p)).real {ω : Set V | (F : Set V) ⊆ ω} = (p : ℝ) ^ F.card := by
  show (prodBernoulli (fun _ : V => p)).real {ω : Set V | (F : Set V) ⊆ ω} = (p : ℝ) ^ F.card
  rw [prodBernoulli_real_subset]
  simp

/-! ## From an infinite open cluster to open words of every length -/

/-- **Open paths of all lengths** (Grimmett 1999, §1.4 p. 16, in its site form): if the open
cluster of the origin is infinite, then for every `n` some step word visits `n` distinct open
vertices `wordPos w k`, `k < n`.  The word is read off the self-avoiding path obtained by
bypassing a walk to a vertex of the cluster lying outside the finite set of endpoints of shorter
words. -/
theorem exists_openSiteWord_of_infinite {d : ℕ} {ω : Set (Site d)}
    (hC : (siteCluster (zdGraph d) ω 0).Infinite) (n : ℕ) :
    ∃ w : Fin n → Fin d × Bool,
      ((Finset.range n).image fun k => wordPos w k).card = n ∧
      (↑((Finset.range n).image fun k => wordPos w k) : Set (Site d)) ⊆ ω := by
  classical
  have hG : openSiteGraph (zdGraph d) ω ≤ zdGraph d := by
    intro x y hxy
    exact ((openSiteGraph_adj_iff' (zdGraph d) ω x y).1 hxy).1
  -- the finitely many endpoints of words shorter than `n`
  set S : Set (Site d) := ⋃ k : Fin n, Set.range fun w : Fin k → Fin d × Bool => wordPos w k
    with hSdef
  have hSfin : S.Finite := Set.finite_iUnion fun _ => Set.finite_range _
  obtain ⟨y, hyC, hyS⟩ := (hC.sdiff hSfin).nonempty
  obtain ⟨-, hreach⟩ := hyC
  obtain ⟨q⟩ := hreach
  set r := q.bypass with hr
  have hrp : r.IsPath := q.bypass_isPath
  -- `r` has length at least `n`, for otherwise `y ∈ S`
  have hn : n ≤ r.length := by
    by_contra hcon
    have hlt : r.length < n := not_le.1 hcon
    obtain ⟨w, hw⟩ := exists_word_of_walk hG r r.length le_rfl
    exact hyS (Set.mem_iUnion.2 ⟨⟨r.length, hlt⟩, w, by simpa using hw r.length le_rfl⟩)
  obtain ⟨w, hw⟩ := exists_word_of_walk hG r n hn
  refine ⟨w, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk l hl hkl
    simp only [Finset.coe_range, Set.mem_Iio] at hk hl
    have hkl' : wordPos w k = wordPos w l := hkl
    rw [hw k hk.le, hw l hl.le] at hkl'
    exact hrp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hkl'
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [hw k hk.le]
    exact ((openSiteGraph_adj_iff' (zdGraph d) ω _ _).1
      (r.adj_getVert_succ (lt_of_lt_of_le hk hn))).2.1

/-! ## Path counting -/

/-- **Path counting** (Grimmett 1999, §1.4, (1.15), in its site form): `θ(p) ≤ (2d)ⁿ pⁿ`, since an
infinite cluster of the origin supplies a word visiting `n` distinct open vertices, there are at
most `(2d)ⁿ` words, and each set of `n` vertices is open with probability `pⁿ`. -/
theorem thetaSite_le_pow (d n : ℕ) (p : unitInterval) :
    thetaSite d p ≤ (2 * d : ℝ) ^ n * (p : ℝ) ^ n := by
  classical
  -- the vertices visited by a word, and the words visiting `n` distinct vertices
  obtain ⟨P, hP⟩ : ∃ P : (Fin n → Fin d × Bool) → Finset (Site d),
      ∀ w, P w = (Finset.range n).image fun k => wordPos w k := ⟨_, fun _ => rfl⟩
  obtain ⟨good, hgood⟩ : ∃ good : Finset (Fin n → Fin d × Bool),
      good = Finset.univ.filter fun w => (P w).card = n := ⟨_, rfl⟩
  have hsub : {ω : Set (Site d) | (siteCluster (zdGraph d) ω 0).Infinite} ⊆
      ⋃ w ∈ good, {ω : Set (Site d) | (↑(P w) : Set (Site d)) ⊆ ω} := by
    intro ω hω
    obtain ⟨w, hcard, hwω⟩ := exists_openSiteWord_of_infinite hω n
    refine Set.mem_biUnion (x := w) ?_ ?_
    · rw [hgood]
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hP]; exact hcard⟩)
    · show (↑(P w) : Set (Site d)) ⊆ ω
      rw [hP]; exact hwω
  calc thetaSite d p
      = (siteBernoulli fun _ : Site d => p).real
          {ω : Set (Site d) | (siteCluster (zdGraph d) ω 0).Infinite} := rfl
    _ ≤ (siteBernoulli fun _ : Site d => p).real
          (⋃ w ∈ good, {ω : Set (Site d) | (↑(P w) : Set (Site d)) ⊆ ω}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ w ∈ good, (siteBernoulli fun _ : Site d => p).real
          {ω : Set (Site d) | (↑(P w) : Set (Site d)) ⊆ ω} :=
        measureReal_biUnion_finset_le _ _
    _ = ∑ w ∈ good, (p : ℝ) ^ n := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [siteBernoulli_real_subset p (P w)]
        rw [hgood, Finset.mem_filter] at hw
        rw [hw.2]
    _ = good.card * (p : ℝ) ^ n := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d : ℝ) ^ n * (p : ℝ) ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg p.2.1 n)
        have h1 : good.card ≤ (Finset.univ : Finset (Fin n → Fin d × Bool)).card :=
          Finset.card_le_univ _
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, Fintype.card_bool] at h1
        calc (good.card : ℝ) ≤ ((d * 2) ^ n : ℕ) := by exact_mod_cast h1
          _ = (2 * d : ℝ) ^ n := by push_cast; ring

/-- **No site percolation below `1/(2d)`** (Grimmett 1999, §1.4, (1.16), in its site form): the
bound `θ(p) ≤ (2dp)ⁿ` of `thetaSite_le_pow` tends to `0` when `2dp < 1`. -/
theorem thetaSite_eq_zero_of_lt (d : ℕ) [NeZero d] (p : unitInterval)
    (hp : (p : ℝ) < 1 / (2 * d)) : thetaSite d p = 0 := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hd : (0 : ℝ) < 2 * d := by linarith
  have hlt : 2 * d * (p : ℝ) < 1 := by rwa [lt_div_iff₀ hd, mul_comm] at hp
  have h0 : 0 ≤ 2 * d * (p : ℝ) := mul_nonneg hd.le p.2.1
  have ht : Tendsto (fun n : ℕ => (2 * d * (p : ℝ)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 hlt
  have hle : thetaSite d p ≤ 0 :=
    ge_of_tendsto' ht fun n => by rw [mul_pow]; exact thetaSite_le_pow d n p
  exact le_antisymm hle (thetaSiteOn_nonneg _ _ _)

/-! ## The critical parameter is positive -/

/-- **`p_c^site(ℤ^d) ≥ 1/(2d)`**: every parameter at which the origin percolates is at least
`1/(2d)`, and so is the extra point `1`. -/
theorem criticalProbSite_ge (d : ℕ) [NeZero d] : 1 / (2 * d : ℝ) ≤ criticalProbSite d := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hd : (0 : ℝ) < 2 * d := by linarith
  refine le_csInf ⟨1, Or.inr rfl⟩ ?_
  rintro q (⟨hq, hpos⟩ | hq)
  · by_contra hcon
    exact hpos.ne' (thetaSite_eq_zero_of_lt d ⟨q, hq⟩ (not_le.1 hcon))
  · rw [Set.mem_singleton_iff] at hq
    rw [hq, div_le_one hd]
    linarith

/-- **`p_c^site(ℤ^d) > 0`** (Grimmett 1999, §1.4, Theorem (1.10), lower bound, in its site form). -/
theorem criticalProbSite_pos (d : ℕ) [NeZero d] : 0 < criticalProbSite d := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have h : (0 : ℝ) < 1 / (2 * d) := by
    apply div_pos one_pos
    linarith
  exact lt_of_lt_of_le h (criticalProbSite_ge d)

end KNAll.Site

end
