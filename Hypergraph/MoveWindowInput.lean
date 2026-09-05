import Hypergraph.GateTwoChain
import Hypergraph.ProdBernoulliFKG
import Percolation.Literature.GMFiniteSize

/-!
# Finite site-percolation target cylinders for the Section 8 move windows

This file contains the site analogue of the finite quarter-face estimate used in
`CORRIDOR_MOVE.md`, Section 5.  In particular, the event below is not `localFaceEvent`: its first
endpoint is required to lie in the named source box and its second endpoint is required to lie in
the named target face.
-/

noncomputable section

open scoped Classical

namespace KNAll.Site.MoveWindowInput

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {d : ℕ}

/-- A finite source set is connected to a finite target set inside a finite allowed set. -/
def finiteTargetHit (Q S T : Finset (Site d)) : Set (SiteConfig (Site d)) :=
  ⋃ s ∈ (↑S : Set (Site d)), ⋃ t ∈ (↑T : Set (Site d)),
    connWithin (zdGraph d) (↑Q : Set (Site d)) s t

theorem mem_finiteTargetHit_iff (Q S T : Finset (Site d)) (ω : SiteConfig (Site d)) :
    ω ∈ finiteTargetHit Q S T ↔
      ∃ s ∈ S, ∃ t ∈ T, ω ∈ connWithin (zdGraph d) (↑Q : Set (Site d)) s t := by
  simp [finiteTargetHit]

theorem determinedBy_finiteTargetHit (Q S T : Finset (Site d)) :
    DeterminedBy (finiteTargetHit Q S T) (↑Q : Set (Site d)) :=
  DeterminedBy.iUnion fun _ => DeterminedBy.iUnion fun _ =>
    DeterminedBy.iUnion fun _ => DeterminedBy.iUnion fun _ =>
      determinedBy_connWithin (zdGraph d) (↑Q : Set (Site d)) _ _

theorem measurableSet_finiteTargetHit (Q S T : Finset (Site d)) :
    MeasurableSet (finiteTargetHit Q S T) :=
  (determinedBy_finiteTargetHit Q S T).measurableSet_of_finset

theorem isUpperSet_finiteTargetHit (Q S T : Finset (Site d)) :
    IsUpperSet (finiteTargetHit Q S T) :=
  isUpperSet_iUnion₂ fun _ _ => isUpperSet_iUnion₂ fun _ _ =>
    isUpperSet_connWithin (zdGraph d) (↑Q : Set (Site d)) _ _

/-- Enlarging any of the three finite geometric sets can only enlarge the hit event. -/
theorem finiteTargetHit_mono {Q Q' S S' T T' : Finset (Site d)}
    (hQ : Q ⊆ Q') (hS : S ⊆ S') (hT : T ⊆ T') :
    finiteTargetHit Q S T ⊆ finiteTargetHit Q' S' T' := by
  intro ω hω
  obtain ⟨s, hs, t, ht, hst⟩ := (mem_finiteTargetHit_iff Q S T ω).1 hω
  exact (mem_finiteTargetHit_iff Q' S' T' ω).2
    ⟨s, hS hs, t, hT ht, connWithin_mono_set (zdGraph d) (Finset.coe_subset.2 hQ) s t hst⟩

/-! ### Translation of finite target connections -/

/-- Translation of a set by `v`. -/
def shiftSet (v : Site d) (S : Set (Site d)) : Set (Site d) :=
  {x | x - v ∈ S}

/-- Translation of a finite set by `v`. -/
def shiftFinset (v : Site d) (F : Finset (Site d)) : Finset (Site d) :=
  F.image fun x => x + v

theorem coe_shiftFinset (v : Site d) (F : Finset (Site d)) :
    (↑(shiftFinset v F) : Set (Site d)) = shiftSet v (↑F : Set (Site d)) := by
  ext x
  simp [shiftFinset, shiftSet, sub_eq_add_neg]

theorem siteShift_inter_shiftSet (v : Site d) (ω : SiteConfig (Site d))
    (S : Set (Site d)) :
    siteShift v (ω ∩ shiftSet v S) = siteShift v ω ∩ S := by
  ext x
  simp [siteShift, shiftSet]

/-- A confined connection is transported exactly by a lattice translation. -/
theorem mem_connWithin_shift_iff (v : Site d) (ω : SiteConfig (Site d))
    (S : Set (Site d)) (x y : Site d) :
    siteShift v ω ∈ connWithin (zdGraph d) S x y ↔
      ω ∈ connWithin (zdGraph d) (shiftSet v S) (x + v) (y + v) := by
  rw [mem_connWithin_iff, mem_connWithin_iff]
  have hreach := reachable_siteShift_iff v (ω ∩ shiftSet v S) x y
  rw [siteShift_inter_shiftSet] at hreach
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨⟨?_, ?_⟩, hreach.1 hxy⟩
    · simpa using hx.1
    · simpa [shiftSet] using hx.2
  · rintro ⟨hx, hxy⟩
    refine ⟨⟨?_, ?_⟩, hreach.2 hxy⟩
    · simpa using hx.1
    · simpa [shiftSet] using hx.2

/-- A connection to a target set is transported exactly by a lattice translation. -/
theorem mem_connWithinSet_shift_iff (v : Site d) (ω : SiteConfig (Site d))
    (S : Set (Site d)) (x : Site d) (B : Set (Site d)) :
    siteShift v ω ∈ connWithinSet (zdGraph d) S x B ↔
      ω ∈ connWithinSet (zdGraph d) (shiftSet v S) (x + v) (shiftSet v B) := by
  rw [mem_connWithinSet_iff, mem_connWithinSet_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y + v, by simpa [shiftSet] using hy,
      (mem_connWithin_shift_iff v ω S x y).1 hxy⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y - v, by simpa [shiftSet] using hy, ?_⟩
    have h := (mem_connWithin_shift_iff v ω S x (y - v)).2
    exact h (by simpa using hxy)

/-- Relabelling commutes with intersection with a relabelled set. -/
theorem relabel_inter_image (e : Site d ≃ Site d) (ω A : Set (Site d)) :
    SiteConfig.relabel e (ω ∩ A) = SiteConfig.relabel e ω ∩ e '' A := by
  ext x
  simp only [SiteConfig.mem_relabel_iff, Set.mem_inter_iff, Set.mem_image]
  constructor
  · intro h
    exact ⟨h.1, e.symm x, h.2, e.apply_symm_apply x⟩
  · rintro ⟨hω, y, hy, hey⟩
    subst x
    exact ⟨by simpa using hω, by simpa using hy⟩

/-- Confined site connections are transported by a lattice graph automorphism. -/
theorem mem_connWithin_relabel_iff (e : Site d ≃ Site d)
    (he : ∀ a b, (zdGraph d).Adj (e a) (e b) ↔ (zdGraph d).Adj a b)
    (ω : SiteConfig (Site d)) (A : Set (Site d)) (x y : Site d) :
    SiteConfig.relabel e ω ∈ connWithin (zdGraph d) (e '' A) (e x) (e y) ↔
      ω ∈ connWithin (zdGraph d) A x y := by
  rw [mem_connWithin_iff, mem_connWithin_iff, ← relabel_inter_image]
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨?_, (siteReach_relabel_iff e he (ω ∩ A) x y).1 hxy⟩
    simpa only [SiteConfig.mem_relabel_iff, Equiv.symm_apply_apply] using hx
  · rintro ⟨hx, hxy⟩
    refine ⟨?_, (siteReach_relabel_iff e he (ω ∩ A) x y).2 hxy⟩
    simpa only [SiteConfig.mem_relabel_iff, Equiv.symm_apply_apply] using hx

/-- I.i.d. site percolation is invariant under a relabelling equivalence. -/
theorem measurePreserving_siteRelabel (p : unitInterval) (e : Site d ≃ Site d) :
    MeasurePreserving (SiteConfig.relabel e)
      (siteBernoulli fun _ : Site d => p) (siteBernoulli fun _ : Site d => p) := by
  have hfun : SiteConfig.relabel e = restrictSite e.symm := by
    funext ω
    ext x
    simp only [SiteConfig.mem_relabel_iff, mem_restrictSite]
  refine ⟨(SiteConfig.relabel e).measurable, ?_⟩
  rw [hfun]
  exact siteBernoulli_map_restrictSite e.symm.injective p

/-- A signed permutation maps the corresponding face piece onto the canonical face. -/
theorem image_piece_sp_eq_faceFin [NeZero d] (g : GM.HOct d) (n : ℕ) :
    (GM.piece g n).image (GM.sp g) = GM.faceFin d n := by
  ext x
  simp only [Finset.mem_image, GM.piece, Finset.mem_filter, GM.mem_faceFin]
  constructor
  · rintro ⟨y, ⟨hybox, hyface⟩, rfl⟩
    exact hyface
  · intro hx
    refine ⟨(GM.sp g).symm x, ?_, (GM.sp g).apply_symm_apply x⟩
    constructor
    · have hxbox : x ∈ box d n := by
        rw [mem_box]
        intro i
        rcases eq_or_ne i 0 with rfl | hi
        · rw [hx.1]; omega
        · have hxi := hx.2 i hi
          omega
      have himage : GM.sp g ((GM.sp g).symm x) ∈ box d n := by simpa using hxbox
      exact (signedPerm_mem_box_iff g.1 g.2).1 himage
    · simpa using hx

/-- Signed permutations preserve the probability of the corresponding finite site-hit event. -/
theorem prob_finiteTargetHit_piece_eq [NeZero d] (g : GM.HOct d) (k n : ℕ)
    (p : unitInterval) :
    (siteBernoulli fun _ : Site d => p).real
        (finiteTargetHit (box d n) (box d k) (GM.piece g n)) =
      (siteBernoulli fun _ : Site d => p).real
        (finiteTargetHit (box d n) (box d k) (GM.faceFin d n)) := by
  let e : Site d ≃ Site d := GM.sp g
  have he : ∀ a b, (zdGraph d).Adj (e a) (e b) ↔ (zdGraph d).Adj a b := by
    intro a b
    exact (GM.spIso g).map_rel_iff
  have hpre : SiteConfig.relabel e ⁻¹'
      finiteTargetHit (box d n) (box d k) (GM.faceFin d n) =
        finiteTargetHit (box d n) (box d k) (GM.piece g n) := by
    ext ω
    simp only [Set.mem_preimage, mem_finiteTargetHit_iff]
    constructor
    · rintro ⟨s', hs', t', ht', hst⟩
      refine ⟨e.symm s', ?_, e.symm t', ?_, ?_⟩
      · have hsImage : e (e.symm s') ∈ box d k := by simpa using hs'
        exact (signedPerm_mem_box_iff g.1 g.2).1 hsImage
      · have htImage : t' ∈ (GM.piece g n).image e := by
          rw [image_piece_sp_eq_faceFin]
          exact ht'
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 htImage
        simpa using ht
      · have hboxImage : e '' (↑(box d n) : Set (Site d)) = ↑(box d n) := by
          ext z
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact Finset.mem_coe.2 ((signedPerm_mem_box_iff g.1 g.2).2 (Finset.mem_coe.1 hy))
          · intro hz
            refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
            have : e (e.symm z) ∈ box d n := by simpa using hz
            exact Finset.mem_coe.2 ((signedPerm_mem_box_iff g.1 g.2).1 this)
        rw [← hboxImage] at hst
        simpa using (mem_connWithin_relabel_iff e he ω _ (e.symm s') (e.symm t')).1
          (by simpa using hst)
    · rintro ⟨s, hs, t, ht, hst⟩
      refine ⟨e s, ?_, e t, ?_, ?_⟩
      · exact (signedPerm_mem_box_iff g.1 g.2).2 hs
      · rw [← image_piece_sp_eq_faceFin]
        exact Finset.mem_image.2 ⟨t, ht, rfl⟩
      · have hboxImage : e '' (↑(box d n) : Set (Site d)) = ↑(box d n) := by
          ext z
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact Finset.mem_coe.2 ((signedPerm_mem_box_iff g.1 g.2).2 (Finset.mem_coe.1 hy))
          · intro hz
            refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
            have : e (e.symm z) ∈ box d n := by simpa using hz
            exact Finset.mem_coe.2 ((signedPerm_mem_box_iff g.1 g.2).1 this)
        rw [← hboxImage]
        exact (mem_connWithin_relabel_iff e he ω _ s t).2 hst
  rw [← hpre]
  have hm := (measurePreserving_siteRelabel p e).measure_preimage
    (measurableSet_finiteTargetHit (box d n) (box d k) (GM.faceFin d n)).nullMeasurableSet
  exact congrArg ENNReal.toReal hm

/-- The site-hit probabilities of all face orthants are equal. -/
theorem prob_finiteTargetHit_orthantFace_eq [NeZero d] (a : Fin d) (τ : Fin d → ℤˣ)
    (k n : ℕ) (p : unitInterval) :
    (siteBernoulli fun _ : Site d => p).real
        (finiteTargetHit (box d n) (box d k) (orthantFace a τ n)) =
      (siteBernoulli fun _ : Site d => p).real
        (finiteTargetHit (box d n) (box d k) (GM.faceFin d n)) := by
  let g : GM.HOct d := (Equiv.swap 0 a, fun j => τ (Equiv.swap 0 a j))
  rw [orthantFace_eq_piece a τ n]
  exact prob_finiteTargetHit_piece_eq g k n p

/-- Harris for a finite intersection of decreasing site events. -/
theorem prod_prob_le_biInter_of_isLowerSet {I : Type*} [Fintype I]
    (p : unitInterval) (A : I → Set (SiteConfig (Site d)))
    (hA : ∀ i, IsLowerSet (A i)) (hAm : ∀ i, MeasurableSet (A i)) :
    ∏ i, (siteBernoulli fun _ : Site d => p).real (A i) ≤
      (siteBernoulli fun _ : Site d => p).real (⋂ i, A i) := by
  classical
  let μ := siteBernoulli fun _ : Site d => p
  have hfin : ∀ s : Finset I, ∏ i ∈ s, μ.real (A i) ≤ μ.real (⋂ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [μ]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.set_biInter_insert]
      calc
        μ.real (A a) * ∏ i ∈ s, μ.real (A i)
            ≤ μ.real (A a) * μ.real (⋂ i ∈ s, A i) :=
          mul_le_mul_of_nonneg_left ih measureReal_nonneg
        _ ≤ μ.real (A a ∩ ⋂ i ∈ s, A i) :=
          prodBernoulli_harris_lower _ (hA a)
            (isLowerSet_iInter₂ fun i _ => hA i) (hAm a)
            (s.measurableSet_biInter fun i _ => hAm i)
  simpa using hfin (Finset.univ : Finset I)

/-! ## The finite quarter-face estimate -/

/-- The `d 2^d` oriented face orthants of a cube. -/
abbrev FaceIndex (d : ℕ) := Fin d × (Fin d → ℤˣ)

/-- A face-orthant hitting event with a genuine source box and confinement to the outer cube. -/
def orthantHit (k n : ℕ) (aτ : FaceIndex d) : Set (SiteConfig (Site d)) :=
  finiteTargetHit (box d n) (box d k) (orthantFace aτ.1 aτ.2 n)

theorem determinedBy_orthantHit (k n : ℕ) (aτ : FaceIndex d) :
    DeterminedBy (orthantHit k n aτ) (↑(box d n) : Set (Site d)) :=
  determinedBy_finiteTargetHit _ _ _

theorem measurableSet_orthantHit (k n : ℕ) (aτ : FaceIndex d) :
    MeasurableSet (orthantHit k n aτ) :=
  measurableSet_finiteTargetHit _ _ _

theorem isUpperSet_orthantHit (k n : ℕ) (aτ : FaceIndex d) :
    IsUpperSet (orthantHit k n aτ) :=
  isUpperSet_finiteTargetHit _ _ _

/-- A walk that first leaves a cube reaches its inner boundary by a connection confined to the
cube.  This is the site-percolation first-exit step in (5.2). -/
theorem exists_innerBoundary_connWithin_of_walk {L : ℕ} {ω : SiteConfig (Site d)} :
    ∀ {u w : Site d}, (openSiteGraph (zdGraph d) ω).Walk u w →
      u ∈ box d L → w ∉ box d L →
        ∃ a ∈ innerBoundary (zdGraph d) (box d L),
          ω ∈ connWithin (zdGraph d) (↑(box d L) : Set (Site d)) u a := by
  intro u w path
  induction path with
  | nil =>
      intro hu hw
      exact absurd hu hw
  | @cons u b w hub rest ih =>
      intro hu hw
      by_cases hb : b ∈ box d L
      · obtain ⟨a, ha, hba⟩ := ih hb hw
        refine ⟨a, ha, ?_⟩
        refine ⟨⟨?_, Finset.mem_coe.2 hu⟩, ?_⟩
        · exact (openSiteGraph_adj_iff' (zdGraph d) ω u b).1 hub |>.2.1
        · have hub' :
              (openSiteGraph (zdGraph d)
                (ω ∩ (↑(box d L) : Set (Site d)))).Adj u b := by
            exact (openSiteGraph_adj_iff' (zdGraph d)
            (ω ∩ (↑(box d L) : Set (Site d))) u b).2
              ⟨(openSiteGraph_adj_iff' (zdGraph d) ω u b).1 hub |>.1,
                ⟨(openSiteGraph_adj_iff' (zdGraph d) ω u b).1 hub |>.2.1,
                  Finset.mem_coe.2 hu⟩,
                ⟨(openSiteGraph_adj_iff' (zdGraph d) ω u b).1 hub |>.2.2,
                  Finset.mem_coe.2 hb⟩⟩
          exact hub'.reachable.trans hba.2
      · have ha : u ∈ innerBoundary (zdGraph d) (box d L) := by
          rw [mem_innerBoundary_iff]
          exact ⟨hu, b, hb, (openSiteGraph_adj_iff' (zdGraph d) ω u b).1 hub |>.1⟩
        refine ⟨u, ha, ?_⟩
        exact ⟨⟨(openSiteGraph_adj_iff' (zdGraph d) ω u b).1 hub |>.2.1,
          Finset.mem_coe.2 hu⟩, SimpleGraph.Reachable.refl u⟩

/-- Every inner-boundary site belongs to one of the `d 2^d` orthant faces. -/
theorem exists_faceIndex_of_mem_innerBoundary [NeZero d] {n : ℕ} {x : Site d}
    (hx : x ∈ innerBoundary (zdGraph d) (box d n)) :
    ∃ aτ : FaceIndex d, x ∈ orthantFace aτ.1 aτ.2 n := by
  obtain ⟨a, ha⟩ := exists_eq_of_mem_innerBoundary_box hx
  let τ : Fin d → ℤˣ := fun j => if 0 ≤ x j then 1 else -1
  refine ⟨(a, τ), ?_⟩
  rw [mem_orthantFace]
  refine ⟨(mem_innerBoundary_iff.1 hx).1, ?_, ?_⟩
  · rcases ha with ha | ha
    · have : 0 ≤ x a := by rw [ha]; positivity
      simp [τ, this, ha]
    · by_cases hn : n = 0
      · subst n
        simp at ha
        simp [τ, ha]
      · have : ¬ 0 ≤ x a := by rw [ha]; omega
        simp [τ, this, ha, hn]
  · intro j _hj
    by_cases hj : 0 ≤ x j
    · simp [τ, hj, hj]
    · simp [τ, hj]
      omega

/-- If the source box meets an infinite cluster, it hits at least one orthant of every larger
cube, along a path confined to that cube. -/
theorem exists_orthantHit_of_sitePerc [NeZero d] {k n : ℕ} (hkn : k ≤ n)
    {ω : SiteConfig (Site d)} {s : Site d} (hs : s ∈ box d k)
    (hperc : ω ∈ sitePerc (zdGraph d) s) :
    ∃ aτ : FaceIndex d, ω ∈ orthantHit k n aτ := by
  have hinf := (mem_sitePerc_iff (zdGraph d) ω s).1 hperc
  obtain ⟨w, hsw, hwn⟩ := hinf.exists_notMem_finset (box d n)
  obtain ⟨path⟩ := hsw
  obtain ⟨a, ha, hsa⟩ := exists_innerBoundary_connWithin_of_walk path
    (box_mono d hkn hs) hwn
  obtain ⟨aτ, haτ⟩ := exists_faceIndex_of_mem_innerBoundary ha
  exact ⟨aτ, (mem_finiteTargetHit_iff _ _ _ ω).2 ⟨s, hs, a, haτ, hsa⟩⟩

/-- The failure of every orthant hit forces the source box to miss every infinite cluster. -/
theorem iInter_compl_orthantHit_subset_missEvent [NeZero d] {k n : ℕ} (hkn : k ≤ n) :
    (⋂ aτ : FaceIndex d, (orthantHit k n aτ)ᶜ) ⊆
      missEvent d (↑(box d k) : Set (Site d)) := by
  intro ω hω s hs hperc
  obtain ⟨aτ, haτ⟩ := exists_orthantHit_of_sitePerc hkn (Finset.mem_coe.1 hs) hperc
  exact (Set.mem_iInter.1 hω aτ) haτ

/-- A hyperplane box is contained in the ambient cube of the same radius. -/
theorem hyperBox_subset_box [NeZero d] (i : Fin d) (m : ℕ) :
    hyperBox d i m ⊆ (↑(box d m) : Set (Site d)) := by
  rintro x ⟨hxi, hx⟩
  rw [Finset.mem_coe, mem_box]
  intro j
  by_cases hji : j = i
  · subst j
    rw [hxi]
    omega
  · exact hx j hji

/-- **Section 5, finite quarter-face estimate.**  At a supercritical parameter, one source box
hits every prescribed orthant face of every sufficiently large cube with probability `> 1-η`.
The Harris step is applied to the decreasing complements under the unconditioned i.i.d. site
product measure. -/
theorem exists_forall_lt_prob_orthantHit [NeZero d] (p : unitInterval)
    (hθ : 0 < thetaSite d p) {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, ∃ n₁ : ℕ, k < n₁ ∧ ∀ n, n₁ ≤ n → ∀ aτ : FaceIndex d,
      1 - η < (siteBernoulli fun _ : Site d => p).real (orthantHit k n aτ) := by
  classical
  by_cases hη1 : 1 < η
  · exact ⟨0, 1, Nat.zero_lt_one, fun n _ aτ =>
      lt_of_lt_of_le (by linarith) measureReal_nonneg⟩
  push_neg at hη1
  let i₀ : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  let Q : ℕ := Fintype.card (FaceIndex d)
  have hQpos : 0 < Q := Fintype.card_pos
  have hηQ : 0 < η ^ Q := pow_pos hη Q
  have htend := tendsto_measure_iInter_atTop
    (μ := siteBernoulli fun _ : Site d => p)
    (s := fun m : ℕ => missEvent d (hyperBox d i₀ m))
    (fun m => (measurableSet_missEvent (hyperBox d i₀ m)).nullMeasurableSet)
    (missEvent_antitone i₀) ⟨0, measure_ne_top _ _⟩
  rw [iInter_missEvent_hyperBox i₀,
    measure_missEvent_hyperplane_eq_zero SiteUniquenessInfiniteCluster_holds
      (Nat.pos_of_ne_zero (NeZero.ne d)) p hθ i₀] at htend
  have htend' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
  rw [ENNReal.toReal_zero] at htend'
  have hev := htend'.eventually_lt_const hηQ
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨k, k + 1, Nat.lt_succ_self k, fun n hn aτ => ?_⟩
  have hkn : k ≤ n := by omega
  let μ := siteBernoulli fun _ : Site d => p
  let D : FaceIndex d → Set (SiteConfig (Site d)) := fun b => (orthantHit k n b)ᶜ
  have hDlow : ∀ b, IsLowerSet (D b) := fun b => (isUpperSet_orthantHit k n b).compl
  have hDmeas : ∀ b, MeasurableSet (D b) := fun b => (measurableSet_orthantHit k n b).compl
  have hprod := prod_prob_le_biInter_of_isLowerSet p D hDlow hDmeas
  have hcanon : FaceIndex d :=
    (i₀, fun _ => 1)
  have heq : ∀ b : FaceIndex d, μ.real (D b) = μ.real (D hcanon) := by
    intro b
    have hp := (prob_finiteTargetHit_orthantFace_eq b.1 b.2 k n p).trans
      (prob_finiteTargetHit_orthantFace_eq hcanon.1 hcanon.2 k n p).symm
    dsimp [D]
    rw [measureReal_compl (measurableSet_orthantHit k n b), probReal_univ,
      measureReal_compl (measurableSet_orthantHit k n hcanon), probReal_univ]
    exact congrArg (fun z : ℝ => 1 - z) hp
  have hprod' : (μ.real (D hcanon)) ^ Q ≤ μ.real (⋂ b, D b) := by
    calc
      (μ.real (D hcanon)) ^ Q = ∏ b : FaceIndex d, μ.real (D b) := by
        simp_rw [heq]
        simp [Q]
      _ ≤ μ.real (⋂ b, D b) := hprod
  have hmiss : μ.real (missEvent d (↑(box d k) : Set (Site d))) < η ^ Q := by
    calc
      μ.real (missEvent d (↑(box d k) : Set (Site d)))
          ≤ μ.real (missEvent d (hyperBox d i₀ k)) :=
        measureReal_mono (fun ω hω x hx => hω x (hyperBox_subset_box i₀ k hx))
          (measure_ne_top _ _)
      _ < η ^ Q := hk
  have hpow : (μ.real (D hcanon)) ^ Q < η ^ Q :=
    lt_of_le_of_lt (hprod'.trans (measureReal_mono
      (iInter_compl_orthantHit_subset_missEvent hkn) (measure_ne_top _ _))) hmiss
  have hcanonlt : μ.real (D hcanon) < η := by
    by_contra hc
    push_neg at hc
    exact (not_lt_of_ge (pow_le_pow_left₀ hη.le hc Q)) hpow
  have hthis : μ.real (D aτ) < η := by rwa [heq aτ]
  rw [measureReal_compl (measurableSet_orthantHit k n aτ), probReal_univ] at hthis
  linarith

/-! ## The three-factor shell window of Section 4 -/

/-- The local-uniqueness factor of (4.1).  Its negation is the finite union of the
geometry-specific ordered-pair failures; in particular this definition contains no probabilistic
or target-hitting assumption. -/
def shellCoalescenceGood (m M N : ℕ) : Set (SiteConfig (Site d)) :=
  (⋃ xy ∈ box d m ×ˢ box d m, localCoalescenceEvent d M N xy.1 xy.2)ᶜ

/-- The event in (4.1), literally in the order
`Gᶜᵒᵃˡ ∩ Gᶠᵃᶜᵉ ∩ Gᵗᵃʳᵍᵉᵗ`.

`U` is the prescribed local quarter-face, while `T` is the desired (possibly much farther)
target.  The two connection factors are deliberately instances of `finiteTargetHit`, not
`localFaceEvent`. -/
def shellWindowEvent (m M N : ℕ) (U Q T : Finset (Site d)) :
    Set (SiteConfig (Site d)) :=
  (shellCoalescenceGood m M N ∩ finiteTargetHit (box d N) (box d m) U) ∩
    finiteTargetHit Q (box d m) T

/-- The support in (4.2): the complete local cube together with the prescribed finite target
geometry. -/
def shellWindowSupport (N : ℕ) (Q : Finset (Site d)) : Finset (Site d) :=
  box d N ∪ Q

theorem determinedBy_shellCoalescenceGood (m M N : ℕ) :
    DeterminedBy (shellCoalescenceGood (d := d) m M N) (↑(box d N) : Set (Site d)) := by
  unfold shellCoalescenceGood
  exact (DeterminedBy.iUnion fun _ => DeterminedBy.iUnion fun _ =>
    determinedBy_localCoalescenceEvent d M N _ _).compl

theorem measurableSet_shellCoalescenceGood (m M N : ℕ) :
    MeasurableSet (shellCoalescenceGood (d := d) m M N) :=
  (determinedBy_shellCoalescenceGood m M N).measurableSet_of_finset

theorem determinedBy_shellWindowEvent (m M N : ℕ) (U Q T : Finset (Site d)) :
    DeterminedBy (shellWindowEvent m M N U Q T)
      (↑(shellWindowSupport N Q) : Set (Site d)) := by
  apply DeterminedBy.inter
  · apply DeterminedBy.inter
    · exact (determinedBy_shellCoalescenceGood m M N).mono
        (Finset.coe_subset.2 Finset.subset_union_left)
    · exact (determinedBy_finiteTargetHit (box d N) (box d m) U).mono
        (Finset.coe_subset.2 Finset.subset_union_left)
  · exact (determinedBy_finiteTargetHit Q (box d m) T).mono
      (Finset.coe_subset.2 Finset.subset_union_right)

theorem measurableSet_shellWindowEvent (m M N : ℕ) (U Q T : Finset (Site d)) :
    MeasurableSet (shellWindowEvent m M N U Q T) :=
  ((measurableSet_shellCoalescenceGood m M N).inter
    (measurableSet_finiteTargetHit (box d N) (box d m) U)).inter
      (measurableSet_finiteTargetHit Q (box d m) T)

/-- The exact three-component union bound (4.3).  All component inequalities are strict, so the
derived bound is strict as well. -/
theorem one_sub_three_mul_lt_prob_shellWindowEvent (p : unitInterval) (m M N : ℕ)
    (U Q T : Finset (Site d)) {χ : ℝ}
    (hcoal : 1 - χ < (siteBernoulli fun _ : Site d => p).real
      (shellCoalescenceGood m M N))
    (hface : 1 - χ < (siteBernoulli fun _ : Site d => p).real
      (finiteTargetHit (box d N) (box d m) U))
    (htarget : 1 - χ < (siteBernoulli fun _ : Site d => p).real
      (finiteTargetHit Q (box d m) T)) :
    1 - 3 * χ < (siteBernoulli fun _ : Site d => p).real
      (shellWindowEvent m M N U Q T) := by
  let μ := siteBernoulli fun _ : Site d => p
  let A := shellCoalescenceGood (d := d) m M N
  let B := finiteTargetHit (box d N) (box d m) U
  let C := finiteTargetHit Q (box d m) T
  have hAm : MeasurableSet A := measurableSet_shellCoalescenceGood m M N
  have hBm : MeasurableSet B := measurableSet_finiteTargetHit _ _ _
  have hCm : MeasurableSet C := measurableSet_finiteTargetHit _ _ _
  have hAc : μ.real Aᶜ < χ := by
    rw [measureReal_compl hAm, probReal_univ]
    linarith
  have hBc : μ.real Bᶜ < χ := by
    rw [measureReal_compl hBm, probReal_univ]
    linarith
  have hCc : μ.real Cᶜ < χ := by
    rw [measureReal_compl hCm, probReal_univ]
    linarith
  have hU₁ := measureReal_union_le (μ := μ) Aᶜ Bᶜ
  have hU₂ := measureReal_union_le (μ := μ) (Aᶜ ∪ Bᶜ) Cᶜ
  have hcomp : μ.real ((A ∩ B) ∩ C)ᶜ < 3 * χ := by
    rw [compl_inter, compl_inter]
    linarith
  change 1 - 3 * χ < μ.real ((A ∩ B) ∩ C)
  rw [measureReal_compl (hAm.inter hBm |>.inter hCm), probReal_univ] at hcomp
  simpa [shellWindowEvent, A, B, C, μ] using (show 1 - 3 * χ < μ.real ((A ∩ B) ∩ C) by
    linarith)

/-- The component tolerance (4.4): pairwise failure `< χ / |Lambda_m|²` makes the
coalescence-good factor have probability `> 1-χ`. -/
theorem one_sub_lt_prob_shellCoalescenceGood (p : unitInterval) (m M N : ℕ) {χ : ℝ}
    (hχ : 0 < χ)
    (hpair : ∀ x ∈ box d m, ∀ y ∈ box d m,
      (siteBernoulli fun _ : Site d => p).real (localCoalescenceEvent d M N x y) <
        χ / (((((2 * m + 1) ^ d) ^ 2 : ℕ) : ℝ))) :
    1 - χ < (siteBernoulli fun _ : Site d => p).real
      (shellCoalescenceGood m M N) := by
  classical
  let μ := siteBernoulli fun _ : Site d => p
  let Bad := ⋃ xy ∈ box d m ×ˢ box d m, localCoalescenceEvent d M N xy.1 xy.2
  have hcard : (box d m ×ˢ box d m).card = (((2 * m + 1) ^ d) ^ 2) := by
    rw [Finset.card_product, card_box]
    ring
  have hden : (0 : ℝ) < (((((2 * m + 1) ^ d) ^ 2 : ℕ) : ℝ)) := by positivity
  have hbad : μ.real Bad < χ := by
    calc
      μ.real Bad ≤ ∑ xy ∈ box d m ×ˢ box d m,
          μ.real (localCoalescenceEvent d M N xy.1 xy.2) :=
        measureReal_biUnion_finset_le _ _
      _ < ∑ _xy ∈ box d m ×ˢ box d m,
          χ / (((((2 * m + 1) ^ d) ^ 2 : ℕ) : ℝ)) := by
        apply Finset.sum_lt_sum
        · intro xy hxy
          rw [Finset.mem_product] at hxy
          exact (hpair xy.1 hxy.1 xy.2 hxy.2).le
        · refine ⟨((0 : Site d), (0 : Site d)), ?_, ?_⟩
          · rw [Finset.mem_product]
            constructor <;> rw [mem_box] <;> simp
          · exact hpair 0 (by rw [mem_box]; simp) 0 (by rw [mem_box]; simp)
      _ = χ := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        field_simp
  have hBadMeas : MeasurableSet Bad :=
    Finset.measurableSet_biUnion _ fun xy _ =>
      measurableSet_localCoalescenceEvent d M N xy.1 xy.2
  change 1 - χ < μ.real Badᶜ
  rw [measureReal_compl hBadMeas, probReal_univ]
  linarith

/-- A confined path from the source box to a point outside `Lambda_M` supplies the arm to
`partial Lambda_M` required by the coalescence factor.  The returned arm is confined to the local
cube `Lambda_N`, independently of the larger region in which the original path was drawn. -/
theorem connWithinSet_boxSphere_of_connWithin {m M N : ℕ} (hmM : m ≤ M) (hMN : M ≤ N)
    {Q : Finset (Site d)} {ω : SiteConfig (Site d)} {s t : Site d}
    (hs : s ∈ box d m) (ht : t ∉ box d M)
    (hst : ω ∈ connWithin (zdGraph d) (↑Q : Set (Site d)) s t) :
    ω ∈ connWithinSet (zdGraph d) (↑(box d N) : Set (Site d)) s (boxSphere d M) := by
  obtain ⟨path⟩ := hst.2
  obtain ⟨a, haBoundary, hsa⟩ := exists_innerBoundary_connWithin_of_walk path
    (box_mono d hmM hs) ht
  have haSphere : a ∈ boxSphere d M := by
    obtain ⟨i, hi⟩ := exists_eq_of_mem_innerBoundary_box haBoundary
    exact ⟨mem_box.1 (mem_innerBoundary_iff.1 haBoundary).1, i, hi⟩
  rw [mem_connWithinSet_iff]
  refine ⟨a, haSphere, ?_⟩
  refine ⟨⟨hst.1.1, Finset.mem_coe.2 (box_mono d hMN (Finset.mem_coe.1 hsa.1.2))⟩,
    hsa.2.mono (openSiteGraph_mono (zdGraph d) ?_)⟩
  rintro z ⟨⟨hzω, -⟩, hzM⟩
  exact ⟨hzω, Finset.mem_coe.2 (box_mono d hMN (Finset.mem_coe.1 hzM))⟩

/-- The deterministic assertion in Section 4.  The local shell pattern fixes the endpoint `u` of
the face path.  In any other realization of the same three-factor event, the target path and that
fixed face path both cross `partial Lambda_M`; `Gᶜᵒᵃˡ` joins their source endpoints inside
`Lambda_N`, hence `u` reaches the actual target in the declared support.

This theorem is the direct discharge shape for the manuscript versions of `hrelay` and `hGdet`:
`determinedBy_shellWindowEvent` supplies `hGdet`, and this result supplies `hrelay`. -/
theorem shellWindowEvent_relay {m M N : ℕ} (hmM : m ≤ M) (hMN : M ≤ N)
    (U Q T : Finset (Site d))
    (hUout : ∀ u ∈ U, u ∉ box d M) (hTout : ∀ t ∈ T, t ∉ box d M) :
    ∀ ω ∈ shellWindowEvent m M N U Q T,
      ∃ u ∈ U, u ∈ ω ∧ ∀ ω' ∈ shellWindowEvent m M N U Q T,
        ω' ∩ (↑(box d N) : Set (Site d)) = ω ∩ ↑(box d N) →
          ω' ∈ connWithinSet (zdGraph d) (↑(shellWindowSupport N Q) : Set (Site d))
            u (↑T : Set (Site d)) := by
  intro ω hω
  obtain ⟨s, hs, u, hu, hsu⟩ :=
    (mem_finiteTargetHit_iff (box d N) (box d m) U ω).1 hω.1.2
  have huOpen : u ∈ ω :=
    (mem_of_mem_siteCluster (zdGraph d) (ω ∩ (↑(box d N) : Set (Site d))) ⟨hsu.1, hsu.2⟩).1
  refine ⟨u, hu, huOpen, fun ω' hω' hagree => ?_⟩
  have hsu' : ω' ∈ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) s u := by
    exact ((determinedBy_iff _ _).1
      (determinedBy_connWithin (zdGraph d) (↑(box d N) : Set (Site d)) s u)
      ω ω' hagree.symm).1 hsu
  obtain ⟨s', hs', t, ht, hs't⟩ :=
    (mem_finiteTargetHit_iff Q (box d m) T ω').1 hω'.2
  have hsArm := connWithinSet_boxSphere_of_connWithin hmM hMN hs (hUout u hu) hsu'
  have hs'Arm := connWithinSet_boxSphere_of_connWithin hmM hMN hs' (hTout t ht) hs't
  have hss' : ω' ∈ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) s s' := by
    by_contra hnot
    exact hω'.1.1 (Set.mem_iUnion₂.2 ⟨(s, s'),
      Finset.mem_product.2 ⟨hs, hs'⟩, ⟨⟨hsArm, hs'Arm⟩, hnot⟩⟩)
  let R : Set (Site d) := ↑(shellWindowSupport N Q)
  have hNR : (↑(box d N) : Set (Site d)) ⊆ R := by
    exact Finset.coe_subset.2 Finset.subset_union_left
  have hQR : (↑Q : Set (Site d)) ⊆ R := by
    exact Finset.coe_subset.2 Finset.subset_union_right
  have hus : ω' ∈ connWithin (zdGraph d) R u s :=
    connWithin_mono_set (zdGraph d) hNR u s
      ⟨mem_of_mem_siteCluster (zdGraph d)
          (ω' ∩ (↑(box d N) : Set (Site d))) ⟨hsu'.1, hsu'.2⟩, hsu'.2.symm⟩
  have hss'R : ω' ∈ connWithin (zdGraph d) R s s' :=
    connWithin_mono_set (zdGraph d) hNR s s' hss'
  have hs'tR : ω' ∈ connWithin (zdGraph d) R s' t :=
    connWithin_mono_set (zdGraph d) hQR s' t hs't
  rw [mem_connWithinSet_iff]
  exact ⟨t, Finset.mem_coe.2 ht,
    ⟨hus.1, (hus.2.trans hss'R.2).trans hs'tR.2⟩⟩

/-- The literal Section 4 version of `shellWindowEvent_relay`: the face factor ends on the
quarter-face of the local cube `Λ_M` itself.  Thus it already supplies one of the two arms to
`∂Λ_M`; only the target path has to be stopped on its first exit from `Λ_M`.

This is the form used by a `TargetExt.LevelGeometry`: its face `U` is part of the boundary of the
complete local cube, not a second, more distant sphere. -/
theorem shellWindowEvent_relay_of_face {m M N : ℕ} (hmM : m ≤ M) (hMN : M ≤ N)
    (U Q T : Finset (Site d))
    (hUface : ∀ u ∈ U, u ∈ boxSphere d M) (hTout : ∀ t ∈ T, t ∉ box d M) :
    ∀ ω ∈ shellWindowEvent m M N U Q T,
      ∃ u ∈ U, u ∈ ω ∧ ∀ ω' ∈ shellWindowEvent m M N U Q T,
        ω' ∩ (↑(box d N) : Set (Site d)) = ω ∩ ↑(box d N) →
          ω' ∈ connWithinSet (zdGraph d) (↑(shellWindowSupport N Q) : Set (Site d))
            u (↑T : Set (Site d)) := by
  intro ω hω
  obtain ⟨s, hs, u, hu, hsu⟩ :=
    (mem_finiteTargetHit_iff (box d N) (box d m) U ω).1 hω.1.2
  have huOpen : u ∈ ω :=
    (mem_of_mem_siteCluster (zdGraph d) (ω ∩ (↑(box d N) : Set (Site d))) ⟨hsu.1, hsu.2⟩).1
  refine ⟨u, hu, huOpen, fun ω' hω' hagree => ?_⟩
  have hsu' : ω' ∈ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) s u := by
    exact ((determinedBy_iff _ _).1
      (determinedBy_connWithin (zdGraph d) (↑(box d N) : Set (Site d)) s u)
      ω ω' hagree.symm).1 hsu
  obtain ⟨s', hs', t, ht, hs't⟩ :=
    (mem_finiteTargetHit_iff Q (box d m) T ω').1 hω'.2
  have hsArm :
      ω' ∈ connWithinSet (zdGraph d) (↑(box d N) : Set (Site d)) s (boxSphere d M) := by
    rw [mem_connWithinSet_iff]
    exact ⟨u, hUface u hu, hsu'⟩
  have hs'Arm := connWithinSet_boxSphere_of_connWithin hmM hMN hs' (hTout t ht) hs't
  have hss' : ω' ∈ connWithin (zdGraph d) (↑(box d N) : Set (Site d)) s s' := by
    by_contra hnot
    exact hω'.1.1 (Set.mem_iUnion₂.2 ⟨(s, s'),
      Finset.mem_product.2 ⟨hs, hs'⟩, ⟨⟨hsArm, hs'Arm⟩, hnot⟩⟩)
  let R : Set (Site d) := ↑(shellWindowSupport N Q)
  have hNR : (↑(box d N) : Set (Site d)) ⊆ R :=
    Finset.coe_subset.2 Finset.subset_union_left
  have hQR : (↑Q : Set (Site d)) ⊆ R :=
    Finset.coe_subset.2 Finset.subset_union_right
  have hus : ω' ∈ connWithin (zdGraph d) R u s :=
    connWithin_mono_set (zdGraph d) hNR u s
      ⟨mem_of_mem_siteCluster (zdGraph d)
          (ω' ∩ (↑(box d N) : Set (Site d))) ⟨hsu'.1, hsu'.2⟩, hsu'.2.symm⟩
  have hss'R : ω' ∈ connWithin (zdGraph d) R s s' :=
    connWithin_mono_set (zdGraph d) hNR s s' hss'
  have hs'tR : ω' ∈ connWithin (zdGraph d) R s' t :=
    connWithin_mono_set (zdGraph d) hQR s' t hs't
  rw [mem_connWithinSet_iff]
  exact ⟨t, Finset.mem_coe.2 ht,
    ⟨hus.1, (hus.2.trans hss'R.2).trans hs'tR.2⟩⟩

end KNAll.Site.MoveWindowInput

end
