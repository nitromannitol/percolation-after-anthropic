import Hypergraph.BoxConnection
import Hypergraph.RenormStable

/-!
# Renormalization plans: a certificate whose geometry points at its own estimates

A `RenormData` is a list of cylinder events with thresholds.  Nothing in it records which estimate is
meant to justify which piece of the construction, so a geometric argument written against it has to
carry the correspondence outside the formal statement, and can help itself to an estimate wherever
one is wanted.

A `RenormPlan` closes that gap.  The probabilistic content sits in a list of `ProbabilityBound`s, one
event with one threshold each.  The geometric content is a finite list of *uses*, each naming a box
of `ℤ^d`, two sites to be joined inside it, and an *index* into the list of bounds.  A use carries no
probability of its own; it can only point at one already stored.

Two propositions are kept strictly apart.

* `RenormPlan.WellFormed` is about geometry and parameter-free arithmetic: the boxes fit inside the
  working scale, the two named sites lie in their box, the thresholds lie in `[0,1)`, and the bound a
  use points at is decided by the sites of that use's own box.  It takes no parameter, and no
  probability appears in it.
* `RenormPlan.ValidAt q` is the finite conjunction of the strict inequalities
  `(bound i).lower < (bound i).experiment.prob q`, and nothing else.  It mentions no percolation
  event, quantifies over no configuration, and does not refer to `thetaSite`.

The separation is what gives `RenormPlan.exists_valid_nhds` its content: validity is a finite list of
strict inequalities between real numbers, each side of each inequality Lipschitz in the parameter, so
it survives a small enough shift.  Were a percolation statement allowed inside `ValidAt`, the
stability theorem would be either circular or empty.

`RenormPlan.toRenormData` forgets the pointers, so `siteCriticality_of_certificate` applies to a plan
with no change to the endgame.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

variable {d : ℕ}

/-! ## Boxes as finite objects

The certificate is only ever about finitely many sites, so the geometry it names has to be finite
too.  The box of radius `n` about a site is the product of `2n+1` integer intervals, a `Finset` by
`Fintype.piFinset`.
-/

/-- The box of radius `n` about the origin of `ℤ^d`, as a `Finset`. -/
def siteBox (d n : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(n : ℤ)) n

/-- The box of radius `n` about `c`, as a `Finset`.  This is the shape the plan's uses name: a use
lives in a box placed somewhere in the lattice, not necessarily at the origin. -/
def siteBoxAt (c : Site d) (n : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun j => Finset.Icc (c j - n) (c j + n)

theorem mem_siteBox {n : ℕ} {x : Site d} :
    x ∈ siteBox d n ↔ ∀ j, -(n : ℤ) ≤ x j ∧ x j ≤ n := by
  simp only [siteBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem mem_siteBoxAt {c x : Site d} {n : ℕ} :
    x ∈ siteBoxAt c n ↔ ∀ j, c j - n ≤ x j ∧ x j ≤ c j + n := by
  simp only [siteBoxAt, Fintype.mem_piFinset, Finset.mem_Icc]

/-- The origin lies in every box about the origin. -/
theorem zero_mem_siteBox (d n : ℕ) : (0 : Site d) ∈ siteBox d n := by
  rw [mem_siteBox]
  intro j
  show -(n : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ n
  omega

theorem siteBox_nonempty (d n : ℕ) : (siteBox d n).Nonempty :=
  ⟨0, zero_mem_siteBox d n⟩

/-- The centre lies in every box about it. -/
theorem mem_siteBoxAt_self (c : Site d) (n : ℕ) : c ∈ siteBoxAt c n := by
  rw [mem_siteBoxAt]
  intro j
  omega

/-- A box about the origin is a box placed at the origin. -/
theorem siteBoxAt_zero (d n : ℕ) : siteBoxAt (0 : Site d) n = siteBox d n := by
  ext x
  rw [mem_siteBoxAt, mem_siteBox]
  constructor
  · intro h j
    have hj : (0 : ℤ) - n ≤ x j ∧ x j ≤ (0 : ℤ) + n := h j
    omega
  · intro h j
    have hj := h j
    show (0 : ℤ) - n ≤ x j ∧ x j ≤ (0 : ℤ) + n
    omega

/-- Boxes about the origin grow with the radius. -/
theorem siteBox_subset {m n : ℕ} (h : m ≤ n) : siteBox d m ⊆ siteBox d n := by
  intro x hx
  rw [mem_siteBox] at hx ⊢
  intro j
  have hj := hx j
  omega

/-- Boxes about a fixed site grow with the radius. -/
theorem siteBoxAt_subset (c : Site d) {m n : ℕ} (h : m ≤ n) : siteBoxAt c m ⊆ siteBoxAt c n := by
  intro x hx
  rw [mem_siteBoxAt] at hx ⊢
  intro j
  have hj := hx j
  omega

theorem siteBox_mono (d : ℕ) : Monotone (siteBox d) := fun _ _ h => siteBox_subset h

theorem siteBoxAt_mono (c : Site d) : Monotone (siteBoxAt c) := fun _ _ h => siteBoxAt_subset c h

/-- A box of radius `n` has `(2n+1)^d` sites. -/
theorem card_siteBoxAt (c : Site d) (n : ℕ) : (siteBoxAt c n).card = (2 * n + 1) ^ d := by
  have hcard : ∀ j : Fin d, (Finset.Icc (c j - (n : ℤ)) (c j + n)).card = 2 * n + 1 := by
    intro j
    rw [Int.card_Icc]
    omega
  calc (siteBoxAt c n).card
      = ∏ j : Fin d, (Finset.Icc (c j - (n : ℤ)) (c j + n)).card := by
        rw [siteBoxAt, Fintype.card_piFinset]
    _ = ∏ _j : Fin d, (2 * n + 1) := Finset.prod_congr rfl fun j _ => hcard j
    _ = (2 * n + 1) ^ d := by simp

theorem card_siteBox (d n : ℕ) : (siteBox d n).card = (2 * n + 1) ^ d := by
  rw [← siteBoxAt_zero d n, card_siteBoxAt]

/-! ## A bound with a name

A stored estimate is one cylinder event together with the number its probability has to exceed.  All
of the probabilistic content of a plan lives here, and a plan's geometry can refer to an estimate
only by pointing at one of these.
-/

/-- One stored estimate: a cylinder event and a number its probability has to exceed. -/
structure ProbabilityBound (d : ℕ) where
  /-- The event the estimate is about. -/
  experiment : CylinderExperiment d
  /-- The number its probability has to exceed. -/
  lower : ℝ

/-- A stored estimate holds at `q` when its event is strictly more likely than its threshold at the
constant parameter `q`.  This is an inequality between two real numbers and nothing more. -/
def ProbabilityBound.HoldsAt (B : ProbabilityBound d) (q : unitInterval) : Prop :=
  B.lower < B.experiment.prob q

/-! ## Plans -/

/-- The finite data a renormalization construction works from.

`bound` carries every estimate the construction is allowed to use.  The remaining fields are
geometry: a working scale, a slab width, a density for the planar comparison lattice, and finitely
many *uses*, the `i`-th of which asks for the sites `source i` and `target i` to be joined inside the
box of radius `radius i` about `centre i`.  A use names no probability: `boundIndex i` says which of
the stored estimates is the one that justifies it. -/
structure RenormPlan (d : ℕ) where
  /-- How many estimates the plan carries. -/
  numBounds : ℕ
  /-- The estimates.  All probabilistic content of the plan is here. -/
  bound : Fin numBounds → ProbabilityBound d
  /-- The side length the construction works at. -/
  scale : ℕ
  /-- The width of the slab the plan is aimed at. -/
  slabWidth : ℕ
  /-- The density of the comparison site percolation on the plane. -/
  macroDensity : ℝ
  /-- How many geometric uses the plan makes. -/
  numSteps : ℕ
  /-- The centre of the box a use takes place in. -/
  centre : Fin numSteps → Site d
  /-- The radius of that box. -/
  radius : Fin numSteps → ℕ
  /-- The site a use starts from. -/
  source : Fin numSteps → Site d
  /-- The site a use reaches. -/
  target : Fin numSteps → Site d
  /-- Which stored estimate justifies a use.  Being an index rather than a number, it cannot invent
  an estimate that the plan does not already carry. -/
  boundIndex : Fin numSteps → Fin numBounds

/-! ## Well-formedness: geometry only

Nothing below mentions a parameter, a measure, or a probability.  The one clause that touches a
stored estimate reads off its support, which is a finite set of sites.
-/

/-- **The geometry of a plan is consistent.**  The scale and the slab width are positive; the
comparison density and every threshold lie in `[0,1)`; every use fits inside the working scale, with
its two named sites inside its own box; and the estimate a use points at is decided by the sites of
that box, so a use cannot be justified by an estimate about a region it does not control. -/
def RenormPlan.WellFormed (C : RenormPlan d) : Prop :=
  0 < C.scale ∧
  0 < C.slabWidth ∧
  0 ≤ C.macroDensity ∧
  C.macroDensity < 1 ∧
  (∀ i, 0 ≤ (C.bound i).lower ∧ (C.bound i).lower < 1) ∧
  (∀ i, C.radius i ≤ C.scale) ∧
  (∀ i, C.source i ∈ siteBoxAt (C.centre i) (C.radius i)) ∧
  (∀ i, C.target i ∈ siteBoxAt (C.centre i) (C.radius i)) ∧
  (∀ i, (C.bound (C.boundIndex i)).experiment.support ⊆ siteBoxAt (C.centre i) (C.radius i))

/-- Every estimate a well-formed plan actually uses is decided inside the box of the working scale
about the corresponding centre. -/
theorem RenormPlan.support_subset_of_wellFormed {C : RenormPlan d} (h : C.WellFormed)
    (i : Fin C.numSteps) :
    (C.bound (C.boundIndex i)).experiment.support ⊆ siteBoxAt (C.centre i) C.scale := by
  obtain ⟨-, -, -, -, -, hrad, -, -, hsupp⟩ := h
  intro x hx
  exact siteBoxAt_subset (C.centre i) (hrad i) (hsupp i hx)

/-- The estimates a well-formed plan uses depend on at most `(2 · scale + 1)^d` sites.  This is the
quantity that controls the Lipschitz constant in `RenormPlan.exists_valid_nhds`, so a plan whose
geometry is well-formed has a stability radius bounded below in terms of its scale alone. -/
theorem RenormPlan.card_support_le_of_wellFormed {C : RenormPlan d} (h : C.WellFormed)
    (i : Fin C.numSteps) :
    (C.bound (C.boundIndex i)).experiment.support.card ≤ (2 * C.scale + 1) ^ d := by
  have hsub := C.support_subset_of_wellFormed h i
  calc (C.bound (C.boundIndex i)).experiment.support.card
      ≤ (siteBoxAt (C.centre i) C.scale).card := Finset.card_le_card hsub
    _ = (2 * C.scale + 1) ^ d := card_siteBoxAt _ _

/-! ## Validity: strict inequalities only

`ValidAt` is a finite conjunction of strict inequalities between real numbers.  It says nothing about
percolation, quantifies over no configuration, and never mentions `thetaSite`.
-/

/-- **A plan holds at `q`.**  Every one of the finitely many stored estimates holds strictly at the
constant parameter `q`.  The geometric fields of the plan play no part. -/
def RenormPlan.ValidAt (C : RenormPlan d) (q : unitInterval) : Prop :=
  ∀ i, (C.bound i).HoldsAt q

theorem RenormPlan.validAt_iff (C : RenormPlan d) (q : unitInterval) :
    C.ValidAt q ↔ ∀ i, (C.bound i).lower < (C.bound i).experiment.prob q := Iff.rfl

/-- **Validity sees the estimates and nothing else.**  Two plans carrying the same list of estimates
are valid at the same parameters, however different their scales, boxes, sites and pointers.  This is
the separation the module is built around, stated so that it can be checked rather than trusted. -/
theorem RenormPlan.validAt_of_bound_eq {C C' : RenormPlan d} (hn : C'.numBounds = C.numBounds)
    (hb : ∀ i : Fin C'.numBounds, C'.bound i = C.bound (Fin.cast hn i)) {q : unitInterval}
    (h : C.ValidAt q) : C'.ValidAt q := by
  intro i
  show (C'.bound i).lower < (C'.bound i).experiment.prob q
  rw [hb i]
  exact h _

/-! ## Stability

The proof is the one for `RenormData`, read one projection deeper: the `i`-th estimate holds at `p`
with margin `(bound i).experiment.prob p - (bound i).lower > 0`, and a parameter shift smaller than
that margin divided by one more than the size of the support moves the probability by less than the
margin.  The `+ 1` keeps the quotient meaningful for an event with empty support, and the case of no
estimates, where the conclusion is vacuous, is treated separately because `Finset.inf'` needs a
nonempty index set.
-/

/-- **A plan valid at `p` is valid near `p`.** -/
theorem RenormPlan.exists_valid_nhds (C : RenormPlan d) {p : unitInterval} (h : C.ValidAt p) :
    ∃ ε > 0, ∀ q : unitInterval, |(q : ℝ) - (p : ℝ)| < ε → C.ValidAt q := by
  classical
  have h' : ∀ i, (C.bound i).lower < (C.bound i).experiment.prob p := h
  rcases eq_or_ne C.numBounds 0 with h0 | h0
  · -- No estimates: validity is vacuous, so any radius works.
    refine ⟨1, one_pos, fun q _ i => ?_⟩
    exact absurd i.isLt (by omega)
  · -- At least one estimate: take the smallest of the individual radii.
    have hne : (Finset.univ : Finset (Fin C.numBounds)).Nonempty :=
      ⟨⟨0, Nat.pos_of_ne_zero h0⟩, Finset.mem_univ _⟩
    obtain ⟨f, hf⟩ : ∃ f : Fin C.numBounds → ℝ, ∀ i,
        f i = ((C.bound i).experiment.prob p - (C.bound i).lower) /
          (((C.bound i).experiment.support.card : ℝ) + 1) :=
      ⟨_, fun _ => rfl⟩
    have hfpos : ∀ i, 0 < f i := by
      intro i
      rw [hf]
      exact div_pos (sub_pos.2 (h' i)) (by positivity)
    refine ⟨Finset.univ.inf' hne f, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff hne).2 fun i _ => hfpos i
    · intro q hq i
      have hle : Finset.univ.inf' hne f ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
      have hcard : (0 : ℝ) < ((C.bound i).experiment.support.card : ℝ) + 1 := by positivity
      have hlip := (C.bound i).experiment.abs_prob_sub_le p q
      have key : (C.bound i).experiment.prob p - (C.bound i).experiment.prob q
          < f i * (((C.bound i).experiment.support.card : ℝ) + 1) := by
        calc (C.bound i).experiment.prob p - (C.bound i).experiment.prob q
            ≤ |(C.bound i).experiment.prob p - (C.bound i).experiment.prob q| := le_abs_self _
          _ ≤ ((C.bound i).experiment.support.card : ℝ) * |(p : ℝ) - (q : ℝ)| := hlip
          _ ≤ (((C.bound i).experiment.support.card : ℝ) + 1) * |(q : ℝ) - (p : ℝ)| := by
              rw [abs_sub_comm]
              exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ < (((C.bound i).experiment.support.card : ℝ) + 1) * Finset.univ.inf' hne f :=
              mul_lt_mul_of_pos_left hq hcard
          _ ≤ (((C.bound i).experiment.support.card : ℝ) + 1) * f i :=
              mul_le_mul_of_nonneg_left hle (le_of_lt hcard)
          _ = f i * (((C.bound i).experiment.support.card : ℝ) + 1) := mul_comm _ _
      have hval : f i * (((C.bound i).experiment.support.card : ℝ) + 1)
          = (C.bound i).experiment.prob p - (C.bound i).lower := by
        rw [hf]
        field_simp
      rw [hval] at key
      show (C.bound i).lower < (C.bound i).experiment.prob q
      linarith

/-! ## The bridge to the existing endgame

Forgetting the pointers turns a plan into a certificate with the same estimates, so the two geometric
propositions of `KN/RenormData.lean` and the capstone `siteCriticality_of_certificate` apply to plans
with no change.
-/

/-- The certificate underlying a plan: the same estimates, with the pointers and the boxes dropped. -/
def RenormPlan.toRenormData (C : RenormPlan d) : RenormData d where
  slabWidth := C.slabWidth
  macroDensity := C.macroDensity
  numBounds := C.numBounds
  bound i := (C.bound i).experiment
  threshold i := (C.bound i).lower

@[simp] theorem RenormPlan.toRenormData_slabWidth (C : RenormPlan d) :
    C.toRenormData.slabWidth = C.slabWidth := rfl

/-- A plan and its certificate hold at exactly the same parameters. -/
theorem RenormPlan.toRenormData_validAt_iff (C : RenormPlan d) (q : unitInterval) :
    C.toRenormData.ValidAt q ↔ C.ValidAt q := Iff.rfl

/-- **Soundness applies to plans.**  A plan valid at `q` forces percolation in its slab at `q`, given
the geometric input already stated for certificates. -/
theorem RenormPlan.thetaSiteOn_pos_of_validAt [NeZero d] (hsound : CertificateSoundness d)
    (C : RenormPlan d) (q : unitInterval) (h : C.ValidAt q) :
    0 < thetaSiteOn (slabGraph d C.slabWidth) (slabOrigin d C.slabWidth) q :=
  hsound C.toRenormData q h

/-- **The geometric input in the language of plans.**  Percolation at a parameter strictly inside the
unit interval yields a well-formed plan valid there. -/
def PlanExtraction (d : ℕ) [NeZero d] : Prop :=
  ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 → 0 < thetaSite d p →
    ∃ C : RenormPlan d, C.WellFormed ∧ C.ValidAt p

theorem certificateExtraction_of_planExtraction (d : ℕ) [NeZero d] (h : PlanExtraction d) :
    CertificateExtraction d := by
  intro p hp0 hp1 hpos
  obtain ⟨C, -, hC⟩ := h p hp0 hp1 hpos
  exact ⟨C.toRenormData, hC⟩

/-- **The capstone, read through plans.**  Extraction of a well-formed plan and soundness of
certificates give the critical statement, by way of the certificate the plan carries. -/
theorem siteCriticality_of_plan (d : ℕ) [NeZero d] (hd : 2 ≤ d) (hex : PlanExtraction d)
    (hsound : CertificateSoundness d) : SiteCriticality d :=
  siteCriticality_of_certificate d hd (certificateExtraction_of_planExtraction d hex) hsound

/-! ## Plans made of confined connections

The estimates a renormalization argument actually stores are about connections confined to a box,
which is what makes them cylinder events.  This is the plan in which every use is such a connection
and points at the estimate for exactly that connection, so that the pointer discipline is discharged
by construction.
-/

/-- The plan whose `i`-th use asks for an open path from `src i` to `tgt i` inside the box of radius
`rad i` about `ctr i`, justified by the stored estimate for that very event. -/
def connPlan (scale slabWidth : ℕ) (macroDensity : ℝ) (n : ℕ) (ctr : Fin n → Site d)
    (rad : Fin n → ℕ) (src tgt : Fin n → Site d) (low : Fin n → ℝ) : RenormPlan d where
  numBounds := n
  bound i :=
    { experiment := cylinderOfConn (siteBoxAt (ctr i) (rad i)) (src i) (tgt i)
      lower := low i }
  scale := scale
  slabWidth := slabWidth
  macroDensity := macroDensity
  numSteps := n
  centre := ctr
  radius := rad
  source := src
  target := tgt
  boundIndex := id

/-- The connection plan is well-formed as soon as its boxes fit inside the working scale, its named
sites lie in their boxes, and its thresholds lie in `[0,1)`.  The pointer clause is automatic: the
support of the estimate a use points at is the use's own box. -/
theorem connPlan_wellFormed {scale slabWidth : ℕ} {macroDensity : ℝ} {n : ℕ} {ctr : Fin n → Site d}
    {rad : Fin n → ℕ} {src tgt : Fin n → Site d} {low : Fin n → ℝ} (hs : 0 < scale)
    (hw : 0 < slabWidth) (hm0 : 0 ≤ macroDensity) (hm1 : macroDensity < 1)
    (hlow : ∀ i, 0 ≤ low i ∧ low i < 1) (hrad : ∀ i, rad i ≤ scale)
    (hsrc : ∀ i, src i ∈ siteBoxAt (ctr i) (rad i))
    (htgt : ∀ i, tgt i ∈ siteBoxAt (ctr i) (rad i)) :
    (connPlan scale slabWidth macroDensity n ctr rad src tgt low).WellFormed := by
  unfold RenormPlan.WellFormed
  exact ⟨hs, hw, hm0, hm1, hlow, hrad, hsrc, htgt, fun i => Finset.Subset.refl _⟩

/-- The estimates of a connection plan are the probabilities of the confined connections it names. -/
theorem connPlan_validAt_iff {scale slabWidth : ℕ} {macroDensity : ℝ} {n : ℕ} {ctr : Fin n → Site d}
    {rad : Fin n → ℕ} {src tgt : Fin n → Site d} {low : Fin n → ℝ} (q : unitInterval) :
    (connPlan scale slabWidth macroDensity n ctr rad src tgt low).ValidAt q ↔
      ∀ i, low i < (siteBernoulli (fun _ : Site d => q)).real
        (connWithin (zdGraph d) (↑(siteBoxAt (ctr i) (rad i)) : Set (Site d)) (src i) (tgt i)) :=
  Iff.rfl

end KNAll.Site

end
