import Hypergraph.ExactCommonQAssembly
import Hypergraph.SiteEndgame
import Hypergraph.SiteThetaMono

/-!
# The canonical public statement: no site percolation at criticality for `d ≥ 3`

This module exposes the finished result of the development with **no mathematical argument other
than the dimension `d` and the numeric side condition `hd : 3 ≤ d`**.  It adds no mathematics: the
whole content is `ExactCommonQAssembly.site_no_percolation_at_criticality`, which is already
unconditional.  What is done here is exactly three things.

1. **The instance argument is discharged.**  The assembly theorem is stated for `{d : Nat}` with an
   instance argument `[NeZero d]`.  `NeZero d` is a `Prop`-valued class, so an unsupplied instance
   would be an *implicit assumption invisible in the printed hypothesis list*.  Here `d` is an
   explicit argument and `NeZero d` is constructed from `hd` by `omega`.  After that the canonical
   theorem's binders are literally `(d : ℕ) (hd : 3 ≤ d)` and nothing else.

2. **The conclusion is spelled at four levels of transparency**, each proved by `rfl`-level
   conversion from the one before, so that the statement can be read without trusting any
   abbreviation of this development:

   * `site_no_percolation_at_critical` — `thetaSite d (criticalProbSiteI d) = 0`;
   * `site_no_percolation_at_critical_real` — the same with the critical parameter written as the
     real number `criticalProbSite d` together with its membership proof.  Note that
     `thetaSite d (criticalProbSite d)` is **not** well typed: `thetaSite _ : unitInterval → ℝ`
     while `criticalProbSite _ : ℝ`, and there is no coercion `ℝ → unitInterval`.  The
     membership-paired form below is the closest well-typed rendering, and it is definitionally
     the canonical statement because `criticalProbSiteI d` is by definition that pair;
   * `site_no_percolation_at_critical_expanded` — `thetaSite`/`thetaSiteOn` unfolded to the
     underlying measure and open cluster;
   * `site_no_percolation_at_critical_primitive` — every definition of this development unfolded,
     leaving only Mathlib's `SimpleGraph.hasse`, `SimpleGraph.fromRel`, `Measure.real`,
     `Set.Infinite` and `Percolation.Literature.LatticeModels.prodBernoulli`.

3. **Non-vacuity is recorded.**  A statement about a critical parameter is worthless if the
   critical parameter could be an endpoint, or if the hypothesis `3 ≤ d` were unsatisfiable.  Both
   are excluded here by machine-checked companions: `criticalProbSite d ∈ Set.Ioo 0 1`, the closed
   subcritical vanishing statement, and a fully instantiated `example` at `d = 3`.

Nothing in this file weakens the result; every declaration below has `(d : ℕ)` and `3 ≤ d` as its
only hypotheses, and each is followed by `#print axioms`.
-/

noncomputable section

namespace KNAll.Site

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels

/-! ## The canonical theorem -/

/-- **No site percolation at the critical parameter, in every dimension at least three.**

For nearest-neighbour Bernoulli site percolation on `ℤ^d` with `d ≥ 3`, the probability that the
open cluster of the origin is infinite vanishes at the critical parameter.

This is the canonical public form: its only arguments are the dimension and `3 ≤ d`.  The proof is
`ExactCommonQAssembly.site_no_percolation_at_criticality`, whose `[NeZero d]` instance argument is
discharged here from `hd`. -/
theorem site_no_percolation_at_critical (d : ℕ) (hd : 3 ≤ d) :
    thetaSite d (criticalProbSiteI d) = 0 := by
  haveI : NeZero d := ⟨by omega⟩
  exact ExactCommonQAssembly.site_no_percolation_at_criticality hd

/-- The same conclusion phrased with the *real-valued* critical parameter `criticalProbSite d`,
paired with the proof that it lies in the unit interval.

`thetaSite d (criticalProbSite d)` is ill typed, because `criticalProbSite d : ℝ` whereas
`thetaSite d` expects a `unitInterval`.  This is the closest well-typed rendering of that intended
expression, and it is *definitionally* the canonical theorem, since `criticalProbSiteI d` is by
definition the pair `⟨criticalProbSite d, criticalProbSite_mem_Icc d⟩`. -/
theorem site_no_percolation_at_critical_real (d : ℕ) (hd : 3 ≤ d) :
    thetaSite d ⟨criticalProbSite d, criticalProbSite_mem_Icc d⟩ = 0 :=
  site_no_percolation_at_critical d hd

/-- The canonical theorem in the packaged form `SiteCriticality`, the proposition the development
set out to prove in `KN/SiteStatements.lean`. -/
theorem siteCriticality_of_three_le (d : ℕ) (hd : 3 ≤ d) : SiteCriticality d :=
  site_no_percolation_at_critical d hd

/-! ## The same statement with the abbreviations unfolded

Each of the following is proved by supplying the canonical theorem directly, so each `=` below is a
definitional unfolding rather than a rewriting step.  Together they certify that no abbreviation of
this development hides content in the conclusion. -/

/-- `thetaSite` and `thetaSiteOn` unfolded: the product Bernoulli measure of the event that the
open cluster of the origin is infinite is zero at the critical parameter. -/
theorem site_no_percolation_at_critical_expanded (d : ℕ) (hd : 3 ≤ d) :
    (siteBernoulli (fun _ : Site d => criticalProbSiteI d)).real
        {ω : Set (Site d) | (siteCluster (zdGraph d) ω (0 : Site d)).Infinite} = 0 :=
  site_no_percolation_at_critical d hd

/-- Every definition of this development unfolded.  Only Mathlib notions and the product Bernoulli
measure of `Percolation.Literature` remain: `Site d` is `Fin d → ℤ`, the lattice is
`SimpleGraph.hasse`, the open graph is `SimpleGraph.fromRel`, and the cluster of the origin is the
set of vertices reachable from an open origin. -/
theorem site_no_percolation_at_critical_primitive (d : ℕ) (hd : 3 ≤ d) :
    (prodBernoulli (fun _ : Fin d → ℤ => criticalProbSiteI d)).real
        {ω : Set (Fin d → ℤ) |
          {y : Fin d → ℤ | (0 : Fin d → ℤ) ∈ ω ∧
              (SimpleGraph.fromRel fun x y : Fin d → ℤ =>
                (SimpleGraph.hasse (Fin d → ℤ)).Adj x y ∧ x ∈ ω ∧ y ∈ ω).Reachable 0 y}.Infinite} =
      0 :=
  site_no_percolation_at_critical d hd

/-- The critical parameter fed to the theorem really is the infimum defining `p_c`: the set of
parameters at which the origin percolates, together with `1`.  Proved by `rfl`, so the reading of
`criticalProbSiteI` above is not taken on trust. -/
theorem coe_criticalProbSiteI_eq_sInf (d : ℕ) :
    (criticalProbSiteI d : ℝ) =
      sInf ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < thetaSite d ⟨p, h⟩} ∪ {1}) := rfl

/-! ## Non-vacuity

A statement about `p_c` says nothing unless `p_c` is an interior point, and a theorem with an
unsatisfiable hypothesis says nothing at all.  Both readings are excluded below. -/

/-- The critical parameter is strictly inside the unit interval, so the canonical theorem is a
statement about a genuine phase transition point and not about an endpoint of `[0,1]`. -/
theorem criticalProbSite_mem_Ioo_of_three_le (d : ℕ) (hd : 3 ≤ d) :
    criticalProbSite d ∈ Set.Ioo (0 : ℝ) 1 := by
  haveI : NeZero d := ⟨by omega⟩
  exact criticalProbSite_mem_Ioo d (by omega)

/-- The percolation probability vanishes on the whole closed subcritical interval `[0, p_c]`.
Strictly below `p_c` this is the definition of the infimum; at `p_c` itself it is the canonical
theorem, which is the only point where a nontrivial argument is needed. -/
theorem thetaSite_eq_zero_of_le_criticalProbSite (d : ℕ) (hd : 3 ≤ d) (p : unitInterval)
    (hp : (p : ℝ) ≤ criticalProbSite d) : thetaSite d p = 0 := by
  rcases lt_or_eq_of_le hp with hlt | heq
  · exact thetaSite_eq_zero_of_lt_criticalProbSite d p hlt
  · have hpc : p = criticalProbSiteI d := Subtype.ext heq
    rw [hpc]
    exact site_no_percolation_at_critical d hd

/-- Percolation does occur at some parameter below one.  Together with the vanishing at `p_c` this
rules out the degenerate reading in which `thetaSite d` were identically zero. -/
theorem exists_thetaSite_pos_of_three_le (d : ℕ) (hd : 3 ≤ d) :
    ∃ a : unitInterval, (a : ℝ) < 1 ∧ 0 < thetaSite d a := by
  haveI : NeZero d := ⟨by omega⟩
  exact exists_thetaSite_pos d (by omega)

/-- **The phase transition, stated in full.**  The critical parameter is an interior point of the
unit interval; the percolation probability vanishes on the whole closed interval `[0, p_c]`,
including at `p_c` itself; and it is positive at some parameter below one.  Every conjunct is
machine checked, so no reading of the canonical theorem in which it is vacuous survives. -/
theorem site_phase_transition (d : ℕ) (hd : 3 ≤ d) :
    0 < criticalProbSite d ∧ criticalProbSite d < 1 ∧
      (∀ p : unitInterval, (p : ℝ) ≤ criticalProbSite d → thetaSite d p = 0) ∧
      ∃ a : unitInterval, (a : ℝ) < 1 ∧ 0 < thetaSite d a :=
  ⟨(criticalProbSite_mem_Ioo_of_three_le d hd).1,
    (criticalProbSite_mem_Ioo_of_three_le d hd).2,
    thetaSite_eq_zero_of_le_criticalProbSite d hd,
    exists_thetaSite_pos_of_three_le d hd⟩

/-- The hypothesis `3 ≤ d` is satisfiable and the theorem has content at a concrete dimension:
there is no infinite open site cluster of the origin at the critical parameter of `ℤ³`. -/
example : thetaSite 3 (criticalProbSiteI 3) = 0 :=
  site_no_percolation_at_critical 3 (by norm_num)

/-- The same at `d = 4`, and with the conclusion in its fully unfolded form. -/
example :
    (prodBernoulli (fun _ : Fin 4 → ℤ => criticalProbSiteI 4)).real
        {ω : Set (Fin 4 → ℤ) |
          {y : Fin 4 → ℤ | (0 : Fin 4 → ℤ) ∈ ω ∧
              (SimpleGraph.fromRel fun x y : Fin 4 → ℤ =>
                (SimpleGraph.hasse (Fin 4 → ℤ)).Adj x y ∧ x ∈ ω ∧ y ∈ ω).Reachable 0 y}.Infinite} =
      0 :=
  site_no_percolation_at_critical_primitive 4 (by norm_num)

#print axioms KNAll.Site.site_no_percolation_at_critical
#print axioms KNAll.Site.site_no_percolation_at_critical_real
#print axioms KNAll.Site.siteCriticality_of_three_le
#print axioms KNAll.Site.site_no_percolation_at_critical_expanded
#print axioms KNAll.Site.site_no_percolation_at_critical_primitive
#print axioms KNAll.Site.coe_criticalProbSiteI_eq_sInf
#print axioms KNAll.Site.criticalProbSite_mem_Ioo_of_three_le
#print axioms KNAll.Site.thetaSite_eq_zero_of_le_criticalProbSite
#print axioms KNAll.Site.exists_thetaSite_pos_of_three_le
#print axioms KNAll.Site.site_phase_transition

end KNAll.Site

end
