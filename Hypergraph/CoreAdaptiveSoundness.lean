import Hypergraph.CoreAcceptedSupported
import Hypergraph.AdmissibleBoundedDamageAdaptiveRegion

/-!
# Slab soundness for admissibility-indexed bounded-damage explorations

The existing `AdaptiveSoundness` consumer is stated for the older `AdaptReg.Exploration`.
Accepted core batches instead use `ABDAdaptReg.Exploration`: reveal phases are entered only from
admissible histories and the final macro verdict may close bounded collateral damage.  This module
ports the configuration-soundness and slab-limit argument to that exact type.
-/

noncomputable section

namespace KNAll.Site.CoreAdaptSound

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

abbrev Tr (kappa V : Type*) := BDDom.Transcript kappa V

namespace RevealPhase

variable {kappa V : Type*} [DecidableEq kappa] [DecidableEq V]
  {Admissible : Tr kappa V → Prop}

/-- A bounded-damage physical step records only sites which are open in the configuration being
read. -/
theorem step_openSites_subset (h : Tr kappa V) (z : V) (F : Finset kappa)
    (damage : Finset V) (b : Bool) (omega : Set kappa)
    (hh : (↑h.openSites : Set kappa) ⊆ omega) :
    (↑(h.step z F damage b omega).openSites : Set kappa) ⊆ omega := by
  classical
  intro x hx
  change x ∈ h.openSites ∪ F.filter (fun y => y ∈ omega) at hx
  rw [Finset.mem_union, Finset.mem_filter] at hx
  exact hx.elim (fun hxo => hh (Finset.mem_coe.2 hxo)) (fun hxo => hxo.2)

variable (R : ABDAdaptReg.RevealPhase kappa V Admissible)

/-- Every reveal-only descendant records genuine states from the single global configuration. -/
theorem run_openSites_subset {base h : Tr kappa V} (hh : R.Phase base h) :
    ∀ n (omega : Set kappa), (↑h.openSites : Set kappa) ⊆ omega →
      (↑(R.run base n h omega).openSites : Set kappa) ⊆ omega := by
  intro n
  induction n generalizing h with
  | zero =>
      intro omega hopen
      simpa using hopen
  | succ n ih =>
      intro omega hopen
      exact ih (R.step_phase base h hh omega) omega
        (step_openSites_subset h (R.anchor base h) (R.region base h) ∅ true omega hopen)

end RevealPhase

namespace Exploration

variable {kappa V : Type*} [DecidableEq kappa] [DecidableEq V]
  {G : SimpleGraph V} {A : Finset V} {o : V} {T : Set V}
  (E : ABDAdaptReg.Exploration kappa G A o T)

/-- Admissibility is invariant along the complete macro exploration. -/
theorem admissible_run : ∀ n (h : Tr kappa V), E.Admissible h →
    ∀ omega : Set kappa, E.Admissible (E.run n h omega) := by
  intro n
  induction n with
  | zero =>
      intro h hh omega
      simpa using hh
  | succ n ih =>
      intro h hh omega
      by_cases hT : h.Terminal G A o T
      · rw [E.run_succ_of_terminal hT]
        exact hh
      · rw [E.run_succ_of_not_terminal hT]
        exact ih _ (E.advance_admissible hh hT omega) omega

/-- A reveal phase followed by its empty-coordinate commit records only genuinely open sites. -/
theorem advance_openSites_subset (h : Tr kappa V) (hadm : E.Admissible h)
    (omega : Set kappa) (hh : (↑h.openSites : Set kappa) ⊆ omega) :
    (↑(E.advance h omega).openSites : Set kappa) ⊆ omega := by
  have hrevealed : (↑(E.revealed h omega).openSites : Set kappa) ⊆ omega :=
    RevealPhase.run_openSites_subset E.revealPhase
      (E.revealPhase.start h hadm) (E.revealPhase.rounds h) omega hh
  rw [ABDAdaptReg.Exploration.advance, E.commit_eq_step _ _ _ omega]
  exact RevealPhase.step_openSites_subset _ _ ∅ (E.damage h (E.revealed h omega))
    (E.bit h omega) omega hrevealed

/-- Along one global-configuration run, every recorded-open physical site is genuinely open. -/
theorem run_openSites_subset : ∀ n (h : Tr kappa V), E.Admissible h →
    ∀ omega : Set kappa, (↑h.openSites : Set kappa) ⊆ omega →
      (↑(E.run n h omega).openSites : Set kappa) ⊆ omega := by
  intro n
  induction n with
  | zero =>
      intro h _ omega hh
      simpa using hh
  | succ n ih =>
      intro h hadm omega hh
      by_cases hT : h.Terminal G A o T
      · rw [E.run_succ_of_terminal hT]
        exact hh
      · rw [E.run_succ_of_not_terminal hT]
        exact ih _ (E.advance_admissible hadm hT omega) omega
          (advance_openSites_subset E h hadm omega hh)

end Exploration

section Slab

variable {d : Nat} [NeZero d] {r t n : Nat} {q a : unitInterval} {δ : Real}

/-- A reaching bounded-damage run gives the usual physical far arm whenever admissibility carries
the standard physical `MacroExp.Good` certificate for its base transcript. -/
theorem far_of_adaptive_run_reaches (hd : 2 ≤ d) (hr : 0 < r)
    (E : ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hadmGood : ∀ k, E.Admissible k → MacroExp.Good d r t k.base q δ)
    (m : Nat) {omega : SiteConfig (Site d)}
    {h0 : Tr (Site d) (Site 2)} (hstart : E.Admissible h0)
    (hbase : h0.base = MacroExp.start d r t)
    (hQ : (↑(MacroExp.Q d r t 0) : Set (Site d)) ⊆ omega)
    (hR : (E.run m h0 omega).Reaches (zdGraph 2) 0 (MacroExp.tgt n)) :
    omega ∈ MacroExp.far d r t n := by
  have hadmFinal := Exploration.admissible_run E m h0 hstart omega
  have hgood := hadmGood _ hadmFinal
  obtain ⟨x, hfar, hpath⟩ := MacroExp.exists_far_of_reaches hd hgood hR
  refine ⟨x, hfar, ?_⟩
  have hstartOpen : (↑h0.openSites : Set (Site d)) ⊆ omega := by
    have hopen : h0.openSites = (MacroExp.start d r t).openSites := by
      change h0.base.openSites = (MacroExp.start d r t).openSites
      rw [hbase]
    rw [hopen]
    simpa [MacroExp.start] using hQ
  have hopen :
      (↑(E.run m h0 omega).openSites : Set (Site d)) ⊆ omega :=
    Exploration.run_openSites_subset E m h0 hstart omega hstartOpen
  exact isUpperSet_connWithin (zdGraph d) _ (MacroExp.emb 0) x hopen
    (connWithin_mono_set (zdGraph d) hgood.inspected_thin (MacroExp.emb 0) x hpath)

/-- Uniform finite-radius domination for an admissibility-indexed bounded-damage exploration.

The macro benchmark is deliberately left as `c ≤ h0.bern ...`.  Bounded damage compares the
physical process to the *safe-site* event `BDDom.Safe.targetConn`, not ordinary iid site
percolation.  No safe-site-to-iid comparison is currently present in the tree, so replacing this
honest premise by `thetaSite 2 a` would be an invalid strengthening. -/
theorem le_real_far_of_adaptive (hd : 2 ≤ d) (hr : 0 < r)
    (E : ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hdensity : E.density = fun _ : Site d => q)
    {h0 : Tr (Site d) (Site 2)} (hstart : E.Admissible h0)
    (hbase : h0.base = MacroExp.start d r t) (hfailed : h0.failed = ∅)
    (hadmGood : ∀ k, E.Admissible k → MacroExp.Good d r t k.base q δ)
    (c : Real)
    (hbern : c ≤ h0.bern a (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hstep : ∀ h, E.Admissible h →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      (a : Real) ≤ h.prob (fun _ : Site d => q) (E.success h)) :
    (q : Real) ^ (MacroExp.Q d r t 0).card * c ≤
      (siteBernoulli (fun _ : Site d => q)).real (MacroExp.far d r t n) := by
  classical
  let m := (box 2 n).card
  have hstep' : ∀ h, E.Admissible h →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      (a : Real) ≤ h.prob E.density (E.success h) := by
    simpa only [hdensity] using hstep
  have hdom := E.bern_le_prob_run (a := a) hstep' m h0 hstart (by
    change h0.base.undetermined (box 2 n) ≤ m
    rw [hbase]
    exact MacroExp.undetermined_start_le n)
  rw [hdensity] at hdom
  have hrun : h0.prob (fun _ : Site d => q)
        {omega | (E.run m h0 omega).Reaches (zdGraph 2) 0 (MacroExp.tgt n)} ≤
      (siteBernoulli (fun _ : Site d => q)).real
        (openSites (↑(MacroExp.Q d r t 0) : Set (Site d)) ⁻¹'
          MacroExp.far d r t n) := by
    change h0.base.prob (fun _ : Site d => q)
      {omega | (E.run m h0 omega).Reaches (zdGraph 2) 0 (MacroExp.tgt n)} ≤ _
    rw [hbase, FRDom.Transcript.prob_eq, pinnedProb]
    refine measureReal_mono (fun omega homega => ?_) (measure_ne_top _ _)
    simp only [Set.mem_preimage] at homega ⊢
    have hsub :
        substitute (↑(MacroExp.start d r t).inspected : Set (Site d))
            (MacroExp.start d r t).state omega =
          openSites (↑(MacroExp.Q d r t 0) : Set (Site d)) omega :=
      MacroExp.substitute_Q_eq_openSites omega
    rw [hsub] at homega
    exact far_of_adaptive_run_reaches hd hr E hadmGood m hstart hbase
      (fun x hx => Or.inr hx) homega
  have hins := prod_mul_real_preimage_openSites_le
    (fun _ : Site d => q) (MacroExp.Q d r t 0)
    (MacroExp.measurableSet_far d r t n)
  rw [Finset.prod_const] at hins
  have hq0 : (0 : Real) ≤ (q : Real) ^ (MacroExp.Q d r t 0).card := pow_nonneg q.2.1 _
  calc
    (q : Real) ^ (MacroExp.Q d r t 0).card * c ≤
        (q : Real) ^ (MacroExp.Q d r t 0).card *
          (siteBernoulli (fun _ : Site d => q)).real
            (openSites (↑(MacroExp.Q d r t 0) : Set (Site d)) ⁻¹'
              MacroExp.far d r t n) :=
      mul_le_mul_of_nonneg_left (hbern.trans (hdom.trans hrun)) hq0
    _ ≤ (siteBernoulli (fun _ : Site d => q)).real (MacroExp.far d r t n) := hins

/-- Thin-slab percolation follows from a family of accepted bounded-damage explorations. -/
theorem thetaSiteOn_thin_pos_of_adaptive (hd : 2 ≤ d) (hr : 0 < r)
    (q a : unitInterval) (hq : 0 < (q : Real)) {c : Real} (hc : 0 < c) (δ : Real)
    (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
      (box 2 n) 0 (MacroExp.tgt n))
    (h0 : Tr (Site d) (Site 2))
    (hbase : h0.base = MacroExp.start d r t) (hfailed : h0.failed = ∅)
    (hdensity : ∀ n, (E n).density = fun _ : Site d => q)
    (hstart : ∀ n, (E n).Admissible h0)
    (hadmGood : ∀ n k, (E n).Admissible k → MacroExp.Good d r t k.base q δ)
    (hbern : ∀ n, c ≤ h0.bern a (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hstep : ∀ n h, (E n).Admissible h →
      ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      (a : Real) ≤ h.prob (fun _ : Site d => q) ((E n).success h)) :
    0 < thetaSiteOn ((zdGraph d).induce (MacroExp.thin d t))
      ⟨0, MacroExp.zero_mem_thin t⟩ q := by
  let c0 : Real := (q : Real) ^ (MacroExp.Q d r t 0).card * c
  have hcpos : 0 < c0 := mul_pos (pow_pos hq _) hc
  have hG : (zdGraph d).induce (MacroExp.thin d t) =
      (zdGraph d).comap (Subtype.val : MacroExp.thin d t → Site d) := by
    ext x y
    rfl
  rw [hG, thetaSiteOn_comap_eq (zdGraph d) Subtype.val_injective]
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := siteBernoulli (fun _ : Site d => q)) (s := MacroExp.far d r t)
    (fun n => (MacroExp.measurableSet_far d r t n).nullMeasurableSet)
    (MacroExp.far_antitone d r t) ⟨0, measure_ne_top _ _⟩
  have hlim' := (ENNReal.tendsto_toReal
    (measure_ne_top (siteBernoulli (fun _ : Site d => q))
      (⋂ n, MacroExp.far d r t n))).comp hlim
  have hge : c0 ≤
      (siteBernoulli (fun _ : Site d => q)).real (⋂ n, MacroExp.far d r t n) :=
    ge_of_tendsto' hlim' fun n =>
      le_real_far_of_adaptive hd hr (E n) (hdensity n) (hstart n)
        hbase hfailed (hadmGood n) c (hbern n) (hstep n)
  refine lt_of_lt_of_le hcpos (hge.trans (measureReal_mono ?_ (measure_ne_top _ _)))
  intro omega homega
  rw [Set.mem_iInter] at homega
  exact MacroExp.infinite_of_forall_far hr homega

/-- Certificate soundness routed through the admissibility-indexed bounded-damage exploration. -/
theorem certificateSound2_of_adaptive (hd : 3 ≤ d)
    (hs : ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval),
      C.WellFormed → C.ValidAt2 q →
      ∃ (r t : Nat) (a : unitInterval) (c δ : Real)
        (h0 : Tr (Site d) (Site 2))
        (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
          (box 2 n) 0 (MacroExp.tgt n)),
        0 < r ∧ 2 * t ≤ C.width ∧ 0 < c ∧
        h0.base = MacroExp.start d r t ∧ h0.failed = ∅ ∧
        (∀ n, (E n).density = fun _ : Site d => q) ∧
        (∀ n, (E n).Admissible h0) ∧
        (∀ n k, (E n).Admissible k → MacroExp.Good d r t k.base q δ) ∧
        (∀ n, c ≤ h0.bern a (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n)) ∧
        (∀ n h, (E n).Admissible h →
          ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
          (a : Real) ≤ h.prob (fun _ : Site d => q) ((E n).success h))) :
    LeftImp2.CertificateSound2 d := by
  intro C q hwf hv
  obtain ⟨r, t, a, c, δ, h0, E, hr, ht, hc, hbase, hfailed,
    hdensity, hstart, hadmGood, hbern, hstep⟩ := hs C q hwf hv
  have hq : 0 < (q : Real) := MacroExp.coe_pos_of_validAt2 hwf hv
  have hthin := thetaSiteOn_thin_pos_of_adaptive (d := d) (r := r) (t := t)
    (by omega) hr q a hq hc δ E h0 hbase hfailed hdensity hstart hadmGood hbern hstep
  exact lt_of_lt_of_le (MacroExp.slab_two_pos_of_thin hd t q hthin)
    (MacroExp.thetaSiteOn_slab_mono ht q)

end Slab

#print axioms KNAll.Site.CoreAdaptSound.Exploration.admissible_run
#print axioms KNAll.Site.CoreAdaptSound.Exploration.run_openSites_subset
#print axioms KNAll.Site.CoreAdaptSound.far_of_adaptive_run_reaches
#print axioms KNAll.Site.CoreAdaptSound.le_real_far_of_adaptive
#print axioms KNAll.Site.CoreAdaptSound.thetaSiteOn_thin_pos_of_adaptive
#print axioms KNAll.Site.CoreAdaptSound.certificateSound2_of_adaptive

end KNAll.Site.CoreAdaptSound

end
