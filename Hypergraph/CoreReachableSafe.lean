import Hypergraph.CoreAcceptedAssembly
import Hypergraph.CoreSafeBenchmark

/-!
# Reachable-state soundness for accepted adaptive core explorations

`CoreAcceptedTransition.Admissible` is a transition invariant, not a physical realization
certificate.  Moreover the accepted one-owner state is intentionally weaker than
`MacroExp.Good`: it neither reserves every oriented edge nor gives a cover whose every tail is
open.  The slab argument only needs inspected-set confinement and realized certificates.  This
module packages exactly those two facts and propagates them along the one-configuration run.
-/

noncomputable section

namespace KNAll.Site.CoreReachSafe

open MeasureTheory Set KN Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

abbrev Tr (kappa V : Type*) := BDDom.Transcript kappa V

variable {kappa V : Type*} [DecidableEq kappa] [DecidableEq V]
  {G : SimpleGraph V} {A : Finset V} {o : V} {T : Set V}

/-- A transcript is reachable when it is literally produced by one finite run from `h0`, for one
global physical configuration. -/
def Reachable (E : ABDAdaptReg.Exploration kappa G A o T)
    (h0 k : Tr kappa V) : Prop :=
  ∃ m : Nat, ∃ omega : Set kappa, k = E.run m h0 omega

theorem reachable_run (E : ABDAdaptReg.Exploration kappa G A o T)
    (h0 : Tr kappa V) (m : Nat) (omega : Set kappa) :
    Reachable E h0 (E.run m h0 omega) :=
  ⟨m, omega, rfl⟩

/-- The exact physical invariant consumed by the far-arm argument.  In particular it has no
all-directions reservation field and no open-tail cover field. -/
structure Physical (d r t : Nat) [NeZero d]
    (k : Tr (Site d) (Site 2)) : Prop where
  inspected_thin : (↑k.inspected : Set (Site d)) ⊆ MacroExp.thin d t
  cert : ∀ z ∈ k.openV, ∃ a ∈ MacroExp.M d r t z,
    (↑k.openSites : Set (Site d)) ∈
      connWithin (zdGraph d) (↑k.inspected : Set (Site d)) (MacroExp.emb 0) a

/-- The genuine macro start has the lightweight physical invariant without any reservation
hypothesis. -/
theorem physical_of_base_eq_start {d r t : Nat} [NeZero d] (hd : 2 ≤ d)
    {h0 : Tr (Site d) (Site 2)} (hbase : h0.base = MacroExp.start d r t) :
    Physical d r t h0 := by
  constructor
  · change (↑h0.base.inspected : Set (Site d)) ⊆ MacroExp.thin d t
    rw [hbase]
    exact MacroExp.Q_subset_thin hd r t 0
  · intro z hz
    change z ∈ h0.base.openV at hz
    rw [hbase] at hz
    have hz0 : z = 0 := Finset.mem_singleton.1 hz
    subst z
    refine ⟨MacroExp.emb 0, MacroExp.emb_zero_mem_M r t, ?_⟩
    change (↑h0.base.openSites : Set (Site d)) ∈
      connWithin (zdGraph d) (↑h0.base.inspected : Set (Site d))
        (MacroExp.emb 0) (MacroExp.emb 0)
    rw [hbase]
    have h0mem : (MacroExp.emb 0 : Site d) ∈ MacroExp.Q d r t 0 :=
      MacroExp.M_subset_Q r t 0 (MacroExp.emb_zero_mem_M r t)
    exact ⟨⟨Finset.mem_coe.2 h0mem, Finset.mem_coe.2 h0mem⟩,
      SimpleGraph.Reachable.refl _⟩

/-- The geometric far-point conclusion uses only `Physical.cert`; the stronger macro invariant is
not involved. -/
theorem exists_far_of_physical_reaches {d r t n : Nat} [NeZero d] (hd : 2 ≤ d)
    {k : Tr (Site d) (Site 2)} (hphysical : Physical d r t k)
    (hR : k.Reaches (zdGraph 2) 0 (MacroExp.tgt n)) :
    ∃ a : Site d, (∃ j : Fin d, 20 * (r : Int) * n - 3 * r ≤ |a j|) ∧
      (↑k.openSites : Set (Site d)) ∈
        connWithin (zdGraph d) (↑k.inspected : Set (Site d)) (MacroExp.emb 0) a := by
  obtain ⟨z, hz, hzex⟩ := hR
  have hzV : z ∈ k.openV := Finset.mem_coe.1 (mem_of_mem_siteCluster _ _ hzex)
  obtain ⟨a, ha, hpath⟩ := hphysical.cert z hzV
  refine ⟨a, ?_, hpath⟩
  obtain ⟨i, hi⟩ := MacroExp.exists_coord_of_mem_innerBoundary (Finset.mem_coe.1 hz)
  have hid : i.val < d := lt_of_lt_of_le i.isLt hd
  refine ⟨⟨i.val, hid⟩, ?_⟩
  rw [MacroExp.M, MacroExp.mem_abox] at ha
  have h1 := ha ⟨i.val, hid⟩
  have hjlt : (⟨i.val, hid⟩ : Fin d).val < 2 := i.isLt
  rw [MacroExp.ctr_apply_of_lt r z hjlt] at h1
  unfold MacroExp.rad at h1
  rw [if_pos hjlt] at h1
  have hzi : z ⟨(⟨i.val, hid⟩ : Fin d).val, hjlt⟩ = z i := rfl
  rw [hzi] at h1
  push_cast at h1
  rcases (abs_eq (Nat.cast_nonneg n)).1 hi with hz' | hz'
  · rw [hz'] at h1
    linarith [le_abs_self (a ⟨i.val, hid⟩)]
  · rw [hz'] at h1
    have h2 : 20 * (r : Int) * (-(n : Int)) = -(20 * r * n) := by ring
    rw [h2] at h1
    linarith [neg_le_abs (a ⟨i.val, hid⟩)]

section PhysicalRun

variable {d r t n : Nat} [NeZero d]

/-- One-step preservation is the precise interface needed to propagate physical certificates;
it is deliberately separate from admissibility. -/
def PreservesPhysical
    (E : ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n)) : Prop :=
  ∀ h, E.Admissible h →
    ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
    Physical d r t h → ∀ omega, Physical d r t (E.advance h omega)

/-- Induction through the actual interpreter.  At a terminal state the run is stationary; at an
active state this uses precisely one physical-preservation step. -/
theorem physical_run_of_preserves
    (E : ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hpres : PreservesPhysical (r := r) (t := t) E) :
    ∀ m h, E.Admissible h → Physical d r t h →
      ∀ omega, Physical d r t (E.run m h omega) := by
  intro m
  induction m with
  | zero =>
      intro h _ hphysical omega
      simpa using hphysical
  | succ m ih =>
      intro h hadm hphysical omega
      by_cases hT : h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n)
      · rw [E.run_succ_of_terminal hT]
        exact hphysical
      · rw [E.run_succ_of_not_terminal hT]
        exact ih (E.advance h omega) (E.advance_admissible hadm hT omega)
          (hpres h hadm hT hphysical omega) omega

/-- Every reachable state is physical once the initial state and active one-step rule are. -/
theorem physical_of_reachable
    (E : ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    {h0 k : Tr (Site d) (Site 2)} (hstart : E.Admissible h0)
    (hphysical0 : Physical d r t h0)
    (hpres : PreservesPhysical (r := r) (t := t) E)
    (hk : Reachable E h0 k) : Physical d r t k := by
  obtain ⟨m, omega, rfl⟩ := hk
  exact physical_run_of_preserves E hpres m h0 hstart hphysical0 omega

end PhysicalRun

section AcceptedPhysical

variable {d : Nat} [NeZero d]

/-- The concrete stopped accepted exploration preserves the lightweight physical invariant.
On failure no macro vertex is added.  On success the scheduler's positive incoming verdict is
the realized certificate for the new centre; the stopped outgoing heads are irrelevant here. -/
theorem acceptedExploration_preservesPhysical
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 2 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y)) :
    PreservesPhysical (r := r) (t := t)
      (CoreAcceptedAssembly.exploration r t s K n q eps axis sign
        hd hr (by omega : 2 * r ≤ t) hs hbudget hsigma hemb) := by
  classical
  let E := CoreAcceptedAssembly.exploration r t s K n q eps axis sign
    hd hr (by omega : 2 * r ≤ t) hs hbudget hsigma hemb
  change PreservesPhysical (r := r) (t := t) E
  intro base hadm hactive hphysical omega
  let k := E.revealed base omega
  let z := CoreStoppedReveal.centre n base
  let damage := CoreBatchShadow.maximalDamage base z
  let b := E.bit base omega
  have hk : CoreStoppedReveal.PhaseRel (box 2 n) r t s K n q eps
      (axis z) (sign z) base k := by
    change E.revealPhase.Phase base k
    exact E.revealed_phase hadm omega
  have hpost : E.advance base omega = k.step z ∅ damage b omega := by
    change E.commit base k b = k.step z ∅ damage b omega
    exact E.commit_eq_step base k b omega
  have hpostAdm : E.Admissible (E.advance base omega) :=
    E.advance_admissible hadm hactive omega
  constructor
  · exact CoreAcceptedTransition.inspected_subset_thin hd hpostAdm.preReveal.tagged
  · rw [hpost]
    have hstepInspected : (k.step z ∅ damage b omega).inspected = k.inspected := by simp
    have hstepOpenSites : (k.step z ∅ damage b omega).openSites = k.openSites := by
      change k.openSites ∪ (∅ : Finset (Site d)).filter (fun x => x ∈ omega) = k.openSites
      simp
    rw [hstepInspected, hstepOpenSites]
    have holdCert : ∀ u ∈ base.openV, ∃ a ∈ MacroExp.M d r t u,
        (↑k.openSites : Set (Site d)) ∈
          connWithin (zdGraph d) (↑k.inspected : Set (Site d)) (MacroExp.emb 0) a := by
      intro u hu
      obtain ⟨a, ha, hconn⟩ := hphysical.cert u hu
      refine ⟨a, ha, ?_⟩
      exact isUpperSet_connWithin (zdGraph d) _ (MacroExp.emb 0) a
        (Finset.coe_subset.2 (CoreStoppedReveal.PhaseRel.openSites_subset hk))
        (connWithin_mono_set (zdGraph d)
          (Finset.coe_subset.2 (CoreStoppedReveal.PhaseRel.extends_base hk).1)
          (MacroExp.emb 0) a hconn)
    intro u hu
    by_cases hb : b = true
    · simp only [BDDom.Transcript.step_openV, hb, if_true, Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · have hb' : E.bit base omega = true := by simpa only [b] using hb
        have hsuccess : omega ∈ E.success base :=
          (E.bit_eq_true_iff base omega).1 hb'
        have hmem : omega ∈
            CoreStoppedReveal.succ r t s K n q eps (axis z) (sign z) base k := by
          exact hsuccess
        have hverdict := (CoreStoppedReveal.mem_succ_iff_verdict
          r t s K n q eps (axis z) (sign z) base k omega).1 hmem
        have hevent := hverdict.2.1
        rw [CoreRes.event, mem_connWithinSet_iff] at hevent
        obtain ⟨a, ha, hconn⟩ := hevent
        refine ⟨a, Finset.mem_coe.2
          (CoreRes.target_subset_M (d := d) ht z (Finset.mem_coe.1 ha)), ?_⟩
        apply connWithin_mono_set (zdGraph d) (x := MacroExp.emb 0) (y := a) ?_ hconn
        intro x hx
        rw [Finset.mem_coe, Finset.mem_union] at hx
        rw [Finset.mem_coe]
        rcases hx with hx | hx
        · exact (CoreStoppedReveal.PhaseRel.extends_base hk).1 hx
        · by_cases hxold : x ∈ base.inspected
          · exact (CoreStoppedReveal.PhaseRel.extends_base hk).1 hxold
          · exact hverdict.1 (Finset.mem_sdiff.2 ⟨hx, hxold⟩)
      · rw [CoreStoppedReveal.PhaseRel.openV_eq hk] at hu
        exact holdCert u hu
    · simp only [BDDom.Transcript.step_openV, hb] at hu
      rw [CoreStoppedReveal.PhaseRel.openV_eq hk] at hu
      exact holdCert u hu

/-- Consequently every state reachable under the accepted interpreter is physically certified. -/
theorem physical_of_reachable_acceptedExploration
    (r t s K n : Nat) (q : unitInterval) (eps : Real)
    (axis : Site 2 → Site 2 → Fin d) (sign : Site 2 → Site 2 → Int)
    (hd : 2 ≤ d) (hr : 0 < r) (ht : 5 * r ≤ t)
    (hs : 0 < s) (hbudget : 10 * s * K ≤ 10 * r)
    (hsigma : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        sign (CoreStoppedReveal.centre n base) y = 1 ∨
          sign (CoreStoppedReveal.centre n base) y = -1)
    (hemb : ∀ base,
      CoreAcceptedTransition.Admissible (d := d) (box 2 n) r t q eps base →
      ¬ base.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
      ∀ y ∈ CoreFrontier.newHeads (d := d) base.base
        (CoreStoppedReveal.centre n base),
        (MacroExp.emb (y - CoreStoppedReveal.centre n base) : Site d) =
          Pi.single (axis (CoreStoppedReveal.centre n base) y)
            (sign (CoreStoppedReveal.centre n base) y))
    {h0 k : Tr (Site d) (Site 2)}
    (hstart : (CoreAcceptedAssembly.exploration r t s K n q eps axis sign
      hd hr (by omega : 2 * r ≤ t) hs hbudget hsigma hemb).Admissible h0)
    (hphysical0 : Physical d r t h0)
    (hk : Reachable (CoreAcceptedAssembly.exploration r t s K n q eps axis sign
      hd hr (by omega : 2 * r ≤ t) hs hbudget hsigma hemb) h0 k) : Physical d r t k :=
  physical_of_reachable _ hstart hphysical0
    (acceptedExploration_preservesPhysical r t s K n q eps axis sign
      hd hr ht hs hbudget hsigma hemb) hk

end AcceptedPhysical

section Slab

variable {d : Nat} [NeZero d] {r t n : Nat} {q a : unitInterval}

/-- Only the final, genuinely reached transcript needs the lightweight physical invariant. -/
theorem far_of_reachable_adaptive_run_reaches (hd : 2 ≤ d)
    (E : ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    {h0 : Tr (Site d) (Site 2)}
    (hreachablePhysical : ∀ k, Reachable E h0 k → Physical d r t k)
    (m : Nat) {omega : SiteConfig (Site d)}
    (hstart : E.Admissible h0)
    (hbase : h0.base = MacroExp.start d r t)
    (hQ : (↑(MacroExp.Q d r t 0) : Set (Site d)) ⊆ omega)
    (hR : (E.run m h0 omega).Reaches (zdGraph 2) 0 (MacroExp.tgt n)) :
    omega ∈ MacroExp.far d r t n := by
  have hphysical := hreachablePhysical _ (reachable_run E h0 m omega)
  obtain ⟨x, hfar, hpath⟩ := exists_far_of_physical_reaches hd hphysical hR
  refine ⟨x, hfar, ?_⟩
  have hstartOpen : (↑h0.openSites : Set (Site d)) ⊆ omega := by
    have hopen : h0.openSites = (MacroExp.start d r t).openSites := by
      change h0.base.openSites = (MacroExp.start d r t).openSites
      rw [hbase]
    rw [hopen]
    simpa [MacroExp.start] using hQ
  have hopen : (↑(E.run m h0 omega).openSites : Set (Site d)) ⊆ omega :=
    CoreAdaptSound.Exploration.run_openSites_subset E m h0 hstart omega hstartOpen
  exact isUpperSet_connWithin (zdGraph d) _ (MacroExp.emb 0) x hopen
    (connWithin_mono_set (zdGraph d) hphysical.inspected_thin (MacroExp.emb 0) x hpath)

/-- Finite-radius domination with `Physical` restricted to actual run states. -/
theorem le_real_far_of_reachable_adaptive (hd : 2 ≤ d)
    (E : ABDAdaptReg.Exploration (Site d) (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n))
    (hdensity : E.density = fun _ : Site d => q)
    {h0 : Tr (Site d) (Site 2)} (hstart : E.Admissible h0)
    (hbase : h0.base = MacroExp.start d r t)
    (hreachablePhysical : ∀ k, Reachable E h0 k → Physical d r t k)
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
    exact far_of_reachable_adaptive_run_reaches hd E hreachablePhysical m hstart hbase
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

/-- Thin-slab positivity with physical certificates only on reachable histories. -/
theorem thetaSiteOn_thin_pos_of_reachable_adaptive (hd : 2 ≤ d) (hr : 0 < r)
    (q a : unitInterval) (hq : 0 < (q : Real)) {c : Real} (hc : 0 < c)
    (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
      (box 2 n) 0 (MacroExp.tgt n))
    (h0 : Tr (Site d) (Site 2))
    (hbase : h0.base = MacroExp.start d r t)
    (hdensity : ∀ n, (E n).density = fun _ : Site d => q)
    (hstart : ∀ n, (E n).Admissible h0)
    (hreachablePhysical : ∀ n k, Reachable (E n) h0 k → Physical d r t k)
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
      le_real_far_of_reachable_adaptive hd (E n) (hdensity n) (hstart n)
        hbase (hreachablePhysical n) c (hbern n) (hstep n)
  refine lt_of_lt_of_le hcpos (hge.trans (measureReal_mono ?_ (measure_ne_top _ _)))
  intro omega homega
  rw [Set.mem_iInter] at homega
  exact MacroExp.infinite_of_forall_far hr homega

/-- Certificate soundness with the reachable-state physical invariant exposed honestly. -/
theorem certificateSound2_of_reachable_adaptive (hd : 3 ≤ d)
    (hsound : ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval),
      C.WellFormed → C.ValidAt2 q →
      ∃ (r t : Nat) (a : unitInterval) (c : Real)
        (h0 : Tr (Site d) (Site 2))
        (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
          (box 2 n) 0 (MacroExp.tgt n)),
        0 < r ∧ 2 * t ≤ C.width ∧ 0 < c ∧
        h0.base = MacroExp.start d r t ∧
        (∀ n, (E n).density = fun _ : Site d => q) ∧
        (∀ n, (E n).Admissible h0) ∧
        (∀ n k, Reachable (E n) h0 k → Physical d r t k) ∧
        (∀ n, c ≤ h0.bern a (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n)) ∧
        (∀ n h, (E n).Admissible h →
          ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
          (a : Real) ≤ h.prob (fun _ : Site d => q) ((E n).success h))) :
    LeftImp2.CertificateSound2 d := by
  intro C q hwf hv
  obtain ⟨r, t, a, c, h0, E, hr, ht, hc, hbase,
    hdensity, hstart, hreachablePhysical, hbern, hstep⟩ := hsound C q hwf hv
  have hq : 0 < (q : Real) := MacroExp.coe_pos_of_validAt2 hwf hv
  have hthin := thetaSiteOn_thin_pos_of_reachable_adaptive (d := d) (r := r) (t := t)
    (by omega) hr q a hq hc E h0 hbase hdensity hstart
    hreachablePhysical hbern hstep
  exact lt_of_lt_of_le (MacroExp.slab_two_pos_of_thin hd t q hthin)
    (MacroExp.thetaSiteOn_slab_mono ht q)

/-- Safe-benchmark certificate wrapper, with `Physical` restricted to reachable histories. -/
theorem certificateSound2_of_reachable_adaptive_safe (hd : 3 ≤ d)
    (hsound : ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval),
      C.WellFormed → C.ValidAt2 q →
      ∃ (r t : Nat)
        (h0 : Tr (Site d) (Site 2))
        (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
          (box 2 n) 0 (MacroExp.tgt n)),
        0 < r ∧ 2 * t ≤ C.width ∧
        h0.base = MacroExp.start d r t ∧ h0.failed = ∅ ∧
        (∀ n, (E n).density = fun _ : Site d => q) ∧
        (∀ n, (E n).Admissible h0) ∧
        (∀ n k, Reachable (E n) h0 k → Physical d r t k) ∧
        (∀ n h, (E n).Admissible h →
          ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
          (CoreSafe.successParam : Real) ≤
            h.prob (fun _ : Site d => q) ((E n).success h))) :
    LeftImp2.CertificateSound2 d := by
  apply certificateSound2_of_reachable_adaptive hd
  intro C q hwf hv
  obtain ⟨r, t, h0, E, hr, ht, hbase, hfailed, hdensity, hstart,
    hreachablePhysical, hstep⟩ := hsound C q hwf hv
  exact ⟨r, t, CoreSafe.successParam, CoreSafe.benchmark, h0, E,
    hr, ht, CoreSafe.benchmark_pos, hbase, hdensity, hstart,
    hreachablePhysical,
    (fun n => CoreSafe.benchmark_le_bern_of_start r t n h0 hbase hfailed), hstep⟩

/-- Assembly-facing safe wrapper.  Rather than asking the caller to quantify over reachable
histories, it accepts the local one-step physical rule; `physical_run_of_preserves` supplies the
reachable invariant used by the slab proof. -/
theorem certificateSound2_of_preserving_adaptive_safe (hd : 3 ≤ d)
    (hsound : ∀ (C : LeftImp2.Certificate2 d) (q : unitInterval),
      C.WellFormed → C.ValidAt2 q →
      ∃ (r t : Nat)
        (h0 : Tr (Site d) (Site 2))
        (E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
          (box 2 n) 0 (MacroExp.tgt n)),
        0 < r ∧ 2 * t ≤ C.width ∧
        h0.base = MacroExp.start d r t ∧ h0.failed = ∅ ∧
        (∀ n, (E n).density = fun _ : Site d => q) ∧
        (∀ n, (E n).Admissible h0) ∧
        (∀ n, PreservesPhysical (r := r) (t := t) (E n)) ∧
        (∀ n h, (E n).Admissible h →
          ¬ h.Terminal (zdGraph 2) (box 2 n) 0 (MacroExp.tgt n) →
          (CoreSafe.successParam : Real) ≤
            h.prob (fun _ : Site d => q) ((E n).success h))) :
    LeftImp2.CertificateSound2 d := by
  apply certificateSound2_of_reachable_adaptive_safe hd
  intro C q hwf hv
  obtain ⟨r, t, h0, E, hr, ht, hbase, hfailed, hdensity, hstart,
    hpres, hstep⟩ := hsound C q hwf hv
  have hphysical0 : Physical d r t h0 :=
    physical_of_base_eq_start (by omega) hbase
  have hreachable : ∀ n k, Reachable (E n) h0 k → Physical d r t k := by
    intro n k hk
    exact physical_of_reachable (E n) (hstart n) hphysical0 (hpres n) hk
  exact ⟨r, t, h0, E, hr, ht, hbase, hfailed, hdensity, hstart,
    hreachable, hstep⟩

end Slab

/-! The exact stopped-interpreter probability bridge, re-exported for the reachable capstone. -/
abbrev acceptedExploration_prob_success_eq_prob_batchSuccess :=
  @CoreAcceptedAssembly.exploration_prob_success_eq_prob_batchSuccess

#print axioms KNAll.Site.CoreReachSafe.far_of_reachable_adaptive_run_reaches
#print axioms KNAll.Site.CoreReachSafe.acceptedExploration_preservesPhysical
#print axioms KNAll.Site.CoreReachSafe.physical_of_reachable_acceptedExploration
#print axioms KNAll.Site.CoreReachSafe.le_real_far_of_reachable_adaptive
#print axioms KNAll.Site.CoreReachSafe.thetaSiteOn_thin_pos_of_reachable_adaptive
#print axioms KNAll.Site.CoreReachSafe.certificateSound2_of_reachable_adaptive_safe
#print axioms KNAll.Site.CoreReachSafe.certificateSound2_of_preserving_adaptive_safe
#print axioms KNAll.Site.CoreReachSafe.acceptedExploration_prob_success_eq_prob_batchSuccess

end KNAll.Site.CoreReachSafe

end
