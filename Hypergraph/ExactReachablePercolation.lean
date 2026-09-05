import Hypergraph.ExactReachableMacroInterpreter

/-!
# Percolation from one exact reachable macro interpreter

This is the certificate-free endpoint of the accepted-only construction.  It uses the physical
invariant only on transcripts actually reached by the concrete exploration, and converts its
thin-slab conclusion directly to full-lattice site percolation.
-/

noncomputable section

namespace KNAll.Site.ExactReachablePercolation

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site

variable {d : Nat} [NeZero d]

/-- A genuine initial core reservation and the local accepted-state success estimate for one
fixed tuple of finite scales imply site percolation at the same parameter.  No certificate or
universal assertion about arbitrary admissible histories occurs in the statement. -/
theorem thetaSite_pos_of_initialCoreBounds_and_localAcceptedSuccess
    (hd : 3 ≤ d) (r t s K : Nat) (q : unitInterval)
    (hr : 0 < r) (ht : 5 * r ≤ t) (hs : 0 < s)
    (hbudget : 10 * s * K ≤ 10 * r) (hq : 0 < (q : Real))
    (hinit : CoreInitial.InitialCoreBounds (d := d) r t q
      (ExactMacroNumerics.deltaC d))
    (hsucc : ExactReachableMacro.LocalAcceptedSuccess (d := d) (by omega : 2 ≤ d)
      r t s K q (ExactMacroNumerics.deltaC d) hr (by omega : 2 * r ≤ t) hs hbudget) :
    0 < thetaSite d q := by
  let h0 : CoreReachSafe.Tr (Site d) (Site 2) :=
    CoreAcceptedTransition.start d r t
  let E : ∀ n, ABDAdaptReg.Exploration (Site d) (zdGraph 2)
      (box 2 n) 0 (MacroExp.tgt n) := fun n =>
    ExactReachableMacro.exploration (by omega : 2 ≤ d) r t s K n q
      (ExactMacroNumerics.deltaC d) hr (by omega : 2 * r ≤ t) hs hbudget
  have hthin := CoreReachSafe.thetaSiteOn_thin_pos_of_reachable_adaptive
    (d := d) (r := r) (t := t) (by omega : 2 ≤ d) hr
    q CoreSafe.successParam hq CoreSafe.benchmark_pos E h0 rfl
    (fun _ => rfl)
    (fun n => ExactReachableMacro.start_admissible (by omega : 2 ≤ d)
      r t s K n q (ExactMacroNumerics.deltaC d) hr (by omega : 2 * r ≤ t)
      hs hbudget hinit)
    (fun n k hk => ExactReachableMacro.reachable_physical (by omega : 2 ≤ d)
      r t s K n q (ExactMacroNumerics.deltaC d) hr ht hs hbudget hinit k hk)
    (fun n => CoreSafe.benchmark_le_bern_of_start r t n h0 rfl rfl)
    hsucc
  exact lt_of_lt_of_le (MacroExp.slab_two_pos_of_thin hd t q hthin)
    (thetaSiteOn_slab_le d (2 * t) q)

#print axioms KNAll.Site.ExactReachablePercolation.thetaSite_pos_of_initialCoreBounds_and_localAcceptedSuccess

end KNAll.Site.ExactReachablePercolation

end
