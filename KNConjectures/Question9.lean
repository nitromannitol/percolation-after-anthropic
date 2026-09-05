import KNConjectures.SourceProjection
import KNConjectures.Question9Reduction

/-!
# Kozma--Nitzan Question 9

The arbitrary-source fixed-minimizer inequality is proved in
`KN.SourceProjection`.  The deleted-star decomposition is proved in
`KN.Question9Reduction`.  This module connects those two independently checked
pieces and exports the unconditional answer to Question 9.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

/-- The set-source fixed-minimizer proposition used by the deleted-star
reduction, now discharged without an extra hypothesis. -/
theorem setSourceFixedMin_holds : SetSourceFixedMin := by
  intro n w A S a F ha hF hmin
  have hgap := Guarded.source_fixedMin w A S a F ha hF hmin
  simpa [Guarded.sourceFixedMinGap, sourceAvoid, sourceConn, and_comm] using hgap

/-- **Kozma--Nitzan Question 9 has an affirmative answer.** -/
theorem question9_holds : Question9 :=
  question9_of_setSourceFixedMin setSourceFixedMin_holds

end KNAll

end

#print axioms KNAll.setSourceFixedMin_holds
#print axioms KNAll.question9_holds
