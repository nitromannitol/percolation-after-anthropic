import KNConjectures
import Hypergraph

set_option pp.explicit true in
#check @Percolation.Continuity.CSH.percolationContinuity_allDimensions
set_option pp.explicit true in
#check @KNAll.Site.site_no_percolation_at_critical
set_option pp.explicit true in
#check @KNAll.Site.site_no_percolation_at_critical_primitive

#print axioms Percolation.Continuity.CSH.percolationContinuity_allDimensions
#print axioms KNAll.Site.site_no_percolation_at_critical
#print axioms KNAll.Site.site_phase_transition
#print axioms KNAll.conjecture1_holds
#print axioms KNAll.conjecture2Strong_holds
#print axioms KNAll.conjecture3_holds
#print axioms KNAll.conjecture4Fixed_holds
#print axioms KNAll.Guarded.conjecture6_holds
#print axioms KNAll.question5_holds
#print axioms KNAll.question7_holds
#print axioms KNAll.question9_holds
#print axioms KNAll.not_question8EveryMin
#print axioms KNAll.Site.FiniteHyperGluingClosed.hyperedgeGluing
#print axioms KNAll.Site.FiniteHyperGluingClosed.pinnedSiteGluing

example : Percolation.Literature.PercolationContinuity 3 :=
  Percolation.Continuity.CSH.percolationContinuity_allDimensions 3 (by norm_num)
example : KNAll.Site.thetaSite 3 (KNAll.Site.criticalProbSiteI 3) = 0 :=
  KNAll.Site.site_no_percolation_at_critical 3 (by norm_num)
