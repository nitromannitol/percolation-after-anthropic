import Hypergraph.HyperOneCluster
import Hypergraph.HyperTwoCluster

/-!
# The two-cluster inequality with its hypothesis discharged

`KN/HyperTwoCluster.lean` carries the one-cluster inequality as an explicit
hypothesis `OneClusterInequality H S T`, so that the two developments could be
built independently.  `KN/HyperOneCluster.lean` proves that hypothesis, in the
strong form with an inherited avoided set.  Specialising it at `X = Y = T` and
simplifying `T ∩ T` and `T ∪ T` discharges it, and this file records the
resulting unconditional statements.
-/

namespace KNAll.Site

open Percolation.Literature.LatticeModels

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
/-- The one-cluster inequality holds for every finite hypergraph. -/
theorem oneClusterInequality_holds (H : Hypergraph V E) (S T : Set V) :
    OneClusterInequality H S T := by
  intro f g hf hg hf0 hg0
  simpa [Set.inter_self, Set.union_self] using
    avoidIntegral_mul_le_inter H S T T hf hg hf0 hg0

/-- Positive association of the two clusters, unconditionally. -/
theorem avoid_cluster_association' (H : Hypergraph V E) (S T : Set V)
    {F G : Set V → ℝ} (hF : Monotone F) (hG : Antitone G) :
    (∫ ω in avoidEvent H S T, F (hyperClusterSet H ω S) ∂(prodBernoulli H.prob)) *
      (∫ ω in avoidEvent H S T, G (hyperClusterSet H ω T) ∂(prodBernoulli H.prob))
      ≤ (prodBernoulli H.prob).real (avoidEvent H S T) *
        ∫ ω in avoidEvent H S T,
          F (hyperClusterSet H ω S) * G (hyperClusterSet H ω T) ∂(prodBernoulli H.prob) :=
  avoid_cluster_association H S T (oneClusterInequality_holds H S T) hF hG

end KNAll.Site
