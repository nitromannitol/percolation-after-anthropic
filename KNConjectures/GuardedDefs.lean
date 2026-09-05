import KNConjectures.Conjectures
import KNConjectures.Conjecture6Reduction
import KNConjectures.PairSource
import Percolation.Continuity.CSH.UnfoldDecoy
import Percolation.Literature.TwoClusterGibbsCovariance

set_option linter.unusedSectionVars false

/-!
# Definitions for the two-vertex-source proof of Kozma–Nitzan's Conjecture 6

Definitions only.  The theorems about them are proved, in dependency order and in the
namespace `KNAll.Guarded`, by the modules `GuardedBasic`, `GuardedKernel`, `GuardedDecoy`,
`GuardedTwoCluster`, `PairGuardedCSH`, `PairSurplus`, `PairSurplusClosure`, `PairFixedMin`
and `Conjecture6Proof`, the last of which contains `conjecture6Strong_holds` and
`conjecture6_holds`.  The exact conditional identity used for a single vertex does not hold
for a two-vertex source; `guardResidMoment_eq` carries the extra term `guardDelta`, which is
nonnegative and vanishes for a single vertex.
-/

noncomputable section

namespace KNAll

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open Percolation.Continuity Percolation.Continuity.CSH
open scoped Classical

variable {V : Type*} [Fintype V]

/-! ## Set-source events and the guarded hierarchy -/

/-- The union of the open vertex clusters rooted in the (possibly empty or disconnected)
source set `R`. -/
def sourceCluster (ω : BondConfig V) (R : Set V) : Set V :=
  ⋃ r ∈ R, openCluster ω r

/-- The event that no vertex of source `R` is connected to any vertex of `Y`. -/
def sourceAvoid (R Y : Set V) : Set (BondConfig V) :=
  {ω | ∀ r ∈ R, ∀ y ∈ Y, ¬ (openGraph ω).Reachable r y}

/-- The event that source `R` is connected to at least one vertex of `X`. -/
def sourceConn (R X : Set V) : Set (BondConfig V) :=
  {ω | ∃ r ∈ R, ∃ x ∈ X, (openGraph ω).Reachable r x}

/-- The guarded contact event `H_{X|Y}(R) = {R ↮ Y, R ↔ X}`. -/
def guardEv (R X Y : Set V) : Set (BondConfig V) :=
  sourceAvoid R Y ∩ sourceConn R X

/-- The vertex set represented by a list. -/
def listSet (D : List V) : Set V := {d | d ∈ D}

/-- Read a vertex-cluster functional on the open edge cluster of its marked root. -/
def vertexClusterFun (z : V) (F : Set V → ℝ) (K : Set (Sym2 V)) : ℝ :=
  F (insert z {u | ∃ e ∈ K, u ∈ e})

/-- The denominator-free guarded covariance `Γ^g_{x,Y}(R)`. -/
def guardCovD (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (R : Set V) : ℝ :=
  (prodBernoulli w).real (sourceAvoid ({x} : Set V) Y) *
      (∫ ω in guardEv R ({x} : Set V) Y,
        g (openEdgeCluster ω x) ∂(prodBernoulli w)) -
    (∫ ω in sourceAvoid ({x} : Set V) Y,
        g (openEdgeCluster ω x) ∂(prodBernoulli w)) *
      (prodBernoulli w).real (guardEv R ({x} : Set V) Y)

/-- The set-source decoy profile `R ↦ P(H_{d|A}(R))/P(d ↮ A)`. -/
def guardAvoidConst (w : Sym2 V → unitInterval) (d : V) (A : Set V)
    (R : Set V) : ℝ :=
  (prodBernoulli w).real (guardEv R ({d} : Set V) A) /
    (prodBernoulli w).real (sourceAvoid ({d} : Set V) A)

/-- The list of set-source decoy profiles.  Decoy vertices are stored as singleton source
sets because `CSH.cshMarg` is instantiated with evaluation type `Set V`. -/
def guardDecoyList (w : Sym2 V → unitInterval) :
    Set V → List V → List (Set V × (Set V → ℝ))
  | _, [] => []
  | A, d :: ds => (({d} : Set V), guardAvoidConst w d A) ::
      guardDecoyList w (insert d A) ds

/-- The set-source observer price `P(H_{v|A}(O))/P(v ↮ A)`. -/
def guardObsConst (w : Sym2 V → unitInterval) (O : Set V) (v : V)
    (A : Set V) : ℝ :=
  (prodBernoulli w).real (guardEv O ({v} : Set V) A) /
    (prodBernoulli w).real (sourceAvoid ({v} : Set V) A)

/-- The guarded CSH margin with primary source `O` and singleton secondary evaluation `{v}`. -/
def guardCSHMargin (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (D : List V) (O : Set V) (v : V) (g : Set (Sym2 V) → ℝ) : ℝ :=
  cshMarg (guardDecoyList w (insert x Y) D)
    (guardObsConst w O v (insert x Y ∪ listSet D)) O ({v} : Set V)
    (guardCovD w x Y g)

/-- The pair-primary guarded hierarchy assertion. -/
def PairGuardCSHHolds (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (D : List V) (s₁ s₂ v : V) : Prop :=
  ∀ g : Set (Sym2 V) → ℝ, Monotone g →
    0 ≤ guardCSHMargin w x Y D ({s₁, s₂} : Set V) v g

/-- The nondegenerate guarded-hierarchy placement assumptions. -/
def PairGuardAdmissible (x : V) (Y : Set V) (D : List V)
    (s₁ s₂ v : V) : Prop :=
  s₁ ≠ s₂ ∧ x ∉ Y ∧ v ∉ insert x Y ∧ D.Nodup ∧
    (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ v) ∧
    Disjoint ({s₁, s₂} : Set V) (insert x (insert v (Y ∪ listSet D)))

/-! ## Induced worlds and the guarded horizontal estimate -/

/-- Delete every edge having an endpoint outside the induced world `U`. -/
def inducedWeight (w : Sym2 V → unitInterval) (U : Set V) :
    Sym2 V → unitInterval := fun e =>
  if ∀ u ∈ e, u ∈ U then w e else 0

/-- Probability in the induced world `U`. -/
def worldProb (w : Sym2 V → unitInterval) (U : Set V)
    (E : Set (BondConfig V)) : ℝ :=
  (prodBernoulli (inducedWeight w U)).real E

/-- The residual-source kernel
`1_{K∩R≠∅} P_{U\K}(C_{R\K} ∩ B = ∅)`. -/
def sourceKernel (w : Sym2 V → unitInterval) (U R B K : Set V) : ℝ :=
  if (K ∩ (R ∩ U)).Nonempty then
    worldProb w (U \ K) (sourceAvoid ((R ∩ U) \ K) (B ∩ U))
  else 0

/-- `M^U_v(B) = P_U(v ↮ B)`. -/
def worldAvoidMass (w : Sym2 V → unitInterval) (U : Set V) (v : V)
    (B : Set V) : ℝ :=
  if v ∈ U then worldProb w U (sourceAvoid ({v} : Set V) (B ∩ U)) else 0

/-- `E^U_{R,v}(B) = P_U(R ↮ B, R ↔ v)`. -/
def worldGuardMass (w : Sym2 V → unitInterval) (U R : Set V) (v : V)
    (B : Set V) : ℝ :=
  if v ∈ U then
    worldProb w U (guardEv (R ∩ U) ({v} : Set V) (B ∩ U))
  else 0

/-- The guarded contact price in an induced world, with the zero-denominator convention. -/
def worldGuardPrice (w : Sym2 V → unitInterval) (U R : Set V) (v : V)
    (X : Set V) : ℝ :=
  worldGuardMass w U R v X / worldAvoidMass w U v X

/-- `Y_h^U(N)` from the guarded two-source induction. -/
def guardedWorldY (w : Sym2 V → unitInterval) (U : Set V) (x : V)
    (N : Set V) (h : Set V → ℝ) : ℝ :=
  if x ∈ U then
    ∫ ω in sourceAvoid ({x} : Set V) (N ∩ U),
      h (U \ sourceCluster ω (N ∩ U)) ∂(prodBernoulli (inducedWeight w U))
  else 0

/-- `X_{R,h}^U(N)` from the guarded two-source induction; both residual
avoidance indicators are retained. -/
def guardedWorldX (w : Sym2 V → unitInterval) (U R : Set V) (x v : V)
    (X N : Set V) (h : Set V → ℝ) : ℝ :=
  if x ∈ U ∧ v ∈ U then
    ∫ ω in sourceAvoid ({x} : Set V) (N ∩ U) ∩
        sourceAvoid (R ∩ U) (N ∩ U),
      worldGuardPrice w (U \ sourceCluster ω (N ∩ U)) R v X *
        h (U \ sourceCluster ω (N ∩ U))
          ∂(prodBernoulli (inducedWeight w U))
  else 0

/-- An ordinary covariance in an induced world between `g(C_x)` and source contact
`{R ↔ X}`. -/
def sourceWorldCov (w : Sym2 V → unitInterval) (U : Set V) (x : V)
    (g : Set (Sym2 V) → ℝ) (R X : Set V) : ℝ :=
  if x ∈ U then
    (∫ ω in sourceConn (R ∩ U) (X ∩ U),
        g (openEdgeCluster ω x) ∂(prodBernoulli (inducedWeight w U))) -
      (∫ ω, g (openEdgeCluster ω x) ∂(prodBernoulli (inducedWeight w U))) *
        worldProb w U (sourceConn (R ∩ U) (X ∩ U))
  else 0

/-- The union-marker horizontal term after the whole `Y`-cluster is exposed. -/
def guardHorizontal (w : Sym2 V → unitInterval) (x : V) (Y X O : Set V)
    (v : V) (g : Set (Sym2 V) → ℝ) : ℝ :=
  (∫ ω in sourceAvoid ({x} : Set V) Y ∩ sourceAvoid O Y,
      sourceWorldCov w (Set.univ \ sourceCluster ω Y) x g O X
        ∂(prodBernoulli w)) -
    guardObsConst w O v (X ∪ Y) *
      (∫ ω in sourceAvoid ({x} : Set V) Y,
        sourceWorldCov w (Set.univ \ sourceCluster ω Y) x g ({v} : Set V) X
          ∂(prodBernoulli w))

/-! ## Corrected guarded decoy identity and one-sided unfolding -/

/-- The centered residual moment against the set-source decoy bracket. -/
def guardResidMoment (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (d : V) (A R : Set V) : ℝ :=
  ∫ ω,
    CSH.resid (fun e => (w e : ℝ)) x Y g ω *
      (Percolation.Literature.DecisionTree.ind (guardEv R ({d} : Set V) A) ω -
        guardAvoidConst w d A R *
          Percolation.Literature.DecisionTree.ind
            (sourceAvoid ({d} : Set V) A) ω) ∂(prodBernoulli w)

/-- The nonnegative correction in the guarded decoy identity:
`E[(Φ(C_R)-Φ(C_d)); H_{d|A}(R)]`. -/
def guardDelta (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (d : V) (A R : Set V) : ℝ :=
  ∫ ω in guardEv R ({d} : Set V) A,
    (CSH.phiFun w x Y g (sourceCluster ω R) -
      CSH.phiFun w x Y g (openCluster ω d)) ∂(prodBernoulli w)

/-- The exact lower-level and `Δ` terms accumulated in the corrected unfolding. -/
def guardUnfoldTerms (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (O : Set V) (v : V) : Set V → List V → ℝ
  | _, [] => 0
  | A, d :: ds =>
      ((prodBernoulli w).real (sourceAvoid ({d} : Set V) A))⁻¹ *
          guardCSHMargin w d A ds O v (CSH.phiT w x Y g d) +
        guardDelta w x Y g d A O +
        guardUnfoldTerms w x Y g O v (insert d A) ds

/-! ## The two-cluster passage from within-world to global covariance -/

/-- Denominator-free covariance on `D` when the test may depend on both explored
clusters `C_S` and `C_T`. -/
def twoClusterCov (w : Sym2 V → ℝ) (S T : Set V)
    (D : Set (BondConfig V)) (φ : Set (Sym2 V) → ℝ)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ) : ℝ :=
  (∑ ω, BHK2006.weight w ω *
      Percolation.Literature.DecisionTree.ind D ω) *
      (∑ ω, BHK2006.weight w ω *
        (φ (BHK2006.setCl ω S) * h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω)) -
    (∑ ω, BHK2006.weight w ω *
      (φ (BHK2006.setCl ω S) *
        Percolation.Literature.DecisionTree.ind D ω)) *
      (∑ ω, BHK2006.weight w ω *
        (h (BHK2006.setCl ω S) (BHK2006.setCl ω T) *
          Percolation.Literature.DecisionTree.ind D ω))

/-- Conditional covariance in the first (`S`) half-step, for a two-cluster test. -/
def twoClusterCondCovFirst (w : Sym2 V → ℝ) (S T : Set V)
    (φ : Set (Sym2 V) → ℝ) (h : Set (Sym2 V) → Set (Sym2 V) → ℝ)
    (B : Set (Sym2 V)) : ℝ :=
  BHK2006.condS w S T (fun A => φ A * h A B) B -
    BHK2006.condS w S T φ B * BHK2006.condS w S T (fun A => h A B) B

/-- The averaged first half-step covariance. -/
def twoClusterWithinFirst (w : Sym2 V → ℝ) (S T : Set V)
    (D : Set (BondConfig V)) (φ : Set (Sym2 V) → ℝ)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, BHK2006.weight w ω *
    (twoClusterCondCovFirst w S T φ h (BHK2006.setCl ω T) *
      Percolation.Literature.DecisionTree.ind D ω)

/-- The averaged second half-step covariance of `B ↦ E[φ(C_S)|C_T=B]`
with the two-cluster test, conditional on `C_S`. -/
def twoClusterWithinSecond (w : Sym2 V → ℝ) (S T : Set V)
    (D : Set (BondConfig V)) (φ : Set (Sym2 V) → ℝ)
    (h : Set (Sym2 V) → Set (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, BHK2006.weight w ω *
    (BHK2006.condCov w T S (BHK2006.condS w S T φ)
        (fun B => h (BHK2006.setCl ω S) B) (BHK2006.setCl ω S) *
      Percolation.Literature.DecisionTree.ind D ω)

/-- Carrier contact test `b_R(A,B)` for the two explored edge clusters. -/
def guardContactTest (x : V) (Y R : Set V) (A B : Set (Sym2 V)) : ℝ :=
  if ((insert x {u | ∃ e ∈ A, u ∈ e}) ∩ R).Nonempty ∧
      Disjoint (Y ∪ {u | ∃ e ∈ B, u ∈ e}) R then 1 else 0

/-- A globally antitone extension of the contact test: the primary source `O` keeps
the full guard, while every other singleton evaluation is read only from the first
cluster.  On `{x ↮ Y}` this agrees with `guardContactTest` at every evaluation used
by the level form. -/
def guardEvalTest (x : V) (Y O R : Set V) (A B : Set (Sym2 V)) : ℝ :=
  if R = O then guardContactTest x Y R A B
  else if hR : ∃ u : V, R = ({u} : Set V) then
    if Classical.choose hR ∈ insert x {u | ∃ e ∈ A, u ∈ e} then 1 else 0
  else guardContactTest x Y R A B

/-- Apply all guarded decoy operators and the observer subtraction to `b_R(A,B)`. -/
def guardLevelTest (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (D : List V) (O : Set V) (v : V) (A B : Set (Sym2 V)) : ℝ :=
  cshMarg (guardDecoyList w (insert x Y) D)
    (guardObsConst w O v (insert x Y ∪ listSet D)) O ({v} : Set V)
    (fun R => guardEvalTest x Y O R A B)

/-- The first-half, within-world term for the guarded level test. -/
def guardWithin (w : Sym2 V → unitInterval) (x : V) (Y : Set V)
    (D : List V) (O : Set V) (v : V) (g : Set (Sym2 V) → ℝ) : ℝ :=
  twoClusterWithinFirst (fun e => (w e : ℝ)) ({x} : Set V) Y
    (sourceAvoid ({x} : Set V) Y) g (guardLevelTest w x Y D O v)

/-! ## Set-source avoided surplus -/

/-- The first-in-rank guarded relay pattern for a source set. -/
def sourceFirstPattern (R Y : Set V) (T : Finset V) (r : V → ℕ)
    (a : V) : Set (BondConfig V) :=
  sourceAvoid R Y ∩
    (sourceConn R ({a} : Set V) ∩
      ⋂ a' ∈ T.filter (fun a' => r a' < r a),
        (sourceConn R ({a'} : Set V))ᶜ)

/-- Avoided first-relay surplus for an arbitrary source set. -/
def sourceSurplusY (w : Sym2 V → unitInterval) (Y : Set V) (T : Finset V)
    (r : V → ℕ) (F : Set V → ℝ) (R : Set V) : ℝ :=
  (∫ ω in sourceAvoid R Y ∩ sourceConn R (↑T : Set V),
      F (sourceCluster ω R) ∂(prodBernoulli w)) -
    ∑ a ∈ T, (prodBernoulli w).real (sourceFirstPattern R Y T r a) *
      condMean w Y F a

/-- The set-source avoided surplus margin. -/
def sourceSurplusMarginY (w : Sym2 V → unitInterval) (Y : Set V)
    (T : Finset V) (r : V → ℕ) (D : List V) (O : Set V) (v : V)
    (F : Set V → ℝ) : ℝ :=
  cshMarg (guardDecoyList w (Y ∪ (↑T : Set V)) D)
    (guardObsConst w O v (Y ∪ (↑T : Set V) ∪ listSet D)) O ({v} : Set V)
    (sourceSurplusY w Y T r F)

/-- Placement assumptions for pair-source surplus peeling.  In particular the auxiliary
observer and every auxiliary decoy are disjoint from all displayed data. -/
def PairSurplusAdmissible (Y : Set V) (T : Finset V) (D : List V)
    (s₁ s₂ v : V) : Prop :=
  s₁ ≠ s₂ ∧ Disjoint (↑T : Set V) Y ∧ D.Nodup ∧
    v ∉ Y ∪ (↑T : Set V) ∪ listSet D ∧
    (∀ d ∈ D, d ∉ Y ∪ (↑T : Set V) ∧ d ≠ v) ∧
    Disjoint ({s₁, s₂} : Set V)
      (insert v (Y ∪ (↑T : Set V) ∪ listSet D))

/-- The centered top-relay increment using the relay cluster `C_z`. -/
def sourceTopIncrement (w : Sym2 V → unitInterval) (Y : Set V)
    (T : Finset V) (F : Set V → ℝ) (z : V) (R : Set V) : ℝ :=
  ∫ ω in guardEv R ({z} : Set V) (Y ∪ (↑T : Set V)),
    (F (openCluster ω z) - condMean w Y F z) ∂(prodBernoulli w)

/-- The repricing error `κ_z` for the rank-maximal relay. -/
def sourceKappa (w : Sym2 V → unitInterval) (Y : Set V) (T : Finset V)
    (F : Set V → ℝ) (z : V) : ℝ :=
  condMean w Y F z *
      (prodBernoulli w).real
        (sourceAvoid ({z} : Set V) (Y ∪ (↑T : Set V))) -
    ∫ ω in sourceAvoid ({z} : Set V) (Y ∪ (↑T : Set V)),
      F (openCluster ω z) ∂(prodBernoulli w)

/-- Indicator that the marked open edge cluster is nonempty. -/
def nonIsolationFun (K : Set (Sym2 V)) : ℝ := if K.Nonempty then 1 else 0

/-- Mass of the isolated `z` cluster while it avoids `B`. -/
def isolatedAvoidMass (w : Sym2 V → unitInterval) (z : V) (B : Set V) : ℝ :=
  (prodBernoulli w).real
    (sourceAvoid ({z} : Set V) B ∩ {ω | openCluster ω z = ({z} : Set V)})

/-- Relays reached by source `R` in configuration `ω`. -/
def sourceReached (R : Set V) (T : Finset V) (ω : BondConfig V) : Finset V :=
  T.filter fun a => ω ∈ sourceConn R ({a} : Set V)

/-- Rank-free minimum representation used for closure to weights `0` and `1`. -/
def sourceMinFormY (w : Sym2 V → unitInterval) (Y : Set V) (T : Finset V)
    (F : Set V → ℝ) (R : Set V) : ℝ :=
  ∫ ω in sourceAvoid R Y ∩ sourceConn R (↑T : Set V),
    (F (sourceCluster ω R) -
      if h : (sourceReached R T ω).Nonempty then
        (sourceReached R T ω).inf' h (fun a => condMean w Y F a)
      else 0) ∂(prodBernoulli w)

/-! ## Pair fixed-minimizer gap -/

/-- The pair-source fixed-minimizer integral (FM2), for a general increasing functional. -/
def pairFixedMinGap (w : Sym2 V → unitInterval) (A : Finset V)
    (v w' a : V) (F : Set V → ℝ) : ℝ :=
  ∫ ω in pairAvoid v w' a ∩ pairConn v w' (A.erase a),
    (F (pairCluster ω v w') - F (openCluster ω a)) ∂(prodBernoulli w)

/-! ## Elementary bridges -/












/-! ## Source kernel, exchange, and horizontal lemmas -/








/-! ## GDI and corrected unfolding lemmas -/








/-! ## Two-half reduction and the joint guarded induction -/








/-! ## Source-surplus peeling, transfer, and closure -/















/-! ## Projection, FM2, and Conjecture 6 -/





/-! ### Internal-edge invariance and the pinned gap -/










end KNAll

end
