import Hypergraph.FiniteHyperGluingClosed
import Hypergraph.TargetExtension

/-!
# Unconditional domain-relative target extension

This is the composition point between the finite labelled-hyperedge theorem and the
support-in-`D` target-extension interface.  The underlying target-extension proof still exposes
its finite shell geometry, relative gate, product weights, and component-cylinder estimates; the
only argument removed here is `PinnedSiteGluing`, now supplied by
`FiniteHyperGluingClosed.pinnedSiteGluing`.
-/

noncomputable section

namespace KNAll.Site.TargetExtensionClosed

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site
open scoped Classical

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- The manuscript support-in-`D` target extension, with no correlation hypothesis. -/
theorem targetExtension_D (Dom : Finset V) (o : V) (T : Set V)
    {Delta : Nat} (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Delta)
    {L : Nat} (hL : 0 < L)
    (lv : Nat → TargetExt.LevelGeometryD G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ (lv i).D →
      ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D)
    (qI : unitInterval) (hq1 : (qI : Real) < 1)
    (w : V → unitInterval) (hwo : w o = 1)
    (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI)
    (N k s : Nat)
    (hsel_card : ∀ i < L, ∀ K ⊆ TargetExt.outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      ((lv i).J x).card ≤ s)
    {delta : Real} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1 / 3)
    (hLdelta : 1 ≤ (L : Real) * delta * (1 - (qI : Real)) ^ (Delta * N))
    (hk : (1 - (qI : Real) ^ s) ^ k ≤ delta)
    (hGood : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      1 - 3 * delta ^ 2 ≤
        (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - delta <
      (prodBernoulli w).real (connWithinSet G (Dom : Set V) o B)) :
    (1 - 3 * delta) * (1 - 3 * delta) * (1 - delta) ≤
      (prodBernoulli w).real (connWithinSet G (Dom : Set V) o T) := by
  exact TargetExt.targetExtension_D G
    FiniteHyperGluingClosed.pinnedSiteGluing Dom o T hdeg hL lv hnest hgateRel hB
    qI hq1 w hwo hw N k s hsel_card hs hdelta0 hdelta1 hLdelta hk hGood hsrc

/-- The epsilon-delta form consumed by finite face, long-box, and post-entry calls. -/
theorem targetExtension_eps_D (Dom : Finset V) (o : V) (T : Set V)
    {Delta : Nat} (hdeg : ∀ x, (Dom.filter (G.Adj x)).card ≤ Delta)
    {L : Nat} (hL : 0 < L)
    (lv : Nat → TargetExt.LevelGeometryD G Dom o T)
    (hnest : ∀ i, i + 1 < L → (lv (i + 1)).D ⊆ (lv i).D)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ (lv i).D →
      ∀ y ∈ (lv i).D, G.Adj x y → y ∉ (lv (i + 1)).D)
    {B : Set V} (hB : ∀ i < L, B ⊆ ↑(lv i).D)
    (qI : unitInterval) (hq1 : (qI : Real) < 1)
    (w : V → unitInterval) (hwo : w o = 1)
    (hw : ∀ i < L, ∀ y ∈ (lv i).D, w y = qI)
    (N k s : Nat)
    (hsel_card : ∀ i < L, ∀ K ⊆ TargetExt.outerBoundary G Dom (lv i).D,
      N ≤ K.card → k ≤ ((lv i).sel K).card)
    (hs : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      ((lv i).J x).card ≤ s)
    {eps : Real} (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hLdelta : 1 ≤ (L : Real) * (eps / 8) *
      (1 - (qI : Real)) ^ (Delta * N))
    (hk : (1 - (qI : Real) ^ s) ^ k ≤ eps / 8)
    (hGood : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (lv i).D,
      1 - 3 * (eps / 8) ^ 2 ≤
        (siteBernoulli (fun _ : V => qI)).real ((lv i).Gx x))
    (hsrc : 1 - eps / 8 <
      (prodBernoulli w).real (connWithinSet G (Dom : Set V) o B)) :
    1 - eps < (prodBernoulli w).real (connWithinSet G (Dom : Set V) o T) := by
  exact TargetExt.targetExtension_eps_D G
    FiniteHyperGluingClosed.pinnedSiteGluing Dom o T hdeg hL lv hnest hgateRel hB
    qI hq1 w hwo hw N k s hsel_card hs heps0 heps1 hLdelta hk hGood hsrc

end KNAll.Site.TargetExtensionClosed

end

#print axioms KNAll.Site.TargetExtensionClosed.targetExtension_D
#print axioms KNAll.Site.TargetExtensionClosed.targetExtension_eps_D
