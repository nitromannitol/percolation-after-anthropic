import KNConjectures.Conjectures

/-!
# Conjecture 4 in the paper's printed vocabulary (monotone cluster properties)

The paper (arXiv:2401.12397, §5.1 p. 31, Conjecture 4 p. 32) quantifies over functions `f(v, ω)` that depend only on the
open cluster `C_ω(v)`, are increasing in it, and satisfy `f(v, ω) = f(w, ω)` when `{v, w}` is open.  `KNAll.Conjecture4`
quantifies over increasing `F : Set (Fin n) → ℝ` with `f(v, ω) = F (C_ω(v))`.  This module shows nothing is lost: every
such `f` is `F (C_ω(v))` for the increasing `F` obtained by evaluating `f` on the clique configuration of a vertex set
(extended by the development's `KNPreFKG.monotoneOnNonempty_extension`), so the printed Conjecture 4 follows
(`conjecture4_clusterProperty_holds`), together with the paper's two examples `f = |C|` and `f = 1{|C| ≥ k}` for every `k`
(the paper's Theorem 9 covers `k ≤ 4`).  Written by a Claude Opus audit pass of the formalization.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature

namespace KNAll

variable {n : ℕ}

/-- The configuration in which the vertex set `S` is a clique and no pair leaves `S`. -/
def cliqueCfg (S : Set (Fin n)) : BondConfig (Fin n) := {e : Sym2 (Fin n) | ∀ x ∈ e, x ∈ S}

theorem mem_of_walk (S : Set (Fin n)) :
    ∀ {v y : Fin n}, (openGraph (cliqueCfg S)).Walk v y → v ∈ S → y ∈ S := by
  intro v y p
  induction p with
  | nil => exact fun h => h
  | @cons u v' y hadj _ ih =>
      intro _
      exact ih (((openGraph_adj _ _ _).1 hadj).1 v' (Sym2.mem_mk_right u v'))

theorem openCluster_cliqueCfg {S : Set (Fin n)} {v : Fin n} (hv : v ∈ S) :
    openCluster (cliqueCfg S) v = S := by
  ext y
  constructor
  · rintro ⟨p⟩
    exact mem_of_walk S p hv
  · intro hy
    rcases eq_or_ne v y with rfl | hne
    · exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ((openGraph_adj _ _ _).2 ⟨?_, hne⟩)
      intro z hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact hv
      · exact hy

open scoped Classical in
/-- The vertex-set function attached to a monotone cluster property. -/
def clusterF (f : Fin n → BondConfig (Fin n) → ℝ) (S : Set (Fin n)) : ℝ :=
  if h : S.Nonempty then f h.choose (cliqueCfg S) else 0

/-- **Conjecture 4 in the paper's printed vocabulary** (§5.1 p. 31, Conjecture 4 p. 32):
`f : G × {0,1}^{E(G)} → ℝ` with (1) `f(v,ω)` depends only on `C_ω(v)` and is increasing in it,
(2) `{v,w} ∈ ω → f(v,ω) = f(w,ω)`.  Conclusion: `E(f(0)·𝟙{0↔A}) ≥ min_{a∈A} E(f(a)·𝟙{0↔A})`.
Derived from `KNAll.Conjecture4` — so nothing is lost by the `F : Set V → ℝ` formulation. -/
theorem conjecture4_clusterProperty (hC4 : KNAll.Conjecture4)
    (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (hA : A.Nonempty) (o : Fin n)
    (f : Fin n → BondConfig (Fin n) → ℝ)
    (hmono : ∀ (v : Fin n) (ω ξ : BondConfig (Fin n)),
      openCluster ω v ⊆ openCluster ξ v → f v ω ≤ f v ξ)
    (hglue : ∀ (v u : Fin n) (ω : BondConfig (Fin n)), s(v, u) ∈ ω → f v ω = f u ω) :
    A.inf' hA (fun x => ∫ ω in ⋃ y ∈ A, openConn o y, f x ω ∂(prodBernoulli w)) ≤
      ∫ ω in ⋃ y ∈ A, openConn o y, f o ω ∂(prodBernoulli w) := by
  classical
  -- `f` at a clique configuration does not depend on which vertex of the clique reads it
  have hrep : ∀ (S : Set (Fin n)) (u v : Fin n), u ∈ S → v ∈ S →
      f u (cliqueCfg S) = f v (cliqueCfg S) := by
    intro S u v hu hv
    rcases eq_or_ne u v with rfl | hne
    · rfl
    · exact hglue u v _ (fun z hz => by
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hu
        · exact hv)
  -- the vertex-set function, monotone along nonempty sets
  set F : Set (Fin n) → ℝ := clusterF f with hFdef
  have hFval : ∀ (S : Set (Fin n)) (v : Fin n), v ∈ S → F S = f v (cliqueCfg S) := by
    intro S v hv
    have hS : S.Nonempty := ⟨v, hv⟩
    simp only [hFdef, clusterF, dif_pos hS]
    exact hrep S _ v hS.choose_spec hv
  have hFmono : ∀ S T : Set (Fin n), S.Nonempty → S ⊆ T → F S ≤ F T := by
    intro S T hS hST
    obtain ⟨v, hv⟩ := hS
    rw [hFval S v hv, hFval T v (hST hv)]
    exact hmono v _ _ (by
      rw [openCluster_cliqueCfg hv, openCluster_cliqueCfg (hST hv)]; exact hST)
  -- extend to all vertex sets (the development's own extension lemma)
  obtain ⟨F', hF'mono, hF'eq⟩ := KNPreFKG.monotoneOnNonempty_extension o F hFmono
  -- `F'(C_ω(x)) = f(x, ω)`
  have hkey : ∀ (ω : BondConfig (Fin n)) (x : Fin n), F' (openCluster ω x) = f x ω := by
    intro ω x
    have hx : x ∈ openCluster ω x := mem_openCluster_self ω x
    rw [hF'eq _ ⟨x, hx⟩, hFval _ x hx]
    have hcl : openCluster (cliqueCfg (openCluster ω x)) x = openCluster ω x :=
      openCluster_cliqueCfg hx
    exact le_antisymm (hmono x _ _ (by rw [hcl])) (hmono x _ _ (by rw [hcl]))
  have h := hC4 n w A hA o F' hF'mono
  simpa only [hkey] using h

/-- Requirement (1) of §5.1 splits as printed: "depends only on `C_ω(v)`" is implied by
"is increasing in `C_ω(v)`", so the two hypotheses above are the whole of the paper's definition. -/
theorem dependsOnCluster_of_mono (f : Fin n → BondConfig (Fin n) → ℝ)
    (hmono : ∀ (v : Fin n) (ω ξ : BondConfig (Fin n)),
      openCluster ω v ⊆ openCluster ξ v → f v ω ≤ f v ξ)
    (v : Fin n) (ω ξ : BondConfig (Fin n)) (h : openCluster ω v = openCluster ξ v) :
    f v ω = f v ξ :=
  le_antisymm (hmono v ω ξ h.le) (hmono v ξ ω h.ge)

/-- Unconditional form: the paper's printed Conjecture 4 is a theorem. -/
theorem conjecture4_clusterProperty_holds
    (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (hA : A.Nonempty) (o : Fin n)
    (f : Fin n → BondConfig (Fin n) → ℝ)
    (hmono : ∀ (v : Fin n) (ω ξ : BondConfig (Fin n)),
      openCluster ω v ⊆ openCluster ξ v → f v ω ≤ f v ξ)
    (hglue : ∀ (v u : Fin n) (ω : BondConfig (Fin n)), s(v, u) ∈ ω → f v ω = f u ω) :
    A.inf' hA (fun x => ∫ ω in ⋃ y ∈ A, openConn o y, f x ω ∂(prodBernoulli w)) ≤
      ∫ ω in ⋃ y ∈ A, openConn o y, f o ω ∂(prodBernoulli w) :=
  conjecture4_clusterProperty KNAll.conjecture4_holds n w A hA o f hmono hglue

/-! ## (iii) degenerate instantiations: no hidden hypotheses -/

variable (w : Sym2 (Fin n) → unitInterval)

/-- Conjecture 4 for `f(v,ω) = |C_ω(v)|` (the hypothesis of the paper's Theorem 10). -/
theorem conjecture4_size (o : Fin n) (A : Finset (Fin n)) (hA : A.Nonempty) :
    A.inf' hA (fun x => ∫ ω in ⋃ y ∈ A, openConn o y,
        ((openCluster ω x).ncard : ℝ) ∂(prodBernoulli w)) ≤
      ∫ ω in ⋃ y ∈ A, openConn o y, ((openCluster ω o).ncard : ℝ) ∂(prodBernoulli w) :=
  KNAll.conjecture4_holds n w A hA o (fun S => (S.ncard : ℝ))
    (fun _ _ h => by exact_mod_cast Set.ncard_le_ncard h (Set.toFinite _))

/-- Conjecture 4 for `f(v,ω) = 𝟙{|C_ω(v)| ≥ k}`, every `k`. -/
theorem conjecture4_sizeGE (k : ℕ) (o : Fin n) (A : Finset (Fin n)) (hA : A.Nonempty) :
    A.inf' hA (fun x => ∫ ω in ⋃ y ∈ A, openConn o y,
        (if k ≤ (openCluster ω x).ncard then (1 : ℝ) else 0) ∂(prodBernoulli w)) ≤
      ∫ ω in ⋃ y ∈ A, openConn o y,
        (if k ≤ (openCluster ω o).ncard then (1 : ℝ) else 0) ∂(prodBernoulli w) := by
  classical
  refine KNAll.conjecture4_holds n w A hA o
    (fun S => if k ≤ S.ncard then (1 : ℝ) else 0) (fun S S' h => ?_)
  have hc : S.ncard ≤ S'.ncard := Set.ncard_le_ncard h (Set.toFinite _)
  by_cases hS : k ≤ S.ncard
  · rw [if_pos hS, if_pos (hS.trans hc)]
  · rw [if_neg hS]; split_ifs <;> norm_num


end KNAll

end

#print axioms KNAll.conjecture4_clusterProperty_holds
#print axioms KNAll.conjecture4_size
#print axioms KNAll.conjecture4_sizeGE
