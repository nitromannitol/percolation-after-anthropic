import Hypergraph.ExactLongBox700
import Hypergraph.ExactLongBoxVariablePlan
import Hypergraph.ExactCorridorPlan
import Hypergraph.SiteRepresentation

/-!
# Set-source soundness for the exact long-box chain

The long-box estimate starts from a finite source set, rather than from a distinguished source
site.  This file supplies the finite wired-source interpretation needed by that estimate and then
packages the resulting aspect-88 cylinders as one ordinary exact target plan.
-/

noncomputable section

namespace KNAll.Site.ExactLongBoxHitBridge

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

open MeasureTheory Set Percolation.Literature Percolation.Literature.LatticeModels
open KNAll.Site KNAll.Site.LongBox700
open scoped Classical

variable {d : Nat} [NeZero d]

/-! ## The local-degree version of the shell scan

Only contacts can contribute inward gate sites.  Thus the degree hypothesis needed by the
fresh-barrier proof is local to the outer boundary.  This is essential after a finite source set
is wired: the auxiliary root can have large exterior degree, but it has no edge into an active
shell.
-/

namespace LocalDegree

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

theorem card_gate_le {D K : Finset V} {Delta : Nat}
    (hK : K ⊆ TargetExt.outerBoundary G (D ∪ K) D)
    (hdeg : ∀ x ∈ TargetExt.outerBoundary G (D ∪ K) D,
      (D.filter (G.Adj x)).card ≤ Delta) :
    (TargetExt.gate G D K).card ≤ Delta * K.card := by
  classical
  have hsub : TargetExt.gate G D K ⊆
      K.biUnion fun x => D.filter (G.Adj x) := by
    intro y hy
    rw [TargetExt.gate, Finset.mem_filter] at hy
    obtain ⟨hyD, x, hxK, hxy⟩ := hy
    exact Finset.mem_biUnion.2 ⟨x, hxK, Finset.mem_filter.2 ⟨hyD, hxy⟩⟩
  calc
    (TargetExt.gate G D K).card ≤
        (K.biUnion fun x => D.filter (G.Adj x)).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ K, (D.filter (G.Adj x)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ K, Delta := Finset.sum_le_sum fun x hx => hdeg x (hK hx)
    _ = Delta * K.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Per-level killing with a degree bound only on actual exterior contacts. -/
theorem real_inter_poor_diff_killed_le (w : V → unitInterval)
    (Dom D : Finset V) (o : V) (N Delta : Nat) {q : Real}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hw : ∀ y ∈ D, (w y : Real) ≤ q)
    (hdeg : ∀ x ∈ TargetExt.outerBoundary G Dom D,
      (D.filter (G.Adj x)).card ≤ Delta)
    {Z : Set (SiteConfig V)} (hZ : DeterminedBy Z (↑(Dom \ D) : Set V)) :
    (prodBernoulli w).real
        (Z ∩ (TargetExt.poor G Dom D o N \ TargetExt.killed G Dom D o N)) ≤
      (1 - (1 - q) ^ (Delta * N)) *
        (prodBernoulli w).real (Z ∩ TargetExt.poor G Dom D o N) := by
  classical
  set Ks : Finset (Finset V) :=
    (TargetExt.outerBoundary G Dom D).powerset.filter fun K => K.card < N
  set C : Finset V → Set (SiteConfig V) := fun K =>
    Z ∩ {omega | TargetExt.contacts G Dom D o omega = K}
  have hCdet : ∀ K, DeterminedBy (C K) (↑(Dom \ D) : Set V) := fun K =>
    hZ.inter (TargetExt.determinedBy_contacts_eq G Dom D o K)
  have hCm : ∀ K, MeasurableSet (C K) := fun K => (hCdet K).measurableSet_of_finset
  have hCdisj : (↑Ks : Set (Finset V)).PairwiseDisjoint C := by
    intro K _ K' _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro omega ⟨-, hK⟩ ⟨-, hK'⟩
    exact hne (hK.symm.trans hK')
  have hopen : ∀ K, DeterminedBy
      {omega : SiteConfig V | ∃ y ∈ TargetExt.gate G D K, y ∈ omega}
      (↑(TargetExt.gate G D K) : Set V) := fun K =>
    TargetExt.determinedBy_exists_mem (TargetExt.gate G D K)
  have hopenm : ∀ K, MeasurableSet
      {omega : SiteConfig V | ∃ y ∈ TargetExt.gate G D K, y ∈ omega} := fun K =>
    (hopen K).measurableSet_of_finset
  have eq1 : Z ∩ TargetExt.poor G Dom D o N = ⋃ K ∈ Ks, C K := by
    ext omega
    simp only [Set.mem_inter_iff, TargetExt.poor, Set.mem_setOf_eq, Set.mem_iUnion,
      C, Ks, Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · rintro ⟨hZomega, hlt⟩
      exact ⟨TargetExt.contacts G Dom D o omega,
        ⟨TargetExt.contacts_subset G Dom D o omega, hlt⟩, hZomega, rfl⟩
    · rintro ⟨K, ⟨-, hlt⟩, hZomega, rfl⟩
      exact ⟨hZomega, hlt⟩
  have eq2 :
      Z ∩ (TargetExt.poor G Dom D o N \ TargetExt.killed G Dom D o N) =
        ⋃ K ∈ Ks, C K ∩
          {omega | ∃ y ∈ TargetExt.gate G D K, y ∈ omega} := by
    ext omega
    simp only [Set.mem_inter_iff, Set.mem_sdiff, TargetExt.poor, TargetExt.killed,
      Set.mem_setOf_eq, Set.mem_iUnion, C, Ks, Finset.mem_filter, Finset.mem_powerset,
      exists_prop, not_and, not_forall, not_not]
    constructor
    · rintro ⟨hZomega, hlt, hex⟩
      obtain ⟨y, hy, hyomega⟩ := hex hlt
      exact ⟨TargetExt.contacts G Dom D o omega,
        ⟨TargetExt.contacts_subset G Dom D o omega, hlt⟩,
        ⟨hZomega, rfl⟩, y, hy, hyomega⟩
    · rintro ⟨K, ⟨-, hlt⟩, ⟨hZomega, rfl⟩, y, hy, hyomega⟩
      exact ⟨hZomega, hlt, fun _ => ⟨y, hy, hyomega⟩⟩
  rw [eq1, eq2,
    measureReal_biUnion_finset hCdisj (fun K _ => hCm K)
      (fun K _ => measure_ne_top _ _),
    measureReal_biUnion_finset (hCdisj.mono fun K => Set.inter_subset_left)
      (fun K _ => (hCm K).inter (hopenm K)) (fun K _ => measure_ne_top _ _),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun K hK => ?_
  have hKlt : K.card < N := (Finset.mem_filter.1 hK).2
  have hKsub : K ⊆ TargetExt.outerBoundary G Dom D :=
    Finset.mem_powerset.1 (Finset.mem_filter.1 hK).1
  have hind : (prodBernoulli w).real
      (C K ∩ {omega | ∃ y ∈ TargetExt.gate G D K, y ∈ omega}) =
      (prodBernoulli w).real (C K) *
        (prodBernoulli w).real
          {omega | ∃ y ∈ TargetExt.gate G D K, y ∈ omega} := by
    rw [Set.inter_comm, mul_comm]
    refine prodBernoulli_real_inter_of_determinedBy w (TargetExt.gate G D K)
      (hopen K) ?_ (hopenm K) (hCm K)
    refine (hCdet K).mono fun i hi hi' => ?_
    rw [Finset.mem_coe, Finset.mem_sdiff] at hi
    rw [Finset.mem_coe, TargetExt.gate, Finset.mem_filter] at hi'
    exact hi.2 hi'.1
  have hgateq : ∀ y ∈ TargetExt.gate G D K, (w y : Real) ≤ q := fun y hy =>
    hw y (Finset.mem_filter.1 hy).1
  have hcard0 : (TargetExt.gate G D K).card ≤ Delta * K.card := by
    classical
    have hsub : TargetExt.gate G D K ⊆
        K.biUnion fun x => D.filter (G.Adj x) := by
      intro y hy
      rw [TargetExt.gate, Finset.mem_filter] at hy
      obtain ⟨hyD, x, hxK, hxy⟩ := hy
      exact Finset.mem_biUnion.2 ⟨x, hxK, Finset.mem_filter.2 ⟨hyD, hxy⟩⟩
    calc
      (TargetExt.gate G D K).card ≤
          (K.biUnion fun x => D.filter (G.Adj x)).card := Finset.card_le_card hsub
      _ ≤ ∑ x ∈ K, (D.filter (G.Adj x)).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ K, Delta :=
        Finset.sum_le_sum fun x hx => hdeg x (hKsub hx)
      _ = Delta * K.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hcard : (TargetExt.gate G D K).card ≤ Delta * N :=
    hcard0.trans (Nat.mul_le_mul_left Delta hKlt.le)
  have hle := TargetExt.real_exists_mem_le w (TargetExt.gate G D K)
    hq0 hq1 hgateq hcard
  rw [hind, mul_comm]
  exact mul_le_mul_of_nonneg_right hle measureReal_nonneg

/-- The nested-shell bound with a degree hypothesis only at the contacts of each level. -/
theorem sum_real_survive_inter_poor_le_rel
    (Dom : Finset V) (o : V) (N Delta : Nat) {q : Real}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∀ (L : Nat) (D : Nat → Finset V) (w : V → unitInterval),
      (∀ i < L, D i ⊆ Dom) →
      (∀ i, i + 1 < L → D (i + 1) ⊆ D i) →
      (∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ D i →
        ∀ y ∈ D i, G.Adj x y → y ∉ D (i + 1)) →
      (∀ i < L, ∀ y ∈ D i, (w y : Real) ≤ q) →
      (∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (D i),
        ((D i).filter (G.Adj x)).card ≤ Delta) →
      ∑ i ∈ Finset.range L,
          (prodBernoulli w).real
            (TargetExt.survive G Dom D o N i ∩ TargetExt.poor G Dom (D i) o N)
        ≤ (1 - (1 - q) ^ (Delta * N)) / (1 - q) ^ (Delta * N) := by
  have hqN0 : 0 < (1 - q) ^ (Delta * N) := pow_pos (by linarith) _
  have hqN1 : (1 - q) ^ (Delta * N) ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  have hb0 : 0 ≤ (1 - (1 - q) ^ (Delta * N)) / (1 - q) ^ (Delta * N) :=
    div_nonneg (by linarith) hqN0.le
  intro L
  induction L with
  | zero =>
      intro D w _ _ _ _ _
      simpa using hb0
  | succ L ih =>
      intro D w hsub hnest hgate hw hdeg
      set qN : Real := (1 - q) ^ (Delta * N)
      set b : Real := (1 - qN) / qN
      have hbqN : b * qN = 1 - qN := div_mul_cancel₀ _ hqN0.ne'
      have h0 := real_inter_poor_diff_killed_le G w Dom (D 0) o N Delta
        hq0 hq1.le (hw 0 (Nat.succ_pos L)) (hdeg 0 (Nat.succ_pos L))
        (Z := Set.univ) (determinedBy_univ _)
      have hpoor0 := h0
      simp only [Set.univ_inter] at hpoor0
      set pi : Real := (prodBernoulli w).real (TargetExt.poor G Dom (D 0) o N)
      set f0 : Real := (prodBernoulli w).real
        (TargetExt.poor G Dom (D 0) o N \ TargetExt.killed G Dom (D 0) o N)
      have hpi0 : 0 ≤ pi := measureReal_nonneg
      have hf00 : 0 ≤ f0 := measureReal_nonneg
      have hkilled :
          (prodBernoulli w).real (TargetExt.killed G Dom (D 0) o N) = pi - f0 := by
        have h := measureReal_inter_add_sdiff (μ := prodBernoulli w)
          (s := TargetExt.poor G Dom (D 0) o N)
          (TargetExt.measurableSet_killed G Dom (D 0) o N) (measure_ne_top _ _)
        rw [Set.inter_eq_right.2
          (TargetExt.killed_subset_poor G Dom (D 0) o N)] at h
        linarith
      have hcompl :
          (prodBernoulli w).real (TargetExt.killed G Dom (D 0) o N)ᶜ =
            1 - pi + f0 := by
        rw [measureReal_compl (TargetExt.measurableSet_killed G Dom (D 0) o N),
          probReal_univ, hkilled]
        ring
      have hrest :
          ∑ i ∈ Finset.range L, (prodBernoulli w).real
              (TargetExt.survive G Dom D o N (i + 1) ∩
                TargetExt.poor G Dom (D (i + 1)) o N) ≤
            b * (prodBernoulli w).real (TargetExt.killed G Dom (D 0) o N)ᶜ := by
        rcases Nat.eq_zero_or_pos L with hL | hL
        · subst hL
          simp only [Finset.range_zero, Finset.sum_empty]
          exact mul_nonneg hb0 measureReal_nonneg
        · set R : Finset V := Dom \ D 1
          have hB : DeterminedBy (TargetExt.killed G Dom (D 0) o N)ᶜ
              (↑R : Set V) :=
            (TargetExt.determinedBy_killed_rel G o N
              (hsub 0 (Nat.succ_pos L)) (hnest 0 (by omega))
              (hgate 0 (by omega))).compl
          let patterns : Finset (Finset V) := R.powerset.filter
            (fun T : Finset V => (↑T : Set V) ∈
              (TargetExt.killed G Dom (D 0) o N)ᶜ)
          have hsumB :
              (prodBernoulli w).real (TargetExt.killed G Dom (D 0) o N)ᶜ =
                ∑ T ∈ patterns,
                  (prodBernoulli w).real
                    (localCylinder (↑R : Set V) (↑T : Set V)) := by
            dsimp only [patterns]
            convert prodBernoulli_real_eq_sum_localCylinder w R hB using 3
          have hX : ∀ i, MeasurableSet
              (TargetExt.survive G Dom (fun j => D (j + 1)) o N i ∩
                TargetExt.poor G Dom (D (i + 1)) o N) := fun i =>
            (TargetExt.measurableSet_survive G Dom (fun j => D (j + 1)) o N i).inter
              (TargetExt.measurableSet_poor G Dom (D (i + 1)) o N)
          have hterm : ∀ i ∈ Finset.range L,
              (prodBernoulli w).real
                  (TargetExt.survive G Dom D o N (i + 1) ∩
                    TargetExt.poor G Dom (D (i + 1)) o N) =
                ∑ T ∈ patterns,
                  (prodBernoulli w).real
                      (localCylinder (↑R : Set V) (↑T : Set V)) *
                    (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                      (TargetExt.survive G Dom (fun j => D (j + 1)) o N i ∩
                        TargetExt.poor G Dom (D (i + 1)) o N) := by
            intro i _
            rw [TargetExt.survive_succ, Set.inter_assoc, Set.inter_comm]
            dsimp only [patterns]
            convert prodBernoulli_real_inter_eq_sum_pinW w R (hX i) hB using 3
          have hIH : ∀ T ∈ patterns,
              ∑ i ∈ Finset.range L,
                  (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                    (TargetExt.survive G Dom (fun j => D (j + 1)) o N i ∩
                      TargetExt.poor G Dom (D (i + 1)) o N) ≤ b := by
            intro T _
            refine ih (fun j => D (j + 1))
              (pinW w (↑R : Set V) (↑T : Set V))
              (fun i hi => hsub (i + 1) (by omega))
              (fun i hi => hnest (i + 1) (by omega))
              (fun i hi => hgate (i + 1) (by omega)) ?_ ?_
            · intro i hi y hy
              have hyD1 : y ∈ D 1 :=
                TargetExt.subset_of_le_of_lt hnest 1 (i + 1) (by omega) (by omega) hy
              have hyR : y ∉ (↑R : Set V) := by
                rw [Finset.mem_coe, Finset.mem_sdiff]
                exact fun h => h.2 hyD1
              rw [pinW_apply_of_not_mem w _ hyR]
              exact hw (i + 1) (by omega) y hy
            · intro i hi x hx
              exact hdeg (i + 1) (by omega) x hx
          calc
            ∑ i ∈ Finset.range L, (prodBernoulli w).real
                  (TargetExt.survive G Dom D o N (i + 1) ∩
                    TargetExt.poor G Dom (D (i + 1)) o N) =
                ∑ i ∈ Finset.range L, ∑ T ∈ patterns,
                  (prodBernoulli w).real
                      (localCylinder (↑R : Set V) (↑T : Set V)) *
                    (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                      (TargetExt.survive G Dom (fun j => D (j + 1)) o N i ∩
                        TargetExt.poor G Dom (D (i + 1)) o N) :=
              Finset.sum_congr rfl hterm
            _ = ∑ T ∈ patterns, ∑ i ∈ Finset.range L,
                  (prodBernoulli w).real
                      (localCylinder (↑R : Set V) (↑T : Set V)) *
                    (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                      (TargetExt.survive G Dom (fun j => D (j + 1)) o N i ∩
                        TargetExt.poor G Dom (D (i + 1)) o N) := Finset.sum_comm
            _ = ∑ T ∈ patterns,
                  (prodBernoulli w).real
                      (localCylinder (↑R : Set V) (↑T : Set V)) *
                    ∑ i ∈ Finset.range L,
                      (prodBernoulli (pinW w (↑R : Set V) (↑T : Set V))).real
                        (TargetExt.survive G Dom (fun j => D (j + 1)) o N i ∩
                          TargetExt.poor G Dom (D (i + 1)) o N) := by
              refine Finset.sum_congr rfl fun T _ => ?_
              rw [Finset.mul_sum]
            _ ≤ ∑ T ∈ patterns,
                  (prodBernoulli w).real
                      (localCylinder (↑R : Set V) (↑T : Set V)) * b :=
              Finset.sum_le_sum fun T hT =>
                mul_le_mul_of_nonneg_left (hIH T hT) measureReal_nonneg
            _ = b * (prodBernoulli w).real
                  (TargetExt.killed G Dom (D 0) o N)ᶜ := by
              rw [← Finset.sum_mul, hsumB, mul_comm]
      rw [Finset.sum_range_succ', TargetExt.survive_zero, Set.inter_comm,
        ← Set.sdiff_eq, ← show f0 = _ from rfl, hcompl] at *
      have h1 : b * (1 - pi + f0) ≤ b * (1 - pi + (1 - qN) * pi) :=
        mul_le_mul_of_nonneg_left (by linarith) hb0
      have h2 : b * (1 - pi + (1 - qN) * pi) = b - (1 - qN) * pi := by
        linear_combination (-pi) * hbqN
      linarith

/-- A deterministic rich shell follows from a source estimate under local boundary degrees. -/
theorem exists_level_real_poor_compl_gt_rel
    (Dom : Finset V) (o : V) (N Delta : Nat) {q : Real}
    (hq0 : 0 ≤ q) (hq1 : q < 1) {L : Nat} (hL : 0 < L)
    (D : Nat → Finset V) (w : V → unitInterval)
    (hsub : ∀ i < L, D i ⊆ Dom)
    (hnest : ∀ i, i + 1 < L → D (i + 1) ⊆ D i)
    (hgateRel : ∀ i, i + 1 < L → ∀ x ∈ Dom, x ∉ D i →
      ∀ y ∈ D i, G.Adj x y → y ∉ D (i + 1))
    (hw : ∀ i < L, ∀ y ∈ D i, (w y : Real) ≤ q)
    (hdeg : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom (D i),
      ((D i).filter (G.Adj x)).card ≤ Delta)
    (ho : ∀ i < L, o ∉ D i) {B : Set V}
    (hB : ∀ i < L, B ⊆ ↑(D i)) {delta : Real}
    (hLdelta : 1 ≤ (L : Real) * delta * (1 - q) ^ (Delta * N))
    (hsrc : 1 - delta <
      (prodBernoulli w).real (connWithinSet G (↑Dom : Set V) o B)) :
    ∃ i < L, 1 - 2 * delta <
      (prodBernoulli w).real (TargetExt.poor G Dom (D i) o N)ᶜ := by
  have hqN0 : 0 < (1 - q) ^ (Delta * N) := pow_pos (by linarith) _
  have hLpos : (0 : Real) < L := Nat.cast_pos.2 hL
  have hsum := sum_real_survive_inter_poor_le_rel G Dom o N Delta hq0 hq1
    L D w hsub hnest hgateRel hw hdeg
  have hA : ∀ j < L,
      connWithinSet G (↑Dom : Set V) o B ⊆
        (TargetExt.killed G Dom (D j) o N)ᶜ := fun j hj =>
    Set.subset_compl_comm.1
      (TargetExt.killed_subset_compl_connWithinSet G Dom (D j) (ho j hj) N (hB j hj))
  have hle :
      ∑ i ∈ Finset.range L, (prodBernoulli w).real
          (connWithinSet G (↑Dom : Set V) o B ∩ TargetExt.poor G Dom (D i) o N) ≤
        ∑ i ∈ Finset.range L, (prodBernoulli w).real
          (TargetExt.survive G Dom D o N i ∩ TargetExt.poor G Dom (D i) o N) :=
    Finset.sum_le_sum fun i hi =>
      measureReal_mono (Set.inter_subset_inter_left _
        (TargetExt.subset_survive_of_forall G hA (Finset.mem_range.1 hi)))
        (measure_ne_top _ _)
  have hbound :
      (1 - (1 - q) ^ (Delta * N)) / (1 - q) ^ (Delta * N) ≤
        ∑ _i ∈ Finset.range L,
          1 / ((L : Real) * (1 - q) ^ (Delta * N)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcancel : (L : Real) *
        (1 / ((L : Real) * (1 - q) ^ (Delta * N))) =
          1 / (1 - q) ^ (Delta * N) := by field_simp
    rw [hcancel]
    exact (div_le_div_iff_of_pos_right hqN0).2 (by linarith)
  obtain ⟨i, hi, hile⟩ := Finset.exists_le_of_sum_le
    ⟨0, Finset.mem_range.2 hL⟩ (hle.trans (hsum.trans hbound))
  refine ⟨i, Finset.mem_range.1 hi, ?_⟩
  have hdelta' : 1 / ((L : Real) * (1 - q) ^ (Delta * N)) ≤ delta := by
    rw [div_le_iff₀ (mul_pos hLpos hqN0)]
    linarith
  have hsplit := measureReal_inter_add_sdiff (μ := prodBernoulli w)
    (s := connWithinSet G (↑Dom : Set V) o B)
    (TargetExt.measurableSet_poor G Dom (D i) o N) (measure_ne_top _ _)
  have hmono : (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set V) o B \ TargetExt.poor G Dom (D i) o N) ≤
      (prodBernoulli w).real (TargetExt.poor G Dom (D i) o N)ᶜ :=
    measureReal_mono (fun omega homega => homega.2) (measure_ne_top _ _)
  linarith

end LocalDegree

/-! ## Graph agreement on the active region -/

namespace ActiveGraph

/-- A graph has the ordinary lattice edges whenever the first endpoint is active.  Symmetry then
gives the same equivalence whenever either endpoint is active. -/
def AgreesOn (G : SimpleGraph (Site d)) (D : Finset (Site d)) : Prop :=
  ∀ x ∈ D, ∀ y, G.Adj x y ↔ (zdGraph d).Adj x y

theorem adj_iff_of_right {G : SimpleGraph (Site d)} {D : Finset (Site d)}
    (hG : AgreesOn G D) {x y : Site d} (hy : y ∈ D) :
    G.Adj x y ↔ (zdGraph d).Adj x y := by
  rw [G.adj_comm, (zdGraph d).adj_comm]
  exact hG y hy x

theorem outerBoundary_eq {G : SimpleGraph (Site d)} {D O Dom : Finset (Site d)}
    (hG : AgreesOn G D) (hOD : O ⊆ D) :
    TargetExt.outerBoundary G Dom O =
      TargetExt.outerBoundary (zdGraph d) Dom O := by
  classical
  ext x
  simp only [TargetExt.outerBoundary, Finset.mem_filter, Finset.mem_sdiff]
  apply and_congr_right
  intro _
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  exact adj_iff_of_right hG (hOD hy)

theorem connWithin_eq {G : SimpleGraph (Site d)} {D : Finset (Site d)}
    (hG : AgreesOn G D) {S : Set (Site d)} (hSD : S ⊆ (↑D : Set (Site d)))
    (x y : Site d) : connWithin G S x y = connWithin (zdGraph d) S x y := by
  ext omega
  simp only [connWithin, Set.mem_setOf_eq]
  apply and_congr_right
  intro _
  constructor
  · intro h
    refine h.map ⟨id, ?_⟩
    intro a b hab
    rw [openSiteGraph_adj_iff'] at hab ⊢
    have haD : a ∈ D := Finset.mem_coe.1 (hSD hab.2.1.2)
    exact ⟨(hG a haD b).1 hab.1, hab.2⟩
  · intro h
    refine h.map ⟨id, ?_⟩
    intro a b hab
    rw [openSiteGraph_adj_iff'] at hab ⊢
    have haD : a ∈ D := Finset.mem_coe.1 (hSD hab.2.1.2)
    exact ⟨(hG a haD b).2 hab.1, hab.2⟩

theorem connWithinSet_eq {G : SimpleGraph (Site d)} {D : Finset (Site d)}
    (hG : AgreesOn G D) {S : Set (Site d)} (hSD : S ⊆ (↑D : Set (Site d)))
    (x : Site d) (T : Set (Site d)) :
    connWithinSet G S x T = connWithinSet (zdGraph d) S x T := by
  simp only [connWithinSet]
  congr 1
  funext y
  congr 1
  funext _hy
  exact connWithin_eq hG hSD x y

/-- It is enough that every possible edge of the confining set has an active endpoint. -/
theorem connWithin_eq_of_edge_cover {G : SimpleGraph (Site d)} {D : Finset (Site d)}
    (hG : AgreesOn G D) {S : Set (Site d)}
    (hcover : ∀ {a b}, a ∈ S → b ∈ S → a ≠ b → a ∈ D ∨ b ∈ D)
    (x y : Site d) : connWithin G S x y = connWithin (zdGraph d) S x y := by
  ext omega
  simp only [connWithin, Set.mem_setOf_eq]
  apply and_congr_right
  intro _
  constructor
  · intro h
    refine h.map ⟨id, ?_⟩
    intro a b hab
    rw [openSiteGraph_adj_iff'] at hab ⊢
    rcases hcover hab.2.1.2 hab.2.2.2 hab.1.ne with ha | hb
    · exact ⟨(hG a ha b).1 hab.1, hab.2⟩
    · exact ⟨(adj_iff_of_right hG hb).1 hab.1, hab.2⟩
  · intro h
    refine h.map ⟨id, ?_⟩
    intro a b hab
    rw [openSiteGraph_adj_iff'] at hab ⊢
    rcases hcover hab.2.1.2 hab.2.2.2 hab.1.ne with ha | hb
    · exact ⟨(hG a ha b).2 hab.1, hab.2⟩
    · exact ⟨(adj_iff_of_right hG hb).2 hab.1, hab.2⟩

/-- Concrete one-level target extension remains valid after changing edges wholly outside the
active set. -/
theorem target_gt_at_level
    (G : SimpleGraph (Site d)) (w : Site d → unitInterval)
    (m k N : Nat) (hm : 1 ≤ m) (z : Site d) (rho : Fin d → Int)
    (hrho : ∀ a, ReinforcedShell.thickness m ≤ rho a)
    {Dom D : Finset (Site d)} (hOD : Corridor.rbox z rho ⊆ D) (hDDom : D ⊆ Dom)
    (hG : AgreesOn G D)
    (o : Site d) (hoDom : o ∈ Dom) (hoD : o ∉ D) (hwo : w o = 1)
    (T : Set (Site d)) (qI : unitInterval)
    (hwO : ∀ y ∈ Corridor.rbox z rho, w y = qI)
    (hpack : k * (CorrMove.cube (0 : Site d) (8 * (m : Int))).card ≤ N)
    (H : Site d → Set (SiteConfig (Site d))) {ε δ δc η : Real}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ = ε ^ 2 / 64)
    (hδc : δc = ε / 4) (hη0 : 0 ≤ η)
    (hbudget : (k : Real) *
      ((qI : Real) ^ ReinforcedShell.seedSize d m * η / δc) ≤ δ)
    (hseed : (1 - (qI : Real) ^ ReinforcedShell.seedSize d m) ^ k ≤ δ)
    (hHup : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox z rho),
      IsUpperSet (H x))
    (hHm : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox z rho),
      MeasurableSet (H x))
    (hforce : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox z rho),
      ReinforcedTarget.openWindow (ReinforcedLevel.J m z rho x) ∩ H x ⊆
        TargetExt.toTarget (zdGraph d) D T (ReinforcedLevel.relay m z rho x))
    (hhit : ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom (Corridor.rbox z rho),
      (prodBernoulli w).real (H x)ᶜ ≤ η)
    (hrich : 1 - 2 * δ <
      (prodBernoulli w).real
        (TargetExt.poor G Dom (Corridor.rbox z rho) o N)ᶜ) :
    1 - ε < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set (Site d)) o T) := by
  let O : Finset (Site d) := Corridor.rbox z rho
  let Int : Finset (Site d) := ReinforcedShell.innerBox m z rho
  let sel : Finset (Site d) → Finset (Site d) := ReinforcedLevel.selected m k z rho
  let win : Site d → Finset (Site d) := ReinforcedLevel.J m z rho
  let v : Site d → Site d := ReinforcedLevel.relay m z rho
  have hboundary : TargetExt.outerBoundary G Dom O =
      TargetExt.outerBoundary (zdGraph d) Dom O := outerBoundary_eq hG hOD
  have hF := ReinforcedLevel.facts m k hm z rho hrho Dom
  have hselLower : ∀ K ⊆ TargetExt.outerBoundary G Dom O,
      N ≤ K.card → k ≤ (sel K).card := by
    intro K hK hNK
    have heq := ReinforcedLevel.card_selected_eq_of_boundary m k N z rho Dom K
      (by simpa only [hboundary] using hK) hpack hNK
    simpa only [sel] using heq.ge
  have hseed0 := TargetExt.real_poorCompl_diff_seeds_le
    G w Dom O o N k (ReinforcedShell.seedSize d m) qI.2.1 qI.2.2 sel win
      (by simpa only [sel] using hF.sel_subset) hselLower
      (by simpa only [sel, win] using hF.sel_disjoint)
      (by
        intro x hx
        have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom O := hboundary ▸ hx
        exact (hF.window_subset x hx').trans hF.collar_subset)
      (by
        intro x hx
        have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom O := hboundary ▸ hx
        rw [show (win x).card = ReinforcedShell.seedSize d m by
          simpa only [win] using hF.window_card x hx'])
      (by
        intro x hx y hy
        have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom O := hboundary ▸ hx
        have hyO : y ∈ O := hF.collar_subset (hF.window_subset x hx' hy)
        rw [hwO y hyO])
  have hnoopen : (prodBernoulli w).real
      ((TargetExt.poor G Dom O o N)ᶜ \
        ReinforcedTarget.selectedOpen G Dom O o sel win) ≤ δ := by
    have hseed0' : (prodBernoulli w).real
        ((TargetExt.poor G Dom O o N)ᶜ \
          ReinforcedTarget.selectedOpen G Dom O o sel win) ≤
        (1 - (qI : Real) ^ ReinforcedShell.seedSize d m) ^ k := by
      simpa only [ReinforcedTarget.selectedOpen, TargetExt.selectedAt,
        ReinforcedTarget.openWindow, TargetExt.seedOpen] using hseed0
    exact hseed0'.trans hseed
  have hopen : ∀ x ∈ TargetExt.outerBoundary G Dom O,
      (prodBernoulli w).real (ReinforcedTarget.openWindow (win x)) ≤
        (qI : Real) ^ ReinforcedShell.seedSize d m := by
    intro x hx
    have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom O := hboundary ▸ hx
    have hcard : (win x).card = ReinforcedShell.seedSize d m := by
      simpa only [win] using hF.window_card x hx'
    have hwinO : win x ⊆ O := (hF.window_subset x hx').trans hF.collar_subset
    change (prodBernoulli w).real {omega | (↑(win x) : Set (Site d)) ⊆ omega} ≤ _
    rw [prodBernoulli_real_subset]
    calc
      ∏ y ∈ win x, (w y : Real) = ∏ _y ∈ win x, (qI : Real) := by
        apply Finset.prod_congr rfl
        intro y hy
        rw [hwO y (hwinO hy)]
      _ ≤ (qI : Real) ^ ReinforcedShell.seedSize d m := by
        rw [Finset.prod_const, hcard]
  apply ReinforcedTarget.oneLevel_target_gt_of_hits G w
    (ReinforcedLevel.innerBox_subset_shell m z rho) hOD hDDom
    o hoDom hoD hwo T N k sel win v H hε0 hε1 hδ hδc
      (pow_nonneg (unitInterval.nonneg qI) _) hη0 hbudget
      (by simpa only [sel] using hF.sel_subset)
      (by simpa only [sel] using hF.sel_card_le)
  · intro x hx
    have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom O := hboundary ▸ hx
    simpa only [O, Int, win, ReinforcedShell.collar] using hF.window_subset x hx'
  · intro x hx
    have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom O := hboundary ▸ hx
    simpa only [O, Int, v, ReinforcedShell.collar] using hF.relay_mem x hx'
  · intro x hx omega hxopen hopen'
    have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom O := hboundary ▸ hx
    have hb := hF.bridge x hx' omega hxopen hopen'
    rw [connWithin_eq_of_edge_cover hG]
    · exact hb
    · intro a b ha hb hab
      simp only [Set.mem_insert_iff, Finset.mem_coe] at ha hb
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact False.elim (hab (ha.trans hb.symm))
        · exact Or.inr (hOD (hF.collar_subset (hF.window_subset x hx' hb)))
      · exact Or.inl (hOD (hF.collar_subset (hF.window_subset x hx' ha)))
  · intro x hx
    exact hHup x (hboundary ▸ hx)
  · intro x hx
    exact hHm x (hboundary ▸ hx)
  · intro x hx
    have hx' : x ∈ TargetExt.outerBoundary (zdGraph d) Dom O := hboundary ▸ hx
    have heq := connWithinSet_eq hG
      (Finset.coe_subset.2 (fun _ h => h : D ⊆ D)) (v x) T
    change ReinforcedTarget.openWindow (win x) ∩ H x ⊆
      connWithinSet G (↑D : Set (Site d)) (v x) T
    rw [heq]
    exact hforce x hx'
  · exact hopen
  · intro x hx
    exact hhit x (hboundary ▸ hx)
  · exact hrich
  · exact hnoopen

/-- The full finite shell scan for a graph which differs from the lattice only wholly outside the
active region.  Its degree premise is checked only at genuine shell contacts. -/
theorem target_gt_from_scan
    (G : SimpleGraph (Site d)) (w : Site d → unitInterval)
    (m k N L : Nat) (hm : 1 ≤ m) (hL : 0 < L)
    (z : Site d) (rho0 : Fin d → Int) (hrho0 : ∀ a, 0 ≤ rho0 a)
    {Dom D : Finset (Site d)}
    (houter : ReinforcedLevel.shell z rho0 m L 0 ⊆ D) (hDDom : D ⊆ Dom)
    (hG : AgreesOn G D)
    (o : Site d) (hoDom : o ∈ Dom) (hoD : o ∉ D) (hwo : w o = 1)
    (B T : Set (Site d))
    (hB : ∀ i < L, B ⊆ ↑(ReinforcedLevel.shell z rho0 m L i))
    (qI : unitInterval) (hq1 : (qI : Real) < 1)
    (hw : ∀ i < L, ∀ y ∈ ReinforcedLevel.shell z rho0 m L i, w y = qI)
    (H : Nat → Site d → Set (SiteConfig (Site d))) {ε δ δc η : Real}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ : δ = ε ^ 2 / 64)
    (hδc : δc = ε / 4) (hη0 : 0 ≤ η)
    (hbarrier : 1 ≤ (L : Real) * δ * (1 - (qI : Real)) ^ ((2 * d) * N))
    (hpack : k * (CorrMove.cube (0 : Site d) (8 * (m : Int))).card ≤ N)
    (hbudget : (k : Real) *
      ((qI : Real) ^ ReinforcedShell.seedSize d m * η / δc) ≤ δ)
    (hseed : (1 - (qI : Real) ^ ReinforcedShell.seedSize d m) ^ k ≤ δ)
    (hHup : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (ReinforcedLevel.shell z rho0 m L i), IsUpperSet (H i x))
    (hHm : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (ReinforcedLevel.shell z rho0 m L i), MeasurableSet (H i x))
    (hforce : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (ReinforcedLevel.shell z rho0 m L i),
      ReinforcedTarget.openWindow
          (ReinforcedLevel.J m z (ReinforcedLevel.radius rho0 m L i) x) ∩ H i x ⊆
        TargetExt.toTarget (zdGraph d) D T
          (ReinforcedLevel.relay m z (ReinforcedLevel.radius rho0 m L i) x))
    (hhit : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (ReinforcedLevel.shell z rho0 m L i),
      (prodBernoulli w).real (H i x)ᶜ ≤ η)
    (hsrc : 1 - δ < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set (Site d)) o B)) :
    1 - ε < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set (Site d)) o T) := by
  classical
  have hsub : ∀ i < L, ReinforcedLevel.shell z rho0 m L i ⊆ Dom := by
    intro i hi
    exact (ReinforcedLevel.shell_subset_active z rho0 m L i houter).trans hDDom
  have hnest : ∀ i, i + 1 < L →
      ReinforcedLevel.shell z rho0 m L (i + 1) ⊆
        ReinforcedLevel.shell z rho0 m L i := by
    intro i _
    exact ReinforcedLevel.shell_succ_subset z rho0 m L i
  have hgate : ∀ i, i + 1 < L → ∀ x ∈ Dom,
      x ∉ ReinforcedLevel.shell z rho0 m L i →
      ∀ y ∈ ReinforcedLevel.shell z rho0 m L i, G.Adj x y →
        y ∉ ReinforcedLevel.shell z rho0 m L (i + 1) := by
    intro i hi x hxDom hx y hy hadj
    have hyD := ReinforcedLevel.shell_subset_active z rho0 m L i houter hy
    exact ReinforcedLevel.scan_gate z rho0 m L i hi hxDom hx hy
      ((adj_iff_of_right hG hyD).1 hadj)
  have hwle : ∀ i < L, ∀ y ∈ ReinforcedLevel.shell z rho0 m L i,
      (w y : Real) ≤ qI := by
    intro i hi y hy
    rw [hw i hi y hy]
  have hdeg : ∀ i < L, ∀ x ∈ TargetExt.outerBoundary G Dom
      (ReinforcedLevel.shell z rho0 m L i),
      ((ReinforcedLevel.shell z rho0 m L i).filter (G.Adj x)).card ≤ 2 * d := by
    intro i hi x hx
    have heq : (ReinforcedLevel.shell z rho0 m L i).filter (G.Adj x) =
        (ReinforcedLevel.shell z rho0 m L i).filter ((zdGraph d).Adj x) := by
      apply Finset.filter_congr
      intro y hy
      exact adj_iff_of_right hG
        (ReinforcedLevel.shell_subset_active z rho0 m L i houter hy)
    rw [heq]
    exact ReinforcedLevel.card_filter_adj_le _ _
  have ho : ∀ i < L, o ∉ ReinforcedLevel.shell z rho0 m L i := by
    intro i hi hoi
    exact hoD (ReinforcedLevel.shell_subset_active z rho0 m L i houter hoi)
  obtain ⟨i, hi, hrich⟩ := LocalDegree.exists_level_real_poor_compl_gt_rel
    G Dom o N (2 * d) qI.2.1 hq1 hL
      (fun j => ReinforcedLevel.shell z rho0 m L j) w hsub hnest hgate hwle hdeg
      ho hB hbarrier hsrc
  have hrhoi : ∀ a, ReinforcedShell.thickness m ≤
      ReinforcedLevel.radius rho0 m L i a := by
    intro a
    have hbase := hrho0 a
    have hoff := ReinforcedLevel.thickness_le_offset m L i hi
    simp only [ReinforcedLevel.radius]
    omega
  exact target_gt_at_level G w m k N hm z
    (ReinforcedLevel.radius rho0 m L i) hrhoi
    (ReinforcedLevel.shell_subset_active z rho0 m L i houter) hDDom hG
    o hoDom hoD hwo T qI (hw i hi) hpack (H i)
    hε0 hε1 hδ hδc hη0 hbudget hseed
    (hHup i hi) (hHm i hi) (hforce i hi) (hhit i hi) hrich

end ActiveGraph

/-! ## Exact-plan soundness on an actively lattice graph -/

namespace ProductSound

private abbrev envCentre (C : ExactTargetPlan.Plan d) : Site d :=
  IntBoxCenteredEnvelope.centre C.sourceBox

private abbrev envRho (C : ExactTargetPlan.Plan d) : Fin d → Int :=
  IntBoxCenteredEnvelope.rho C.sourceBox

private abbrev levelRho (C : ExactTargetPlan.Plan d) (i : Nat) : Fin d → Int :=
  ReinforcedLevel.radius (envRho C) C.m C.L i

private abbrev levelRelay (C : ExactTargetPlan.Plan d) (i : Nat) (x : Site d) : Site d :=
  ReinforcedLevel.relay C.m (envCentre C) (levelRho C i) x

private theorem cube_zero_eq_siteBox (n : Nat) :
    CorrMove.cube (0 : Site d) (n : Int) = siteBox d n := by
  ext x
  rw [CorrMove.mem_cube, mem_siteBox]
  constructor
  · intro h a
    have ha := h a
    rw [abs_le] at ha
    simpa using ha
  · intro h a
    have ha := h a
    rw [abs_le]
    simpa using ha

private theorem budget_of_le_inv {a delta deltaC eta : Real}
    (hdelta : 0 < delta) (hdeltaC : 0 < deltaC) (ha : a ≤ delta⁻¹)
    (heta : eta = delta ^ 2 * deltaC) : a * (eta / deltaC) ≤ delta := by
  have hratio : eta / deltaC = delta ^ 2 := by
    rw [heta]
    field_simp
  rw [hratio]
  calc
    a * delta ^ 2 ≤ delta⁻¹ * delta ^ 2 :=
      mul_le_mul_of_nonneg_right ha (sq_nonneg delta)
    _ = delta := by field_simp

private theorem relay_mem_sourcePlus (C : ExactTargetPlan.Plan d) (hC : C.WellFormed)
    {Dom : Finset (Site d)} {i : Nat} (hi : i < C.L) {x : Site d}
    (hx : x ∈ TargetExt.outerBoundary (zdGraph d) Dom
      (ReinforcedLevel.shell (envCentre C) (envRho C) C.m C.L i)) :
    levelRelay C i x ∈ C.sourcePlus := by
  have hsourceOrd : C.sourceBox.Ordered := hC.1.2.2.1
  have hR : 2 * C.m + C.L + 2 ≤ C.radius := hC.2.2.1.1
  have hrho : ∀ a, ReinforcedShell.thickness C.m ≤ levelRho C i a := by
    intro a
    have hbase := IntBoxCenteredEnvelope.rho_nonneg C.sourceBox a
    have hoff := ReinforcedLevel.thickness_le_offset C.m C.L i hi
    change ReinforcedShell.thickness C.m ≤
      envRho C a + ReinforcedLevel.offset C.m C.L i
    exact hoff.trans (by linarith)
  have hcollar : levelRelay C i x ∈
      ReinforcedShell.collar C.m (envCentre C) (levelRho C i) :=
    ReinforcedLevel.relay_mem_collar_of_boundary C.m (envCentre C)
      (levelRho C i) hrho Dom hx
  have hshell : levelRelay C i x ∈
      ReinforcedLevel.shell (envCentre C) (envRho C) C.m C.L i :=
    ReinforcedLevel.collar_subset_shell C.m (envCentre C) (levelRho C i) hcollar
  exact IntBoxCenteredEnvelope.shell_subset_inflate hsourceOrd
    C.m C.L C.radius i hi hR hshell

/-- Exact target-plan soundness for a graph whose edges touching the active box are precisely the
lattice edges.  In particular this applies to a source-wired graph when the wired source is
disjoint from the active box. -/
theorem soundProduct
    (C : ExactTargetPlan.Plan d) (hC : C.WellFormed)
    {q : unitInterval} (hvalid : C.ValidAt q)
    (G : SimpleGraph (Site d)) (w : Site d → unitInterval) {Dom : Finset (Site d)}
    (hactiveDom : C.active ⊆ Dom) (hG : ActiveGraph.AgreesOn G C.active)
    (hwactive : ∀ x ∈ C.active, w x = q)
    (o : Site d) (ho : o ∈ Dom \ C.active) (hwo : w o = 1)
    (hsrc : 1 - C.delta < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set (Site d)) o (↑C.source : Set (Site d)))) :
    1 - C.epsilon < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set (Site d)) o (↑C.target : Set (Site d))) := by
  have h1 := hC.1
  have h2 := hC.2.1
  have h3 := hC.2.2.1
  have h4 := hC.2.2.2.1
  have h5 := hC.2.2.2.2.1
  have h6 := hC.2.2.2.2.2
  have hm : 1 ≤ C.m := h2.2.2.1
  have hL : 0 < C.L := h2.2.2.2.2.2
  have hq1 : (q : Real) < 1 := lt_of_le_of_lt hvalid.2.1 h1.2.1
  have hdeltaPos : 0 < C.delta := by
    unfold ExactTargetPlan.Plan.delta
    exact div_pos (sq_pos_of_pos h2.1) (by norm_num)
  have hdeltaCPos : 0 < C.deltaC := by
    unfold ExactTargetPlan.Plan.deltaC
    exact div_pos h2.1 (by norm_num)
  have heta0 : 0 ≤ C.eta := by
    unfold ExactTargetPlan.Plan.eta
    positivity
  have houter : ReinforcedLevel.shell (envCentre C) (envRho C) C.m C.L 0 ⊆ C.active := by
    have hs := IntBoxCenteredEnvelope.shell_subset_inflate h1.2.2.1
      C.m C.L C.radius 0 hL h3.1
    exact hs.trans h1.2.2.2.2.2.1
  have hB : ∀ i < C.L, (↑C.source : Set (Site d)) ⊆
      ↑(ReinforcedLevel.shell (envCentre C) (envRho C) C.m C.L i) := by
    intro i hi x hx
    exact Finset.mem_coe.2
      (IntBoxCenteredEnvelope.sites_subset_shell h1.2.2.1 C.m C.L i hi
        (Finset.mem_coe.1 hx))
  have hwShell : ∀ i < C.L, ∀ y ∈
      ReinforcedLevel.shell (envCentre C) (envRho C) C.m C.L i, w y = q := by
    intro i hi y hy
    exact hwactive y
      (ReinforcedLevel.shell_subset_active (envCentre C) (envRho C) C.m C.L i houter hy)
  have hpack : C.k *
      (CorrMove.cube (0 : Site d) (8 * (C.m : Int))).card ≤ C.N := by
    rw [show 8 * (C.m : Int) = ((8 * C.m : Nat) : Int) by norm_num,
      cube_zero_eq_siteBox]
    exact h3.2.1
  have hbarrierProb : C.barrierLower <
      (1 - (q : Real)) ^ ((2 * d) * C.N) := by
    have hv := hvalid.barrierLeaf_holds
    unfold ProbabilityBound.HoldsAt at hv
    rw [h6.2.2.2.1, FreshLeafTransport.plan_barrierLeaf_prob_eq q hC] at hv
    simpa only [Nat.mul_assoc] using hv
  have hcoefpos : 0 < (C.L : Real) * C.delta :=
    mul_pos (by positivity) hdeltaPos
  have hbarrier : 1 ≤ (C.L : Real) * C.delta *
      (1 - (q : Real)) ^ ((2 * d) * C.N) := by
    have hmul := mul_lt_mul_of_pos_left hbarrierProb hcoefpos
    exact le_of_lt (lt_trans h6.2.2.2.2.2.2 hmul)
  have hseedSize : ReinforcedShell.seedSize d C.m = C.seedCard := rfl
  have hseed : (1 - (q : Real) ^ ReinforcedShell.seedSize d C.m) ^ C.k ≤ C.delta := by
    have hv := hvalid.seedLeaf_holds
    unfold ProbabilityBound.HoldsAt at hv
    rw [h5.2.2.2.2, FreshLeafTransport.plan_seedLeaf_prob_eq q hC] at hv
    rw [hseedSize]
    linarith
  have hpow : (q : Real) ^ ReinforcedShell.seedSize d C.m ≤
      (C.p0 : Real) ^ C.seedCard := by
    rw [hseedSize]
    exact pow_le_pow_left₀ q.2.1 hvalid.2.1 C.seedCard
  have hkpow : (C.k : Real) * (q : Real) ^ ReinforcedShell.seedSize d C.m ≤
      C.delta⁻¹ :=
    (mul_le_mul_of_nonneg_left hpow (by positivity)).trans h3.2.2
  have hbudget : (C.k : Real) *
      ((q : Real) ^ ReinforcedShell.seedSize d C.m * C.eta / C.deltaC) ≤ C.delta := by
    calc
      (C.k : Real) *
          ((q : Real) ^ ReinforcedShell.seedSize d C.m * C.eta / C.deltaC) =
          ((C.k : Real) * (q : Real) ^ ReinforcedShell.seedSize d C.m) *
            (C.eta / C.deltaC) := by ring
      _ ≤ C.delta := budget_of_le_inv hdeltaPos hdeltaCPos hkpow rfl
  apply ActiveGraph.target_gt_from_scan G w C.m C.k C.N C.L hm hL
    (envCentre C) (envRho C) (IntBoxCenteredEnvelope.rho_nonneg C.sourceBox)
    houter hactiveDom hG o (Finset.mem_sdiff.1 ho).1 (Finset.mem_sdiff.1 ho).2 hwo
    (↑C.source : Set (Site d)) (↑C.target : Set (Site d)) hB q hq1 hwShell
    (fun i => ExactTargetPlan.Plan.scanHit C i)
    h2.1 h2.2.1 rfl rfl heta0 hbarrier hpack hbudget hseed
  · intro i hi x hx
    have hrelay := relay_mem_sourcePlus C hC hi hx
    simp only [ExactTargetPlan.Plan.scanHit, dif_pos hrelay]
    exact ReinforcedHit.isUpperSet_hitEvent _ _ _
  · intro i hi x hx
    have hrelay := relay_mem_sourcePlus C hC hi hx
    simp only [ExactTargetPlan.Plan.scanHit, dif_pos hrelay]
    exact ReinforcedHit.measurableSet_hitEvent _ _ _
  · intro i hi x hx
    have hrelay := relay_mem_sourcePlus C hC hi hx
    let v : C.sourcePlus := ⟨levelRelay C i x, hrelay⟩
    rcases h4 v with ⟨_, _, hregion, hface, _, _, _, _⟩
    have hrho : ∀ a, ReinforcedShell.thickness C.m ≤ levelRho C i a := by
      intro a
      have hbase := IntBoxCenteredEnvelope.rho_nonneg C.sourceBox a
      have hoff := ReinforcedLevel.thickness_le_offset C.m C.L i hi
      change ReinforcedShell.thickness C.m ≤
        envRho C a + ReinforcedLevel.offset C.m C.L i
      exact hoff.trans (by linarith)
    have hwin : ReinforcedShell.window C.m (envCentre C) (levelRho C i) x ⊆ C.active :=
      (ReinforcedLevel.window_subset_collar_of_boundary C.m (envCentre C)
          (levelRho C i) hrho Dom hx).trans
        (ReinforcedLevel.collar_subset_active (envCentre C) (envRho C) C.m C.L i houter)
    simp only [ExactTargetPlan.Plan.scanHit, dif_pos hrelay]
    apply ReinforcedHit.openWindow_inter_hitEvent_subset_toTarget C.m (envCentre C)
      (levelRho C i) (ReinforcedLevel.isContact_of_mem_outerBoundary_rbox Dom
        (envCentre C) (levelRho C i) hx)
      (C.selectedRegion v) (C.selectedFace v) C.active (↑C.target : Set (Site d))
      hwin hregion
    exact fun y hy => Finset.mem_coe.2 (hface (Finset.mem_coe.1 hy))
  · intro i hi x hx
    have hrelay := relay_mem_sourcePlus C hC hi hx
    let v : C.sourcePlus := ⟨levelRelay C i x, hrelay⟩
    rcases h4 v with ⟨_, _, hregion, _, _, hsupp, hevent, hlower⟩
    have hv := hvalid.hitLeaf_holds v
    unfold ProbabilityBound.HoldsAt at hv
    have hsource : ReinforcedShell.sourceCube C.m (envCentre C) (levelRho C i) x =
        siteBoxAt v.1 C.m :=
      ReinforcedHit.sourceCube_eq_siteBoxAt C.m (envCentre C) (levelRho C i) x
    have hhitq : 1 - C.eta < (prodBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (C.selectedRegion v)
          (ReinforcedShell.sourceCube C.m (envCentre C) (levelRho C i) x)
          (C.selectedFace v)) := by
      rw [hlower, CylinderExperiment.prob, hevent] at hv
      change 1 - C.eta < (prodBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (C.selectedRegion v) (siteBoxAt v.1 C.m)
          (C.selectedFace v)) at hv
      simpa only [hsource] using hv
    have hmeas := ReinforcedHit.measurableSet_hitEvent (C.selectedRegion v)
      (ReinforcedShell.sourceCube C.m (envCentre C) (levelRho C i) x)
      (C.selectedFace v)
    have hdet : DeterminedBy
        (ExactTargetPlan.hitEvent (C.selectedRegion v)
          (ReinforcedShell.sourceCube C.m (envCentre C) (levelRho C i) x)
          (C.selectedFace v)) (↑(C.selectedRegion v) : Set (Site d)) := by
      have hd := (C.leaf (C.hitLeaf v)).experiment.determined
      rw [hsupp, hevent] at hd
      simpa only [hsource] using hd
    have hcompq : (prodBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (C.selectedRegion v)
          (ReinforcedShell.sourceCube C.m (envCentre C) (levelRho C i) x)
          (C.selectedFace v))ᶜ ≤ C.eta := by
      have hc : (prodBernoulli (fun _ : Site d => q)).real
          (ExactTargetPlan.hitEvent (C.selectedRegion v)
            (ReinforcedShell.sourceCube C.m (envCentre C) (levelRho C i) x)
            (C.selectedFace v))ᶜ =
          1 - (prodBernoulli (fun _ : Site d => q)).real
            (ExactTargetPlan.hitEvent (C.selectedRegion v)
              (ReinforcedShell.sourceCube C.m (envCentre C) (levelRho C i) x)
              (C.selectedFace v)) := by
        rw [measureReal_compl hmeas, probReal_univ]
      linarith
    have htransfer := prodBernoulli_real_eq_of_determinedBy
      (fun _ : Site d => q) w
      (fun y hy => (hwactive y (hregion (Finset.mem_coe.1 hy))).symm)
      hdet.compl hmeas.compl
    simp only [ExactTargetPlan.Plan.scanHit, dif_pos hrelay]
    rw [← htransfer]
    exact hcompq
  · exact hsrc

/-- Finite exact-target composition in one actively lattice product graph. -/
theorem soundChain (n : Nat) (C : Fin (n + 1) → ExactTargetPlan.Plan d)
    {q : unitInterval} (G : SimpleGraph (Site d)) (w : Site d → unitInterval)
    (Dom : Finset (Site d)) (o : Site d)
    (hC : ∀ i, (C i).WellFormed) (hvalid : ∀ i, (C i).ValidAt q)
    (hactiveDom : ∀ i, (C i).active ⊆ Dom)
    (hG : ∀ i, ActiveGraph.AgreesOn G (C i).active)
    (hwactive : ∀ i, ∀ x ∈ (C i).active, w x = q)
    (hoDom : o ∈ Dom) (hoActive : ∀ i, o ∉ (C i).active) (hwo : w o = 1)
    (hbase : 1 - (C 0).delta < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set (Site d)) o (↑(C 0).source : Set (Site d))))
    (hTargetSource : ∀ i : Fin n, (C i.castSucc).target ⊆ (C i.succ).source)
    (hepsdelta : ∀ i : Fin n, (C i.castSucc).epsilon ≤ (C i.succ).delta) :
    1 - (C (Fin.last n)).epsilon < (prodBernoulli w).real
      (connWithinSet G (↑Dom : Set (Site d)) o
        (↑(C (Fin.last n)).target : Set (Site d))) := by
  have hstage : ∀ j (hj : j ≤ n),
      1 - (C ⟨j, Nat.lt_succ_iff.mpr hj⟩).epsilon < (prodBernoulli w).real
        (connWithinSet G (↑Dom : Set (Site d)) o
          (↑(C ⟨j, Nat.lt_succ_iff.mpr hj⟩).target : Set (Site d))) := by
    intro j
    induction j with
    | zero =>
        intro hj
        have hu : (⟨0, Nat.lt_succ_iff.mpr hj⟩ : Fin (n + 1)) = 0 := Fin.ext (by rfl)
        rw [hu]
        exact soundProduct (C 0) (hC 0) (hvalid 0) G w
          (hactiveDom 0) (hG 0) (hwactive 0) o
          (Finset.mem_sdiff.2 ⟨hoDom, hoActive 0⟩) hwo hbase
    | succ j ih =>
        intro hj
        have hjlt : j < n := Nat.lt_of_succ_le hj
        let i : Fin n := ⟨j, hjlt⟩
        have hprev := ih (Nat.le_of_lt hjlt)
        have hprevIndex :
            (⟨j, Nat.lt_succ_iff.mpr (Nat.le_of_lt hjlt)⟩ : Fin (n + 1)) =
              i.castSucc := Fin.ext (by rfl)
        rw [hprevIndex] at hprev
        have hevent : connWithinSet G (↑Dom : Set (Site d)) o
              (↑(C i.castSucc).target : Set (Site d)) ⊆
            connWithinSet G (↑Dom : Set (Site d)) o
              (↑(C i.succ).source : Set (Site d)) := by
          intro omega homega
          obtain ⟨x, hx, hox⟩ := (mem_connWithinSet_iff G
            (↑Dom : Set (Site d)) o (↑(C i.castSucc).target : Set (Site d)) omega).1 homega
          exact (mem_connWithinSet_iff G (↑Dom : Set (Site d)) o
            (↑(C i.succ).source : Set (Site d)) omega).2
              ⟨x, Finset.mem_coe.2 (hTargetSource i (Finset.mem_coe.1 hx)), hox⟩
        have hprob := measureReal_mono hevent (measure_ne_top (prodBernoulli w) _)
        have hsrc : 1 - (C i.succ).delta < (prodBernoulli w).real
            (connWithinSet G (↑Dom : Set (Site d)) o
              (↑(C i.succ).source : Set (Site d))) := by
          have ht : 1 - (C i.succ).delta ≤ 1 - (C i.castSucc).epsilon := by
            linarith [hepsdelta i]
          exact lt_of_le_of_lt ht (lt_of_lt_of_le hprev hprob)
        have hnext := soundProduct (C i.succ) (hC i.succ) (hvalid i.succ)
          G w (hactiveDom i.succ) (hG i.succ) (hwactive i.succ) o
          (Finset.mem_sdiff.2 ⟨hoDom, hoActive i.succ⟩) hwo hsrc
        have hnextIndex :
            (⟨j + 1, Nat.lt_succ_iff.mpr hj⟩ : Fin (n + 1)) = i.succ :=
          Fin.ext (by rfl)
        rw [hnextIndex]
        exact hnext
  have hf := hstage n le_rfl
  have hlast : (⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ : Fin (n + 1)) = Fin.last n :=
    Fin.ext (by rfl)
  rwa [hlast] at hf

end ProductSound

/-! ## A same-type wired source -/

namespace Wired

/-- Delete all ordinary edges incident to `o`, then join `o` to every member of `S`. -/
def graph (o : Site d) (S : Finset (Site d)) : SimpleGraph (Site d) :=
  SimpleGraph.fromRel fun x y =>
    (x ≠ o ∧ y ≠ o ∧ (zdGraph d).Adj x y) ∨ (x = o ∧ y ∈ S)

def weight (q : unitInterval) (o : Site d) : Site d → unitInterval :=
  fun x => if x = o then 1 else q

@[simp] theorem weight_root (q : unitInterval) (o : Site d) : weight q o o = 1 := by
  simp [weight]

theorem weight_of_ne (q : unitInterval) (o : Site d) {x : Site d} (hx : x ≠ o) :
    weight q o x = q := by simp [weight, hx]

theorem graph_adj_old (o : Site d) (S : Finset (Site d)) {x y : Site d}
    (hx : x ≠ o) (hy : y ≠ o) :
    (graph o S).Adj x y ↔ (zdGraph d).Adj x y := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, (⟨_, _, h⟩ | ⟨h, _⟩) | (⟨_, _, h⟩ | ⟨h, _⟩)⟩
    · exact h
    · exact absurd h hx
    · exact h.symm
    · exact absurd h hy
  · intro h
    exact ⟨h.ne, Or.inl (Or.inl ⟨hx, hy, h⟩)⟩

theorem graph_adj_root (o : Site d) (S : Finset (Site d)) (hoS : o ∉ S)
    (y : Site d) : (graph o S).Adj o y ↔ y ∈ S := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, (⟨hne, _⟩ | ⟨_, hy⟩) | (⟨_, hne, _⟩ | ⟨hy, ho⟩)⟩
    · exact absurd rfl hne
    · exact hy
    · exact absurd rfl hne
    · exact absurd ho hoS
  · intro hy
    exact ⟨fun (heq : o = y) => hoS (heq ▸ hy), Or.inl (Or.inr ⟨rfl, hy⟩)⟩

/-- The wired graph agrees with the lattice on an active set disjoint from both the root and the
wired source. -/
theorem agreesOn {o : Site d} {S D : Finset (Site d)}
    (hoS : o ∉ S) (hoD : o ∉ D) (hfar : ∀ x ∈ D, ¬(zdGraph d).Adj x o)
    (hSD : Disjoint S D) : ActiveGraph.AgreesOn (graph o S) D := by
  intro x hx y
  by_cases hy : y = o
  · subst y
    rw [(graph o S).adj_comm, graph_adj_root o S hoS]
    constructor
    · intro hxS
      exact False.elim (Finset.disjoint_left.1 hSD hxS hx)
    · exact fun hadj => False.elim (hfar x hx hadj)
  · exact graph_adj_old o S (fun h => hoD (h ▸ hx)) hy

private def Good (o : Site d) (S Reg : Finset (Site d))
    (omega : SiteConfig (Site d)) (x : Site d) : Prop :=
  x = o ∨ ∃ s ∈ S, omega ∈ connWithin (zdGraph d) (↑Reg : Set (Site d)) s x

private theorem good_step {o : Site d} {S Reg : Finset (Site d)}
    (hoS : o ∉ S) (hoReg : o ∉ Reg) (omega : SiteConfig (Site d))
    {x y : Site d} (hx : Good o S Reg omega x)
    (hxy : (openSiteGraph (graph o S)
      (omega ∩ (↑(insert o Reg) : Set (Site d)))).Adj x y) :
    Good o S Reg omega y := by
  rw [openSiteGraph_adj_iff'] at hxy
  rcases eq_or_ne y o with rfl | hyo
  · exact Or.inl rfl
  have hyOpen : y ∈ omega := hxy.2.2.1
  have hyDom : y ∈ insert o Reg := Finset.mem_coe.1 hxy.2.2.2
  have hyReg : y ∈ Reg := (Finset.mem_insert.1 hyDom).resolve_left hyo
  rcases hx with hxo | ⟨s, hsS, hsx⟩
  · have hyS : y ∈ S := (graph_adj_root o S hoS y).1 (hxo ▸ hxy.1)
    exact Or.inr ⟨y, hyS, ⟨⟨hyOpen, Finset.mem_coe.2 hyReg⟩,
      SimpleGraph.Reachable.refl y⟩⟩
  · have hxReg : x ∈ Reg := Finset.mem_coe.1 (TargetExt.mem_of_connWithin _ hsx).2
    have hxo : x ≠ o := fun h => hoReg (h ▸ hxReg)
    have hlat : (zdGraph d).Adj x y := (graph_adj_old o S hxo hyo).1 hxy.1
    have hedge : (openSiteGraph (zdGraph d) (omega ∩ (↑Reg : Set (Site d)))).Adj x y :=
      (openSiteGraph_adj_iff' _ _ _ _).2
        ⟨hlat, TargetExt.mem_of_connWithin _ hsx, ⟨hyOpen, Finset.mem_coe.2 hyReg⟩⟩
    exact Or.inr ⟨s, hsS, ⟨hsx.1, hsx.2.trans hedge.reachable⟩⟩

private theorem good_of_walk {o : Site d} {S Reg : Finset (Site d)}
    (hoS : o ∉ S) (hoReg : o ∉ Reg) (omega : SiteConfig (Site d)) :
    ∀ {x y : Site d},
      (openSiteGraph (graph o S)
        (omega ∩ (↑(insert o Reg) : Set (Site d)))).Walk x y →
      Good o S Reg omega x → Good o S Reg omega y := by
  intro x y p
  induction p with
  | nil => exact fun h => h
  | cons hadj _ ih => exact fun h => ih (good_step hoS hoReg omega h hadj)

/-- With the root open, wired connection to `T` is exactly the ordinary set-source hit event. -/
theorem event_iff_of_root_open {o : Site d} {S Reg T : Finset (Site d)}
    (hoS : o ∉ S) (hoReg : o ∉ Reg) (hoT : o ∉ T) (hSReg : S ⊆ Reg)
    {omega : SiteConfig (Site d)} (hoOpen : o ∈ omega) :
    omega ∈ connWithinSet (graph o S) (↑(insert o Reg) : Set (Site d)) o
        (↑T : Set (Site d)) ↔
      omega ∈ ExactTargetPlan.hitEvent Reg S T := by
  constructor
  · intro h
    obtain ⟨t, htT, hot⟩ :=
      (mem_connWithinSet_iff (graph o S) (↑(insert o Reg) : Set (Site d)) o
        (↑T : Set (Site d)) omega).1 h
    obtain ⟨p⟩ := hot.2
    have hgood := good_of_walk hoS hoReg omega p (Or.inl rfl)
    rcases hgood with hto | ⟨s, hsS, hst⟩
    · exact False.elim (hoT (hto ▸ Finset.mem_coe.1 htT))
    · rw [ExactTargetPlan.hitEvent]
      exact Set.mem_biUnion (Finset.mem_coe.2 hsS)
        ((mem_connWithinSet_iff (zdGraph d) (↑Reg : Set (Site d)) s
          (↑T : Set (Site d)) omega).2 ⟨t, htT, hst⟩)
  · intro h
    rw [ExactTargetPlan.hitEvent] at h
    obtain ⟨s, hsS, hsT⟩ := Set.mem_iUnion₂.1 h
    obtain ⟨t, htT, hst⟩ :=
      (mem_connWithinSet_iff (zdGraph d) (↑Reg : Set (Site d)) s
        (↑T : Set (Site d)) omega).1 hsT
    have hsReg : s ∈ Reg := hSReg (Finset.mem_coe.1 hsS)
    have hso : s ≠ o := fun heq => hoReg (heq ▸ hsReg)
    have hrootAdj : (openSiteGraph (graph o S)
        (omega ∩ (↑(insert o Reg) : Set (Site d)))).Adj o s :=
      (openSiteGraph_adj_iff' _ _ _ _).2
        ⟨(graph_adj_root o S hoS s).2 (Finset.mem_coe.1 hsS),
          ⟨hoOpen, Finset.mem_coe.2 (Finset.mem_insert_self o Reg)⟩,
          ⟨hst.1.1, Finset.mem_coe.2 (Finset.mem_insert_of_mem hsReg)⟩⟩
    have htail : (openSiteGraph (graph o S)
        (omega ∩ (↑(insert o Reg) : Set (Site d)))).Reachable s t := by
      refine hst.2.map ⟨id, ?_⟩
      intro a b hab
      rw [openSiteGraph_adj_iff'] at hab ⊢
      have haReg : a ∈ Reg := Finset.mem_coe.1 hab.2.1.2
      have hbReg : b ∈ Reg := Finset.mem_coe.1 hab.2.2.2
      exact ⟨(graph_adj_old o S (fun heq => hoReg (heq ▸ haReg))
          (fun heq => hoReg (heq ▸ hbReg))).2 hab.1,
        ⟨hab.2.1.1, Finset.mem_coe.2 (Finset.mem_insert_of_mem haReg)⟩,
        ⟨hab.2.2.1, Finset.mem_coe.2 (Finset.mem_insert_of_mem hbReg)⟩⟩
    exact (mem_connWithinSet_iff (graph o S)
      (↑(insert o Reg) : Set (Site d)) o (↑T : Set (Site d)) omega).2
      ⟨t, htT, ⟨⟨hoOpen, Finset.mem_coe.2 (Finset.mem_insert_self o Reg)⟩,
        hrootAdj.reachable.trans htail⟩⟩

/-- The forced-root product law computes the wired event as the original finite set-source
cylinder, with no designated source site. -/
theorem measureReal_connWithinSet_eq_hitEvent
    (q : unitInterval) {o : Site d} {S Reg T : Finset (Site d)}
    (hoS : o ∉ S) (hoReg : o ∉ Reg) (hoT : o ∉ T) (hSReg : S ⊆ Reg) :
    (prodBernoulli (weight q o)).real
        (connWithinSet (graph o S) (↑(insert o Reg) : Set (Site d)) o
          (↑T : Set (Site d))) =
      (prodBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent Reg S T) := by
  have hroot : ∀ᵐ omega ∂(prodBernoulli (weight q o)), o ∈ omega :=
    prodBernoulli_ae_mem_of_eq_one (weight q o) (weight_root q o)
  have heq : (prodBernoulli (weight q o)).real
      (ExactTargetPlan.hitEvent Reg S T) =
      (prodBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent Reg S T) := by
    have hdet : DeterminedBy (ExactTargetPlan.hitEvent Reg S T)
        (↑Reg : Set (Site d)) := by
      unfold ExactTargetPlan.hitEvent
      exact DeterminedBy.iUnion fun x => DeterminedBy.iUnion fun _ =>
        determinedBy_connWithinSet (zdGraph d) (↑Reg : Set (Site d)) x
          (↑T : Set (Site d))
    have hmeas := ReinforcedHit.measurableSet_hitEvent Reg S T
    exact prodBernoulli_real_eq_of_determinedBy (weight q o)
      (fun _ : Site d => q)
      (fun x hx => weight_of_ne q o (fun heq => hoReg (heq ▸ Finset.mem_coe.1 hx)))
      hdet hmeas
  rw [← heq]
  refine measureReal_congr (Filter.eventuallyEq_set.2 ?_)
  filter_upwards [hroot] with omega homega
  exact event_iff_of_root_open hoS hoReg hoT hSReg homega

end Wired

/-! ## Set-source soundness of a variable-aspect exact chain -/

namespace VariableBridge

open KNAll.Site.LongBoxVariable
open KNAll.Site.ExactLongBoxVariablePlan

private abbrev region {p0 : unitInterval} {alpha : Real} {A : Nat}
    (P : ExactLongBoxVariablePlan.Plan d p0 alpha A) : Finset (Site d) :=
  allowedRegion A P.axis P.sigma P.macroScale P.rem P.radius

theorem hitEvent_mono {Q Q' S S' T T' : Finset (Site d)}
    (hQ : Q ⊆ Q') (hS : S ⊆ S') (hT : T ⊆ T') :
    ExactTargetPlan.hitEvent Q S T ⊆ ExactTargetPlan.hitEvent Q' S' T' := by
  intro omega h
  rw [ExactTargetPlan.hitEvent] at h ⊢
  obtain ⟨s, hs, hsT⟩ := Set.mem_iUnion₂.1 h
  obtain ⟨t, ht, hst⟩ := (mem_connWithinSet_iff (zdGraph d)
    (↑Q : Set (Site d)) s (↑T : Set (Site d)) omega).1 hsT
  exact Set.mem_biUnion (hS hs) ((mem_connWithinSet_iff (zdGraph d)
    (↑Q' : Set (Site d)) s (↑T' : Set (Site d)) omega).2
      ⟨t, hT ht, connWithin_mono_set (zdGraph d) (Finset.coe_subset.2 hQ) s t hst⟩)

private theorem initial_qface_subset_Bset
    {A : Nat} (axis : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    (s rem R : Nat) :
    TargetAwareLattice.shiftedTarget (LongBoxVariable.L0 A s rem) 0
        (axis, TargetAwareLattice.qfaceUnits axis sigma (fun _ => 1)) ⊆
      LongBoxVariable.Bset A axis sigma s rem R 0 := by
  intro x hx
  have hq := TargetAwareLattice.shifted_orthantFace_subset_qface
    (0 : Site d) (LongBoxVariable.L0 A s rem) axis sigma (fun _ => 1) hsigma hx
  rw [CorrMove.mem_qface] at hq
  rw [LongBoxVariable.mem_Bset hsigma]
  simp only [Pi.zero_apply, sub_zero, LongBoxVariable.L, Nat.zero_mul, Nat.add_zero,
    LongBoxVariable.width]
  exact ⟨by simpa using hq.2.1, fun j hji => by simpa using hq.1 j⟩

private theorem chain_base_error_lt
    {A : Nat} (hA : 1 ≤ A) {beta : Real} (hb0 : 0 < beta) (hb1 : beta ≤ 1) :
    ExactTargetArithmetic.etaOf (LongBoxVariable.tol A beta 1) <
      LongBoxVariable.tol A beta 0 := by
  have hstep : 0 < LongBoxVariable.stepCount A := by
    unfold LongBoxVariable.stepCount
    omega
  let e := LongBoxVariable.tol A beta 1
  have he0 : 0 < e := LongBoxVariable.tol_pos A hb0 1
  have he1 : e ≤ 1 := LongBoxVariable.tol_le_one A hb0 hb1 1
  have hp : e ^ 5 ≤ e ^ 2 := pow_le_pow_of_le_one he0.le he1 (by omega)
  have hrec := LongBoxVariable.tol_rec A beta hstep
  change ExactTargetArithmetic.etaOf e < LongBoxVariable.tol A beta 0
  rw [hrec]
  unfold ExactTargetArithmetic.etaOf ExactTargetArithmetic.deltaOf
    ExactTargetArithmetic.deltaCOf CorrMove.f
  nlinarith [sq_pos_of_pos he0]

/-- The first extracted quarter leaf supplies the source estimate for a centered exact long chain.
The source is the whole radius-`m` cube. -/
theorem centered_base
    {p0 : unitInterval} {beta : Real} {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 beta A)
    (hA : 1 ≤ A) (hb0 : 0 < beta) (hb1 : beta ≤ 1)
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (m s rem : Nat) (hm : (F.scheme 0).scales.source ≤ m) (hrem : rem ≤ 7)
    (hscale : 3 * A + 3 * A * F.radius + m + 8 ≤ s) :
    1 - LongBoxVariable.tol A beta 0 <
      (prodBernoulli (fun _ : Site d => p0)).real
        (ExactTargetPlan.hitEvent
          (LongBoxVariable.allowedRegion A axis sigma s rem F.radius)
          (siteBoxAt 0 m)
          (LongBoxVariable.Bset A axis sigma s rem F.radius 0)) := by
  have hlocal : (F.scheme 0).scales.localRadius ≤ LongBoxVariable.L0 A s rem := by
    have hR := (F.local_lt 0).le
    have hRs : F.radius ≤ s := by
      have := hscale
      nlinarith
    unfold LongBoxVariable.L0
    omega
  have hsmall := ExactTargetHits.one_sub_lt_prob_hitEvent_mono_source
    (F.scheme 0).scales m (LongBoxVariable.L0 A s rem) hm hlocal 0
      (axis, TargetAwareLattice.qfaceUnits axis sigma (fun _ => 1))
  simp only [Fin.val_zero, Nat.zero_add] at hsmall
  have howner : TargetAwareLattice.shiftedOwner (LongBoxVariable.L0 A s rem) 0 ⊆
      LongBoxVariable.allowedRegion A axis sigma s rem F.radius := by
    rw [TargetAwareLattice.shiftedOwner, TargetAwareLattice.shiftFinset_box_eq_cube,
      LongBoxVariable.allowedRegion]
    exact fun _ hx => Finset.mem_union_left _ hx
  have hevent : ExactTargetPlan.hitEvent
        (TargetAwareLattice.shiftedOwner (LongBoxVariable.L0 A s rem) 0)
        (siteBoxAt 0 m)
        (TargetAwareLattice.shiftedTarget (LongBoxVariable.L0 A s rem) 0
          (axis, TargetAwareLattice.qfaceUnits axis sigma (fun _ => 1))) ⊆
      ExactTargetPlan.hitEvent
        (LongBoxVariable.allowedRegion A axis sigma s rem F.radius)
        (siteBoxAt 0 m) (LongBoxVariable.Bset A axis sigma s rem F.radius 0) :=
    hitEvent_mono howner (fun _ h => h)
      (initial_qface_subset_Bset (A := A) axis hsigma s rem F.radius)
  have hmono : (prodBernoulli (fun _ : Site d => p0)).real
        (ExactTargetPlan.hitEvent
          (TargetAwareLattice.shiftedOwner (LongBoxVariable.L0 A s rem) 0)
          (siteBoxAt 0 m)
          (TargetAwareLattice.shiftedTarget (LongBoxVariable.L0 A s rem) 0
            (axis, TargetAwareLattice.qfaceUnits axis sigma (fun _ => 1)))) ≤
      (prodBernoulli (fun _ : Site d => p0)).real
        (ExactTargetPlan.hitEvent
          (LongBoxVariable.allowedRegion A axis sigma s rem F.radius)
          (siteBoxAt 0 m) (LongBoxVariable.Bset A axis sigma s rem F.radius 0)) :=
    measureReal_mono hevent (measure_ne_top _ _)
  exact lt_of_le_of_lt (by
      linarith [chain_base_error_lt hA hb0 hb1])
    (lt_of_lt_of_le hsmall hmono)

private theorem siteBoxAt_zero_eq_cube (m : Nat) :
    siteBoxAt (0 : Site d) m = CorrMove.cube 0 (m : Int) := by
  rw [← ExactTargetHits.shiftFinset_box_eq_siteBoxAt,
    TargetAwareLattice.shiftFinset_box_eq_cube]

/-- An exact `8*A-4` chain carries a genuine finite set-source hit to its aspect-`A` far face.
The auxiliary root is only an implementation device; both the premise and conclusion are ordinary
homogeneous `hitEvent`s and quantify over the whole source set. -/
theorem soundSetSourceWithRoot
    {p0 q : unitInterval} {alpha : Real} {A : Nat}
    (P : ExactLongBoxVariablePlan.Plan d p0 alpha A)
    (hP : P.WellFormed) (hvalid : P.ValidAt q)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (S : Finset (Site d)) (o : Site d)
    (hSReg : S ⊆ region P) (hoS : o ∉ S) (hoReg : o ∉ region P)
    (hoFace : o ∉ CorrMove.longFace 0
      (LongBoxVariable.longScale P.macroScale P.rem : Int)
      P.axis P.sigma A)
    (hSactive : ∀ u, Disjoint S (P.node u).active)
    (hfar : ∀ u, ∀ x ∈ (P.node u).active, ¬(zdGraph d).Adj x o)
    (hbase : 1 - tol A alpha 0 <
      (prodBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (region P) S
          (Bset A P.axis P.sigma P.macroScale P.rem P.radius 0))) :
    1 - alpha < (prodBernoulli (fun _ : Site d => q)).real
      (ExactTargetPlan.hitEvent (region P) S
        (CorrMove.longFace 0 (LongBoxVariable.longScale P.macroScale P.rem : Int)
          P.axis P.sigma A)) := by
  have hstepPos : 0 < LongBoxVariable.stepCount A := by
    have hA := hP.aspect_pos
    unfold LongBoxVariable.stepCount
    omega
  have hB0Reg : Bset A P.axis P.sigma P.macroScale P.rem P.radius 0 ⊆ region P := by
    rw [region, LongBoxVariable.allowedRegion]
    exact fun _ hx => Finset.mem_union_left _
      (LongBoxVariable.Bset_zero_subset_initialCube A P.axis hP.sign_unit
        P.macroScale P.rem P.radius hx)
  have hoB0 : o ∉ Bset A P.axis P.sigma P.macroScale P.rem P.radius 0 :=
    fun ho => hoReg (hB0Reg ho)
  have hbaseW : 1 - (P.node 0).delta <
      (prodBernoulli (Wired.weight q o)).real
        (connWithinSet (Wired.graph o S) (↑(insert o (region P)) : Set (Site d)) o
          (↑(P.node 0).source : Set (Site d))) := by
    rw [hP.node_source]
    simp only [Fin.val_zero]
    rw [Wired.measureReal_connWithinSet_eq_hitEvent q hoS hoReg hoB0 hSReg]
    apply lt_of_le_of_lt ?_ hbase
    have heps : (P.node 0).epsilon = tol A alpha 1 := by
      simpa using hP.node_epsilon 0
    have hrec := tol_rec A alpha hstepPos
    rw [ExactTargetPlan.Plan.delta, heps, hrec, CorrMove.f]
    nlinarith [sq_nonneg (tol A alpha 1)]
  have hchain := ProductSound.soundChain P.transitions P.node
    (Wired.graph o S) (Wired.weight q o) (insert o (region P)) o
    (fun u => hP.node_wf u) hvalid
    (fun u x hx => Finset.mem_insert_of_mem
      (ExactLongBoxVariablePlan.Dset_subset_allowedRegion A P.axis P.sigma
        P.macroScale P.rem P.radius u.val (by
          exact lt_of_lt_of_eq u.isLt P.count_eq)
        (by simpa only [hP.node_active] using hx)))
    (fun u => Wired.agreesOn hoS
      (fun hou => hoReg (ExactLongBoxVariablePlan.Dset_subset_allowedRegion
        A P.axis P.sigma P.macroScale P.rem P.radius u.val (by
          exact lt_of_lt_of_eq u.isLt P.count_eq)
        (by simpa only [hP.node_active] using hou)))
      (hfar u) (hSactive u))
    (fun u x hx => Wired.weight_of_ne q o (fun hxo =>
      hoReg (ExactLongBoxVariablePlan.Dset_subset_allowedRegion
        A P.axis P.sigma P.macroScale P.rem P.radius u.val
          (lt_of_lt_of_eq u.isLt P.count_eq)
          (by simpa only [hP.node_active, hxo] using hx))))
    (Finset.mem_insert_self o (region P))
    (fun u hou => hoReg (ExactLongBoxVariablePlan.Dset_subset_allowedRegion
      A P.axis P.sigma P.macroScale P.rem P.radius u.val (by
        exact lt_of_lt_of_eq u.isLt P.count_eq)
      (by simpa only [hP.node_active] using hou)))
    (Wired.weight_root q o) hbaseW
    (fun u => by rw [hP.node_target, hP.node_source]; exact Finset.Subset.rfl)
    (fun u => by
      rw [hP.node_epsilon, ExactTargetPlan.Plan.delta, hP.node_epsilon]
      change tol A alpha (u.val + 1) ≤ tol A alpha (u.val + 2) ^ 2 / 64
      have hu : u.val + 1 < stepCount A := by
        have huLt := u.isLt
        have hcount := P.count_eq
        omega
      rw [LongBoxVariable.tol_rec A alpha hu, CorrMove.f]
      nlinarith [sq_nonneg (LongBoxVariable.tol A alpha (u.val + 2))])
  have hlastEps : (P.node (Fin.last P.transitions)).epsilon = alpha := by
    rw [hP.node_epsilon]
    have hv : (Fin.last P.transitions).val + 1 = stepCount A := by
      simpa using P.count_eq
    rw [hv, LongBoxVariable.tol_final]
  rw [hlastEps] at hchain
  have htarget := P.final_target_subset_longFace hP
  have hevent : connWithinSet (Wired.graph o S)
      (↑(insert o (region P)) : Set (Site d)) o
      (↑(P.node (Fin.last P.transitions)).target : Set (Site d)) ⊆
    connWithinSet (Wired.graph o S) (↑(insert o (region P)) : Set (Site d)) o
      (↑(CorrMove.longFace 0 (LongBoxVariable.longScale P.macroScale P.rem : Int)
        P.axis P.sigma A) : Set (Site d)) := by
    intro omega homega
    obtain ⟨x, hx, hox⟩ := (mem_connWithinSet_iff _ _ _ _ _).1 homega
    exact (mem_connWithinSet_iff _ _ _ _ _).2
      ⟨x, Finset.mem_coe.2 (htarget (Finset.mem_coe.1 hx)), hox⟩
  have hfaceProb : 1 - alpha < (prodBernoulli (Wired.weight q o)).real
      (connWithinSet (Wired.graph o S) (↑(insert o (region P)) : Set (Site d)) o
        (↑(CorrMove.longFace 0 (LongBoxVariable.longScale P.macroScale P.rem : Int)
          P.axis P.sigma A) : Set (Site d))) :=
    hchain.trans_le (measureReal_mono hevent (measure_ne_top _ _))
  rw [Wired.measureReal_connWithinSet_eq_hitEvent q hoS hoReg hoFace hSReg] at hfaceProb
  exact hfaceProb

private def forbidden
    {p0 : unitInterval} {alpha : Real} {A : Nat}
    (P : ExactLongBoxVariablePlan.Plan d p0 alpha A) (S : Finset (Site d)) :
    Finset (Site d) :=
  S ∪ region P ∪
    CorrMove.longFace 0 (LongBoxVariable.longScale P.macroScale P.rem : Int)
      P.axis P.sigma A ∪
    (region P).biUnion fun x => (zdGraph d).neighborFinset x

/-- A root can be chosen outside the finite chain, its final face, its source, and every lattice
neighbor of the active region. -/
theorem exists_safeRoot
    {p0 : unitInterval} {alpha : Real} {A : Nat}
    (P : ExactLongBoxVariablePlan.Plan d p0 alpha A) (hP : P.WellFormed)
    (S : Finset (Site d)) :
    ∃ o : Site d,
      o ∉ S ∧ o ∉ region P ∧
      o ∉ CorrMove.longFace 0
        (LongBoxVariable.longScale P.macroScale P.rem : Int) P.axis P.sigma A ∧
      ∀ u, ∀ x ∈ (P.node u).active, ¬(zdGraph d).Adj x o := by
  obtain ⟨o, ho⟩ := Infinite.exists_notMem_finset (forbidden P S)
  refine ⟨o, ?_, ?_, ?_, ?_⟩
  · exact fun h => ho (by simp only [forbidden, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl h)))
  · exact fun h => ho (by simp only [forbidden, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr h)))
  · exact fun h => ho (by simp only [forbidden, Finset.mem_union]; exact Or.inl (Or.inr h))
  · intro u x hx hadj
    have hxReg : x ∈ region P :=
      ExactLongBoxVariablePlan.Dset_subset_allowedRegion A P.axis P.sigma
        P.macroScale P.rem P.radius u.val (lt_of_lt_of_eq u.isLt P.count_eq)
        (by simpa only [hP.node_active] using hx)
    apply ho
    simp only [forbidden, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.2
      ⟨x, hxReg, (SimpleGraph.mem_neighborFinset _ _ _).2 hadj⟩)

/-- Root-free set-source form of the exact variable-aspect chain. -/
theorem soundSetSource
    {p0 q : unitInterval} {alpha : Real} {A : Nat}
    (P : ExactLongBoxVariablePlan.Plan d p0 alpha A)
    (hP : P.WellFormed) (hvalid : P.ValidAt q)
    (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (S : Finset (Site d)) (hSReg : S ⊆ region P)
    (hSactive : ∀ u, Disjoint S (P.node u).active)
    (hbase : 1 - LongBoxVariable.tol A alpha 0 <
      (prodBernoulli (fun _ : Site d => q)).real
        (ExactTargetPlan.hitEvent (region P) S
          (LongBoxVariable.Bset A P.axis P.sigma P.macroScale P.rem P.radius 0))) :
    1 - alpha < (prodBernoulli (fun _ : Site d => q)).real
      (ExactTargetPlan.hitEvent (region P) S
        (CorrMove.longFace 0
          (LongBoxVariable.longScale P.macroScale P.rem : Int) P.axis P.sigma A)) := by
  obtain ⟨o, hoS, hoReg, hoFace, hfar⟩ := exists_safeRoot P hP S
  exact soundSetSourceWithRoot P hP hvalid ha0 ha1 S o hSReg hoS hoReg hoFace
    hSactive hfar hbase

/-- The extracted family gives the honest centered set-source long-box cylinder. -/
theorem centered_hit
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {beta : Real} {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 beta A)
    (hA : 1 ≤ A) (hb0 : 0 < beta) (hb1 : beta ≤ 1)
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (m s rem : Nat) (hm : (F.scheme 0).scales.source ≤ m) (hrem : rem ≤ 7)
    (hscale : 3 * A + 3 * A * F.radius + m + 8 ≤ s) :
    1 - beta < (prodBernoulli (fun _ : Site d => p0)).real
      (ExactTargetPlan.hitEvent
        (CorrMove.longBox 0 (LongBoxVariable.longScale s rem : Int) axis sigma A)
        (siteBoxAt 0 m)
        (CorrMove.longFace 0 (LongBoxVariable.longScale s rem : Int) axis sigma A)) := by
  let P := F.planAt hA axis sigma hsigma s rem hrem (by omega)
  have hP : P.WellFormed := F.planAt_wellFormed hp0 hp1 hb0 hb1
    hA axis sigma hsigma s rem hrem (by omega)
  have hvalid : P.ValidAt p0 := F.planAt_validAt hp0 hp1 hb0 hb1
    hA axis sigma hsigma s rem hrem (by omega)
  have hsourceReg : siteBoxAt (0 : Site d) m ⊆ region P := by
    rw [siteBoxAt_zero_eq_cube]
    change CorrMove.cube 0 (m : Int) ⊆
      LongBoxVariable.allowedRegion A axis sigma s rem F.radius
    exact LongBoxVariable.sourceCube_subset_allowedRegion axis sigma hA
      (k := m) (n1 := 0) (by omega)
  have hsourceActive : ∀ u, Disjoint (siteBoxAt (0 : Site d) m) (P.node u).active := by
    intro u
    rw [siteBoxAt_zero_eq_cube, hP.node_active]
    change Disjoint (CorrMove.cube 0 (m : Int))
      (LongBoxVariable.Dset A axis sigma s rem F.radius u.val)
    exact LongBoxVariable.sourceCube_disjoint_Dset axis hsigma hA
      (k := m) (n1 := 0) (by omega)
  have hbase : 1 - LongBoxVariable.tol A beta 0 <
      (prodBernoulli (fun _ : Site d => p0)).real
        (ExactTargetPlan.hitEvent (region P) (siteBoxAt 0 m)
          (LongBoxVariable.Bset A axis sigma s rem F.radius 0)) := by
    change 1 - LongBoxVariable.tol A beta 0 <
      (prodBernoulli (fun _ : Site d => p0)).real
        (ExactTargetPlan.hitEvent
          (LongBoxVariable.allowedRegion A axis sigma s rem F.radius)
          (siteBoxAt 0 m) (LongBoxVariable.Bset A axis sigma s rem F.radius 0))
    exact centered_base F hA hb0 hb1 axis sigma hsigma m s rem hm hrem hscale
  have hout := soundSetSource P hP hvalid hb0 hb1 (siteBoxAt 0 m)
    hsourceReg hsourceActive hbase
  have hreg : region P ⊆
      CorrMove.longBox 0 (LongBoxVariable.longScale s rem : Int) axis sigma A := by
    change LongBoxVariable.allowedRegion A axis sigma s rem F.radius ⊆ _
    apply LongBoxVariable.allowedRegion_subset_longBox axis hsigma hA hrem
    omega
  exact hout.trans_le (measureReal_mono
    (hitEvent_mono hreg (fun _ h => h) (fun _ h => h)) (measure_ne_top _ _))

theorem shift_hitEvent (v : Site d) (Q S T : Finset (Site d)) :
    ExactTargetPlan.hitEvent (MoveWindowInput.shiftFinset v Q)
        (MoveWindowInput.shiftFinset v S) (MoveWindowInput.shiftFinset v T) =
      siteShift v ⁻¹' ExactTargetPlan.hitEvent Q S T := by
  ext omega
  constructor
  · intro h
    rw [ExactTargetPlan.hitEvent] at h ⊢
    obtain ⟨sv, hsv, hsvT⟩ := Set.mem_iUnion₂.1 h
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hsv
    obtain ⟨tv, htv, hst⟩ := (mem_connWithinSet_iff (zdGraph d)
      (↑(MoveWindowInput.shiftFinset v Q) : Set (Site d)) (s + v)
      (↑(MoveWindowInput.shiftFinset v T) : Set (Site d)) omega).1 hsvT
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 htv)
    exact Set.mem_biUnion (Finset.mem_coe.2 hs)
      ((mem_connWithinSet_iff (zdGraph d) (↑Q : Set (Site d)) s
        (↑T : Set (Site d)) (siteShift v omega)).2
        ⟨t, Finset.mem_coe.2 ht,
          (MoveWindowInput.mem_connWithin_shift_iff v omega
            (↑Q : Set (Site d)) s t).2 (by
              simpa only [MoveWindowInput.coe_shiftFinset] using hst)⟩)
  · intro h
    rw [ExactTargetPlan.hitEvent] at h ⊢
    obtain ⟨s, hs, hsT⟩ := Set.mem_iUnion₂.1 h
    obtain ⟨t, ht, hst⟩ := (mem_connWithinSet_iff (zdGraph d)
      (↑Q : Set (Site d)) s (↑T : Set (Site d))
      (siteShift v omega)).1 hsT
    exact Set.mem_biUnion
      (Finset.mem_image.2 ⟨s, Finset.mem_coe.1 hs, rfl⟩)
      ((mem_connWithinSet_iff (zdGraph d)
        (↑(MoveWindowInput.shiftFinset v Q) : Set (Site d)) (s + v)
        (↑(MoveWindowInput.shiftFinset v T) : Set (Site d)) omega).2
        ⟨t + v, Finset.mem_coe.2 (Finset.mem_image.2
          ⟨t, Finset.mem_coe.1 ht, rfl⟩), by
          have hs' := (MoveWindowInput.mem_connWithin_shift_iff v omega
            (↑Q : Set (Site d)) s t).1 hst
          simpa only [MoveWindowInput.coe_shiftFinset] using hs'⟩)

theorem shift_longBox (v : Site d) {l : Int} (hl : 0 ≤ l)
    (axis : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {A : Nat} (hA : 1 ≤ A) :
    MoveWindowInput.shiftFinset v (CorrMove.longBox 0 l axis sigma A) =
      CorrMove.longBox v l axis sigma A := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [CorrMove.mem_longBox hsigma hl (by exact_mod_cast hA)] at hy ⊢
    simpa only [Pi.add_apply, Pi.zero_apply, sub_zero, add_sub_cancel_right] using hy
  · intro hx
    refine Finset.mem_image.2 ⟨x - v, ?_, ?_⟩
    · rw [CorrMove.mem_longBox hsigma hl (by exact_mod_cast hA)] at hx ⊢
      simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, sub_add_cancel] using hx
    · ext j
      simp

theorem shift_longFace (v : Site d) {l : Int} (hl : 0 ≤ l)
    (axis : Fin d) {sigma : Int} (hsigma : sigma = 1 ∨ sigma = -1)
    {A : Nat} (hA : 1 ≤ A) :
    MoveWindowInput.shiftFinset v (CorrMove.longFace 0 l axis sigma A) =
      CorrMove.longFace v l axis sigma A := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [CorrMove.mem_longFace hsigma hl (by exact_mod_cast hA)] at hy ⊢
    simpa only [Pi.add_apply, Pi.zero_apply, sub_zero, add_sub_cancel_right] using hy
  · intro hx
    refine Finset.mem_image.2 ⟨x - v, ?_, ?_⟩
    · rw [CorrMove.mem_longFace hsigma hl (by exact_mod_cast hA)] at hx ⊢
      simpa only [Pi.sub_apply, Pi.zero_apply, sub_zero, sub_add_cancel] using hx
    · ext j
      simp

theorem shift_siteBoxAt_zero (v : Site d) (m : Nat) :
    MoveWindowInput.shiftFinset v (siteBoxAt 0 m) = siteBoxAt v m := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    rw [mem_siteBoxAt] at hy ⊢
    intro j
    have hj := hy j
    simp only [Pi.add_apply, Pi.zero_apply] at hj ⊢
    omega
  · intro hx
    refine Finset.mem_image.2 ⟨x - v, ?_, ?_⟩
    · rw [mem_siteBoxAt] at hx ⊢
      intro j
      have hj := hx j
      simp only [Pi.sub_apply, Pi.zero_apply] at hj ⊢
      omega
    · ext j
      simp

/-- Translation of the centered result gives every set-source long-box cylinder used by a T4
leaf. -/
theorem translated_hit
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {beta : Real} {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 beta A)
    (hA : 1 ≤ A) (hb0 : 0 < beta) (hb1 : beta ≤ 1)
    (v : Site d) (axis : Fin d) (sigma : Int)
    (hsigma : sigma = 1 ∨ sigma = -1)
    (m s rem : Nat) (hm : (F.scheme 0).scales.source ≤ m) (hrem : rem ≤ 7)
    (hscale : 3 * A + 3 * A * F.radius + m + 8 ≤ s) :
    1 - beta < (prodBernoulli (fun _ : Site d => p0)).real
      (ExactTargetPlan.hitEvent
        (CorrMove.longBox v (LongBoxVariable.longScale s rem : Int) axis sigma A)
        (siteBoxAt v m)
        (CorrMove.longFace v (LongBoxVariable.longScale s rem : Int) axis sigma A)) := by
  have hc := centered_hit hp0 hp1 F hA hb0 hb1 axis sigma hsigma
    m s rem hm hrem hscale
  have hmset := ReinforcedHit.measurableSet_hitEvent
    (CorrMove.longBox 0 (LongBoxVariable.longScale s rem : Int) axis sigma A)
    (siteBoxAt 0 m)
    (CorrMove.longFace 0 (LongBoxVariable.longScale s rem : Int) axis sigma A)
  have hp := TargetAwareLattice.prob_shift_preimage p0 v hmset
  rw [← shift_hitEvent,
    shift_longBox v (by positivity) axis hsigma hA,
    shift_siteBoxAt_zero,
    shift_longFace v (by positivity) axis hsigma hA] at hp
  have hc' : 1 - beta < (siteBernoulli (fun _ : Site d => p0)).real
      (ExactTargetPlan.hitEvent
        (CorrMove.longBox 0 (LongBoxVariable.longScale s rem : Int) axis sigma A)
        (siteBoxAt 0 m)
        (CorrMove.longFace 0 (LongBoxVariable.longScale s rem : Int) axis sigma A)) := by
    simpa only [siteBernoulli] using hc
  change 1 - beta < (siteBernoulli (fun _ : Site d => p0)).real _
  exact hp.symm ▸ hc'

end VariableBridge

/-! ## One transparent rank-one target plan

The relation below is the variable-aspect form of `CorrMove.LongTarget`.  Keeping the source,
active set and target abstract is what lets the same constructor serve both the aspect-88 outer
move and the aspect-`2*K` stopped move. -/

namespace RankOne

open ExactTargetArithmetic ExactTargetSchemeNumbers

def LongTargetAspect (A R : Nat) (axis : Fin d) (sigma : Int)
    (active source target : Finset (Site d)) : Prop :=
  ∀ v : Site d, (∃ b ∈ source, ∀ j, |v j - b j| ≤ (R : Int)) →
    ∃ l : Int, (R : Int) ≤ l ∧
      CorrMove.longBox v l axis sigma A ⊆ active ∧
      CorrMove.longFace v l axis sigma A ⊆ target

theorem longTargetAspect_88_iff (R : Nat) (axis : Fin d) (sigma : Int)
    (active source target : Finset (Site d)) :
    LongTargetAspect 88 R axis sigma active source target ↔
      CorrMove.LongTarget (R : Int) axis sigma active source target := Iff.rfl

def sourceRadius {p0 : unitInterval} {beta : Real} {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 beta A) : Nat :=
  (F.scheme 0).scales.source + 1

def scaleThreshold {p0 : unitInterval} {beta : Real} {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 beta A) : Nat :=
  3 * A + 3 * A * F.radius + sourceRadius F + 8

def params {p0 : unitInterval} {alpha : Real} {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F)) (R : Nat) :
    ExactTargetPlan.ConstructorParams d where
  p0 := p0
  epsilon := alpha
  m := sourceRadius F
  k := N.k
  N := N.N
  L := N.L
  radius := R
  barrierLower := N.barrierLower

theorem params_admissible
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F)) (R : Nat) (hR : N.R0 ≤ R) :
    (params F N R).Admissible := by
  refine {
    p0_pos := hp0
    p0_lt_one := hp1
    epsilon_pos := ha0
    epsilon_le_one := ha1
    m_pos := by
      change 0 < (F.scheme 0).scales.source + 1
      omega
    k_pos := N.k_pos
    N_pos := N.N_pos
    L_pos := N.L_pos
    radius_large := N.radius_budget.trans hR
    packing := by simpa [params] using N.packing
    selected_budget := by
      simpa [params, ExactTargetPlan.ConstructorParams.seedCard,
        ExactTargetPlan.ConstructorParams.delta, seedCardOf, deltaOf] using N.seed_budget
    seed_valid := by
      simpa [params, ExactTargetPlan.ConstructorParams.seedCard,
        ExactTargetPlan.ConstructorParams.delta, seedCardOf, deltaOf] using N.seed_failure
    barrier_pos := N.barrier_pos
    barrier_lt_one := N.barrier_lt_one
    barrier_valid := by simpa [params] using N.barrier_leaf
    barrier_budget := by
      simpa [params, ExactTargetPlan.ConstructorParams.delta, deltaOf] using N.level_budget }

/-- Pure finite geometry needed to place the rank-one plan. -/
structure Instantiation
    {p0 : unitInterval} {alpha : Real} {A : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F)) (R : Nat)
    (axis : Fin d) (sigma : Int) where
  sourceBox : ExactTargetPlan.IntBox d
  activeBox : ExactTargetPlan.IntBox d
  target : Finset (Site d)
  source_ordered : sourceBox.Ordered
  active_ordered : activeBox.Ordered
  target_nonempty : target.Nonempty
  target_subset_active : target ⊆ activeBox.sites
  longTarget : LongTargetAspect A R axis sigma activeBox.sites sourceBox.sites target

namespace Instantiation

variable {p0 : unitInterval} {alpha : Real} {A R : Nat}
  {F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A}
  {N : Numbers d p0 alpha (sourceRadius F)} {axis : Fin d} {sigma : Int}

structure Choice (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) where
  l : Int
  radius_le : (R : Int) ≤ l
  region_subset : CorrMove.longBox v.1 l axis sigma A ⊆ I.activeBox.sites
  face_subset : CorrMove.longFace v.1 l axis sigma A ⊆ I.target

theorem exists_choice (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : Nonempty (Choice I v) := by
  obtain ⟨b, hb, hnear⟩ :=
    ExactQuarterPlanExtraction.exists_near_of_mem_inflate
      I.sourceBox I.source_ordered R v
  obtain ⟨l, hl, hreg, hface⟩ := I.longTarget v.1 ⟨b, hb, hnear⟩
  exact ⟨⟨l, hl, hreg, hface⟩⟩

noncomputable def choice (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : Choice I v :=
  Classical.choice (exists_choice I v)

def scale (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : Nat := (I.choice v).l.toNat

def macroScale (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : Nat := I.scale v / 8

def remainder (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : Nat := I.scale v % 8

theorem choice_nonneg (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : 0 ≤ (I.choice v).l :=
  (Int.natCast_nonneg R).trans (I.choice v).radius_le

theorem scale_cast (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : (I.scale v : Int) = (I.choice v).l := by
  exact Int.toNat_of_nonneg (I.choice_nonneg v)

theorem scale_eq (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) :
    LongBoxVariable.longScale (I.macroScale v) (I.remainder v) = I.scale v := by
  unfold macroScale remainder LongBoxVariable.longScale
  omega

theorem radius_le_scale (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : R ≤ I.scale v := by
  exact_mod_cast (show (R : Int) ≤ (I.scale v : Int) by
    simpa only [I.scale_cast v] using (I.choice v).radius_le)

theorem remainder_le (I : Instantiation F N R axis sigma)
    (v : (I.sourceBox.inflate R).sites) : I.remainder v ≤ 7 := by
  unfold remainder
  have := Nat.mod_lt (I.scale v) (by omega : 0 < 8)
  omega

end Instantiation

theorem sourcePlus_subset_active
    {p0 : unitInterval} {alpha : Real} {A R : Nat}
    {F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A}
    {N : Numbers d p0 alpha (sourceRadius F)} {axis : Fin d} {sigma : Int}
    (hA : 1 ≤ A) (hsigma : sigma = 1 ∨ sigma = -1)
    (I : Instantiation F N R axis sigma) :
    (I.sourceBox.inflate R).sites ⊆ I.activeBox.sites := by
  intro v hv
  let vv : (I.sourceBox.inflate R).sites := ⟨v, hv⟩
  have hl0 : 0 ≤ (I.choice vv).l := I.choice_nonneg vv
  have hvbox : v ∈ CorrMove.longBox v (I.choice vv).l axis sigma A := by
    rw [CorrMove.mem_longBox hsigma hl0 (by exact_mod_cast hA)]
    simp only [sub_self, mul_zero, abs_zero]
    exact ⟨⟨neg_nonpos.2 hl0, by positivity⟩, fun _ _ => hl0⟩
  exact (I.choice vv).region_subset hvbox

def concreteTarget
    {p0 : unitInterval} {alpha : Real} {A R : Nat}
    {F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A}
    {N : Numbers d p0 alpha (sourceRadius F)} {axis : Fin d} {sigma : Int}
    (hA : 1 ≤ A) (hsigma : sigma = 1 ∨ sigma = -1)
    (I : Instantiation F N R axis sigma) :
    ExactTargetPlan.ConcreteTarget (params F N R) where
  sourceBox := I.sourceBox
  activeBox := I.activeBox
  target := I.target
  source_ordered := I.source_ordered
  active_ordered := I.active_ordered
  target_nonempty := I.target_nonempty
  sourcePlus_subset_active := sourcePlus_subset_active hA hsigma I
  target_subset_active := I.target_subset_active

theorem source_subset_longBox
    {p0 : unitInterval} {alpha : Real} {A R : Nat}
    {F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A}
    {N : Numbers d p0 alpha (sourceRadius F)} {axis : Fin d} {sigma : Int}
    (hA : 1 ≤ A) (hsigma : sigma = 1 ∨ sigma = -1)
    (I : Instantiation F N R axis sigma)
    (hlarge : 8 * scaleThreshold F ≤ R)
    (v : (I.sourceBox.inflate R).sites) :
    siteBoxAt v.1 (sourceRadius F) ⊆
      CorrMove.longBox v.1 (I.choice v).l axis sigma A := by
  intro x hx
  have hl0 : 0 ≤ (I.choice v).l := I.choice_nonneg v
  have hmR : sourceRadius F ≤ R := by
    unfold scaleThreshold at hlarge
    omega
  have hml : (sourceRadius F : Int) ≤ (I.choice v).l := by
    have hRI : (R : Int) ≤ (I.choice v).l := (I.choice v).radius_le
    have hmRI : (sourceRadius F : Int) ≤ (R : Int) := by exact_mod_cast hmR
    exact hmRI.trans hRI
  rw [mem_siteBoxAt] at hx
  rw [CorrMove.mem_longBox hsigma hl0 (by exact_mod_cast hA)]
  have haxis := hx axis
  have hlA : (I.choice v).l ≤ (A : Int) * (I.choice v).l :=
    le_mul_of_one_le_left hl0 (by exact_mod_cast hA)
  constructor
  · rcases hsigma with rfl | rfl <;> norm_num at haxis ⊢ <;> omega
  · intro j hji
    have hj := hx j
    rw [abs_le]
    omega

def concreteHits
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R)
    (I : Instantiation F N R axis sigma) :
    ExactTargetPlan.ConcreteHits (params F N R) (concreteTarget hA hsigma I) where
  scale := I.scale
  region := fun v => CorrMove.longBox v.1 (I.choice v).l axis sigma A
  face := fun v => CorrMove.longFace v.1 (I.choice v).l axis sigma A
  scale_ge := I.radius_le_scale
  region_subset_active := fun v => (I.choice v).region_subset
  face_subset_target := fun v => (I.choice v).face_subset
  source_subset_region := fun v => source_subset_longBox hA hsigma I hlarge v
  hit_valid := fun v => by
    have hbeta0 : 0 < etaOf alpha := by
      unfold etaOf deltaOf deltaCOf
      positivity
    have hbeta1 : etaOf alpha ≤ 1 := by
      unfold etaOf deltaOf deltaCOf
      have hd0 : 0 ≤ alpha ^ 2 / 64 := by positivity
      have hd1 : alpha ^ 2 / 64 ≤ 1 := by nlinarith [sq_nonneg alpha]
      have hdc0 : 0 ≤ alpha / 4 := by positivity
      have hdc1 : alpha / 4 ≤ 1 := by linarith
      have hd2 : (alpha ^ 2 / 64) ^ 2 ≤ 1 := pow_le_one₀ hd0 hd1
      nlinarith [mul_le_mul hd2 hdc1 hdc0 (by positivity : (0 : Real) ≤ 1)]
    have hmacro : scaleThreshold F ≤ I.macroScale v := by
      have hRs := I.radius_le_scale v
      unfold Instantiation.macroScale
      omega
    have hhit := VariableBridge.translated_hit hp0 hp1 F hA hbeta0 hbeta1
      v.1 axis sigma hsigma (sourceRadius F) (I.macroScale v) (I.remainder v)
      (by unfold sourceRadius; omega) (I.remainder_le v) hmacro
    have hcast : (LongBoxVariable.longScale (I.macroScale v) (I.remainder v) : Int) =
        (I.choice v).l := by
      rw [I.scale_eq v, I.scale_cast v]
    simpa [siteBernoulli, params, ExactTargetPlan.ConstructorParams.eta,
      ExactTargetPlan.ConstructorParams.delta,
      ExactTargetPlan.ConstructorParams.deltaC, etaOf, deltaOf, deltaCOf,
      hcast] using hhit

/-- The requested transparent rank-one plan.  Its only noncanonical leaves are the whole
aspect-`A` set-source cylinders supplied by the exact long-box chain. -/
def buildPlan
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R)
    (I : Instantiation F N R axis sigma) : ExactTargetPlan.Plan d :=
  ExactTargetPlan.buildPlan (params F N R) (concreteTarget hA hsigma I)
    (concreteHits hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I)

theorem buildPlan_wellFormed
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hR : N.R0 ≤ R) (hlarge : 8 * scaleThreshold F ≤ R)
    (I : Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).WellFormed := by
  exact ExactTargetPlan.buildPlan_wellFormed _
    (params_admissible hp0 hp1 ha0 ha1 F N R hR) _ _

theorem buildPlan_validAt
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hR : N.R0 ≤ R) (hlarge : 8 * scaleThreshold F ≤ R)
    (I : Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).ValidAt p0 := by
  exact ExactTargetPlan.buildPlan_validAt _
    (params_admissible hp0 hp1 ha0 ha1 F N R hR) _ _

@[simp] theorem buildPlan_p0
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R) (I : Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).p0 = p0 := rfl

@[simp] theorem buildPlan_epsilon
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R) (I : Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).epsilon = alpha := rfl

@[simp] theorem buildPlan_radius
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R) (I : Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).radius = R := rfl

@[simp] theorem buildPlan_sourceBox
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R) (I : Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).sourceBox =
      I.sourceBox := rfl

@[simp] theorem buildPlan_activeBox
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R) (I : Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).activeBox =
      I.activeBox := rfl

@[simp] theorem buildPlan_target
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hlarge : 8 * scaleThreshold F ≤ R) (I : Instantiation F N R axis sigma) :
    (buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I).target = I.target := rfl

/-- Constructor form used by the macro geometry: all plan data remain definitionally visible. -/
theorem exists_rankOnePlan
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    {A R : Nat} (hA : 1 ≤ A)
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) A)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hR : N.R0 ≤ R) (hlarge : 8 * scaleThreshold F ≤ R)
    (I : Instantiation F N R axis sigma) :
    ∃ C : ExactTargetPlan.Plan d,
      C.WellFormed ∧ C.ValidAt p0 ∧ C.p0 = p0 ∧ C.epsilon = alpha ∧ C.radius = R ∧
      C.sourceBox = I.sourceBox ∧ C.activeBox = I.activeBox ∧ C.target = I.target ∧
      LongTargetAspect A C.radius axis sigma C.active C.source C.target := by
  let C := buildPlan hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hlarge I
  refine ⟨C, buildPlan_wellFormed hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hR hlarge I,
    buildPlan_validAt hp0 hp1 ha0 ha1 hA F N axis sigma hsigma hR hlarge I,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simpa [C, ExactTargetPlan.Plan.active, ExactTargetPlan.Plan.source] using I.longTarget

/-- Aspect `88`: the generic geometry clause is literally `CorrMove.LongTarget`. -/
theorem exists_rankOnePlan_88
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1) {R : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) 88)
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hR : N.R0 ≤ R) (hlarge : 8 * scaleThreshold F ≤ R)
    (I : Instantiation F N R axis sigma) :
    ∃ C : ExactTargetPlan.Plan d,
      C.WellFormed ∧ C.ValidAt p0 ∧ C.p0 = p0 ∧ C.epsilon = alpha ∧ C.radius = R ∧
      C.sourceBox = I.sourceBox ∧ C.activeBox = I.activeBox ∧ C.target = I.target ∧
      CorrMove.LongTarget (C.radius : Int) axis sigma C.active C.source C.target := by
  obtain ⟨C, hwf, hvalid, hp, he, hr, hs, ha, ht, hlong⟩ :=
    exists_rankOnePlan hp0 hp1 ha0 ha1 (by omega : 1 ≤ 88) F N axis sigma hsigma
      hR hlarge I
  exact ⟨C, hwf, hvalid, hp, he, hr, hs, ha, ht,
    (longTargetAspect_88_iff C.radius axis sigma C.active C.source C.target).1 hlong⟩

/-- Aspect `2*K`: the stopped-move specialization, still with the same transparent data. -/
theorem exists_rankOnePlan_two_mul
    {p0 : unitInterval} (hp0 : 0 < (p0 : Real)) (hp1 : (p0 : Real) < 1)
    {alpha : Real} (ha0 : 0 < alpha) (ha1 : alpha ≤ 1)
    (K : Nat) (hK : 1 ≤ K) {R : Nat}
    (F : ExactLongBoxVariablePlan.SchemeFamily d p0 (etaOf alpha) (2 * K))
    (N : Numbers d p0 alpha (sourceRadius F))
    (axis : Fin d) (sigma : Int) (hsigma : sigma = 1 ∨ sigma = -1)
    (hR : N.R0 ≤ R) (hlarge : 8 * scaleThreshold F ≤ R)
    (I : Instantiation F N R axis sigma) :
    ∃ C : ExactTargetPlan.Plan d,
      C.WellFormed ∧ C.ValidAt p0 ∧ C.p0 = p0 ∧ C.epsilon = alpha ∧ C.radius = R ∧
      C.sourceBox = I.sourceBox ∧ C.activeBox = I.activeBox ∧ C.target = I.target ∧
      LongTargetAspect (2 * K) C.radius axis sigma C.active C.source C.target := by
  exact exists_rankOnePlan hp0 hp1 ha0 ha1 (by omega) F N axis sigma hsigma hR hlarge I

end RankOne

end KNAll.Site.ExactLongBoxHitBridge

end

#print axioms KNAll.Site.ExactLongBoxHitBridge.VariableBridge.soundSetSource
#print axioms KNAll.Site.ExactLongBoxHitBridge.VariableBridge.translated_hit
#print axioms KNAll.Site.ExactLongBoxHitBridge.RankOne.exists_rankOnePlan
#print axioms KNAll.Site.ExactLongBoxHitBridge.RankOne.exists_rankOnePlan_88
#print axioms KNAll.Site.ExactLongBoxHitBridge.RankOne.exists_rankOnePlan_two_mul
