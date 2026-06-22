import Lollipop.Concrete.EndToEnd.Lower.Genericity
import Lollipop.Internal.Manuscript.Construction.AutomaticCardinalityWitness
import Lollipop.Internal.Manuscript.ExplicitInputs.PairwiseLower
import Mathlib.Tactic

/-!
# Four-cluster blow-up

This file combines:

1. the exact rational four-lollipop base;
2. the corrected polynomial four-crossing family inside each cluster;
3. openness of all strict inter-cluster pair chambers;
4. genericization without changing any pair count;
5. the repository's existing finite cluster-cardinality algebra.

The result is a concrete `LowerCrossingRealization` for every admissible
quadruple, with no caller-supplied geometry certificate.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Lower
namespace BlowUp

open Set BigOperators
open TheoremOneManuscript ExplicitInputs

/-- Canonical cluster label supplied by the existing finite equivalence. -/
def clusterOf {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    Fin n → Fin 4 :=
  canonicalQuadCluster q hq

/-- Position of a member inside its canonical cluster. -/
def rankOf {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i : Fin n) : ℕ :=
  (quadClusterEquiv q hq i).2.1

@[simp] theorem clusterOf_eq_first {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i : Fin n) :
    clusterOf q hq i = (quadClusterEquiv q hq i).1 := rfl

/-- Rank is strictly smaller than its cluster size. -/
theorem rankOf_lt_clusterSize {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i : Fin n) :
    rankOf q hq i < (q (clusterOf q hq i) : ℕ) :=
  (quadClusterEquiv q hq i).2.2

/-- Every cluster size is at most the total size. -/
theorem clusterSize_le_n {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) (r : Fin 4) :
    (q r : ℕ) ≤ n := by
  have hsum : (∑ s : Fin 4, quadEntry q s) = (n : ℚ) := by
    simpa [Fin.sum_univ_four] using quadEntry_sum_eq_of_mem hq
  have hnonneg : ∀ s : Fin 4, (0 : ℚ) ≤ quadEntry q s := by
    intro s
    unfold quadEntry
    positivity
  have hr : quadEntry q r ≤ n := by
    have hle : quadEntry q r ≤ ∑ s : Fin 4, quadEntry q s :=
      Finset.single_le_sum (fun s _ => hnonneg s) (Finset.mem_univ r)
    rwa [hsum] at hle
  have hr' : (((q r : ℕ) : ℚ) ≤ (n : ℚ)) := by
    simpa [quadEntry] using hr
  exact_mod_cast hr'

/-- A small, distinct positive parameter for each member. -/
def memberParameter {n : ℕ}
    (ε : ℝ) (q : QuadVec n) (hq : q ∈ quadVecs n) (i : Fin n) : ℝ :=
  ε * ((rankOf q hq i + 1 : ℕ) : ℝ) / (n + 1 : ℕ)

/-- Member parameters lie in `(0,ε)` when `ε>0`. -/
theorem memberParameter_bounds {n : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i : Fin n) :
    0 < memberParameter ε q hq i ∧
      memberParameter ε q hq i < ε := by
  have hrank := rankOf_lt_clusterSize q hq i
  have hsize := clusterSize_le_n q hq (clusterOf q hq i)
  have hnum : rankOf q hq i + 1 ≤ n := by omega
  have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hratio0 : 0 < (((rankOf q hq i + 1 : ℕ) : ℝ) /
      (n + 1 : ℕ)) := by positivity
  have hratio1 : (((rankOf q hq i + 1 : ℕ) : ℝ) /
      (n + 1 : ℕ)) < 1 := by
    rw [div_lt_one hden]
    exact_mod_cast (Nat.lt_succ_of_le hnum)
  unfold memberParameter
  constructor
  · positivity
  · have hlt : ε *
        ((((rankOf q hq i + 1 : ℕ) : ℝ) / (n + 1 : ℕ))) < ε :=
      mul_lt_of_lt_one_right hε hratio1
    simpa [mul_div_assoc] using hlt

/-- Two different members in the same cluster receive different parameters. -/
theorem memberParameter_ne_of_same_cluster {n : ℕ}
    {ε : ℝ} (hε : 0 < ε)
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    {i j : Fin n} (hij : i ≠ j)
    (hcluster : clusterOf q hq i = clusterOf q hq j) :
    memberParameter ε q hq i ≠ memberParameter ε q hq j := by
  intro ht
  have hrank : rankOf q hq i = rankOf q hq j := by
    unfold memberParameter at ht
    have hε0 : ε ≠ 0 := hε.ne'
    have hden0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have ht' :
        ε * ((((rankOf q hq i + 1 : ℕ) : ℝ) / (n + 1 : ℕ))) =
          ε * ((((rankOf q hq j + 1 : ℕ) : ℝ) / (n + 1 : ℕ))) := by
      simpa [mul_div_assoc] using ht
    have hratio :
        (((rankOf q hq i + 1 : ℕ) : ℝ) / (n + 1 : ℕ)) =
          (((rankOf q hq j + 1 : ℕ) : ℝ) / (n + 1 : ℕ)) :=
      mul_left_cancel₀ hε0 ht'
    rw [div_left_inj' hden0] at hratio
    exact Nat.succ.inj (Nat.cast_injective hratio)
  apply hij
  apply (quadClusterEquiv q hq).injective
  change (quadClusterEquiv q hq i).1 = (quadClusterEquiv q hq j).1 at hcluster
  change (quadClusterEquiv q hq i).2.1 =
    (quadClusterEquiv q hq j).2.1 at hrank
  rcases hxi : quadClusterEquiv q hq i with ⟨ri, ki⟩
  rcases hxj : quadClusterEquiv q hq j with ⟨rj, kj⟩
  rw [hxi, hxj] at hcluster hrank
  dsimp at hcluster hrank ⊢
  subst rj
  congr
  exact Fin.ext hrank

/-- Crossing code determined only by two base clusters. -/
def interClusterCode (r s : Fin 4) : StrictPairCode :=
  RationalBase.baseCode r s

theorem interClusterCode_swap (r s : Fin 4) :
    interClusterCode s r = (interClusterCode r s).swap :=
  RationalBase.baseCode_swap r s

/-- The numerical contribution of a base-cluster code is Karlsson's symmetric
`4/5/7` table for distinct clusters. -/
theorem interClusterCode_crossings
    {r s : Fin 4} (hrs : r ≠ s) :
    ((interClusterCode r s).crossings : ℚ) =
      karlssonClusterPairCrossing r s := by
  fin_cases r <;> fin_cases s <;>
    first
    | contradiction
    | norm_num [interClusterCode, RationalBase.baseCode,
        StrictPairCode.crossings, StrictPairCode.five,
        StrictPairCode.seven, StrictPairCode.swap,
        MixedCode.crossings, karlssonClusterPairCrossing]

@[simp] theorem strictPairCode_swap_swap (code : StrictPairCode) :
    code.swap.swap = code := by
  rcases code with ⟨left, right, rayRay⟩
  rfl

@[simp] theorem strictPairCode_four_swap_crossings :
    StrictPairCode.four.swap.crossings = 4 := by
  rfl

/-- Remaining theorem package for the concrete blow-up layer.

The fields are concrete statements, not project axioms.  They name the exact
facts still to prove in this file: a uniform strict inter-cluster chamber,
similarity invariance of strict pair codes, and the generic Euler/region
equation supplied by planar topology. -/
structure BlowUpPorts : Prop where
  uniform_intercluster_radius :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ (1 : ℝ) / 4 ∧
      ∀ r s : Fin 4, r ≠ s →
      ∀ u v : ℝ, 0 ≤ u → u ≤ ε → 0 ≤ v → v ≤ ε →
        RealizesStrictPairCode (interClusterCode r s)
          (PolynomialFamily.around (RationalBase.base r) u)
          (PolynomialFamily.around (RationalBase.base s) v)
  realizes_map_iff :
    ∀ (S : PlaneSimilarity) (code : StrictPairCode) (L M : Lollipop),
    RealizesStrictPairCode code (S.mapLollipop L) (S.mapLollipop M) ↔
      RealizesStrictPairCode code L M
  generic_region_eq :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1

/-- Choose one uniform radius once and for all. -/
def epsilon (P : BlowUpPorts) : ℝ :=
  Classical.choose P.uniform_intercluster_radius

@[simp] theorem epsilon_pos (P : BlowUpPorts) : 0 < epsilon P :=
  (Classical.choose_spec P.uniform_intercluster_radius).1

@[simp] theorem epsilon_le_quarter (P : BlowUpPorts) :
    epsilon P ≤ (1 : ℝ) / 4 :=
  (Classical.choose_spec P.uniform_intercluster_radius).2.1

/-- Concrete pre-arrangement before genericization. -/
def preArrangement (P : BlowUpPorts)
    {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    Arrangement n :=
  fun i => PolynomialFamily.around
    (RationalBase.base (clusterOf q hq i))
    (memberParameter (epsilon P) q hq i)

/-- Oriented code of one pre-arrangement pair. -/
def pairCode (P : BlowUpPorts)
    {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i j : Fin n) : StrictPairCode :=
  if clusterOf q hq i = clusterOf q hq j then
    if memberParameter (epsilon P) q hq i <
        memberParameter (epsilon P) q hq j
    then StrictPairCode.four
    else StrictPairCode.four.swap
  else interClusterCode (clusterOf q hq i) (clusterOf q hq j)

@[simp] theorem pairCode_swap {n : ℕ}
    (P : BlowUpPorts)
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i j : Fin n)
    (hij : i ≠ j) :
    pairCode P q hq j i = (pairCode P q hq i j).swap := by
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · have hc' : clusterOf q hq j = clusterOf q hq i := hc.symm
    have hpne : memberParameter (epsilon P) q hq i ≠
        memberParameter (epsilon P) q hq j :=
      memberParameter_ne_of_same_cluster (epsilon_pos P) q hq hij hc
    by_cases hlt : memberParameter (epsilon P) q hq i <
        memberParameter (epsilon P) q hq j
    · have hnot : ¬ memberParameter (epsilon P) q hq j <
          memberParameter (epsilon P) q hq i := not_lt_of_ge (le_of_lt hlt)
      rw [if_pos hc', if_neg hnot, if_pos hc, if_pos hlt]
    · have hrev : memberParameter (epsilon P) q hq j <
          memberParameter (epsilon P) q hq i :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpne)
      rw [if_pos hc', if_pos hrev, if_pos hc, if_neg hlt,
        strictPairCode_swap_swap]
  · have hc' : clusterOf q hq j ≠ clusterOf q hq i := by
      exact fun h => hc h.symm
    rw [if_neg hc', if_neg hc]
    exact interClusterCode_swap (clusterOf q hq i) (clusterOf q hq j)

/-- Pair-code specification of one quadruple. -/
def codeSpec (P : BlowUpPorts)
    {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    PairCodeSpec n where
  code := pairCode P q hq
  swap := pairCode_swap P q hq

/-- The exact remaining realization theorem for the blow-up pre-arrangement.

This is separated from `BlowUpPorts` because it depends on the canonical
quadruple indexing functions defined above.  It is still a concrete theorem
target: for every admissible quadruple, the constructed pre-arrangement lies in
the intended strict pair-code chamber. -/
structure BlowUpRealizationPorts (P : BlowUpPorts) : Prop where
  preArrangement_realizes :
    ∀ {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n),
      RealizesPairCodeSpec (codeSpec P q hq) (preArrangement P q hq)

/-- Numerical pair code is exactly Karlsson's symmetric cluster table. -/
theorem pairCode_crossings_eq_clusterTable {n : ℕ}
    (P : BlowUpPorts)
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i j : Fin n) (_hij : i ≠ j) :
    (((pairCode P q hq i j).crossings : ℕ) : ℚ) =
      karlssonClusterPairCrossing (clusterOf q hq i) (clusterOf q hq j) := by
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · by_cases hlt : memberParameter (epsilon P) q hq i <
    memberParameter (epsilon P) q hq j
    · rw [if_pos hc, if_pos hlt]
      rw [hc]
      simp [karlssonClusterPairCrossing]
    · rw [if_pos hc, if_neg hlt]
      rw [hc]
      simp [karlssonClusterPairCrossing]
  · rw [if_neg hc]
    exact interClusterCode_crossings hc

/-- Generic concrete realization of one admissible quadruple. -/
theorem exists_generic_blowUp {n : ℕ}
    (P : BlowUpPorts)
    (R : BlowUpRealizationPorts P)
    (havoid : GenericityPort.GenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      IsGeneric A ∧
      ∀ i j : Fin n, i < j →
        pairCrossingCount (A i) (A j) =
          (pairCode P q hq i j).crossings := by
  exact exists_generic_with_pairCrossingCounts_of_avoidance havoid
    (R.preArrangement_realizes q hq)

/-- The generic blow-up crossing sum is exactly the existing clustered table. -/
theorem totalCrossingsRat_eq_clusteredTable {n : ℕ}
    (P : BlowUpPorts)
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    {A : Arrangement n} (hpair : ∀ i j : Fin n, i < j →
      pairCrossingCount (A i) (A j) = (pairCode P q hq i j).crossings) :
    ((totalCrossingsNat A : ℕ) : ℚ) =
      clusteredKarlssonPairTableCrossings (clusterOf q hq) := by
  unfold totalCrossingsNat clusteredKarlssonPairTableCrossings pairSum
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_lt : p.1 < p.2 := by
    rw [pairFinset, Finset.mem_filter] at hp
    exact hp.2
  rw [hpair p.1 p.2 hp_lt]
  exact pairCode_crossings_eq_clusterTable P q hq p.1 p.2 (ne_of_lt hp_lt)

/-- Exact lower crossing total for one admissible quadruple. -/
theorem exists_generic_crossings_eq_lowerCrossingsOfQuad {n : ℕ}
    (P : BlowUpPorts)
    (R : BlowUpRealizationPorts P)
    (havoid : GenericityPort.GenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      IsGeneric A ∧
      ((totalCrossingsNat A : ℕ) : ℚ) = lowerCrossingsOfQuad q := by
  rcases exists_generic_blowUp P R havoid q hq with ⟨A, hgen, hpair⟩
  refine ⟨A, hgen, ?_⟩
  calc
    ((totalCrossingsNat A : ℕ) : ℚ) =
        clusteredKarlssonPairTableCrossings (clusterOf q hq) :=
      totalCrossingsRat_eq_clusteredTable P q hq hpair
    _ = karlssonClusterTableCrossingsOfQuad q := by
      exact (cardinalityClusteredKarlssonTableWitnessOfQuad q hq).pairSum_eq_table
    _ = lowerCrossingsOfQuad q :=
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q

/-- Exact generic region equation for one admissible quadruple. -/
theorem exists_region_eq_lowerRegionsOfQuad {n : ℕ}
    (P : BlowUpPorts)
    (R : BlowUpRealizationPorts P)
    (havoid : GenericityPort.GenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      regionCountRat A = lowerRegionsOfQuad q := by
  rcases exists_generic_crossings_eq_lowerCrossingsOfQuad P R havoid q hq with
    ⟨A, hgen, hcross⟩
  refine ⟨A, ?_⟩
  unfold lowerRegionsOfQuad
  rw [P.generic_region_eq hgen, hcross]

/-- Concrete lower realization in the existing algebraic interface. -/
theorem lowerRealization (P : BlowUpPorts) (R : BlowUpRealizationPorts P)
    (havoid : ∀ n : ℕ, GenericityPort.GenericityAvoidance n) (n : ℕ) :
    LowerRealization (Arrangement n) regionCountRat n := by
  intro q hq
  exact exists_region_eq_lowerRegionsOfQuad P R (havoid n) q hq

/-- Crossing-level concrete lower realization. -/
theorem lowerCrossingRealization (P : BlowUpPorts)
    (R : BlowUpRealizationPorts P)
    (havoid : ∀ n : ℕ, GenericityPort.GenericityAvoidance n) (n : ℕ) :
    LowerCrossingRealization (Arrangement n) regionCountRat
      (fun A => ((totalCrossingsNat A : ℕ) : ℚ)) n := by
  intro q hq
  rcases exists_generic_crossings_eq_lowerCrossingsOfQuad P R (havoid n) q hq with
    ⟨A, hgen, hcross⟩
  refine ⟨A, hcross, ?_⟩
  exact P.generic_region_eq hgen

end BlowUp
end Lower
end EndToEnd
end Concrete
end Lollipop
