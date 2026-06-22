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
  have hsum := quadEntry_sum_eq_of_mem hq
  have hnonneg : ∀ s : Fin 4, (0 : ℚ) ≤ quadEntry q s := by
    intro s
    exact_mod_cast (q s).property.1
  have hr : quadEntry q r ≤ n := by
    rw [hsum]
    exact Finset.single_le_sum (fun s _ => hnonneg s) (Finset.mem_univ r)
  exact_mod_cast hr

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
  · nlinarith

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
    field_simp [hε0, hden0] at ht
    exact_mod_cast ht
  apply hij
  apply (quadClusterEquiv q hq).injective
  apply Sigma.ext hcluster
  apply Fin.ext
  exact hrank

/-- Crossing code determined only by two base clusters. -/
def interClusterCode (r s : Fin 4) : StrictPairCode :=
  RationalBase.baseCode r s

@[simp] theorem interClusterCode_swap (r s : Fin 4) :
    interClusterCode s r = (interClusterCode r s).swap :=
  RationalBase.baseCode_swap r s

/-- The numerical contribution of a base-cluster code is Karlsson's symmetric
`4/5/7` table for distinct clusters. -/
theorem interClusterCode_crossings
    {r s : Fin 4} (hrs : r ≠ s) :
    ((interClusterCode r s).crossings : ℚ) =
      karlssonClusterPairCrossing r s := by
  fin_cases r <;> fin_cases s <;>
    simp_all [interClusterCode, RationalBase.baseCode,
      StrictPairCode.crossings, StrictPairCode.four,
      StrictPairCode.five, StrictPairCode.seven,
      StrictPairCode.swap, karlssonClusterPairCrossing]

namespace BlowUpPort

/-- Uniform inter-cluster chamber radius.  This is a finite minimum argument:
for each of the twelve ordered distinct base pairs, continuity of `around` and
openness of the strict pair chamber give a positive rectangle around `(0,0)`;
take the minimum radius and `1/4`. -/
theorem exists_uniform_intercluster_radius :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ (1 : ℝ) / 4 ∧
      ∀ r s : Fin 4, r ≠ s →
      ∀ u v : ℝ, 0 ≤ u → u ≤ ε → 0 ≤ v → v ≤ ε →
        RealizesStrictPairCode (interClusterCode r s)
          (PolynomialFamily.around (RationalBase.base r) u)
          (PolynomialFamily.around (RationalBase.base s) v) := by
  classical
  have hbase : ∀ r s : Fin 4, r ≠ s →
      RealizesStrictPairCode (interClusterCode r s)
        (PolynomialFamily.around (RationalBase.base r) 0)
        (PolynomialFamily.around (RationalBase.base s) 0) := by
    intro r s hrs
    simpa [interClusterCode] using RationalBase.base_realizes_code hrs
  have hopen : ∀ r s : Fin 4, r ≠ s →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ u v : ℝ, |u| < δ → |v| < δ →
          RealizesStrictPairCode (interClusterCode r s)
            (PolynomialFamily.around (RationalBase.base r) u)
            (PolynomialFamily.around (RationalBase.base s) v) := by
    intro r s hrs
    have hU := isOpen_realizesStrictPairCode (interClusterCode r s)
    have hcont := (PolynomialFamily.continuous_around
      (RationalBase.base r)).prodMk
      (PolynomialFamily.continuous_around (RationalBase.base s))
    exact continuousAt_pair_mem_open_box hcont.continuousAt hU (hbase r s hrs)
  let δ : Fin 4 → Fin 4 → ℝ := fun r s =>
    if h : r = s then 1 else Classical.choose (hopen r s h)
  have hδ : ∀ r s : Fin 4, 0 < δ r s := by
    intro r s
    by_cases h : r = s
    · simp [δ, h]
    · exact (Classical.choose_spec (hopen r s h)).1
  let ε := min ((1 : ℝ) / 4)
    (Finset.univ.inf' (by simp : (Finset.univ : Finset (Fin 4 × Fin 4)).Nonempty)
      (fun p => δ p.1 p.2 / 2))
  have hε : 0 < ε := by
    exact min_pos (by norm_num)
      (Finset.inf'_pos (fun p hp => by positivity))
  refine ⟨ε, hε, min_le_left _ _, ?_⟩
  intro r s hrs u v hu0 hu hv0 hv
  have hεδ : ε ≤ δ r s / 2 := by
    exact le_trans (min_le_right _ _)
      (Finset.inf'_le _ (Finset.mem_univ (r,s)))
  have hu : |u| < δ r s := by
    rw [abs_of_nonneg hu0]
    nlinarith [hδ r s]
  have hv : |v| < δ r s := by
    rw [abs_of_nonneg hv0]
    nlinarith [hδ r s]
  exact (Classical.choose_spec (hopen r s hrs)).2 u v hu hv

/-- Positive similarities preserve every strict pair code. -/
theorem realizes_map_iff
    (S : PlaneSimilarity) (code : StrictPairCode) (L M : Lollipop) :
    RealizesStrictPairCode code (S.mapLollipop L) (S.mapLollipop M) ↔
      RealizesStrictPairCode code L M := by
  have houter : circleOuterMargin (S.mapLollipop L) (S.mapLollipop M) =
      S.scale ^ 2 * circleOuterMargin L M :=
    similarity_circleOuterMargin S L M
  have hinner : circleInnerMargin (S.mapLollipop L) (S.mapLollipop M) =
      S.scale ^ 2 * circleInnerMargin L M :=
    similarity_circleInnerMargin S L M
  have hdisc : ∀ X Y,
      lineDiscriminant (S.mapLollipop X) (S.mapLollipop Y) =
        S.scale ^ 2 * lineDiscriminant X Y :=
    similarity_lineDiscriminant S
  have hpower : ∀ X Y,
      anchorPower (S.mapLollipop X) (S.mapLollipop Y) =
        S.scale ^ 2 * anchorPower X Y :=
    similarity_anchorPower S
  have hvertex : ∀ X Y,
      vertexAhead (S.mapLollipop X) (S.mapLollipop Y) =
        S.scale * vertexAhead X Y :=
    similarity_vertexAhead S
  have hdet : directionDet (S.mapLollipop L) (S.mapLollipop M) = 0 ↔
      directionDet L M = 0 :=
    similarity_directionDet_eq_zero_iff S L M
  have hleft : leftLineParameter (S.mapLollipop L) (S.mapLollipop M) -
      (S.mapLollipop L).radius =
      S.scale * (leftLineParameter L M - L.radius) :=
    similarity_leftParameterMargin S L M
  have hright : rightLineParameter (S.mapLollipop L) (S.mapLollipop M) -
      (S.mapLollipop M).radius =
      S.scale * (rightLineParameter L M - M.radius) :=
    similarity_rightParameterMargin S L M
  unfold RealizesStrictPairCode MixedCode.Realized RayRayCodeRealized
  simp only [houter, hinner, hdisc, hpower, hvertex, hdet, hleft, hright]
  positivity

end BlowUpPort

/-- Choose one uniform radius once and for all. -/
def epsilon : ℝ := Classical.choose BlowUpPort.exists_uniform_intercluster_radius

@[simp] theorem epsilon_pos : 0 < epsilon :=
  (Classical.choose_spec BlowUpPort.exists_uniform_intercluster_radius).1

@[simp] theorem epsilon_le_quarter : epsilon ≤ (1 : ℝ) / 4 :=
  (Classical.choose_spec BlowUpPort.exists_uniform_intercluster_radius).2.1

/-- Concrete pre-arrangement before genericization. -/
def preArrangement {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    Arrangement n :=
  fun i => PolynomialFamily.around
    (RationalBase.base (clusterOf q hq i))
    (memberParameter epsilon q hq i)

/-- Oriented code of one pre-arrangement pair. -/
def pairCode {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i j : Fin n) : StrictPairCode :=
  if hcluster : clusterOf q hq i = clusterOf q hq j then
    if memberParameter epsilon q hq i < memberParameter epsilon q hq j
    then StrictPairCode.four
    else StrictPairCode.four.swap
  else interClusterCode (clusterOf q hq i) (clusterOf q hq j)

@[simp] theorem pairCode_swap {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) (i j : Fin n)
    (hij : i ≠ j) :
    pairCode q hq j i = (pairCode q hq i j).swap := by
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · have hc' : clusterOf q hq j = clusterOf q hq i := hc.symm
    have hpne : memberParameter epsilon q hq i ≠
        memberParameter epsilon q hq j :=
      memberParameter_ne_of_same_cluster epsilon_pos q hq hij hc
    by_cases hlt : memberParameter epsilon q hq i <
        memberParameter epsilon q hq j
    · have hnot : ¬ memberParameter epsilon q hq j <
          memberParameter epsilon q hq i := not_lt_of_ge (le_of_lt hlt)
      simp [hc, hc', hlt, hnot, StrictPairCode.swap]
    · have hrev : memberParameter epsilon q hq j <
          memberParameter epsilon q hq i :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpne)
      simp [hc, hc', hlt, hrev, StrictPairCode.swap]
  · have hc' : clusterOf q hq j ≠ clusterOf q hq i := by
      exact fun h => hc h.symm
    simp [hc, hc', interClusterCode_swap]

/-- Pair-code specification of one quadruple. -/
def codeSpec {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    PairCodeSpec n where
  code := pairCode q hq
  swap := pairCode_swap q hq

/-- The pre-arrangement realizes every intended pair chamber. -/
theorem preArrangement_realizes {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    RealizesPairCodeSpec (codeSpec q hq) (preArrangement q hq) := by
  intro i j hij
  have hpi := memberParameter_bounds epsilon_pos q hq i
  have hpj := memberParameter_bounds epsilon_pos q hq j
  unfold codeSpec pairCode preArrangement
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · simp only [hc, dite_true]
    have hpne : memberParameter epsilon q hq i ≠
        memberParameter epsilon q hq j :=
      memberParameter_ne_of_same_cluster epsilon_pos q hq
        (ne_of_lt hij) hc
    by_cases hlt : memberParameter epsilon q hq i <
        memberParameter epsilon q hq j
    · simp [hlt]
      apply (BlowUpPort.realizes_map_iff
        (similarityTo (RationalBase.base (clusterOf q hq i)))
        StrictPairCode.four _ _).2
      exact PolynomialFamily.local_realizes_four
        (le_of_lt hpi.1) hlt
        (le_trans (le_of_lt hpj.2) epsilon_le_quarter)
    · have hrev : memberParameter epsilon q hq j <
          memberParameter epsilon q hq i :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpne)
      simp [hlt]
      have hforward := PolynomialFamily.local_realizes_four
        (le_of_lt hpj.1) hrev
        (le_trans (le_of_lt hpi.2) epsilon_le_quarter)
      have hmapped := (BlowUpPort.realizes_map_iff
        (similarityTo (RationalBase.base (clusterOf q hq i)))
        StrictPairCode.four _ _).2 hforward
      exact (realizes_swap_iff StrictPairCode.four _ _).1 hmapped
  · simp only [hc, dite_false]
    exact (Classical.choose_spec BlowUpPort.exists_uniform_intercluster_radius).2.2
      (clusterOf q hq i) (clusterOf q hq j) hc
      (memberParameter epsilon q hq i)
      (memberParameter epsilon q hq j)
      (le_of_lt hpi.1) (le_of_lt hpi.2)
      (le_of_lt hpj.1) (le_of_lt hpj.2)

/-- Numerical pair code is exactly Karlsson's symmetric cluster table. -/
theorem pairCode_crossings_eq_clusterTable {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i j : Fin n) (hij : i ≠ j) :
    (((pairCode q hq i j).crossings : ℕ) : ℚ) =
      karlssonClusterPairCrossing (clusterOf q hq i) (clusterOf q hq j) := by
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · simp [hc, StrictPairCode.crossings_swap]
  · simp [hc]
    exact interClusterCode_crossings hc

/-- Generic concrete realization of one admissible quadruple. -/
theorem exists_generic_blowUp {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      IsGeneric A ∧
      ∀ i j : Fin n, i < j →
        pairCrossingCount (A i) (A j) =
          (pairCode q hq i j).crossings := by
  exact exists_generic_with_pairCrossingCounts
    (preArrangement_realizes q hq)

/-- The generic blow-up crossing sum is exactly the existing clustered table. -/
theorem totalCrossingsRat_eq_clusteredTable {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    {A : Arrangement n} (hpair : ∀ i j : Fin n, i < j →
      pairCrossingCount (A i) (A j) = (pairCode q hq i j).crossings) :
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
  exact pairCode_crossings_eq_clusterTable q hq p.1 p.2 (ne_of_lt hp_lt)

/-- Exact lower crossing total for one admissible quadruple. -/
theorem exists_generic_crossings_eq_lowerCrossingsOfQuad {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      IsGeneric A ∧
      ((totalCrossingsNat A : ℕ) : ℚ) = lowerCrossingsOfQuad q := by
  rcases exists_generic_blowUp q hq with ⟨A, hgen, hpair⟩
  refine ⟨A, hgen, ?_⟩
  calc
    ((totalCrossingsNat A : ℕ) : ℚ) =
        clusteredKarlssonPairTableCrossings (clusterOf q hq) :=
      totalCrossingsRat_eq_clusteredTable q hq hpair
    _ = karlssonClusterTableCrossingsOfQuad q := by
      exact (cardinalityClusteredKarlssonTableWitnessOfQuad q hq).pairSum_eq_table
    _ = lowerCrossingsOfQuad q :=
      karlssonClusterTableCrossingsOfQuad_eq_lowerCrossingsOfQuad q

/-- Exact generic region equation for one admissible quadruple. -/
theorem exists_region_eq_lowerRegionsOfQuad {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      regionCountRat A = lowerRegionsOfQuad q := by
  rcases exists_generic_crossings_eq_lowerCrossingsOfQuad q hq with
    ⟨A, hgen, hcross⟩
  refine ⟨A, ?_⟩
  have hregion := regionCount_eq_crossings_add hgen
  unfold regionCountRat lowerRegionsOfQuad
  exact_mod_cast (show (regionCount A : ℚ) =
      lowerCrossingsOfQuad q + (n : ℚ) + 1 by
    rw [show (regionCount A : ℚ) =
      (totalCrossingsNat A : ℚ) + n + 1 by exact_mod_cast hregion,
      hcross])

/-- Concrete lower realization in the existing algebraic interface. -/
theorem lowerRealization (n : ℕ) :
    LowerRealization (Arrangement n) regionCountRat n := by
  intro q hq
  exact exists_region_eq_lowerRegionsOfQuad q hq

/-- Crossing-level concrete lower realization. -/
theorem lowerCrossingRealization (n : ℕ) :
    LowerCrossingRealization (Arrangement n) regionCountRat
      (fun A => ((totalCrossingsNat A : ℕ) : ℚ)) n := by
  intro q hq
  rcases exists_generic_crossings_eq_lowerCrossingsOfQuad q hq with
    ⟨A, hgen, hcross⟩
  refine ⟨A, hcross, ?_⟩
  have hregion := regionCount_eq_crossings_add hgen
  unfold regionCountRat
  exact_mod_cast hregion

end BlowUp
end Lower
end EndToEnd
end Concrete
end Lollipop
