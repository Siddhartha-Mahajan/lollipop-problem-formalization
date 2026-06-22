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

/-- A one-sided nonnegative interval inside an open neighborhood of `0`. -/
theorem exists_nonneg_interval_subset_of_isOpen
    {U : Set ℝ} (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ δ → x ∈ U := by
  rcases (Metric.isOpen_iff.mp hU 0 h0) with ⟨δ, hδ, hsub⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x hx0 hx
  apply hsub
  rw [Metric.mem_ball, Real.dist_eq]
  have habs : |x - 0| = x := by
    simpa using abs_of_nonneg hx0
  rw [habs]
  nlinarith

/-- A strict chamber for one ordered distinct base pair persists on a small
rectangle of polynomial perturbation parameters. -/
theorem exists_intercluster_radius (r s : Fin 4) (hrs : r ≠ s) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : ℝ, 0 ≤ u → u ≤ δ → 0 ≤ v → v ≤ δ →
        RealizesStrictPairCode (interClusterCode r s)
          (PolynomialFamily.around (RationalBase.base r) u)
          (PolynomialFamily.around (RationalBase.base s) v) := by
  have hbase : RealizesStrictPairCode (interClusterCode r s)
      (RationalBase.base r) (RationalBase.base s) := by
    change RealizesStrictPairCode (RationalBase.baseCode r s)
      (RationalBase.base r) (RationalBase.base s)
    exact RationalBase.base_realizes_code hrs
  rcases exists_pair_chamber_neighborhood hbase with
    ⟨U, V, hU, hV, hbaseU, hbaseV, hsub⟩
  have hpreU : IsOpen
      {t : ℝ | PolynomialFamily.around (RationalBase.base r) t ∈ U} :=
    hU.preimage (PolynomialFamily.continuous_around (RationalBase.base r))
  have hpreV : IsOpen
      {t : ℝ | PolynomialFamily.around (RationalBase.base s) t ∈ V} :=
    hV.preimage (PolynomialFamily.continuous_around (RationalBase.base s))
  have h0U : (0 : ℝ) ∈
      {t : ℝ | PolynomialFamily.around (RationalBase.base r) t ∈ U} := by
    simpa using hbaseU
  have h0V : (0 : ℝ) ∈
      {t : ℝ | PolynomialFamily.around (RationalBase.base s) t ∈ V} := by
    simpa using hbaseV
  rcases exists_nonneg_interval_subset_of_isOpen hpreU h0U with
    ⟨δU, hδU, hsubU⟩
  rcases exists_nonneg_interval_subset_of_isOpen hpreV h0V with
    ⟨δV, hδV, hsubV⟩
  refine ⟨min δU δV, lt_min hδU hδV, ?_⟩
  intro u v hu0 hu hv0 hv
  exact hsub
    (PolynomialFamily.around (RationalBase.base r) u)
    (hsubU u hu0 (le_trans hu (min_le_left _ _)))
    (PolynomialFamily.around (RationalBase.base s) v)
    (hsubV v hv0 (le_trans hv (min_le_right _ _)))

/-- Uniform inter-cluster chamber radius for all ordered distinct base pairs. -/
theorem exists_uniform_intercluster_radius :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ (1 : ℝ) / 4 ∧
      ∀ r s : Fin 4, r ≠ s →
      ∀ u v : ℝ, 0 ≤ u → u ≤ ε → 0 ≤ v → v ≤ ε →
        RealizesStrictPairCode (interClusterCode r s)
          (PolynomialFamily.around (RationalBase.base r) u)
          (PolynomialFamily.around (RationalBase.base s) v) := by
  classical
  let δ : Fin 4 → Fin 4 → ℝ := fun r s =>
    if h : r = s then 1 else Classical.choose (exists_intercluster_radius r s h)
  have hδpos : ∀ r s : Fin 4, 0 < δ r s := by
    intro r s
    by_cases h : r = s
    · simp [δ, h]
    · simpa [δ, h] using
        (Classical.choose_spec (exists_intercluster_radius r s h)).1
  have hnonempty : (Finset.univ : Finset (Fin 4 × Fin 4)).Nonempty := by
    simp
  let ε := min ((1 : ℝ) / 4)
    (Finset.univ.inf' hnonempty
      (fun p : Fin 4 × Fin 4 => δ p.1 p.2 / 2))
  have hinfpos :
      0 < Finset.univ.inf' hnonempty
        (fun p : Fin 4 × Fin 4 => δ p.1 p.2 / 2) := by
    rw [Finset.lt_inf'_iff hnonempty]
    intro p _hp
    exact half_pos (hδpos p.1 p.2)
  have hεpos : 0 < ε := by
    exact lt_min (by norm_num) hinfpos
  refine ⟨ε, hεpos, min_le_left _ _, ?_⟩
  intro r s hrs u v hu0 hu hv0 hv
  have hεδ : ε ≤ δ r s / 2 := by
    exact le_trans (min_le_right _ _)
      (Finset.inf'_le _ (Finset.mem_univ (r, s)))
  have huδ : u ≤ δ r s := by
    nlinarith [hu, hεδ, hδpos r s]
  have hvδ : v ≤ δ r s := by
    nlinarith [hv, hεδ, hδpos r s]
  have hlocal :=
    (Classical.choose_spec (exists_intercluster_radius r s hrs)).2
  exact hlocal u v hu0 (by simpa [δ, hrs] using huδ)
    hv0 (by simpa [δ, hrs] using hvδ)

/-- Choose one uniform radius once and for all. -/
def epsilon : ℝ :=
  Classical.choose exists_uniform_intercluster_radius

@[simp] theorem epsilon_pos : 0 < epsilon :=
  (Classical.choose_spec exists_uniform_intercluster_radius).1

@[simp] theorem epsilon_le_quarter :
    epsilon ≤ (1 : ℝ) / 4 :=
  (Classical.choose_spec exists_uniform_intercluster_radius).2.1

/-- Concrete pre-arrangement before genericization. -/
def preArrangement {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    Arrangement n :=
  fun i => PolynomialFamily.around
    (RationalBase.base (clusterOf q hq i))
    (memberParameter epsilon q hq i)

/-- Oriented code of one pre-arrangement pair. -/
def pairCode {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i j : Fin n) : StrictPairCode :=
  if clusterOf q hq i = clusterOf q hq j then
    if memberParameter epsilon q hq i <
        memberParameter epsilon q hq j
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
      rw [if_pos hc', if_neg hnot, if_pos hc, if_pos hlt]
    · have hrev : memberParameter epsilon q hq j <
          memberParameter epsilon q hq i :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpne)
      rw [if_pos hc', if_pos hrev, if_pos hc, if_neg hlt,
        strictPairCode_swap_swap]
  · have hc' : clusterOf q hq j ≠ clusterOf q hq i := by
      exact fun h => hc h.symm
    rw [if_neg hc', if_neg hc]
    exact interClusterCode_swap (clusterOf q hq i) (clusterOf q hq j)

/-- Pair-code specification of one quadruple. -/
def codeSpec {n : ℕ} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    PairCodeSpec n where
  code := pairCode q hq
  swap := pairCode_swap q hq

/-- The constructed pre-arrangement realizes every intended strict pair
chamber. -/
theorem preArrangement_realizes_concrete {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    RealizesPairCodeSpec (codeSpec q hq) (preArrangement q hq) := by
  intro i j hij
  have hpi := memberParameter_bounds epsilon_pos q hq i
  have hpj := memberParameter_bounds epsilon_pos q hq j
  change RealizesStrictPairCode (pairCode q hq i j)
    (PolynomialFamily.around (RationalBase.base (clusterOf q hq i))
      (memberParameter epsilon q hq i))
    (PolynomialFamily.around (RationalBase.base (clusterOf q hq j))
      (memberParameter epsilon q hq j))
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · have hpne : memberParameter epsilon q hq i ≠
        memberParameter epsilon q hq j :=
      memberParameter_ne_of_same_cluster epsilon_pos q hq
        (ne_of_lt hij) hc
    by_cases hlt : memberParameter epsilon q hq i <
        memberParameter epsilon q hq j
    · rw [if_pos hc, if_pos hlt]
      rw [← hc]
      have hlocal := PolynomialFamily.local_realizes_four
        (le_of_lt hpi.1) hlt
        (le_trans (le_of_lt hpj.2) epsilon_le_quarter)
      have hmapped := (Lower.realizes_similarityTo_iff
        (RationalBase.base (clusterOf q hq i))
        StrictPairCode.four _ _).2 hlocal
      simpa [PolynomialFamily.around] using hmapped
    · rw [if_pos hc, if_neg hlt]
      rw [← hc]
      have hrev : memberParameter epsilon q hq j <
          memberParameter epsilon q hq i :=
        lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hpne)
      have hlocal := PolynomialFamily.local_realizes_four
        (le_of_lt hpj.1) hrev
        (le_trans (le_of_lt hpi.2) epsilon_le_quarter)
      have hmapped := (Lower.realizes_similarityTo_iff
        (RationalBase.base (clusterOf q hq i))
        StrictPairCode.four _ _).2 hlocal
      exact (realizes_swap_iff StrictPairCode.four _ _).1
        (by simpa [PolynomialFamily.around] using hmapped)
  · rw [if_neg hc]
    exact (Classical.choose_spec exists_uniform_intercluster_radius).2.2
      (clusterOf q hq i) (clusterOf q hq j) hc
      (memberParameter epsilon q hq i)
      (memberParameter epsilon q hq j)
      (le_of_lt hpi.1) (le_of_lt hpi.2)
      (le_of_lt hpj.1) (le_of_lt hpj.2)

/-- Numerical pair code is exactly Karlsson's symmetric cluster table. -/
theorem pairCode_crossings_eq_clusterTable {n : ℕ}
    (q : QuadVec n) (hq : q ∈ quadVecs n)
    (i j : Fin n) (_hij : i ≠ j) :
    (((pairCode q hq i j).crossings : ℕ) : ℚ) =
      karlssonClusterPairCrossing (clusterOf q hq i) (clusterOf q hq j) := by
  unfold pairCode
  by_cases hc : clusterOf q hq i = clusterOf q hq j
  · by_cases hlt : memberParameter epsilon q hq i <
    memberParameter epsilon q hq j
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
    (havoid : GenericityPort.GenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      IsGeneric A ∧
      ∀ i j : Fin n, i < j →
        pairCrossingCount (A i) (A j) =
          (pairCode q hq i j).crossings := by
  exact exists_generic_with_pairCrossingCounts_of_avoidance havoid
    (preArrangement_realizes_concrete q hq)

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
    (havoid : GenericityPort.GenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      IsGeneric A ∧
      ((totalCrossingsNat A : ℕ) : ℚ) = lowerCrossingsOfQuad q := by
  rcases exists_generic_blowUp havoid q hq with ⟨A, hgen, hpair⟩
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
    (hregion : ∀ {m : ℕ} {A : Arrangement m}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (m : ℚ) + 1)
    (havoid : GenericityPort.GenericityAvoidance n)
    (q : QuadVec n) (hq : q ∈ quadVecs n) :
    ∃ A : Arrangement n,
      regionCountRat A = lowerRegionsOfQuad q := by
  rcases exists_generic_crossings_eq_lowerCrossingsOfQuad havoid q hq with
    ⟨A, hgen, hcross⟩
  refine ⟨A, ?_⟩
  unfold lowerRegionsOfQuad
  rw [hregion hgen, hcross]

/-- Concrete lower realization in the existing algebraic interface. -/
theorem lowerRealization
    (hregion : ∀ {m : ℕ} {A : Arrangement m}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (m : ℚ) + 1)
    (havoid : ∀ n : ℕ, GenericityPort.GenericityAvoidance n) (n : ℕ) :
    LowerRealization (Arrangement n) regionCountRat n := by
  intro q hq
  exact exists_region_eq_lowerRegionsOfQuad hregion (havoid n) q hq

/-- Crossing-level concrete lower realization. -/
theorem lowerCrossingRealization
    (hregion : ∀ {m : ℕ} {A : Arrangement m}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (m : ℚ) + 1)
    (havoid : ∀ n : ℕ, GenericityPort.GenericityAvoidance n) (n : ℕ) :
    LowerCrossingRealization (Arrangement n) regionCountRat
      (fun A => ((totalCrossingsNat A : ℕ) : ℚ)) n := by
  intro q hq
  rcases exists_generic_crossings_eq_lowerCrossingsOfQuad (havoid n) q hq with
    ⟨A, hgen, hcross⟩
  refine ⟨A, hcross, ?_⟩
  exact hregion hgen

end BlowUp
end Lower
end EndToEnd
end Concrete
end Lollipop
